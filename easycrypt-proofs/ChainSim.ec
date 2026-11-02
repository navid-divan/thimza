require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

module Fz = {
  var fz : (request * int, vec * vec) fmap
}.

op pkey (a b : int) (d : view) : (pidx * pidx) * view =
  ((toidx (if a < b then a else b), toidx (if a < b then b else a)), d).

op sgnv (a b : int) (v : vec) : vec = if a < b then v else - v.

op hmask (m : ((pidx * pidx) * view, vec) fmap) (d : view) (H : int list) (a : int) : vec =
  vmap (fun b => sgnv a b (oget m.[pkey a b d])) (filter (fun b => b <> a) H).

module SOFs (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) : SOr = {
  proc o1 = SOF(MPI, H0h, H1).o1
  proc o2 = SOF(MPI, H0h, H1).o2

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f, vv;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <@ SOF(MPI, H0h, H1).h1hon(e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ SOF(MPI, H0h, H1).h0any((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
            okk <- okk /\ y = nth witness cs k;
            k <- k + 1;
          }
          if (okk) {
            c <- HCO.QRO.fh (liftw (aggw ws), (S.t, tok.`tk_msg));
            ys <- filter (fun j => j <> tok.`tk_i /\ hpair S.cs tok.`tk_i j
                                   /\ !((oget S.req.[u], j) \in S.lr)) T;
            mkh <- RqVec.Vector.zerov;
            mkc <- RqVec.Vector.zerov;
            k <- 0;
            while (k < size T) {
              j <- nth 0 T k;
              if (j <> tok.`tk_i /\ !(ys <> [] /\ j = head 0 ys)) {
                if (hpair S.cs tok.`tk_i j) {
                  v <@ MPI.f(if tok.`tk_i < j then tok.`tk_i else j,
                             if tok.`tk_i < j then j else tok.`tk_i, d);
                  mkh <- mkh + (if tok.`tk_i < j then v else - v);
                } else {
                  v <- prf (S.sdc (toidx (if tok.`tk_i < j then tok.`tk_i else j),
                                   toidx (if tok.`tk_i < j then j else tok.`tk_i))) d;
                  mkc <- mkc + (if tok.`tk_i < j then v else - v);
                }
              }
              k <- k + 1;
            }
            f <- (Rq.( * ) c (lam_of T tok.`tk_i)) ** shr S.s S.p tok.`tk_i + tok.`tk_r + mkc;
            if ((oget S.req.[u], tok.`tk_i) \in S.lr) {
              z <- (oget Fz.fz.[(oget S.req.[u], tok.`tk_i)]).`1 + f
                   - (oget Fz.fz.[(oget S.req.[u], tok.`tk_i)]).`2;
            } else {
              if (ys <> []) {
                j <- head 0 ys;
                z <$ dvec;
                vv <- z - f - mkh;
                MPI.m.[pkey tok.`tk_i j d] <- sgnv tok.`tk_i j vv;
              } else {
                z <- f + vmap (fun a => (oget Fz.fz.[(oget S.req.[u], a)]).`2
                                        - (oget Fz.fz.[(oget S.req.[u], a)]).`1)
                              (filter (fun a => a <> tok.`tk_i) (honest T S.cs));
              }
              Fz.fz.[(oget S.req.[u], tok.`tk_i)] <- (z, f);
            }
            S.toks.[u] <- erase tok;
            S.lr <- (oget S.req.[u], tok.`tk_i) :: S.lr;
            out <- Some z;
          }
        }
      }
    }
    return out;
  }
}.

module GameFs (A : Adv) (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOF(H0h, H1)), CntO(SOFs(H0h, H1))).corrupt();
    S.s <$ dskey;
    S.e <$ dekey;
    S.p <$ dpoly;
    S.t <- rndkey (mulA mA S.s + S.e);
    S.sdc <$ dseedf;
    S.toks <- empty;
    S.req <- empty;
    S.ctr <- 0;
    S.lo <- [];
    S.lr <- [];
    Lg.l0 <- [];
    Lg.l1 <- [];
    Fz.fz <- empty;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOF(H0h, H1)), CntO(SOFs(H0h, H1))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

module G1s (A : Adv) = {
  proc main() : bool = {
    var b;
    MPI.init();
    H0H.QRO.init();
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameFs(A, H0H.QRO, H1O.QRO).run();
    return b;
  }
}.

(* Pair keys ignore the order *)
lemma pkey_sym (a b : int) (d : view) : pkey a b d = pkey b a d.
proof. by rewrite /pkey; smt(). qed.

(* Pair keys of valid indices determine the pair *)
lemma pkey_inj (a b c e : int) (d d' : view) :
  1 <= a <= nmax => 1 <= b <= nmax => 1 <= c <= nmax => 1 <= e <= nmax =>
  pkey a b d = pkey c e d' => d = d' /\ ((a = c /\ b = e) \/ (a = e /\ b = c)).
proof.
move=> ha hb hc he; rewrite /pkey /= => -[#] h1 h2 ->.
have h1' : (if a < b then a else b) = (if c < e then c else e).
+ by have := congr1 PIdx.val _ _ h1; rewrite toidxK 1:/# toidxK /#.
have h2' : (if a < b then b else a) = (if c < e then e else c).
+ by have := congr1 PIdx.val _ _ h2; rewrite toidxK 1:/# toidxK /#.
smt().
qed.

(* Signs are involutive *)
lemma sgnvK (a b : int) (v : vec) : sgnv a b (sgnv a b v) = v.
proof. by rewrite /sgnv; case: (a < b) => //= _; rewrite RqVec.Vector.ZModule.opprK. qed.

(* Opposite signs cancel *)
lemma sgnv_anti (a b : int) (v : vec) : a <> b => sgnv a b v + sgnv b a v = RqVec.Vector.zerov.
proof.
move=> hne; rewrite /sgnv; case: (a < b) => hab.
+ have -> /= : !(b < a) by smt().
  by rewrite RqVec.Vector.ZModule.addrN.
have -> /= : b < a by smt().
by rewrite RqVec.Vector.ZModule.addNr.
qed.

(* Filtered sums are guarded sums *)
lemma vmap_filter (f : 'a -> vec) (p : 'a -> bool) (L : 'a list) :
  vmap f (filter p L) = vmap (fun x => if p x then f x else RqVec.Vector.zerov) L.
proof.
elim L => [| a L ih] /=; first by rewrite !vmap_nil.
case: (p a) => hp.
+ by rewrite !vmap_cons /= hp /= ih.
by rewrite vmap_cons /= hp /= ih RqVec.Vector.ZModule.add0r.
qed.

(* Sums commute with negation *)
lemma vmap_opp (f : 'a -> vec) (L : 'a list) :
  vmap (fun x => - f x) L = - vmap f L.
proof.
elim L => [| a L ih]; first by rewrite !vmap_nil RqVec.Vector.ZModule.oppr0.
by rewrite !vmap_cons /= ih RqVec.Vector.ZModule.opprD.
qed.

(* Honest masks are guarded committee sums *)
lemma hmask_T (m : ((pidx * pidx) * view, vec) fmap) (d : view) (T : committee)
              (C : corrset) (i : int) :
  !(i \in C) =>
  hmask m d (honest T C) i
  = vmap (fun b => if b <> i /\ hpair C i b then sgnv i b (oget m.[pkey i b d]) else RqVec.Vector.zerov) T.
proof.
move=> hi; rewrite /hmask /honest -filter_predI vmap_filter.
by apply vmap_eq => b _ /=; rewrite /predI /hpair hi.
qed.

(* The designated partner completes a guarded sum *)
lemma vmap_desig (g : int -> vec) (P : int -> bool) (T : int list) (j : int) :
  uniq T => j \in T => P j =>
  vmap (fun b => if P b /\ b <> j then g b else RqVec.Vector.zerov) T + g j
  = vmap (fun b => if P b then g b else RqVec.Vector.zerov) T.
proof.
move=> + + hp; elim: T => [| a T ih] //= [ha hu] hj.
rewrite !vmap_cons /=.
case: (a = j) => [<<- | hne].
+ have -> : vmap (fun b => if P b /\ b <> a then g b else RqVec.Vector.zerov) T
          = vmap (fun b => if P b then g b else RqVec.Vector.zerov) T.
  - apply vmap_eq => b hb /=.
    have -> // : b <> a.
    by apply/negP => e; move: ha; rewrite -e hb.
  rewrite hp /= RqVec.Vector.ZModule.addrC; congr.
  exact RqVec.Vector.ZModule.add0r.
have hjT : j \in T by case: hj => [e | //]; move: hne; rewrite e.
by rewrite /= -(ih hu hjT) RqVec.Vector.ZModule.addrA.
qed.

(* The honest masks of a committee sum to zero *)
lemma hmask_sum0 (m : ((pidx * pidx) * view, vec) fmap) (d : view) (H : int list) :
  vmap (fun a => hmask m d H a) H = RqVec.Vector.zerov.
proof.
have -> : (fun a => hmask m d H a)
        = (fun a => vmap (fun b => if a = b then RqVec.Vector.zerov else sgnv a b (oget m.[pkey a b d])) H).
+ apply fun_ext => a; rewrite /hmask vmap_filter; apply vmap_eq => b _ /=; smt().
apply (dsum_anti (fun a b => if a = b then RqVec.Vector.zerov else sgnv a b (oget m.[pkey a b d])) H).
+ by move=> i /=.
move=> i j /=; case: (i = j) => [-> | hne] /=; first exact RqVec.Vector.ZModule.addr0.
have -> /= : j <> i by smt().
by rewrite (pkey_sym j i) sgnv_anti.
qed.

(* A uniq sum splits off one member *)
lemma vmap_rem1 (f : int -> vec) (H : int list) (i : int) :
  uniq H => i \in H => vmap f H = f i + vmap f (filter (fun a => a <> i) H).
proof.
elim H => [| a H ih] //= [ha hu] hi.
case: (a = i) => [<<- | hne].
+ rewrite vmap_cons /=.
  have -> // : filter (fun b => b <> a) H = H.
  by apply/all_filterP/allP => b hb /=; apply/negP => e; move: ha; rewrite -e hb.
have hiH : i \in H by case: hi => [e | //]; move: hne; rewrite e.
by rewrite /= !vmap_cons ih // RqVec.Vector.ZModule.addrCA.
qed.

(* The last honest response closes the masks *)
lemma close_masks (fz : (request * int, vec * vec) fmap) (m : ((pidx * pidx) * view, vec) fmap)
                  (d : view) (H : int list) (V : request) (i : int) :
  uniq H => i \in H =>
  (forall a, a \in H => a <> i =>
     (oget fz.[(V, a)]).`1 - (oget fz.[(V, a)]).`2 = hmask m d H a) =>
  vmap (fun a => (oget fz.[(V, a)]).`2 - (oget fz.[(V, a)]).`1) (filter (fun a => a <> i) H)
  = hmask m d H i.
proof.
move=> hu hi hz.
have h0 := hmask_sum0 m d H.
rewrite (vmap_rem1 _ H i hu hi) /= RqVec.Vector.ZModule.addr_eq0 in h0.
rewrite h0 -vmap_opp; apply vmap_eq => a; rewrite mem_filter => -[hne ha] /=.
by rewrite -hz // RqVec.Vector.ZModule.opprB.
qed.

(* Masks only read their own pair keys *)
lemma hmask_ext (m m' : ((pidx * pidx) * view, vec) fmap) (d : view) (H : int list) (a : int) :
  (forall b, b \in H => b <> a => pkey a b d \in m) =>
  (forall k, k \in m => m'.[k] = m.[k]) =>
  hmask m' d H a = hmask m d H a.
proof.
move=> hk hm; rewrite /hmask; apply vmap_eq => b; rewrite mem_filter => -[hne hb] /=.
by rewrite hm // hk.
qed.

(* One loop step extends a guarded prefix sum *)
lemma step_sum (m m' : ((pidx * pidx) * view, vec) fmap) (i : int) (P : int -> bool)
               (T : int list) (k : int) (d : view) :
  0 <= k < size T =>
  (forall b, b \in take k T => P b => pkey i b d \in m) =>
  (forall key, key \in m => m'.[key] = m.[key]) =>
  vmap (fun b => if P b then sgnv i b (oget m'.[pkey i b d]) else RqVec.Vector.zerov) (take (k + 1) T)
  = vmap (fun b => if P b then sgnv i b (oget m.[pkey i b d]) else RqVec.Vector.zerov) (take k T)
    + (if P (nth 0 T k) then sgnv i (nth 0 T k) (oget m'.[pkey i (nth 0 T k) d]) else RqVec.Vector.zerov).
proof.
move=> hk hin hm; rewrite (take_nth 0) // -cats1 vmap_cat vmap_single.
have -> // : vmap (fun b => if P b then sgnv i b (oget m'.[pkey i b d]) else RqVec.Vector.zerov) (take k T)
           = vmap (fun b => if P b then sgnv i b (oget m.[pkey i b d]) else RqVec.Vector.zerov) (take k T).
apply vmap_eq => b hb /=.
by case: (P b) => // hp; rewrite hm // hin.
qed.

op wfreq (V : request) : bool =
  wf_committee V.`2 /\ inrange V.`2 /\ size V.`3 = size V.`2.

op dg (h : h1in -> view) (t : row) (V : request) : view = h (e1 t V.`1 V.`2 V.`3).

op ainv (fz : (request * int, vec * vec) fmap) (m : ((pidx * pidx) * view, vec) fmap)
        (lr : alog) (C : corrset) (h : h1in -> view) (t : row) (l1 : (h1in * view) list) : bool =
  forall V a, (V, a) \in lr =>
    (V, a) \in fz
    /\ (oget fz.[(V, a)]).`1 - (oget fz.[(V, a)]).`2 = hmask m (dg h t V) (honest V.`2 C) a
    /\ (forall b, b \in honest V.`2 C => b <> a => pkey a b (dg h t V) \in m)
    /\ a \in honest V.`2 C /\ wfreq V /\ (e1 t V.`1 V.`2 V.`3, dg h t V) \in l1.

op binv (m : ((pidx * pidx) * view, vec) fmap) (lr : alog) (h : h1in -> view) (t : row) : bool =
  forall k, k \in m => exists V a b, (V, a) \in lr /\ b \in V.`2 /\ k = pkey a b (dg h t V).

op cinv (toks : (int, token) fmap) (req : (int, request) fmap) (C : corrset)
        (h : h1in -> view) (t : row) (l1 : (h1in * view) list) : bool =
  forall u, u \in toks =>
    !((oget toks.[u]).`tk_i \in C)
    /\ ((oget toks.[u]).`tk_phase = 2 =>
        u \in req /\ wfreq (oget req.[u])
        /\ (oget req.[u]).`1 = (oget toks.[u]).`tk_msg
        /\ (oget req.[u]).`2 = (oget toks.[u]).`tk_T
        /\ (oget toks.[u]).`tk_i \in (oget toks.[u]).`tk_T
        /\ (oget toks.[u]).`tk_dig = dg h t (oget req.[u])
        /\ (e1 t (oget req.[u]).`1 (oget req.[u]).`2 (oget req.[u]).`3,
            dg h t (oget req.[u])) \in l1).

(* Longer digest logs keep the response invariant *)
lemma ainv_l1 fz m lr C h t l1 e : ainv fz m lr C h t l1 => ainv fz m lr C h t (e :: l1).
proof.
move=> ha V a hl; have [#] h1 h2 h3 h4 h5 h6 := ha V a hl.
by rewrite in_cons h6 /= h1 h2 h4 h5 /=; exact h3.
qed.

(* Longer digest logs keep the token invariant *)
lemma cinv_l1 toks req C h t l1 e : cinv toks req C h t l1 => cinv toks req C h t (e :: l1).
proof.
move=> hc u hu; have [hi h2] := hc u hu; split => // hp.
have [#] g1 g2 g3 g4 g5 g6 g7 := h2 hp.
by rewrite in_cons g7 /= g1 g2 g3 g4 g5 g6.
qed.

op keysok (m : ((pidx * pidx) * view, vec) fmap) (lr : alog) (h : h1in -> view) (t : row)
          (i : int) (T : int list) (d : view) : bool =
  forall k, k \in m =>
    (exists V a b, (V, a) \in lr /\ b \in V.`2 /\ k = pkey a b (dg h t V))
    \/ (exists b, b \in T /\ k = pkey i b d).

op lpred (C : corrset) (i : int) (ys : int list) (b : int) : bool =
  (b <> i /\ !(ys <> [] /\ b = head 0 ys)) /\ hpair C i b.

op lsum (m : ((pidx * pidx) * view, vec) fmap) (C : corrset) (i : int) (ys : int list)
        (d : view) (L : int list) : vec =
  vmap (fun b => if lpred C i ys b then sgnv i b (oget m.[pkey i b d]) else RqVec.Vector.zerov) L.

(* Range membership bounds indices *)
lemma inrange_mem (T : committee) (x : int) : inrange T => x \in T => 1 <= x <= nmax.
proof. by move=> /allP h hx; exact (h x hx). qed.

(* Extending the masks keeps the response invariant *)
lemma ainv_ext fz m m' lr C h t l1 :
  ainv fz m lr C h t l1 => (forall k, k \in m => m'.[k] = m.[k]) => ainv fz m' lr C h t l1.
proof.
move=> ha hm V a hl; have [#] h1 h2 h3 h4 h5 h6 := ha V a hl.
rewrite h1 h4 h5 h6 /=; split.
+ by rewrite (hmask_ext m m') // h2.
move=> b hb hba; have hk := h3 b hb hba.
by rewrite domE hm // -domE.
qed.

op lkeys (m : ((pidx * pidx) * view, vec) fmap) (C : corrset) (i : int) (ys : int list)
         (d : view) (L : int list) : bool =
  forall b, b \in L => lpred C i ys b => pkey i b d \in m.

op dfresh (m : ((pidx * pidx) * view, vec) fmap) (V : request) (lr : alog) (i : int)
          (ys : int list) (d : view) : bool =
  ys <> [] => !((V, i) \in lr) => !(pkey i (head 0 ys) d \in m).

(* Empty prefixes have no masks *)
lemma loop_init m C (i : int) (ys : int list) (d : view) (T : int list) :
  lsum m C i ys d (take 0 T) = RqVec.Vector.zerov /\ lkeys m C i ys d (take 0 T).
proof. by rewrite take0 /lsum /lkeys vmap_nil. qed.

(* A masked loop step keeps the loop facts *)
lemma step_P fz m m' lr C h t l1 (i : int) (T ys : int list) (k : int) (d : view) (V : request) :
  0 <= k < size T => inrange T => i \in T => (ys <> [] => head 0 ys \in T) =>
  lpred C i ys (nth 0 T k) =>
  lkeys m C i ys d (take k T) =>
  keysok m lr h t i T d =>
  dfresh m V lr i ys d =>
  ainv fz m lr C h t l1 =>
  (forall k0, k0 \in m => m'.[k0] = m.[k0]) =>
  pkey i (nth 0 T k) d \in m' =>
  (forall k0, k0 \in m' => k0 \in m \/ k0 = pkey i (nth 0 T k) d) =>
  lsum m C i ys d (take k T) + sgnv i (nth 0 T k) (oget m'.[pkey i (nth 0 T k) d])
    = lsum m' C i ys d (take (k + 1) T)
  /\ lkeys m' C i ys d (take (k + 1) T)
  /\ keysok m' lr h t i T d
  /\ dfresh m' V lr i ys d
  /\ ainv fz m' lr C h t l1.
proof.
rewrite /lkeys /dfresh => hk hr hi hy hp hin hks hfr ha hm hkey hnew.
have hnT : nth 0 T k \in T by exact mem_nth.
split.
+ by rewrite /lsum (step_sum m m' i (lpred C i ys) T k d) // hp.
split.
+ move=> b; rewrite (take_nth 0) // mem_rcons in_cons => -[-> _ // | hb hpb].
  by rewrite domE hm ?hin // -domE hin.
split.
+ move=> k0 hk0; case: (hnew k0 hk0) => [hkm | ->].
  - by move: hks; rewrite /keysok => /(_ k0 hkm).
  by right; exists (nth 0 T k).
split.
+ move=> hys hnl; apply/negP => hk0; case: (hnew _ hk0) => [hkm | heq].
  - by have := hfr hys hnl; rewrite hkm.
  have [_ hor] := pkey_inj i (head 0 ys) i (nth 0 T k) d d
                    (inrange_mem T i hr hi) (inrange_mem T _ hr (hy hys))
                    (inrange_mem T i hr hi) (inrange_mem T _ hr hnT) heq.
  by move: hp; rewrite /lpred hys /=; smt().
exact (ainv_ext fz m m').
qed.

(* An unmasked loop step keeps the loop facts *)
lemma step_nP m C (i : int) (T ys : int list) (k : int) (d : view) :
  0 <= k < size T => !lpred C i ys (nth 0 T k) =>
  lkeys m C i ys d (take k T) =>
  lsum m C i ys d (take k T) = lsum m C i ys d (take (k + 1) T)
  /\ lkeys m C i ys d (take (k + 1) T).
proof.
rewrite /lkeys => hk hp hin; split.
+ rewrite /lsum (take_nth 0) // -cats1 vmap_cat vmap_single /= hp /=.
  by rewrite eq_sym; exact RqVec.Vector.ZModule.addr0.
move=> b; rewrite (take_nth 0) // mem_rcons in_cons => -[-> // | hb hpb].
exact hin.
qed.

(* The full loop sum and its partner give the honest mask *)
lemma mask_full m C (i : int) (T ys : int list) (d : view) :
  uniq T => !(i \in C) =>
  (ys <> [] => head 0 ys \in T /\ head 0 ys <> i /\ hpair C i (head 0 ys)) =>
  lsum m C i ys d T
  + (if ys <> [] then sgnv i (head 0 ys) (oget m.[pkey i (head 0 ys) d]) else RqVec.Vector.zerov)
  = hmask m d (honest T C) i.
proof.
move=> hu hi hy; rewrite hmask_T // /lsum.
case: (ys <> []) => hys /=.
+ have [hh1 [hh2 hh3]] := hy hys.
  rewrite -(vmap_desig (fun b => sgnv i b (oget m.[pkey i b d]))
                       (fun b => b <> i /\ hpair C i b) T (head 0 ys) hu hh1 _) /=.
  - by rewrite hh2 hh3.
  congr; apply vmap_eq => b _ /=; rewrite /lpred hys /=; smt().
rewrite /lpred hys /=.
exact RqVec.Vector.ZModule.addr0.
qed.

(* The designated partner completes the honest mask *)
lemma mask_full_ne m C (i : int) (T ys : int list) (d : view) :
  uniq T => !(i \in C) => ys <> [] => head 0 ys \in T => head 0 ys <> i =>
  hpair C i (head 0 ys) =>
  lsum m C i ys d T + sgnv i (head 0 ys) (oget m.[pkey i (head 0 ys) d])
  = hmask m d (honest T C) i.
proof.
move=> hu hi hys hh hne hp.
by have := mask_full m C i T ys d hu hi _; [move=> _; rewrite hh hne hp | rewrite hys].
qed.

(* Without a designated partner the loop gives the honest mask *)
lemma mask_full_nil m C (i : int) (T : int list) (d : view) :
  uniq T => !(i \in C) => lsum m C i [] d T = hmask m d (honest T C) i.
proof.
move=> hu hi; have := mask_full m C i T [] d hu hi _ => //=.
by move=> <-; rewrite eq_sym; exact RqVec.Vector.ZModule.addr0.
qed.

(* New tokens keep the token invariant *)
lemma cinv_new toks req C h t l1 (k : int) (tok : token) :
  cinv toks req C h t l1 => !(tok.`tk_i \in C) => tok.`tk_phase <> 2 =>
  cinv toks.[k <- tok] req C h t l1.
proof.
move=> hc hi hp u; rewrite mem_set get_setE; case: (u = k) => [-> _ /= | hne /= hu].
+ by rewrite hi hp.
exact (hc u hu).
qed.

(* Second rounds keep the token invariant *)
lemma cinv_o2 toks req C h t l1 (u : int) (tok : token) (T : committee) (cs : cmt list) :
  cinv toks req C h t l1 => u \in toks => tok = oget toks.[u] => ok2 tok T cs =>
  cinv toks.[u <- {| tok with tk_phase = 2; tk_T = T; tk_dig = h (e1 t tok.`tk_msg T cs) |}]
       req.[u <- (tok.`tk_msg, T, cs)] C h t
       ((e1 t tok.`tk_msg T cs, h (e1 t tok.`tk_msg T cs)) :: l1).
proof.
move=> hc hu htok hok u'; rewrite mem_set get_setE.
case: (u' = u) => [-> _ /= | hne /= hu'].
+ have [hi _] := hc u hu.
  move: hok; rewrite /ok2 => [#] hp1 hwf hrg hiT hsz hown.
  rewrite -htok in hi.
  by rewrite hi /= get_set_sameE mem_set /= /wfreq /dg /= hwf hrg hsz hiT.
have [hi h2] := hc u' hu'; split => // hp.
have [#] g1 g2 g3 g4 g5 g6 g7 := h2 hp.
by rewrite mem_set get_set_neqE // g7 g1 g2 g3 g4 g5 g6.
qed.

(* Erasing a token keeps the token invariant *)
lemma cinv_erase toks req C h t l1 (u : int) :
  cinv toks req C h t l1 => u \in toks => cinv toks.[u <- erase (oget toks.[u])] req C h t l1.
proof.
move=> hc hu; apply cinv_new => //; last by rewrite /erase.
by have [hi _] := hc u hu; rewrite /erase /=.
qed.

(* Repeated responses keep the response invariant *)
lemma ainv_dup fz m lr C h t l1 (V : request) (i : int) :
  ainv fz m lr C h t l1 => (V, i) \in lr => ainv fz m ((V, i) :: lr) C h t l1.
proof.
move=> ha hl V' a; rewrite in_cons; case=> [heq | hl'].
+ by move: heq => /= [-> ->]; exact (ha V i hl).
exact (ha V' a hl').
qed.

(* New responses with their masks keep the response invariant *)
lemma ainv_new fz m lr C h t l1 (V : request) (i : int) (z f : vec) :
  ainv fz m lr C h t l1 => !((V, i) \in lr) =>
  z - f = hmask m (dg h t V) (honest V.`2 C) i =>
  (forall b, b \in honest V.`2 C => b <> i => pkey i b (dg h t V) \in m) =>
  i \in honest V.`2 C => wfreq V => (e1 t V.`1 V.`2 V.`3, dg h t V) \in l1 =>
  ainv fz.[(V, i) <- (z, f)] m ((V, i) :: lr) C h t l1.
proof.
move=> ha hn hz hk hi hw hl V' a; rewrite in_cons; case=> [heq | hl'].
+ move: heq => /= [-> ->].
  rewrite mem_set get_set_sameE /=.
  split; first exact hz.
  split; first exact hk.
  by rewrite hi hw hl.
have [#] h1 h2 h3 h4 h5 h6 := ha V' a hl'.
have hne : (V', a) <> (V, i) by apply/negP => e; move: hl'; rewrite e hn.
rewrite mem_set get_set_neqE // h1 /=.
split; first exact h2.
split; first exact h3.
by rewrite h4 h5 h6.
qed.

(* Loop keys belong to the new response *)
lemma binv_keys m lr h t (V : request) (i : int) (d : view) :
  keysok m lr h t i V.`2 d => d = dg h t V => binv m ((V, i) :: lr) h t.
proof.
rewrite /keysok /binv => hk hd k0 hk0.
case: (hk k0 hk0) => [[V' a b] [#] hl hb -> | [b] [hb ->]].
+ by exists V' a b; rewrite in_cons hl.
by exists V i b; rewrite hd in_cons.
qed.

(* Stored keys are loop keys *)
lemma keysok_binv m lr h t (i : int) (T : int list) (d : view) :
  binv m lr h t => keysok m lr h t i T d.
proof. by rewrite /keysok /binv => hb k0 hk0; left; exact (hb k0 hk0). qed.

(* Adding a committee key keeps the loop keys *)
lemma keysok_set m lr h t (i : int) (T : int list) (d : view) (b : int) (v : vec) :
  keysok m lr h t i T d => b \in T => keysok m.[pkey i b d <- v] lr h t i T d.
proof.
rewrite /keysok => hk hb k0; rewrite mem_set; case=> [hk0 | ->].
+ exact (hk k0 hk0).
by right; exists b.
qed.

(* Loop sums only read their own keys *)
lemma lsum_ext m m' C (i : int) (ys : int list) (d : view) (L : int list) :
  (forall b, b \in L => lpred C i ys b => pkey i b d \in m) =>
  (forall k, k \in m => m'.[k] = m.[k]) =>
  lsum m' C i ys d L = lsum m C i ys d L.
proof.
move=> hk hm; rewrite /lsum; apply vmap_eq => b hb /=.
by case: (lpred C i ys b) => // hp; rewrite hm // hk.
qed.

(* Repeated responses reuse the stored offset *)
lemma resp_dup (zf ff f mk : vec) : zf - ff = mk => zf + f - ff = f + mk.
proof.
move=> <-; rewrite RqVec.Vector.ZModule.addrAC.
by rewrite RqVec.Vector.ZModule.addrC.
qed.

(* The designated partner absorbs a uniform response *)
lemma resp_new (z f mk : vec) (a b : int) :
  f + (mk + sgnv a b (sgnv a b (z - f - mk))) = z.
proof.
rewrite sgnvK (RqVec.Vector.ZModule.addrC mk) RqVec.Vector.ZModule.subrK.
by rewrite RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.subrK.
qed.

(* The stored offset of a uniform response is its mask *)
lemma off_new (z f mk : vec) (a b : int) :
  z - f = mk + sgnv a b (sgnv a b (z - f - mk)).
proof.
rewrite sgnvK (RqVec.Vector.ZModule.addrC mk) RqVec.Vector.ZModule.subrK //.
qed.

op sinv fz m lr toks req C h t l1 : bool =
  ainv fz m lr C h t l1 /\ binv m lr h t /\ cinv toks req C h t l1.

op tokok (toks : (int, token) fmap) (u : int) (tok : token) (T : committee) : bool =
  tok = oget toks.[u] /\ u \in toks /\ tok.`tk_phase = 2 /\ T = tok.`tk_T.

op freshk (m : ((pidx * pidx) * view, vec) fmap) (lr : alog) (h : h1in -> view) (t : row)
          (req : (int, request) fmap) (u : int) (tok : token) (T : committee) : bool =
  forall j, j \in T => !((oget req.[u], tok.`tk_i) \in lr) => !((oget req.[u], j) \in lr) =>
    !(pkey tok.`tk_i j (dg h t (oget req.[u])) \in m).

(* Heads of nonempty filters satisfy the filter *)
lemma head_filter (p : int -> bool) (L : int list) :
  filter p L <> [] => head 0 (filter p L) \in L /\ p (head 0 (filter p L)).
proof.
move=> h.
have : head 0 (filter p L) \in filter p L.
+ by apply/(mem_head_behead 0 _ h); left.
by rewrite mem_filter => -[hp hm].
qed.

(* The designated partner starts without a mask *)
lemma dfresh_init m lr h t req toks C l1 (u : int) (tok : token) (T : committee) :
  freshk m lr h t req u tok T => cinv toks req C h t l1 => tok = oget toks.[u] =>
  u \in toks => tok.`tk_phase = 2 =>
  dfresh m (oget req.[u]) lr tok.`tk_i
    (filter (fun j => j <> tok.`tk_i /\ hpair C tok.`tk_i j /\ !((oget req.[u], j) \in lr)) T)
    tok.`tk_dig.
proof.
move=> hf hc htok hu hph; rewrite /dfresh => hys hnl.
have [hhT [_ [_ hnj]]] := head_filter _ _ hys.
have [_ h2] := hc u hu.
have hph' : (oget toks.[u]).`tk_phase = 2 by rewrite -htok.
have [#] _ _ _ _ _ hdig _ := h2 hph'.
move: hdig; rewrite -htok => ->.
exact (hf _ hhT hnl hnj).
qed.

(* Repeated requests reuse their partner keys *)
lemma dup_key fz m lr C h t l1 toks req (u : int) (ys : int list) :
  ainv fz m lr C h t l1 => cinv toks req C h t l1 => u \in toks =>
  (oget toks.[u]).`tk_phase = 2 => (oget req.[u], (oget toks.[u]).`tk_i) \in lr =>
  ys <> [] => head 0 ys \in (oget toks.[u]).`tk_T => head 0 ys <> (oget toks.[u]).`tk_i =>
  hpair C (oget toks.[u]).`tk_i (head 0 ys) =>
  pkey (oget toks.[u]).`tk_i (head 0 ys) (oget toks.[u]).`tk_dig \in m.
proof.
move=> ha hc hu hph hlr _ hhT hne hp.
have [#] _ _ hk _ _ _ := ha _ _ hlr.
have [_ h2] := hc u hu; have [#] _ _ _ hT _ hdig _ := h2 hph.
rewrite hdig; apply hk => //.
by rewrite /honest mem_filter hT hhT /=; move: hp; rewrite /hpair.
qed.

(* Adding then removing two vectors is neutral *)
lemma addsub3 (a b x : vec) : a + b + x - a - b = x.
proof.
by smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.addrN
       RqVec.Vector.ZModule.add0r).
qed.

(* Adding then removing a vector is neutral *)
lemma addsubK (a x : vec) : a + x - a = x.
proof.
by smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.addrN
       RqVec.Vector.ZModule.add0r).
qed.

(* A sum and its parts recombine *)
lemma addsub3r (a b x : vec) : a + b + (x - a - b) = x.
proof.
by smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.addrN
       RqVec.Vector.ZModule.add0r).
qed.

(* Members of an empty filter fail the filter *)
lemma nil_resp (C : corrset) (i : int) (T : int list) (V : request) (lr : alog) (a : int) :
  filter (fun j => j <> i /\ hpair C i j /\ !((V, j) \in lr)) T = [] =>
  !(i \in C) => a \in honest T C => a <> i => (V, a) \in lr.
proof.
move=> h hi; rewrite /honest mem_filter => -[haC haT] hne.
apply/contraT => hn.
have : a \in filter (fun j => j <> i /\ hpair C i j /\ !((V, j) \in lr)) T.
+ by rewrite mem_filter /= hne /hpair hi haC hn haT.
by rewrite h.
qed.

(* A uniform response with its partner key keeps the invariants *)
lemma fin_new_B fz m lr C h t l1 (V : request) (i : int) (T ys : int list) (d : view)
                (z f : vec) :
  ainv fz m lr C h t l1 => keysok m lr h t i T d => lkeys m C i ys d T =>
  !((V, i) \in lr) => uniq T => !(i \in C) => i \in T => wfreq V => V.`2 = T =>
  d = dg h t V => (e1 t V.`1 V.`2 V.`3, dg h t V) \in l1 =>
  ys <> [] => head 0 ys \in T => head 0 ys <> i => hpair C i (head 0 ys) =>
  !(pkey i (head 0 ys) d \in m) =>
  ainv fz.[(V, i) <- (z, f)]
       m.[pkey i (head 0 ys) d <- sgnv i (head 0 ys) (z - f - lsum m C i ys d T)]
       ((V, i) :: lr) C h t l1
  /\ binv m.[pkey i (head 0 ys) d <- sgnv i (head 0 ys) (z - f - lsum m C i ys d T)]
          ((V, i) :: lr) h t.
proof.
move=> ha hks hlk hn hu hi hiT hw hT hd hl hys hhT hne hp hfr.
pose j := head 0 ys.
pose m' := m.[pkey i j d <- sgnv i j (z - f - lsum m C i ys d T)].
have hext : forall k, k \in m => m'.[k] = m.[k].
+ move=> k hk; rewrite /m' get_set_neqE //.
  by apply/negP => e; move: hfr; rewrite -e hk.
split; last first.
+ apply (binv_keys _ _ _ _ _ _ d); last exact hd.
  by rewrite hT; apply keysok_set.
apply ainv_new.
+ exact (ainv_ext fz m m').
+ exact hn.
+ have hls : lsum m' C i ys d T = lsum m C i ys d T.
  - by apply (lsum_ext m m').
  rewrite -hd hT -(mask_full_ne m' C i T ys d hu hi hys hhT hne hp) hls.
  by rewrite /m' get_set_sameE /=; exact (off_new z f (lsum m C i ys d T) i j).
+ rewrite -hd hT => b hb hbi; rewrite /m' mem_set.
  case: (b = j) => [-> | hbj]; first by right.
  left; move: hlk; rewrite /lkeys => hlk; apply hlk.
  - by move: hb; rewrite /honest mem_filter.
  move: hb; rewrite /honest mem_filter /lpred /hpair hi /= => -[hbC _].
  split; [split; [exact hbi | ] | exact hbC].
  by apply/negP => -[_ e]; apply hbj; exact e.
+ by rewrite hT /honest mem_filter /= hi hiT.
+ exact hw.
exact hl.
qed.

(* The last honest response keeps the invariants *)
lemma fin_new_C fz m lr C h t l1 (V : request) (i : int) (T : int list) (d : view) (f : vec) :
  ainv fz m lr C h t l1 => keysok m lr h t i T d => lkeys m C i [] d T =>
  !((V, i) \in lr) => uniq T => !(i \in C) => i \in T => wfreq V => V.`2 = T =>
  d = dg h t V => (e1 t V.`1 V.`2 V.`3, dg h t V) \in l1 =>
  filter (fun j => j <> i /\ hpair C i j /\ !((V, j) \in lr)) T = [] =>
  vmap (fun a => (oget fz.[(V, a)]).`2 - (oget fz.[(V, a)]).`1)
       (filter (fun a => a <> i) (honest T C)) = lsum m C i [] d T
  /\ ainv fz.[(V, i) <- (f + lsum m C i [] d T, f)] m ((V, i) :: lr) C h t l1
  /\ binv m ((V, i) :: lr) h t.
proof.
move=> ha hks hlk hn hu hi hiT hw hT hd hl hnil.
have hHu : uniq (honest T C) by apply filter_uniq.
have hiH : i \in honest T C by rewrite /honest mem_filter /= hi hiT.
have hclose : vmap (fun a => (oget fz.[(V, a)]).`2 - (oget fz.[(V, a)]).`1)
                (filter (fun a => a <> i) (honest T C)) = hmask m d (honest T C) i.
+ apply close_masks => // a haH hai.
  have [#] _ hz _ _ _ _ := ha _ _ (nil_resp C i T V lr a hnil hi haH hai).
  by rewrite hz -hd hT.
rewrite hclose (mask_full_nil m C i T d hu hi).
split; first done.
split; last first.
+ apply (binv_keys _ _ _ _ _ _ d); last exact hd.
  by rewrite hT.
apply ainv_new => //.
+ by rewrite -hd hT addsubK.
+ rewrite -hd hT => b hb hbi; move: hlk; rewrite /lkeys => hlk; apply hlk.
  - by move: hb; rewrite /honest mem_filter.
  by move: hb; rewrite /honest mem_filter /lpred /hpair hi hbi /= => -[-> _].
by rewrite hT.
qed.

section SimHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO,
                          -H0H.CQ, -H1O.CQ}.

declare axiom A_ll (H <: HOr {-A}) (O <: SOr {-A}) :
  islossless H.h0 => islossless H.h1 => islossless H.hc =>
  islossless O.o1 => islossless O.o2 => islossless O.o3 =>
  islossless A(H, O).forge.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

declare axiom e1_inj (t t' : row) (V V' : request) :
  wfreq V => wfreq V' => e1 t V.`1 V.`2 V.`3 = e1 t' V'.`1 V'.`2 V'.`3 => t = t' /\ V = V'.

(* Unopened pairs of a request have no mask yet *)
lemma fresh_key fz m lr toks req C h t l1 (u : int) :
  !hascol l1 => ainv fz m lr C h t l1 => binv m lr h t => cinv toks req C h t l1 =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 =>
  freshk m lr h t req u (oget toks.[u]) (oget toks.[u]).`tk_T.
proof.
move=> hnc ha hb hc hu hph j hj hni hnj; apply/negP => hk.
move: hb; rewrite /binv => /(_ _ hk) [V a b] [#] hl hbV hkey.
have [#] _ _ _ haH hwV hl1V := ha _ _ hl.
have [_ /(_ hph) [#] hur hwW hm hT hiT hdig hl1W] := hc u hu.
have haV : a \in V.`2 by move: haH; rewrite /honest mem_filter.
have hrW : inrange (oget req.[u]).`2 by move: hwW; rewrite /wfreq.
have hrV : inrange V.`2 by move: hwV; rewrite /wfreq.
move: hiT hj; rewrite -hT => hiT hj.
have [hd hab] := pkey_inj _ _ _ _ _ _ (inrange_mem _ _ hrW hiT) (inrange_mem _ _ hrW hj)
                   (inrange_mem _ _ hrV haV) (inrange_mem _ _ hrV hbV) hkey.
case: (V = oget req.[u]) => hVW.
+ move: hl; rewrite hVW => hl; case: hab => [[hia _] | [_ hja]].
  - by move: hni; rewrite hia hl.
  by move: hnj; rewrite hja hl.
have hcol : hascol l1; last by move: hnc; rewrite hcol.
exists (e1 t (oget req.[u]).`1 (oget req.[u]).`2 (oget req.[u]).`3)
       (e1 t V.`1 V.`2 V.`3) (dg h t (oget req.[u])).
rewrite hl1W hd hl1V /=.
apply/negP => heq; apply hVW.
by have [_ ->] := e1_inj _ _ _ _ hwW hwV heq.
qed.

(* First rounds keep the simulation invariant *)
equiv o1_sim :
  SOFs(H0H.QRO, H1O.QRO).o1 ~ SOF(MPI, H0H.QRO, H1O.QRO).o1 :
  ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
                MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
                  MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}.
proof.
proc; sp; if; first by move=> />.
+ inline *; auto => /> &1 &2 ha hb hc hr1 hr2 hi nn _.
  by apply cinv_new.
by auto.
qed.

(* Second rounds keep the simulation invariant *)
equiv o2_sim :
  SOFs(H0H.QRO, H1O.QRO).o2 ~ SOF(MPI, H0H.QRO, H1O.QRO).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
                   MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
                  MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}.
proof.
proc; sp; if; first by move=> />.
+ sp; if; first by move=> />.
  + inline *; auto => /> &1 &2 ha hb hc hu hp1 hun hsz hrg hiT hcs hown.
    split; first exact ainv_l1.
    by apply (cinv_o2 _ _ _ _ _ _ u{2} (oget S.toks{2}.[u{2}]) T{2} cs{2} hc hu _ _).
  by auto.
by auto.
qed.

(* Simulated third rounds match the real ones *)
equiv o3_sim :
  SOFs(H0H.QRO, H1O.QRO).o3 ~ SOF(MPI, H0H.QRO, H1O.QRO).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ !hascol Lg.l1{2} /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh} /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}.
proof.
proc; sp; if; first by move=> />.
+ sp; if; first by move=> />.
  + seq 1 1 : (={u, T, cs, ws, tok, d, out} /\ out{1} = None /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
       /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1} /\ tokok S.toks{1} u{1} tok{1} T{1} /\ freshk MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} S.req{1} u{1} tok{1} T{1}).
    + inline *; auto => /> &1 &2 hnc ha hb hc hu hph _ _ _.
      split; first by split; [exact ainv_l1 | exact cinv_l1].
      exact (fresh_key _ _ _ _ _ _ _ _ _ u{2} hnc ha hb hc hu hph).
    if; first by move=> />.
    + seq 3 3 : (={u, T, cs, ws, tok, d, out, okk} /\ out{1} = None /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
         /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1} /\ tokok S.toks{1} u{1} tok{1} T{1} /\ freshk MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} S.req{1} u{1} tok{1} T{1} /\ d{1} = tok{1}.`tk_dig).
      + while (={k, okk, u, T, cs, ws, tok, d, out} /\ out{1} = None /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
           /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1} /\ tokok S.toks{1} u{1} tok{1} T{1} /\ freshk MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} S.req{1} u{1} tok{1} T{1} /\ d{1} = tok{1}.`tk_dig).
        + wp; call (_ : ={x, Lg.l0, H0H.QRO.fh, H0C.QRO.fh, S.cs} ==> ={res, Lg.l0}); first by sim.
          by auto.
        by auto.
      if; first by move=> />.
      + seq 5 5 : (={k, mkh, mkc, c, ys, u, T, cs, ws, tok, d, out} /\ out{1} = None
         /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
         /\ tokok S.toks{1} u{1} tok{1} T{1} /\ d{1} = tok{1}.`tk_dig
         /\ ys{1} = filter (fun j => j <> tok{1}.`tk_i /\ hpair S.cs{1} tok{1}.`tk_i j
                                  /\ !((oget S.req{1}.[u{1}], j) \in S.lr{1})) T{1}
         /\ 0 <= k{1} <= size T{1}
         /\ mkh{1} = lsum MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ lkeys MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ keysok MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} tok{1}.`tk_i T{1} d{1}
         /\ dfresh MPI.m{1} (oget S.req{1}.[u{1}]) S.lr{1} tok{1}.`tk_i ys{1} d{1}
         /\ ainv Fz.fz{1} MPI.m{1} S.lr{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
         /\ cinv S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1} /\ k{1} = 0).
        + auto => /> &1 &2 ha hb hc hu hph hfr _.
          rewrite size_ge0 /=; split; first by rewrite take0 /lsum vmap_nil.
          split; first by rewrite take0 /lkeys.
          split; first exact keysok_binv.
          exact (dfresh_init _ _ _ _ _ _ _ _ u{2} _ _ hfr hc _ hu hph).
        seq 1 1 : (={k, mkh, mkc, c, ys, u, T, cs, ws, tok, d, out} /\ out{1} = None
         /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
         /\ tokok S.toks{1} u{1} tok{1} T{1} /\ d{1} = tok{1}.`tk_dig
         /\ ys{1} = filter (fun j => j <> tok{1}.`tk_i /\ hpair S.cs{1} tok{1}.`tk_i j
                                  /\ !((oget S.req{1}.[u{1}], j) \in S.lr{1})) T{1}
         /\ 0 <= k{1} <= size T{1}
         /\ mkh{1} = lsum MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ lkeys MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ keysok MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} tok{1}.`tk_i T{1} d{1}
         /\ dfresh MPI.m{1} (oget S.req{1}.[u{1}]) S.lr{1} tok{1}.`tk_i ys{1} d{1}
         /\ ainv Fz.fz{1} MPI.m{1} S.lr{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
         /\ cinv S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1} /\ k{1} = size T{1}).
        + while (={k, mkh, mkc, c, ys, u, T, cs, ws, tok, d, out} /\ out{1} = None
         /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
         /\ tokok S.toks{1} u{1} tok{1} T{1} /\ d{1} = tok{1}.`tk_dig
         /\ ys{1} = filter (fun j => j <> tok{1}.`tk_i /\ hpair S.cs{1} tok{1}.`tk_i j
                                  /\ !((oget S.req{1}.[u{1}], j) \in S.lr{1})) T{1}
         /\ 0 <= k{1} <= size T{1}
         /\ mkh{1} = lsum MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ lkeys MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ keysok MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} tok{1}.`tk_i T{1} d{1}
         /\ dfresh MPI.m{1} (oget S.req{1}.[u{1}]) S.lr{1} tok{1}.`tk_i ys{1} d{1}
         /\ ainv Fz.fz{1} MPI.m{1} S.lr{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
         /\ cinv S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}).
          + seq 1 1 : (={k, mkh, mkc, c, ys, u, T, cs, ws, tok, d, out} /\ out{1} = None
         /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
         /\ tokok S.toks{1} u{1} tok{1} T{1} /\ d{1} = tok{1}.`tk_dig
         /\ ys{1} = filter (fun j => j <> tok{1}.`tk_i /\ hpair S.cs{1} tok{1}.`tk_i j
                                  /\ !((oget S.req{1}.[u{1}], j) \in S.lr{1})) T{1}
         /\ 0 <= k{1} <= size T{1}
         /\ mkh{1} = lsum MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ lkeys MPI.m{1} S.cs{1} tok{1}.`tk_i ys{1} d{1} (take k{1} T{1})
         /\ keysok MPI.m{1} S.lr{1} H1O.QRO.fh{1} S.t{1} tok{1}.`tk_i T{1} d{1}
         /\ dfresh MPI.m{1} (oget S.req{1}.[u{1}]) S.lr{1} tok{1}.`tk_i ys{1} d{1}
         /\ ainv Fz.fz{1} MPI.m{1} S.lr{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}
         /\ cinv S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1} /\ k{1} < size T{1} /\ ={j} /\ j{1} = nth 0 T{1} k{1}).
            + by auto.
            if; first by move=> />.
            + if; first by move=> />.
              + inline MPI.f; sp; if; first by move=> />.
                + auto => /> &1 &2 hu hph hk0 _ hlk hks hdf ha hc hkT hj1 hj2 hiC hjC hnot v0 _.
                  have [_ /(_ hph) [#] _ hw _ hT hiT _ _] := hc _ hu.
                  pose i := (oget S.toks{2}.[u{2}]).`tk_i.
                  pose T := (oget S.toks{2}.[u{2}]).`tk_T.
                  pose d := (oget S.toks{2}.[u{2}]).`tk_dig.
                  pose ys := filter (fun (j1 : int) => j1 <> i /\ hpair S.cs{2} i j1
                                       /\ !((oget S.req{2}.[u{2}], j1) \in S.lr{2})) T.
                  pose j := nth 0 T k{2}.
                  have -> : forall (x : vec), (if i < j then x else - x) = sgnv i j x.
                  - by move=> x; rewrite /sgnv.
                  have -> : ((toidx (if i < j then i else j), toidx (if i < j then j else i)), d)
                            = pkey i j d by rewrite /pkey.
                  have hr : inrange T by move: hw; rewrite /wfreq hT => -[_ []].
                  have hlp : lpred S.cs{2} i ys j.
                  - by rewrite /lpred /hpair; split; [split; [exact hj1 | exact hj2] | split; [exact hiC | exact hjC]].
                  have hkey : !(pkey i j d \in MPI.m{2}) by move: hnot; rewrite /pkey.
                  have := step_P Fz.fz{1} MPI.m{2} MPI.m{2}.[pkey i j d <- v0] S.lr{2} S.cs{2}
                            H1O.QRO.fh{2} S.t{2} Lg.l1{2} i T ys k{2} d (oget S.req{2}.[u{2}])
                            _ hr hiT _ hlp hlk hks hdf ha _ _ _.
                  - by rewrite hk0 hkT.
                  - by move=> hys; have [] := head_filter _ _ hys.
                  - move=> k0 hk0'; rewrite get_set_neqE //.
                    by apply/negP => e; move: hkey; rewrite -e hk0'.
                  - by rewrite mem_set /j; right.
                  - by move=> k0; rewrite mem_set /j.
                  by move=> [#] -> -> -> -> ->; smt().
                + auto => /> &1 &2 hu hph hk0 _ hlk hks hdf ha hc hkT hj1 hj2 hiC hjC hin.
                  have [_ /(_ hph) [#] _ hw _ hT hiT _ _] := hc _ hu.
                  pose i := (oget S.toks{2}.[u{2}]).`tk_i.
                  pose T := (oget S.toks{2}.[u{2}]).`tk_T.
                  pose d := (oget S.toks{2}.[u{2}]).`tk_dig.
                  pose ys := filter (fun (j1 : int) => j1 <> i /\ hpair S.cs{2} i j1
                                       /\ !((oget S.req{2}.[u{2}], j1) \in S.lr{2})) T.
                  pose j := nth 0 T k{2}.
                  have -> : forall (x : vec), (if i < j then x else - x) = sgnv i j x.
                  - by move=> x; rewrite /sgnv.
                  have -> : ((toidx (if i < j then i else j), toidx (if i < j then j else i)), d)
                            = pkey i j d by rewrite /pkey.
                  have hr : inrange T by move: hw; rewrite /wfreq hT => -[_ []].
                  have hlp : lpred S.cs{2} i ys j.
                  - by rewrite /lpred /hpair; split; [split; [exact hj1 | exact hj2] | split; [exact hiC | exact hjC]].
                  have hkey : pkey i j d \in MPI.m{2} by move: hin; rewrite /pkey.
                  have := step_P Fz.fz{1} MPI.m{2} MPI.m{2} S.lr{2} S.cs{2}
                            H1O.QRO.fh{2} S.t{2} Lg.l1{2} i T ys k{2} d (oget S.req{2}.[u{2}])
                            _ hr hiT _ hlp hlk hks hdf ha _ _ _.
                  - by rewrite hk0 hkT.
                  - by move=> hys; have [] := head_filter _ _ hys.
                  - done.
                  - by rewrite /j.
                  - by move=> k0 ->.
                  by move=> [#] -> -> _ _ _; smt().
              + auto => /> &1 &2 hu hph hk0 _ hlk hks hdf ha hc hkT hj1 hj2 hnh.
                have := step_nP _ _ _ _ _ _ _ _ _ hlk.
                - by rewrite hk0 hkT.
                - by rewrite /lpred hnh.
                by move=> [-> ->]; smt().
            + auto => /> &1 &2 hu hph hk0 _ hlk hks hdf ha hc hkT hcond.
              have := step_nP _ _ _ _ _ _ _ _ _ hlk.
              - by rewrite hk0 hkT.
              - by rewrite /lpred negb_and; left; exact hcond.
              by move=> [-> ->]; smt().
          + by auto => />; smt().
        case (((oget S.req.[u], tok.`tk_i) \in S.lr){1}).
        + rcondt{1} 2; first by auto.
          case (ys{2} <> []).
          + rcondt{2} 1; first by auto.
            inline{2} MPI.f.
            rcondf{2} 5.
            + move=> &1; auto => /> hu hph _ hlk hks hdf ha hc hlr hys.
              have [hhT [hne [hp _]]] := head_filter _ _ hys.
              exact (dup_key _ _ _ _ _ _ _ _ _ _ _ ha hc hu hph hlr hys hhT hne hp).
            auto => /> &1 &2 hu hph _ hlk hks hdf ha hc hlr hys.
            have [hiC h2] := hc _ hu; have [#] _ hw _ hT hiT hdig hl1 := h2 hph.
            have hu' : uniq (oget S.toks{2}.[u{2}]).`tk_T.
            - by move: hw; rewrite /wfreq hT /wf_committee => -[[]].
            have [hhT [hne [hp _]]] := head_filter _ _ hys.
            have [#] _ hz _ hiH _ _ := ha _ _ hlr.
            pose i := (oget S.toks{2}.[u{2}]).`tk_i.
            pose T := (oget S.toks{2}.[u{2}]).`tk_T.
            pose d := (oget S.toks{2}.[u{2}]).`tk_dig.
            pose ys := filter (fun (j1 : int) => j1 <> i /\ hpair S.cs{2} i j1
                                 /\ !((oget S.req{2}.[u{2}], j1) \in S.lr{2})) T.
            pose j := head 0 ys.
            have -> : forall (x : vec), (if i < j then x else - x) = sgnv i j x.
            - by move=> x; rewrite /sgnv.
            have -> : ((toidx (if i < j then i else j), toidx (if i < j then j else i)), d)
                      = pkey i j d by rewrite /pkey.
            rewrite take_size (mask_full_ne MPI.m{2} S.cs{2} i T ys d hu' hiC hys hhT hne hp).
            split.
            - apply resp_dup; move: hz; rewrite hT -hdig => ->.
              done.
            split; first exact ainv_dup.
            split; last exact cinv_erase.
            apply (binv_keys _ _ _ _ _ _ d); [by rewrite hT | exact hdig].
          rcondf{2} 1; first by auto.
          auto => /> &1 &2 hu hph _ hlk hks hdf ha hc hlr hys.
          have [hiC h2] := hc _ hu; have [#] _ hw _ hT hiT hdig hl1 := h2 hph.
          have hu' : uniq (oget S.toks{2}.[u{2}]).`tk_T.
          - by move: hw; rewrite /wfreq hT /wf_committee => -[[]].
          have [#] _ hz _ hiH _ _ := ha _ _ hlr.
          rewrite take_size hys (mask_full_nil _ _ _ _ _ hu' hiC).
          split.
          - apply resp_dup; move: hz; rewrite hT -hdig => ->.
            done.
          split; first exact ainv_dup.
          split; last exact cinv_erase.
          apply (binv_keys _ _ _ _ _ _ (oget S.toks{2}.[u{2}]).`tk_dig); [by rewrite hT | exact hdig].
        rcondf{1} 2; first by auto.
        case (ys{2} <> []).
        + rcondt{1} 2; first by auto.
          rcondt{2} 1; first by auto.
          inline{2} MPI.f.
          rcondt{2} 5.
          + move=> &1; auto => /> hu hph _ hlk hks hdf ha hc hlr hys.
            by move: hdf; rewrite /dfresh => /(_ hys hlr); rewrite /pkey.
          wp; rnd (fun (zz : vec) => sgnv tok{1}.`tk_i (head 0 ys{1}) (zz - f{1} - mkh{1}))
                  (fun (vv : vec) => f{1} + mkh{1} + sgnv tok{1}.`tk_i (head 0 ys{1}) vv).
          wp; skip => /> &1 &2 hu hph _ hlk hks hdf ha hc hlr hys.
          have [hiC h2] := hc _ hu; have [#] _ hw _ hT hiT hdig hl1 := h2 hph.
          have hu' : uniq (oget S.toks{2}.[u{2}]).`tk_T.
          - by move: hw; rewrite /wfreq hT /wf_committee => -[[]].
          have [hhT [hne [hp _]]] := head_filter _ _ hys.
          have hfr : !(pkey (oget S.toks{2}.[u{2}]).`tk_i (head 0 (filter (fun (j1 : int) =>
                        j1 <> (oget S.toks{2}.[u{2}]).`tk_i /\ hpair S.cs{2} (oget S.toks{2}.[u{2}]).`tk_i j1
                        /\ !((oget S.req{2}.[u{2}], j1) \in S.lr{2})) (oget S.toks{2}.[u{2}]).`tk_T))
                        (oget S.toks{2}.[u{2}]).`tk_dig \in MPI.m{2}).
          - by move: hdf; rewrite /dfresh => /(_ hys hlr).
          rewrite take_size.
          move: hlk; rewrite take_size => hlk.
          pose i := (oget S.toks{2}.[u{2}]).`tk_i.
          pose T := (oget S.toks{2}.[u{2}]).`tk_T.
          pose d := (oget S.toks{2}.[u{2}]).`tk_dig.
          pose ys := filter (fun (j1 : int) => j1 <> i /\ hpair S.cs{2} i j1
                               /\ !((oget S.req{2}.[u{2}], j1) \in S.lr{2})) T.
          split; first by move=> v _; rewrite addsub3 sgnvK.
          move=> _; split; first by move=> v _; apply dvec_funi.
          move=> _ zL _; split; first by apply dvec_fu.
          move=> _; split; first by rewrite sgnvK addsub3r.
          move=> _; split; first by rewrite get_set_sameE /= resp_new.
          have [hA hB] := fin_new_B Fz.fz{1} MPI.m{2} S.lr{2} S.cs{2} H1O.QRO.fh{2} S.t{2} Lg.l1{2}
                            (oget S.req{2}.[u{2}]) i T ys d zL
                            (Rq.( * ) c{2} (lam_of T i) ** shr S.s{2} S.p{2} i
                             + (oget S.toks{2}.[u{2}]).`tk_r + mkc{2})
                            ha hks hlk hlr hu' hiC hiT hw hT hdig hl1 hys hhT hne hp hfr.
          split; first exact hA.
          split; first exact hB.
          exact cinv_erase.
        rcondf{1} 2; first by auto.
        rcondf{2} 1; first by auto.
        auto => /> &1 &2 hu hph _ hlk hks hdf ha hc hlr hys.
        have [hiC h2] := hc _ hu; have [#] _ hw _ hT hiT hdig hl1 := h2 hph.
        have hu' : uniq (oget S.toks{2}.[u{2}]).`tk_T.
        - by move: hw; rewrite /wfreq hT /wf_committee => -[[]].
        rewrite take_size hys.
        move: hlk; rewrite take_size hys => hlk.
        have [hv [hA hB]] := fin_new_C Fz.fz{1} MPI.m{2} S.lr{2} S.cs{2} H1O.QRO.fh{2} S.t{2} Lg.l1{2}
                               (oget S.req{2}.[u{2}]) (oget S.toks{2}.[u{2}]).`tk_i
                               (oget S.toks{2}.[u{2}]).`tk_T (oget S.toks{2}.[u{2}]).`tk_dig
                               (Rq.( * ) c{2} (lam_of (oget S.toks{2}.[u{2}]).`tk_T (oget S.toks{2}.[u{2}]).`tk_i)
                                ** shr S.s{2} S.p{2} (oget S.toks{2}.[u{2}]).`tk_i
                                + (oget S.toks{2}.[u{2}]).`tk_r + mkc{2})
                               ha hks hlk hlr hu' hiC hiT hw hT hdig hl1 hys.
        rewrite hv; split; first done.
        split; first exact hA.
        split; first exact hB.
        exact cinv_erase.
      by auto.
    by auto.
  by auto.
by auto.
qed.


(* Simulated first rounds terminate *)
lemma sofs_o1_ll : islossless SOFs(H0H.QRO, H1O.QRO).o1.
proof. by proc; inline *; sp; if => //; auto => />; smt(dnp_ll). qed.

(* Simulated second rounds terminate *)
lemma sofs_o2_ll : islossless SOFs(H0H.QRO, H1O.QRO).o2.
proof. by proc; inline *; auto. qed.

(* Simulated third rounds terminate *)
lemma sofs_o3_ll : islossless SOFs(H0H.QRO, H1O.QRO).o3.
proof.
proc; sp; if => //.
sp; if => //.
seq 1 : true => //; first by inline *; auto.
if => //.
seq 3 : true => //.
+ while true (size T - k); last by auto => /> /#.
  by move=> z; inline *; auto => /> /#.
if => //.
seq 6 : true => //.
+ while true (size T - k); last by auto => /> /#.
  move=> z; inline *; sp; if; last by auto => /> /#.
  if; last by auto => /> /#.
  by sp; if; auto => />; smt(dvec_ll).
sp; if; first by auto.
wp; if; last by auto.
by wp; rnd; auto => />; smt(dvec_ll).
qed.

(* Real third rounds terminate *)
lemma sof_o3_ll : islossless SOF(MPI, H0H.QRO, H1O.QRO).o3.
proof.
proc; sp; if => //.
sp; if => //.
seq 1 : true => //; first by inline *; auto.
if => //.
seq 3 : true => //.
+ while true (size T - k); last by auto => /> /#.
  by move=> z; inline *; auto => /> /#.
if => //.
seq 6 : true => //.
+ while true (size T - k); last by auto => /> /#.
  move=> z; inline *; sp; if; last by auto => /> /#.
  if; last by auto => /> /#.
  by sp; if; auto => />; smt(dvec_ll).
wp; if; last by auto.
by inline *; sp; if; auto => />; smt(dvec_ll).
qed.

(* Collisions persist when logs grow *)
lemma hascol_cons ['a 'b] (l : ('a * 'b) list) (e : 'a * 'b) : hascol l => hascol (e :: l).
proof. by move=> [x x' y] [#] h1 h2 h3; exists x x' y; rewrite !in_cons h1 h2 h3. qed.

(* Digest collisions persist through third rounds *)
lemma o3_bad : hoare [SOF(MPI, H0H.QRO, H1O.QRO).o3 : hascol Lg.l1 ==> hascol Lg.l1].
proof.
proc.
seq 1 : (hascol Lg.l1); first by auto.
if => //.
seq 1 : (hascol Lg.l1); first by auto.
if => //.
seq 1 : (hascol Lg.l1); first by inline *; auto => &hr [h _] /=; exact (hascol_cons _ _ h).
if => //.
seq 2 : (hascol Lg.l1); first by auto.
seq 1 : (hascol Lg.l1).
+ while (hascol Lg.l1); last by auto.
  by inline *; auto.
if => //.
seq 5 : (hascol Lg.l1); first by auto.
seq 1 : (hascol Lg.l1).
+ while (hascol Lg.l1); last by auto.
  seq 1 : (hascol Lg.l1); first by auto.
  if; last by auto.
  if; last by auto.
  by inline *; wp; sp; if; auto.
seq 1 : (hascol Lg.l1).
+ if; last by auto.
  by inline *; wp; sp; if; auto.
by auto.
qed.

(* Empty states satisfy the simulation invariant *)
lemma sinv_empty fz (req : (int, request) fmap) C h t l1 :
  sinv fz empty [] empty req C h t l1.
proof.
rewrite /sinv /ainv /binv /cinv /=.
by split => [k | u]; rewrite mem_empty.
qed.

(* The simulated game agrees with the first game until a digest collision *)
equiv run_sim :
  GameFs(A, H0H.QRO, H1O.QRO).run ~ GameF(A, MPI, H0H.QRO, H1O.QRO).run :
  ={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh} /\ MPI.m{1} = empty
  ==> !hascol Lg.l1{2} => ={res}.
proof.
proc; wp.
call (_ : hascol Lg.l1,
          ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            Cnt.c0, Cnt.c1, Cnt.cc, Cnt.cs, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
          /\ sinv Fz.fz{1} MPI.m{1} S.lr{1} S.toks{1} S.req{1} S.cs{1} H1O.QRO.fh{1} S.t{1} Lg.l1{1}).
+ move=> H O ho1 ho2 ho3 hh0 hh1 hhc.
  exact (A_ll H O hh0 hh1 hhc ho1 ho2 ho3).
+ by proc; wp; call o1_sim; auto => />.
+ by move=> &2 _; proc; call sofs_o1_ll; auto.
+ by move=> &1; proc; inline *; sp; if; [auto => />; smt(dnp_ll) | auto].
+ by proc; wp; call o2_sim; auto => />.
+ by move=> &2 _; proc; call sofs_o2_ll; auto.
+ by move=> &1; proc; inline *; auto => />; smt(hascol_cons).
+ by proc; wp; call o3_sim; auto => />.
+ by move=> &2 _; proc; call sofs_o3_ll; auto.
+ move=> &1; proc; wp; call (_ : hascol Lg.l1 ==> hascol Lg.l1); last by auto.
  by conseq sof_o3_ll o3_bad.
+ by proc; inline *; auto => />.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
+ by proc; inline *; auto => />.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
+ by proc; inline *; auto => />.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
auto; call (_ : true); auto => />.
move=> &2 cs s _ e _ p _ sdc _; split.
+ move=> _; split; first by rewrite /binv => k; rewrite mem_empty.
  by rewrite /cinv => u; rewrite mem_empty.
move=> _ _ _ r1 r2 a1 fz c0 c1 cc csn ctr lo lr req toks l0 l1 m
       a2 c0' c1' cc' csn' ctr' lo' lr' req' toks' l0' l1' m' h hnc.
have [#] hr _ _ _ _ hlo _ := h hnc.
by rewrite hr hlo.
qed.

(* The first game splits on digest collisions *)
lemma g1_split &m :
  Pr[G1(A).main() @ &m : res]
  <= Pr[G1(A).main() @ &m : res /\ !hascol Lg.l1] + Pr[G1(A).main() @ &m : hascol Lg.l1].
proof.
have -> : Pr[G1(A).main() @ &m : res]
        = Pr[G1(A).main() @ &m : (res /\ !hascol Lg.l1) \/ (res /\ hascol Lg.l1)].
+ by rewrite Pr[mu_eq] => /#.
rewrite Pr[mu_disjoint] 1:/#.
have : Pr[G1(A).main() @ &m : res /\ hascol Lg.l1] <= Pr[G1(A).main() @ &m : hascol Lg.l1].
+ by rewrite Pr[mu_sub].
smt().
qed.

(* The first game exceeds the simulated one by a digest collision *)
lemma g1_sim &m :
  Pr[G1(A).main() @ &m : res]
  <= Pr[G1s(A).main() @ &m : res] + Pr[G1(A).main() @ &m : hascol Lg.l1].
proof.
have h : Pr[G1(A).main() @ &m : res /\ !hascol Lg.l1] <= Pr[G1s(A).main() @ &m : res].
+ byequiv => //; symmetry; proc.
  call run_sim; inline *; auto => /> _ _ _ _ _ _ _ _ rL rR l1 h hr hnc.
  by rewrite h.
have := g1_split &m; smt().
qed.

(* Simulating the responses costs a digest collision *)
lemma g1_g1s &m :
  Pr[G1(A).main() @ &m : res]
  <= Pr[G1s(A).main() @ &m : res] + 27%r * (qh1 + 2 * qsig + 2)%r ^ 3 * p_max dview.
proof. by have := g1_sim &m; have := col1_bound A A_bnd &m; smt(). qed.

end section SimHop.

