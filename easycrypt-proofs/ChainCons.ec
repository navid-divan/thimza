require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt ChainRep ChainProg.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* ---------- the consistency of the game with programmed challenges ----------

   The flag Rp.bH of the game GP is raised only when one of the flags b1, b2, b3, extbad, bP,
   bC is raised.  We prove this with an invariant: either a flag is raised, or bH is not raised
   and the state satisfies the structural facts below. *)

(* The first message that a request gives to the member j *)
op owncmt (V : request) (j : int) : cmt = nth witness V.`3 (index j V.`2).

(* A token that opened the request V *)
op reqok (tk : token) (V : request) (lo : alog) : bool =
  tk.`tk_T = V.`2 /\ tk.`tk_msg = V.`1 /\ tk.`tk_i \in V.`2 /\ wf_committee V.`2 /\ inrange V.`2
  /\ size V.`3 = size V.`2 /\ owncmt V tk.`tk_i = tk.`tk_cmt /\ (V, tk.`tk_i) \in lo.

(* Facts on tokens, requests and the logs *)
op [opaque] gtok (toks : (int, token) fmap) (req : (int, request) fmap) (lo lr : alog)
                 (C : corrset) (ctr : int) (sv : (int, vec * row) fmap) : bool =
  0 <= ctr
  /\ (forall u, u \in toks => 0 <= u < ctr)
  /\ (forall u, u \in toks => !((oget toks.[u]).`tk_i \in C) /\ 1 <= (oget toks.[u]).`tk_i <= nmax)
  /\ (forall u, u \in sv => u \in toks /\ (oget toks.[u]).`tk_phase <> 1)
  /\ (forall u, u \in toks => ((oget toks.[u]).`tk_phase <> 1 <=> u \in req))
  /\ (forall u, u \in req => u \in toks /\ reqok (oget toks.[u]) (oget req.[u]) lo)
  /\ (forall (V : request) (j : int), (V, j) \in lo =>
        exists u, u \in toks /\ req.[u] = Some V /\ (oget toks.[u]).`tk_i = j)
  /\ (forall (V : request) (j : int), (V, j) \in lr =>
        exists u, u \in toks /\ req.[u] = Some V /\ (oget toks.[u]).`tk_i = j
                  /\ (oget toks.[u]).`tk_phase = 0)
  /\ (forall u u', u \in toks => u' \in toks => u <> u' =>
        (oget toks.[u]).`tk_cmt <> (oget toks.[u']).`tk_cmt)
  /\ (forall (V : request) (a u : int), (V, a) \in lr => u \in toks => (oget toks.[u]).`tk_phase = 1 =>
        (oget toks.[u]).`tk_i \in V.`2 => owncmt V (oget toks.[u]).`tk_i <> (oget toks.[u]).`tk_cmt).

(* Facts on complete requests *)
op [opaque] gdone (toks : (int, token) fmap) (req : (int, request) fmap) (lo : alog) (C : corrset)
                  (dn : request list) (cV : (request, rq) fmap) (sV : (request, vec * row) fmap)
                  (lop : (request, int) fmap) (ix : (request * int, int) fmap) (ts : cmt list) : bool =
  (forall (V : request), honest V.`2 C <> [] => complete V C lo => V \in dn)
  /\ (forall (V : request), V \in cV \/ V \in lop \/ V \in sV => V \in dn)
  /\ (forall (V : request), V \in dn => V \in cV /\ V \in lop /\ V \in sV /\ complete V C lo
        /\ oget lop.[V] \in toks /\ req.[oget lop.[V]] = Some V
        /\ ((oget toks.[oget lop.[V]]).`tk_phase = 2 =>
            (oget toks.[oget lop.[V]]).`tk_r = (oget sV.[V]).`1))
  /\ (forall (V : request) (j : int), V \in dn => j \in V.`2 => j \in C =>
        (V, j) \in ix /\ 0 <= oget ix.[(V, j)] < size ts
        /\ nth witness ts (oget ix.[(V, j)]) = owncmt V j).

(* Facts on programmed challenges *)
op [opaque] gprog (toks : (int, token) fmap) (req : (int, request) fmap) (C : corrset)
                  (xs : h0in option list) (ix : (request * int, int) fmap) (cV : (request, rq) fmap)
                  (pts : hcin list) (fhp : hcin -> rq) (t : row) : bool =
  forall (V : request), V \in cV => fhp (xpt t V.`1 (wsV toks req C xs ix V)) = oget cV.[V]
                       /\ xpt t V.`1 (wsV toks req C xs ix V) \in pts.

(* Facts on the stored responses *)
op [opaque] gresp (toks : (int, token) fmap) (lr : alog) (cV : (request, rq) fmap)
                  (sV : (request, vec * row) fmap) (cz : (request * int, rq) fmap)
                  (fz : (request * int, vec * vec) fmap) (dz : (request * int, vec) fmap)
                  (lop : (request, int) fmap) : bool =
  forall (V : request) (a : int), (V, a) \in lr => (V, a) \in fz /\ (V, a) \in cz /\ (V, a) \in dz
    /\ (V \in cV => oget cz.[(V, a)] = oget cV.[V]
                   /\ oget dz.[(V, a)] = (if a = (oget toks.[oget lop.[V]]).`tk_i
                                          then (oget sV.[V]).`1 else RqVec.Vector.zerov)).

(* One of the flags is raised *)
op flg (b1 b2 b3 bP bC : bool) (ts : cmt list) (xs : h0in option list)
       (cks : (int * h0in * cmt) list) : bool =
  b1 \/ b2 \/ b3 \/ H0C.extbad ts xs cks \/ bP \/ bC.

(* ---------- basic facts ---------- *)

(* The extraction flag survives new checks and submissions *)
lemma extbad_cks (ts : cmt list) xs cks e :
  H0C.extbad ts xs cks => H0C.extbad ts xs (rcons cks e).
proof. by move=> [e0] [h1 h2]; exists e0; rewrite mem_rcons /= h1. qed.

lemma extbad_sub (ts : cmt list) (xs : h0in option list) cks (t : cmt) (r : h0in option) :
  size xs = size ts => H0C.extbad ts xs cks => H0C.extbad (rcons ts t) (rcons xs r) cks.
proof.
move=> hs [e] [he [[h0 h1] [h2 h3]]]; exists e; split => //.
rewrite size_rcons; split; first smt().
have h1' : e.`1 < size xs by rewrite hs.
by rewrite !nth_rcons h1 h1' /=.
qed.

(* A token found by the opener choice *)
lemma tokofP (toks : (int, token) fmap) (req : (int, request) fmap) (V : request) (j : int) :
  (exists u, u \in toks /\ req.[u] = Some V /\ (oget toks.[u]).`tk_i = j) =>
  tokof toks req V j \in toks /\ req.[tokof toks req V j] = Some V
  /\ (oget toks.[tokof toks req V j]).`tk_i = j.
proof.
move=> [u hu]; rewrite /tokof.
have := choicebP (fun u => u \in toks /\ req.[u] = Some V /\ (oget toks.[u]).`tk_i = j) 0 _.
+ by exists u.
done.
qed.

(* The position of a member in a committee without repetition *)
lemma index_nth_uniq (T : int list) (k : int) : uniq T => 0 <= k < size T => index (nth 0 T k) T = k.
proof. by move=> hu hk; rewrite index_uniq. qed.

(* Committee members of a request *)
lemma owncmt_nth (V : request) (k : int) :
  uniq V.`2 => 0 <= k < size V.`2 => owncmt V (nth 0 V.`2 k) = nth witness V.`3 k.
proof. by move=> hu hk; rewrite /owncmt index_nth_uniq. qed.

(* Before any query the facts hold *)
lemma good_init (t : row) (C : corrset) (fhp : hcin -> rq) :
  gtok empty empty [] [] C 0 empty /\ gdone empty empty [] C [] empty empty empty empty []
  /\ gprog empty empty C [] empty empty [] fhp t /\ gresp empty [] empty empty empty empty empty empty.
proof.
split; first by rewrite /gtok; smt(mem_empty).
split.
+ rewrite /gdone; split.
  - move=> V hn hc; have [j hj] : exists j, j \in honest V.`2 C.
    + by exists (head 0 (honest V.`2 C)); move: hn; case: (honest V.`2 C) => //.
    by move: hc; rewrite /complete => /allP /(_ j hj).
  smt(mem_empty).
split; first by rewrite /gprog; smt(mem_empty).
by rewrite /gresp; smt(mem_empty).
qed.

(* The openings of a request depend only on its openers *)
lemma wsV_frame (toks1 toks2 : (int, token) fmap) (req1 req2 : (int, request) fmap) (C : corrset)
                xs ix (V : request) :
  (forall j, j \in V.`2 => !(j \in C) =>
     (fun u => u \in toks1 /\ req1.[u] = Some V /\ (oget toks1.[u]).`tk_i = j)
     = (fun u => u \in toks2 /\ req2.[u] = Some V /\ (oget toks2.[u]).`tk_i = j)
     /\ (oget toks1.[tokof toks1 req1 V j]).`tk_wbar = (oget toks2.[tokof toks1 req1 V j]).`tk_wbar) =>
  wsV toks1 req1 C xs ix V = wsV toks2 req2 C xs ix V.
proof.
move=> h; rewrite /wsV; apply eq_in_map => j hj /=.
case: (j \in C) => // hc.
have [hp hw] := h j hj hc.
by rewrite /hwbar /tokof -hp -/(tokof toks1 req1 V j) hw.
qed.

(* A complete request has an opener for each honest member *)
lemma good_opener toks req lo lr C ctr sv dn cV sV lop ix ts (V : request) (j : int) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  V \in dn => j \in V.`2 => !(j \in C) =>
  exists u, u \in toks /\ req.[u] = Some V /\ (oget toks.[u]).`tk_i = j.
proof.
rewrite /gtok /gdone => -[#] _ _ _ _ _ _ hlo _ _ _ [_ [_ [hd _]]] hV hj hc.
have [_ [_ [_ [hcmp _]]]] := hd V hV.
apply (hlo V j); move: hcmp; rewrite /complete => /allP; apply.
by rewrite /honest List.mem_filter.
qed.

(* A first round keeps the facts unless it raises the second flag *)
lemma cons_o1 toks req lo lr C ctr sv dn cV sV lop ix ts xs pts fhp t cz fz dz (tk : token) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  gprog toks req C xs ix cV pts fhp t => gresp toks lr cV sV cz fz dz lop =>
  1 <= tk.`tk_i <= nmax => !(tk.`tk_i \in C) => tk.`tk_phase = 1 =>
  !(dupc toks tk.`tk_cmt) => !(seenc lr tk.`tk_cmt) =>
  gtok toks.[ctr <- tk] req lo lr C (ctr + 1) sv /\ gdone toks.[ctr <- tk] req lo C dn cV sV lop ix ts
  /\ gprog toks.[ctr <- tk] req C xs ix cV pts fhp t /\ gresp toks.[ctr <- tk] lr cV sV cz fz dz lop.
proof.
move=> hgt hgd hgp hgr hi hic hph hdup hseen.
have hfresh : !(ctr \in toks) by move: hgt; rewrite /gtok => -[#] h0 h1 *; smt().
have hreq : !(ctr \in req) by move: hgt; rewrite /gtok => -[#] h0 h1 h2 h3 h4 h5 *; smt().
have hlop : forall V, V \in dn => oget lop.[V] <> ctr.
+ move=> V hV; move: hgd; rewrite /gdone => -[_ [_ [hd _]]].
  have [_ [_ [_ [_ [hl _]]]]] := hd V hV; smt().
split.
+ move: hgt; rewrite /gtok => -[#] h0 h1 h2 h3 h4 h5 h6 h7 h8 h9.
  do !split.
  - smt().
  - by move=> u; rewrite mem_set; smt().
  - by move=> u; rewrite mem_set get_setE; case: (u = ctr) => [-> /= | hne /=]; [smt() | exact h2].
  - move=> u hu; have [hu1 hu2] := h3 u hu.
    by rewrite mem_set get_setE hu1 /=; smt().
  - move=> u; rewrite mem_set get_setE; case: (u = ctr) => [-> /= | hne /= hu]; first by rewrite hph hreq.
    exact (h4 u hu).
  - move=> u hu; have [hu1 hu2] := h5 u hu.
    by rewrite mem_set get_setE hu1 /=; smt().
  - move=> V j hV; have [u [hu [hr hj]]] := h6 V j hV.
    by exists u; rewrite mem_set get_setE hu /=; smt().
  - move=> V j hV; have [u [hu [hr [hj hp]]]] := h7 V j hV.
    by exists u; rewrite mem_set get_setE hu /=; smt().
  - move=> u u'; rewrite !mem_set !get_setE => hu hu' hne.
    by move: hdup; rewrite /dupc; smt().
  move=> V a u hV; rewrite mem_set get_setE; case: (u = ctr) => [-> /= | hne /= hu].
  - move=> _ hiV; apply/negP => heq; apply hseen; exists V a; split => //.
    have [w [hw [hrw [hjw _]]]] := h7 V a hV.
    have [_ hok] := h5 w _; first by rewrite domE hrw.
    move: hok; rewrite hrw /= /reqok => -[_ [_ [_ [_ [_ [hsz _]]]]]].
    rewrite -heq /owncmt; apply mem_nth; split; first exact index_ge0.
    by rewrite hsz index_mem.
  exact (h9 V a u hV hu).
split.
+ move: hgd; rewrite /gdone => -[h1 [h2 [h3 h4]]]; do !split => //.
  move=> V hV; have [#] hc hl hs hcp hm hr hp := h3 V hV.
  do !split => //; first by rewrite mem_set hm.
  have hne := hlop V hV.
  by rewrite get_setE hne /=.
split.
+ move: hgp; rewrite /gprog => h V hV.
  have hVd : V \in dn by move: hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
  have hw : wsV toks req C xs ix V = wsV toks.[ctr <- tk] req C xs ix V.
  - apply wsV_frame => j hj hjc; split.
    + apply fun_ext => u /=; rewrite mem_set get_setE.
      by case: (u = ctr) => [-> | hne] /=; smt().
    have [w hw] := good_opener _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hgt hgd hVd hj hjc.
    have [hw1 [hw2 _]] := tokofP toks req V j _; first by exists w.
    have hne : tokof toks req V j <> ctr by smt().
    by rewrite get_setE hne.
  by rewrite -hw; exact (h V hV).
move: hgr; rewrite /gresp => h V a hV; have [#] h1 h2 h3 h4 := h V a hV.
do !split => // hcv; have [h5 h6] := h4 hcv; split => //.
have hVd : V \in dn by move: hgd; rewrite /gdone => -[_ [h7 _]]; apply h7; left.
by rewrite get_setE (hlop V hVd) /=.
qed.

(* ---------- the checks of a response ---------- *)

(* The checks so far accepted only openings that agree with the openers *)
op [opaque] chkok (toks : (int, token) fmap) (req : (int, request) fmap) (C : corrset)
                  (xs : h0in option list) (ix : (request * int, int) fmap) (cV : (request, rq) fmap)
                  (V : request) (T : committee) (cs : cmt list) (ws : row list) (k : int) : bool =
  forall k', 0 <= k' < k =>
    (!(nth 0 T k' \in C) => forall u, u \in toks => (oget toks.[u]).`tk_phase = 1 =>
        (oget toks.[u]).`tk_i = nth 0 T k' => (oget toks.[u]).`tk_cmt <> nth witness cs k')
    /\ (V \in cV => nth witness ws k' = nth witness (wsV toks req C xs ix V) k').

lemma chkok0 toks req C xs ix cV V T cs ws : chkok toks req C xs ix cV V T cs ws 0.
proof. by rewrite /chkok => k' /#. qed.

(* The opening of a complete request at an honest position *)
lemma wsV_hon (toks : (int, token) fmap) req C xs ix (V : request) (k : int) :
  0 <= k < size V.`2 => !(nth 0 V.`2 k \in C) =>
  nth witness (wsV toks req C xs ix V) k = hwbar toks req V (nth 0 V.`2 k).
proof. by move=> hk hc; rewrite /wsV (nth_map 0) //= hc. qed.

lemma wsV_cor (toks : (int, token) fmap) req C xs ix (V : request) (k : int) :
  0 <= k < size V.`2 => nth 0 V.`2 k \in C =>
  nth witness (wsV toks req C xs ix V) k = xwbar xs ix V (nth 0 V.`2 k).
proof. by move=> hk hc; rewrite /wsV (nth_map 0) //= hc. qed.

(* An honest check that accepts either raises the first flag or agrees with the openers *)
lemma chkok_hon toks req lo lr C ctr sv dn cV sV lop ix ts xs (V : request) (cs : cmt list)
                (ws : row list) (k : int) (mu : msg) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  cs = V.`3 => uniq V.`2 => 0 <= k < size V.`2 => !(nth 0 V.`2 k \in C) =>
  chkok toks req C xs ix cV V V.`2 cs ws k =>
  incons toks (nth 0 V.`2 k) mu (nth witness cs k) (nth witness ws k)
  \/ chkok toks req C xs ix cV V V.`2 cs ws (k + 1).
proof.
move=> hgt hgd hcs hu hk hc hok.
case: (incons toks (nth 0 V.`2 k) mu (nth witness cs k) (nth witness ws k)) => hinc; [by left | right].
move: hok; rewrite /chkok => hok k' hk'.
case: (k' < k) => hlt.
+ by apply (hok k'); smt().
have -> : k' = k by smt().
split.
+ move=> _ u hu1 hph hi; apply/negP => heq; apply hinc.
  by exists u; rewrite /cmtok hu1 hi heq /= hph.
move=> hcv.
have hVd : V \in dn by move: hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
have hj : nth 0 V.`2 k \in V.`2 by apply mem_nth.
have [w hw] := good_opener _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgt hgd hVd hj hc.
have [hw1 [hw2 hw3]] := tokofP toks req V (nth 0 V.`2 k) _; first by exists w.
rewrite (wsV_hon _ _ _ _ _ _ _ hk hc) /hwbar.
case: (nth witness ws k = (oget toks.[tokof toks req V (nth 0 V.`2 k)]).`tk_wbar) => // hne.
have : incons toks (nth 0 V.`2 k) mu (nth witness cs k) (nth witness ws k); last by smt().
exists (tokof toks req V (nth 0 V.`2 k)); split.
+ rewrite /cmtok hw1 hw3 /=.
  move: hgt; rewrite /gtok => -[#] _ _ _ _ _ hreq _.
  have [_ hro] := hreq (tokof toks req V (nth 0 V.`2 k)) _; first by rewrite domE hw2.
  move: hro; rewrite hw2 /= /reqok => -[_ [_ [_ [_ [_ [_ [hcm _]]]]]]].
  by rewrite -hcm hw3 owncmt_nth // hcs.
by right; right; rewrite eq_sym.
qed.

(* A corrupt check that accepts either raises the extraction flag or agrees with the extraction *)
lemma chkok_cor toks req lo lr C ctr sv dn cV sV lop ix ts xs (cks : (int * h0in * cmt) list)
                (V : request) (cs : cmt list) (ws : row list) (k : int) (x : h0in) (y : cmt) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  cs = V.`3 => uniq V.`2 => 0 <= k < size V.`2 => nth 0 V.`2 k \in C =>
  x.`2 = nth witness ws k => y = nth witness cs k =>
  (V \in cV => (oget ix.[(V, nth 0 V.`2 k)], x, y) \in cks) =>
  chkok toks req C xs ix cV V V.`2 cs ws k =>
  H0C.extbad ts xs cks \/ chkok toks req C xs ix cV V V.`2 cs ws (k + 1).
proof.
move=> hgt hgd hcs hu hk hc hx hy hck hok.
case: (V \in cV) => hcv; last first.
+ right; move: hok; rewrite /chkok => hok k' hk'.
  case: (k' < k) => hlt.
  - by apply (hok k'); smt().
  have -> : k' = k by smt().
  by split; smt().
have hVd : V \in dn by move: hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
have hj : nth 0 V.`2 k \in V.`2 by apply mem_nth.
move: hgd; rewrite /gdone => -[_ [_ [_ hix]]].
have [hin [[h0 h1] hts]] := hix V (nth 0 V.`2 k) hVd hj hc.
case: (nth None xs (oget ix.[(V, nth 0 V.`2 k)]) = Some x) => hxs; last first.
+ left; exists (oget ix.[(V, nth 0 V.`2 k)], x, y); do !split => //=.
  - by apply hck.
  by rewrite hts hy hcs owncmt_nth.
right; move: hok; rewrite /chkok => hok k' hk'.
case: (k' < k) => hlt.
+ by apply (hok k'); smt().
have -> : k' = k by smt().
split.
+ by move=> hnc; have := hnc; rewrite hc.
by move=> _; rewrite (wsV_cor _ _ _ _ _ _ _ hk hc) /xwbar hxs /= hx.
qed.

(* ---------- a response ---------- *)

(* A responding token opened its request *)
lemma resp_req toks req lo lr C ctr sv (u : int) :
  gtok toks req lo lr C ctr sv => u \in toks => (oget toks.[u]).`tk_phase = 2 =>
  u \in req /\ reqok (oget toks.[u]) (oget req.[u]) lo.
proof.
rewrite /gtok => -[#] _ _ _ _ h4 h5 _ _ _ _ hu hph.
have hr : u \in req by rewrite -(h4 u hu) hph.
by have [_ ?] := h5 u hr; split.
qed.

(* Two openers of a request by one member are the same token *)
lemma same_opener toks req lo lr C ctr sv (u u' : int) (V : request) :
  gtok toks req lo lr C ctr sv => u \in toks => u' \in toks =>
  req.[u] = Some V => req.[u'] = Some V =>
  (oget toks.[u]).`tk_i = (oget toks.[u']).`tk_i => u = u'.
proof.
move=> hgt hu hu' hr hr' hi; move: hgt; rewrite /gtok => -[#] _ _ _ _ _ h5 _ _ h8 _.
have [_ hok] := h5 u _; first by rewrite domE hr.
have [_ hok'] := h5 u' _; first by rewrite domE hr'.
move: hok hok'; rewrite hr hr' /= /reqok => -[_ [_ [_ [_ [_ [_ [hc _]]]]]]] [_ [_ [_ [_ [_ [_ [hc' _]]]]]]].
case: (u = u') => // hne.
by have := h8 u u' hu hu' hne; rewrite -hc -hc' hi.
qed.

(* The member set of a request whose other honest members responded is complete *)
lemma ys_complete toks req lo lr C ctr sv (u : int) (V : request) (T : committee) :
  gtok toks req lo lr C ctr sv => u \in toks => req.[u] = Some V =>
  reqok (oget toks.[u]) V lo => T = V.`2 =>
  filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                   /\ !((V, j) \in lr)) T = [] =>
  complete V C lo /\ honest V.`2 C <> [].
proof.
move=> hgt hu hr hok hT hys.
have hiC : !((oget toks.[u]).`tk_i \in C) by move: hgt; rewrite /gtok => -[#] _ _ h2 *; have [] := h2 u hu.
have hiT : (oget toks.[u]).`tk_i \in V.`2 by move: hok; rewrite /reqok.
split; last first.
+ have : (oget toks.[u]).`tk_i \in honest V.`2 C by rewrite /honest List.mem_filter.
  by case: (honest V.`2 C).
rewrite /complete; apply/allP => j; rewrite /honest List.mem_filter => -[/= hjC hjT] /=.
case: (j = (oget toks.[u]).`tk_i) => [-> | hne]; first by move: hok; rewrite /reqok.
have hlr : (V, j) \in lr.
+ case: ((V, j) \in lr) => // hn.
  have : j \in filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                               /\ !((V, j) \in lr)) T.
  - by rewrite List.mem_filter /hpair; smt().
  by rewrite hys.
move: hgt; rewrite /gtok => -[#] _ _ _ _ _ h5 _ h7 _ _.
have [w [hw [hrw [hjw _]]]] := h7 V j hlr.
have [_ hokw] := h5 w _; first by rewrite domE hrw.
by move: hokw; rewrite hrw /= /reqok hjw => -[#] *.
qed.

(* The nonce part of a response that is not a closing one *)
lemma dzk_ok toks req lo lr C ctr sv dn cV sV lop ix ts (u : int) (V : request) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 => req.[u] = Some V => V \in cV =>
  (if lop.[V] = Some u then (oget toks.[u]).`tk_r else RqVec.Vector.zerov)
  = (if (oget toks.[u]).`tk_i = (oget toks.[oget lop.[V]]).`tk_i then (oget sV.[V]).`1
     else RqVec.Vector.zerov).
proof.
move=> hgt hgd hu hph hr hcv.
have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
have := hgd; rewrite /gdone => -[_ [_ [hd _]]].
have [#] _ hl _ _ hlt hlr hlp := hd V hVd.
have hsome : lop.[V] = Some (oget lop.[V]) by move: hl; rewrite domE; case: (lop.[V]).
case: (oget lop.[V] = u) => [heq | hne].
+ move: hlp; rewrite hsome heq /= => hlp.
  by rewrite (hlp hph).
have hi : (oget toks.[u]).`tk_i <> (oget toks.[oget lop.[V]]).`tk_i.
+ by apply/negP => hi; have := same_opener _ _ _ _ _ _ _ _ _ _ hgt hu hlt hr hlr hi; smt().
have hl' : lop.[V] <> Some u by rewrite hsome; smt().
by rewrite hi hl'.
qed.

(* Under the facts, none of the conditions of the simulation flag holds at a response *)
lemma cons_noh toks req lo lr C ctr sv dn cV sV lop ix ts xs pts fhp t cz fz dz
               (u : int) (V : request) (T : committee) (cs : cmt list) (ws : row list) (c : rq) :
  (forall T, wf_committee T => inrange T => wf_nodes T) =>
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  gprog toks req C xs ix cV pts fhp t => gresp toks lr cV sV cz fz dz lop =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 => req.[u] = Some V =>
  T = (oget toks.[u]).`tk_T => cs = V.`3 => size ws = size T =>
  chkok toks req C xs ix cV V V.`2 cs ws (size V.`2) =>
  c = fhp (liftw (aggw ws), (t, (oget toks.[u]).`tk_msg)) =>
  !((V, (oget toks.[u]).`tk_i) \in lr
    \/ (V \in cV /\ c <> oget cV.[V])
    \/ (filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                         /\ !((V, j) \in lr)) T = [] /\ !(V \in cV))
    \/ (V \in lop /\ oget lop.[V] <> u /\ (oget toks.[oget lop.[V]]).`tk_i = (oget toks.[u]).`tk_i)
    \/ T <> V.`2
    \/ (filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                         /\ !((V, j) \in lr)) T = []
        /\ !((V, (oget toks.[u]).`tk_i) \in lr)
        /\ !okclose lop sV cV toks fz cz dz C V T (oget toks.[u]).`tk_i
                    (if lop.[V] = Some u then (oget toks.[u]).`tk_r else RqVec.Vector.zerov))).
proof.
move=> hsep hgt hgd hgp hgr hu hph hr hT hcs hws hok hc.
have [hur hro] := resp_req _ _ _ _ _ _ _ _ hgt hu hph.
move: hro; rewrite hr /= => hro.
have := hro; rewrite /reqok => -[hTV [hmsg [hiV [hwf [hin [hsz [hown hlo]]]]]]].
have hiC : !((oget toks.[u]).`tk_i \in C).
+ by have := hgt; rewrite /gtok => -[#] _ _ h2 *; have [] := h2 u hu.
(* a duplicate response *)
have h3 : !((V, (oget toks.[u]).`tk_i) \in lr).
+ apply/negP => hin3.
  have := hgt; rewrite /gtok => -[#] _ _ _ _ _ _ _ h7 _ _.
  have [w [hw [hrw [hjw hpw]]]] := h7 V _ hin3.
  have heq := same_opener _ _ _ _ _ _ _ u w V hgt hu hw hr hrw _; first by rewrite hjw.
  by move: hpw; rewrite -heq hph.
(* the closing condition gives a complete request *)
have hcl : filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                            /\ !((V, j) \in lr)) T = [] => V \in cV.
+ move=> hys.
  have [hcp hne] := ys_complete _ _ _ _ _ _ _ u V T hgt hu hr hro _ hys; first by rewrite hT.
  have hVd : V \in dn by have := hgd; rewrite /gdone => -[h1 _]; apply h1.
  by have := hgd; rewrite /gdone => -[_ [_ [hd _]]]; have [] := hd V hVd.
(* another opener of the same member *)
have h6 : !(V \in lop /\ oget lop.[V] <> u
            /\ (oget toks.[oget lop.[V]]).`tk_i = (oget toks.[u]).`tk_i).
+ apply/negP => -[hl [hne hi]].
  have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; right; left.
  have := hgd; rewrite /gdone => -[_ [_ [hd _]]].
  have [#] _ _ _ _ hlt hlr _ := hd V hVd.
  by have := same_opener _ _ _ _ _ _ _ _ _ _ hgt hu hlt hr hlr _; [rewrite hi | rewrite eq_sym hne].
(* the challenge of a complete request *)
have h4 : !(V \in cV /\ c <> oget cV.[V]).
+ apply/negP => -[hcv hne]; apply hne.
  have hwsV : ws = wsV toks req C xs ix V.
  - apply (eq_from_nth witness); first by rewrite /wsV size_map hws hT hTV.
    move=> k hk; move: hok; rewrite /chkok => hok.
    have [_ h2] := hok k _; first smt().
    by apply h2.
  have := hgp; rewrite /gprog => /(_ V hcv) [<- _].
  by rewrite hc /xpt hwsV hmsg.
apply/negP => -[h | [h | [h | [h | [h | h]]]]].
+ by move: h3; rewrite h.
+ by move: h4; rewrite h.
+ by move: h => [hys hcv]; apply hcv; apply hcl.
+ by move: h6; rewrite h.
+ by move: h; rewrite hT hTV.
move: h => [hys [_ hncl]]; apply hncl.
have hcv := hcl hys.
have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
have := hgd; rewrite /gdone => -[_ [_ [hd _]]].
have [#] _ hl hs _ hlt hlr _ := hd V hVd.
have hTV' : T = V.`2 by rewrite hT hTV.
have hpT : (oget toks.[oget lop.[V]]).`tk_i \in honest T C.
+ have := hgt; rewrite /gtok => -[#] _ _ h2 _ _ h5 *.
  have [_ hrl] := h5 (oget lop.[V]) _; first by rewrite domE hlr.
  move: hrl; rewrite hlr /= /reqok => -[#] _ _ hpi *.
  rewrite /honest List.mem_filter hTV' hpi /=.
  by have [] := h2 _ hlt.
have [hn1 [hn2 hn3]] : PolyList.sep (nodesOf T) /\ uniq (nodesOf T) /\ size (nodesOf T) = tthr.
+ by have := hsep T _ _; [rewrite hTV' | rewrite hTV' | rewrite /wf_nodes].
rewrite /okclose /=; do !split => //.
+ by rewrite /honest; apply filter_uniq; rewrite hTV'; move: hwf; rewrite /wf_committee.
+ by rewrite /honest List.mem_filter hTV' hiV.
+ move=> a; rewrite List.mem_filter => -[hai haT].
  have hlra : (V, a) \in lr.
  - case: ((V, a) \in lr) => // hn.
    have : a \in filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                                  /\ !((V, j) \in lr)) T.
    + move: haT; rewrite /honest List.mem_filter => -[/= haC haT].
      by rewrite List.mem_filter /hpair; smt().
    by rewrite hys.
  have := hgr; rewrite /gresp => /(_ V a hlra) [#] hf hcz hdz /(_ hcv) [hcz' hdz'].
  by do !split.
by rewrite (dzk_ok _ _ _ _ _ _ _ _ _ _ _ _ _ u V hgt hgd hu hph hr hcv).
qed.

(* Erasing keeps the public fields of a token *)
lemma erase_flds (tk : token) :
  (erase tk).`tk_i = tk.`tk_i /\ (erase tk).`tk_msg = tk.`tk_msg /\ (erase tk).`tk_wbar = tk.`tk_wbar
  /\ (erase tk).`tk_cmt = tk.`tk_cmt /\ (erase tk).`tk_T = tk.`tk_T /\ (erase tk).`tk_phase = 0.
proof. by rewrite /erase. qed.

(* A first response keeps the facts *)
lemma cons_o3 toks req lo lr C ctr sv dn cV sV lop ix ts xs pts fhp t cz fz dz
              (u : int) (V : request) (cs : cmt list) (ws : row list) (c : rq) (z f : vec) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  gprog toks req C xs ix cV pts fhp t => gresp toks lr cV sV cz fz dz lop =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 => req.[u] = Some V => cs = V.`3 =>
  chkok toks req C xs ix cV V V.`2 cs ws (size V.`2) =>
  !((V, (oget toks.[u]).`tk_i) \in lr) => (V \in cV => c = oget cV.[V]) =>
  gtok toks.[u <- erase (oget toks.[u])] req lo ((V, (oget toks.[u]).`tk_i) :: lr) C ctr sv
  /\ gdone toks.[u <- erase (oget toks.[u])] req lo C dn cV sV lop ix ts
  /\ gprog toks.[u <- erase (oget toks.[u])] req C xs ix cV pts fhp t
  /\ gresp toks.[u <- erase (oget toks.[u])] ((V, (oget toks.[u]).`tk_i) :: lr) cV sV
           cz.[(V, (oget toks.[u]).`tk_i) <- c] fz.[(V, (oget toks.[u]).`tk_i) <- (z, f)]
           dz.[(V, (oget toks.[u]).`tk_i) <- (if lop.[V] = Some u then (oget toks.[u]).`tk_r
                                               else RqVec.Vector.zerov)] lop.
proof.
move=> hgt hgd hgp hgr hu hph hr hcs hok hnd hc.
have [hur hro] := resp_req _ _ _ _ _ _ _ _ hgt hu hph.
move: hro; rewrite hr /= => hro.
have := hro; rewrite /reqok => -[hTV [hmsg [hiV [hwf [hin [hsz [hown hlo]]]]]]].
have [#] he1 he2 he3 he4 he5 he6 := erase_flds (oget toks.[u]).
split.
+ have := hgt; rewrite /gtok => -[#] h0 h1 h2 h3 h4 h5 h6 h7 h8 h9.
  do !split => //.
  - by move=> w; rewrite mem_set; smt().
  - by move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /=]; [rewrite he1; exact (h2 u hu) | exact h2].
  - move=> w hw; have [hw1 hw2] := h3 w hw.
    by rewrite mem_set get_setE; case: (w = u) => [-> | hne] /=; smt().
  - move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; first by rewrite he6.
    exact (h4 w hw).
  - move=> w hw; have [hw1 hw2] := h5 w hw.
    rewrite mem_set get_setE hw1 /=; case: (w = u) => [-> /= | hne /=] //.
    by move: hro; rewrite hr /= /reqok he1 he2 he4 he5.
  - move=> W j hW; have [w [hw [hrw hjw]]] := h6 W j hW.
    exists w; rewrite mem_set get_setE hw hrw /=.
    by case: (w = u) => [heq | hne] /=; smt().
  - move=> W j; rewrite in_cons; case => [[-> ->] | hW].
    + by exists u; rewrite mem_set get_setE /= he1 he6 hr.
    have [w [hw [hrw [hjw hpw]]]] := h7 W j hW.
    have hne : w <> u by smt().
    by exists w; rewrite mem_set !get_setE hne /= hw hrw hjw hpw.
  - move=> w w'; rewrite !mem_set !get_setE => hw hw' hne.
    smt().
  move=> W a w; rewrite in_cons mem_set get_setE.
  case: (w = u) => [-> /= | hne /=]; first by rewrite he6.
  move=> hWa hw hph1 hiw; case: hWa => [[hW _] | hWa]; last exact (h9 W a w hWa hw hph1 hiw).
  rewrite hW; move: hiw; rewrite hW => hiw.
  have hk : 0 <= index (oget toks.[w]).`tk_i V.`2 < size V.`2 by rewrite index_ge0 index_mem.
  move: hok; rewrite /chkok => /(_ _ hk) [h1' _].
  have := h1' _ w hw hph1 _.
  - by rewrite nth_index //; have [] := h2 w hw.
  - by rewrite nth_index.
  by rewrite hcs /owncmt; apply contra => ->.
split.
+ have := hgd; rewrite /gdone => -[h1 [h2 [h3 h4]]]; do !split => //.
  move=> W hW; have [#] hc' hl hs hcp hm hrq hp := h3 W hW.
  do !split => //; first by rewrite mem_set hm.
  rewrite get_setE; case: (oget lop.[W] = u) => [heq | hne] /=; first by rewrite he6.
  exact hp.
split.
+ have := hgp; rewrite /gprog => h W hW.
  have hw : wsV toks req C xs ix W = wsV toks.[u <- erase (oget toks.[u])] req C xs ix W.
  - apply wsV_frame => j hj hjc; split.
    + apply fun_ext => w /=; rewrite mem_set get_setE.
      by case: (w = u) => [-> | hne] /=; smt().
    by rewrite get_setE; case: (tokof toks req W j = u) => [-> | hne] /=; smt().
  by have := h W hW; rewrite hw.
have := hgr; rewrite /gresp => h W a; rewrite in_cons.
case: ((W, a) = (V, (oget toks.[u]).`tk_i)) => [heq | hne].
+ move: heq => [-> ->] _; rewrite !mem_set !get_set_sameE /=.
  move=> hcv; split; first by rewrite hc.
  have hlt : oget lop.[V] \in toks.
  - have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
    by have := hgd; rewrite /gdone => -[_ [_ [hd _]]]; have [#] := hd V hVd.
  rewrite get_setE; case: (oget lop.[V] = u) => [heq | hne] /=.
  - have := dzk_ok _ _ _ _ _ _ _ _ _ _ _ _ _ u V hgt hgd hu hph hr hcv.
    rewrite heq /= => ->.
    by rewrite he1.
  exact (dzk_ok _ _ _ _ _ _ _ _ _ _ _ _ _ u V hgt hgd hu hph hr hcv).
move=> /= hWa; have hWa' : (W, a) \in lr by smt().
have [#] h1 h2 h3 h4 := h W a hWa'.
rewrite !mem_set !get_setE hne /= h1 h2 h3 /=.
move=> hcv; have [h5 h6] := h4 hcv; split => //.
have hlt : oget lop.[W] \in toks.
+ have hVd : W \in dn by have := hgd; rewrite /gdone => -[_ [h7 _]]; apply h7; left.
  by have := hgd; rewrite /gdone => -[_ [_ [hd _]]]; have [#] := hd W hVd.
case: (oget lop.[W] = u) => [heq | hne'] /=; last exact h6.
by move: h6; rewrite heq he1.
qed.

(* ---------- an opening ---------- *)

(* A token opened with the nonce s for the committee T *)
op topen (tk' tk : token) (s : vec * row) (T : committee) : bool =
  tk'.`tk_i = tk.`tk_i /\ tk'.`tk_msg = tk.`tk_msg /\ tk'.`tk_cmt = tk.`tk_cmt /\ tk'.`tk_phase = 2
  /\ tk'.`tk_T = T /\ tk'.`tk_wbar = popn s /\ tk'.`tk_r = s.`1.

lemma topen_rec (tk : token) (s : vec * row) (T : committee) (d : view) :
  topen {| tk with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2; tk_T = T; tk_dig = d |}
        tk s T.
proof. by rewrite /topen. qed.

(* The token of a member that opens a complete request is the only opener of that member *)
lemma opener_unique toks req lo lr C ctr sv (u w : int) (V : request) :
  gtok toks req lo lr C ctr sv => u \in toks => !(u \in req) =>
  owncmt V (oget toks.[u]).`tk_i = (oget toks.[u]).`tk_cmt =>
  w \in toks => req.[w] = Some V => (oget toks.[w]).`tk_i = (oget toks.[u]).`tk_i => false.
proof.
move=> hgt hu hur hown hw hrw hi; have := hgt; rewrite /gtok => -[#] _ _ _ _ _ h5 _ _ h8 _.
have [_ hok] := h5 w _; first by rewrite domE hrw.
have hc : owncmt V (oget toks.[w]).`tk_i = (oget toks.[w]).`tk_cmt.
+ by move: hok; rewrite hrw /reqok /= => -[_ [_ [_ [_ [_ [_ [hc _]]]]]]].
have hne : w <> u by apply/negP => heq; move: hur; rewrite -heq domE hrw.
by have := h8 w u hw hu hne; rewrite -hc hi hown.
qed.

(* The openings of a complete request survive new extractions *)
lemma wsV_ext (toks : (int, token) fmap) req C (xs xs' : h0in option list)
              (ix ix' : (request * int, int) fmap) (V : request) :
  (forall j, j \in V.`2 => j \in C => ix'.[(V, j)] = ix.[(V, j)] /\ 0 <= oget ix.[(V, j)] < size xs) =>
  (forall k, 0 <= k < size xs => nth None xs' k = nth None xs k) =>
  wsV toks req C xs' ix' V = wsV toks req C xs ix V.
proof.
move=> hix hxs; rewrite /wsV; apply eq_in_map => j hj /=.
case: (j \in C) => // hc.
have [h1 h2] := hix j hj hc.
by rewrite /xwbar h1 hxs.
qed.

(* The extraction flag survives new submissions *)
lemma extbad_ext (ts ts' : cmt list) (xs xs' : h0in option list) cks :
  size xs = size ts => size ts <= size ts' =>
  (forall k, 0 <= k < size ts => nth witness ts' k = nth witness ts k) =>
  (forall k, 0 <= k < size xs => nth None xs' k = nth None xs k) =>
  H0C.extbad ts xs cks => H0C.extbad ts' xs' cks.
proof.
move=> hs hle hts hxs [e] [he [[h0 h1] [h2 h3]]]; exists e; split => //.
have hk : 0 <= e.`1 < size ts by smt().
have hk' : 0 <= e.`1 < size xs by smt().
rewrite (hts _ hk) (hxs _ hk') h2 h3 /=.
smt().
qed.

(* The openings after the opening of the token u at its position *)
lemma wsV_put (toks : (int, token) fmap) (req : (int, request) fmap) C xs ix (V : request)
              (u : int) (tk : token) :
  u \in toks => req.[u] = Some V => uniq V.`2 => tk.`tk_i = (oget toks.[u]).`tk_i =>
  (oget toks.[u]).`tk_i \in V.`2 => !((oget toks.[u]).`tk_i \in C) =>
  (forall w, w \in toks => req.[w] = Some V => (oget toks.[w]).`tk_i = (oget toks.[u]).`tk_i => w = u) =>
  (forall j, j \in V.`2 => !(j \in C) =>
     exists w, w \in toks /\ req.[w] = Some V /\ (oget toks.[w]).`tk_i = j) =>
  wsV toks.[u <- tk] req C xs ix V
  = put (wsV toks req C xs ix V) (index (oget toks.[u]).`tk_i V.`2) tk.`tk_wbar.
proof.
move=> hu hr hU hti hiV hiC huniq hex.
apply (eq_from_nth witness); first by rewrite size_put /wsV !size_map.
move=> k; rewrite /wsV size_map => hk.
rewrite nth_put; first by rewrite size_map index_ge0 index_mem.
rewrite !(nth_map 0) //=.
case: (index (oget toks.[u]).`tk_i V.`2 = k) => [hik | hik].
+ have hnk : nth 0 V.`2 k = (oget toks.[u]).`tk_i by rewrite -hik nth_index.
  rewrite hnk hiC /= /hwbar.
  have [ht1 [ht2 ht3]] := tokofP toks.[u <- tk] req V (oget toks.[u]).`tk_i _.
  - by exists u; rewrite mem_set get_set_sameE /= hr hti.
  have hX : tokof toks.[u <- tk] req V (oget toks.[u]).`tk_i = u.
  - case: (tokof toks.[u <- tk] req V (oget toks.[u]).`tk_i = u) => // hne.
    have ht1' : tokof toks.[u <- tk] req V (oget toks.[u]).`tk_i \in toks.
    + by move: ht1; rewrite mem_set hne.
    have ht3' : (oget toks.[tokof toks.[u <- tk] req V (oget toks.[u]).`tk_i]).`tk_i
                = (oget toks.[u]).`tk_i.
    + by move: ht3; rewrite get_setE hne.
    by have := huniq _ ht1' ht2 ht3'; rewrite hne.
  by rewrite hX get_set_sameE.
have hjne : nth 0 V.`2 k <> (oget toks.[u]).`tk_i.
+ apply/negP => heq; apply hik; rewrite -heq index_uniq //.
case: (nth 0 V.`2 k \in C) => // hjc; rewrite /hwbar.
have hP : (fun w => w \in toks.[u <- tk] /\ req.[w] = Some V /\ (oget toks.[u <- tk].[w]).`tk_i = nth 0 V.`2 k)
        = (fun w => w \in toks /\ req.[w] = Some V /\ (oget toks.[w]).`tk_i = nth 0 V.`2 k).
+ apply fun_ext => w /=; rewrite mem_set get_setE.
  case: (w = u) => [-> | hne] /=; last by done.
  by rewrite hti hu /=; smt().
have -> : tokof toks.[u <- tk] req V (nth 0 V.`2 k) = tokof toks req V (nth 0 V.`2 k).
+ by rewrite /tokof hP.
have [w hw] := hex (nth 0 V.`2 k) _ hjc; first by apply mem_nth.
have [hw1 [hw2 hw3]] := tokofP toks req V (nth 0 V.`2 k) _; first by exists w.
have hne : tokof toks req V (nth 0 V.`2 k) <> u.
+ by apply/negP => heq; move: hw3; rewrite heq; apply/negP; rewrite eq_sym.
by rewrite get_setE hne.
qed.

(* The token facts survive an opening *)
lemma gtok_open toks req lo lr C ctr sv (u : int) (T : committee) (cs : cmt list)
                (s : vec * row) (tk' : token) :
  gtok toks req lo lr C ctr sv => u \in toks => ok2 (oget toks.[u]) T cs =>
  topen tk' (oget toks.[u]) s T =>
  gtok toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
       ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) lr C ctr sv.[u <- s].
proof.
move=> hgt hu hok2 hto.
have [hph [hwf [hin [hiT [hsz hown]]]]] := hok2.
have [o1 [o2 [o3 [o4 [o5 [o6 o7]]]]]] := hto.
have hur : !(u \in req).
+ by have := hgt; rewrite /gtok => -[#] _ _ _ _ h4 *; rewrite -(h4 u hu) hph.
have := hgt; rewrite /gtok => -[#] h0 h1 h2 h3 h4 h5 h6 h7 h8 h9.
do !split => //.
- by move=> w; rewrite mem_set; smt().
- by move=> w; rewrite mem_set get_setE; case: (w = u) => [-> | hne] /=; smt().
- move=> w; rewrite !mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; first by rewrite o4.
  by have [] := h3 w hw.
- move=> w; rewrite !mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; first by rewrite o4.
  by rewrite (h4 w hw).
- move=> w; rewrite !mem_set !get_setE; case: (w = u) => [-> /= | hne /= hw].
  + rewrite /reqok o1 o2 o3 o5 /= /owncmt /=.
    by move: hown hwf; rewrite /own_cmt; smt().
  have [hw1 hok] := h5 w hw; split; first by rewrite hw1.
  by move: hok; rewrite /reqok in_cons; smt().
- move=> V j; rewrite in_cons; case => [[-> ->] | hV].
  + by exists u; rewrite mem_set !get_setE /= o1.
  have [w [hw [hrw hjw]]] := h6 V j hV.
  have hne : w <> u by apply/negP => heq; move: hur; rewrite -heq domE hrw.
  by exists w; rewrite mem_set !get_setE hne /= hw hrw hjw.
- move=> V j hV; have [w [hw [hrw [hjw hpw]]]] := h7 V j hV.
  have hne : w <> u by apply/negP => heq; move: hpw; rewrite heq hph.
  by exists w; rewrite mem_set !get_setE hne /= hw hrw hjw hpw.
- by move=> w w'; rewrite !mem_set !get_setE => hw hw' hne; smt().
move=> V a w hV; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; first by rewrite o4.
exact (h9 V a w hV hw).
qed.

(* The facts survive an opening that does not complete a request *)
lemma cons_open toks req lo lr C ctr sv dn cV sV lop ix ts xs pts fhp t cz fz dz
                (u : int) (T : committee) (cs : cmt list) (s : vec * row) (tk' : token) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  gprog toks req C xs ix cV pts fhp t => gresp toks lr cV sV cz fz dz lop =>
  u \in toks => ok2 (oget toks.[u]) T cs => topen tk' (oget toks.[u]) s T =>
  let vr = ((oget toks.[u]).`tk_msg, T, cs) in
  !(complete vr C ((vr, (oget toks.[u]).`tk_i) :: lo) /\ !(vr \in dn)) =>
  gtok toks.[u <- tk'] req.[u <- vr] ((vr, (oget toks.[u]).`tk_i) :: lo)
       lr C ctr sv.[u <- s]
  /\ gdone toks.[u <- tk'] req.[u <- vr] ((vr, (oget toks.[u]).`tk_i) :: lo)
           C dn cV sV lop ix ts
  /\ gprog toks.[u <- tk'] req.[u <- vr] C xs ix cV pts fhp t
  /\ gresp toks.[u <- tk'] lr cV sV cz fz dz lop.
proof.
move=> hgt hgd hgp hgr hu hok2 hto /= hnc.
have [hph [hwf [hin [hiT [hsz hown]]]]] := hok2.
have [o1 [o2 [o3 [o4 [o5 [o6 o7]]]]]] := hto.
have hur : !(u \in req).
+ by have := hgt; rewrite /gtok => -[#] _ _ _ _ h4 *; rewrite -(h4 u hu) hph.
have hlopu : forall V, V \in dn => oget lop.[V] <> u.
+ move=> V hV; have := hgd; rewrite /gdone => -[_ [_ [hd _]]].
  have [#] _ _ _ _ _ hr _ := hd V hV.
  by apply/negP => heq; move: hur; rewrite -heq domE hr.
split; first exact (gtok_open _ _ _ _ _ _ _ u T cs s tk' hgt hu hok2 hto).
split.
+ have := hgd; rewrite /gdone => -[h1 [h2 [h3 h4]]]; do !split => //.
  - move=> V hn hc; case: (V = ((oget toks.[u]).`tk_msg, T, cs)) => [hV | hV].
    + by subst V; move: hnc; rewrite hc.
    apply h1 => //; move: hc; rewrite /complete => /allP hc; apply/allP => j hj.
    by have := hc j hj; smt().
  move=> V hV; have [#] hc' hl hs hcp hm hrq hp := h3 V hV.
  have hne := hlopu V hV.
  do !split => //.
  - by move: hcp; rewrite /complete => /allP hcp; apply/allP => j hj; have := hcp j hj; smt().
  - by rewrite mem_set hm.
  - by rewrite get_setE hne.
  by rewrite get_setE hne.
split.
+ have := hgp; rewrite /gprog => h V hV.
  have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
  have hVne : V <> ((oget toks.[u]).`tk_msg, T, cs).
  - apply/negP => hV'.
    have hiV : (oget toks.[u]).`tk_i \in V.`2 by rewrite hV'.
    have hic : !((oget toks.[u]).`tk_i \in C).
    + by have := hgt; rewrite /gtok => -[#] _ _ h2 *; have [] := h2 u hu.
    have [w [hw [hrw hjw]]] := good_opener _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgt hgd hVd hiV hic.
    apply (opener_unique _ _ _ _ _ _ _ u w V hgt hu hur _ hw hrw hjw).
    by rewrite hV' /owncmt /=; move: hown; rewrite /own_cmt.
  have hw : wsV toks req C xs ix V = wsV toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs ix V.
  - apply wsV_frame => j hj hjc; split.
    + apply fun_ext => w /=; rewrite mem_set !get_setE.
      case: (w = u) => [-> /= | hne /=] //.
      have hru : req.[u] = None by move: hur; rewrite domE.
      by rewrite hru /=; smt().
    have [w hw] := good_opener _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hgt hgd hVd hj hjc.
    have [hw1 [hw2 _]] := tokofP toks req V j _; first by exists w.
    have hne : tokof toks req V j <> u by apply/negP => heq; move: hur; rewrite -heq domE hw2.
    by rewrite get_setE hne.
  by have := h V hV; rewrite hw.
have := hgr; rewrite /gresp => h V a hV; have [#] h1 h2 h3 h4 := h V a hV.
do !split => // hcv; have [h5 h6] := h4 hcv; split => //.
have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h7 _]]; apply h7; left.
by rewrite get_setE (hlopu V hVd) /=.
qed.


(* An opening raises no simulation flag: the token holds no nonce and its request has no
   response yet *)
lemma comp_nobh toks req lo lr C ctr sv (u : int) (T : committee) (cs : cmt list) :
  gtok toks req lo lr C ctr sv => u \in toks => ok2 (oget toks.[u]) T cs =>
  !(u \in sv) /\ !(exists a, (((oget toks.[u]).`tk_msg, T, cs), a) \in lr).
proof.
move=> hgt hu hok2.
have [hph [hwf [hin [hiT [hsz hown]]]]] := hok2.
have := hgt; rewrite /gtok => -[#] h0 h1 h2 h3 h4 h5 h6 h7 h8 h9.
split.
+ by apply/negP => hsv; have [_ hp] := h3 u hsv; move: hp; rewrite hph.
apply/negP => -[a ha].
have := h9 _ a u ha hu hph _; first by rewrite /= hiT.
by rewrite /owncmt /=; move: hown; rewrite /own_cmt => ->.
qed.

(* The facts survive an opening that completes a request, with a fresh programmed point *)
lemma cons_comp toks req lo lr C ctr sv dn cV sV lop ix ts xs pts fhp t cz fz dz
                (u : int) (T : committee) (cs : cmt list) (s : vec * row) (tk' : token)
                (ts' : cmt list) (xs' : h0in option list) (ix' : (request * int, int) fmap) (c : rq) :
  gtok toks req lo lr C ctr sv => gdone toks req lo C dn cV sV lop ix ts =>
  gprog toks req C xs ix cV pts fhp t => gresp toks lr cV sV cz fz dz lop =>
  u \in toks => ok2 (oget toks.[u]) T cs => topen tk' (oget toks.[u]) s T =>
  complete ((oget toks.[u]).`tk_msg, T, cs) C
           ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) =>
  !(((oget toks.[u]).`tk_msg, T, cs) \in dn) =>
  size xs = size ts => size ts <= size ts' =>
  (forall k, 0 <= k < size ts => nth witness ts' k = nth witness ts k) =>
  (forall k, 0 <= k < size xs => nth None xs' k = nth None xs k) =>
  (forall (V : request) j, V <> ((oget toks.[u]).`tk_msg, T, cs) => ix'.[(V, j)] = ix.[(V, j)]) =>
  (forall j, j \in T => j \in C =>
     (((oget toks.[u]).`tk_msg, T, cs), j) \in ix'
     /\ 0 <= oget ix'.[(((oget toks.[u]).`tk_msg, T, cs), j)] < size ts'
     /\ nth witness ts' (oget ix'.[(((oget toks.[u]).`tk_msg, T, cs), j)])
        = owncmt ((oget toks.[u]).`tk_msg, T, cs) j) =>
  !(xpt t (oget toks.[u]).`tk_msg
        (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix' ((oget toks.[u]).`tk_msg, T, cs))
             (index (oget toks.[u]).`tk_i T) (popn s)) \in pts) =>
  gtok toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
       ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) lr C ctr sv.[u <- s]
  /\ gdone toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
           ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) C
           (((oget toks.[u]).`tk_msg, T, cs) :: dn) cV.[((oget toks.[u]).`tk_msg, T, cs) <- c]
           sV.[((oget toks.[u]).`tk_msg, T, cs) <- s] lop.[((oget toks.[u]).`tk_msg, T, cs) <- u] ix' ts'
  /\ gprog toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
           cV.[((oget toks.[u]).`tk_msg, T, cs) <- c]
           (xpt t (oget toks.[u]).`tk_msg
              (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                        ((oget toks.[u]).`tk_msg, T, cs))
                   (index (oget toks.[u]).`tk_i T) (popn s)) :: pts)
           fhp.[xpt t (oget toks.[u]).`tk_msg
                  (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                            ((oget toks.[u]).`tk_msg, T, cs))
                       (index (oget toks.[u]).`tk_i T) (popn s)) <- c] t
  /\ gresp toks.[u <- tk'] lr cV.[((oget toks.[u]).`tk_msg, T, cs) <- c]
           sV.[((oget toks.[u]).`tk_msg, T, cs) <- s] cz fz dz lop.[((oget toks.[u]).`tk_msg, T, cs) <- u].
proof.
move=> hgt hgd hgp hgr hu hok2 hto hcmp hndn hsx hle hts hxs hix3 hix4 hxp.
have [hph [hwf [hin [hiT [hsz hown]]]]] := hok2.
have [o1 [o2 [o3 [o4 [o5 [o6 o7]]]]]] := hto.
have hur : !(u \in req).
+ by have := hgt; rewrite /gtok => -[#] _ _ _ _ h4 *; rewrite -(h4 u hu) hph.
have hiC : !((oget toks.[u]).`tk_i \in C).
+ by have := hgt; rewrite /gtok => -[#] _ _ h2 *; have [] := h2 u hu.
have hlopu : forall V, V \in dn => oget lop.[V] <> u.
+ move=> V hV; have := hgd; rewrite /gdone => -[_ [_ [hd _]]].
  have [#] _ _ _ _ _ hr _ := hd V hV.
  by apply/negP => heq; move: hur; rewrite -heq domE hr.
have hgt' := gtok_open _ _ _ _ _ _ _ u T cs s tk' hgt hu hok2 hto.
have [_ hnlr] := comp_nobh _ _ _ _ _ _ _ u T cs hgt hu hok2.
split; first exact hgt'.
split.
+ have := hgd; rewrite /gdone => -[h1 [h2 [h3 h4]]]; do !split.
  - move=> V hn hc; rewrite in_cons.
    case: (V = ((oget toks.[u]).`tk_msg, T, cs)) => [-> // | hV] /=.
    apply h1 => //; move: hc; rewrite /complete => /allP hc; apply/allP => j hj.
    by have := hc j hj; smt().
  - by move=> V; rewrite !mem_set in_cons => hV; smt().
  - move=> V; rewrite in_cons; case: (V = ((oget toks.[u]).`tk_msg, T, cs)) => [-> /= | hV /= hVd].
    + rewrite !mem_set !get_set_sameE /= ?get_set_sameE /= o7 /=.
      by rewrite hcmp.
    have [#] hc' hl hs hcp hm hrq hp := h3 V hVd.
    have hne := hlopu V hVd.
    rewrite !mem_set !get_setE hV /= hne /= hc' hl hs hm hrq /=.
    split; last by move=> hph2; rewrite (hp hph2).
    by move: hcp; rewrite /complete => /allP hcp; apply/allP => j hj; have := hcp j hj; smt().
  move=> V j; rewrite in_cons; case: (V = ((oget toks.[u]).`tk_msg, T, cs)) => [-> /= | hV /= hVd] hj hjc.
  - exact (hix4 j hj hjc).
  have [hin' [hk hts']] := h4 V j hVd hj hjc.
  have hk' : 0 <= oget ix.[(V, j)] < size ts by done.
  rewrite domE (hix3 V j hV) -domE hin' /= (hts _ hk') hts' /=.
  smt().
split.
+ have := hgp; rewrite /gprog => h V; rewrite mem_set => hV.
  case: (V = ((oget toks.[u]).`tk_msg, T, cs)) => [hVr | hVr].
  - rewrite hVr get_set_sameE /=.
    have hw := wsV_put toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                 ((oget toks.[u]).`tk_msg, T, cs) u (tk') hu _ _ o1 _ _ _ _.
    + by rewrite get_set_sameE.
    + by move: hwf; rewrite /wf_committee.
    + by rewrite /= hiT.
    + exact hiC.
    + move=> w hw hrw hiw; case: (w = u) => // hne.
      have := same_opener _ _ _ _ _ _ _ w u ((oget toks.[u]).`tk_msg, T, cs) hgt' _ _ hrw _ _.
      * by rewrite mem_set hw.
      * by rewrite mem_set hu.
      * by rewrite get_set_sameE.
      * by rewrite !get_setE hne /= o1 hiw.
      by rewrite hne.
    + move=> j /= hj hjc.
      have hjl : (((oget toks.[u]).`tk_msg, T, cs), j)
                 \in ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo).
      * by move: hcmp; rewrite /complete => /allP; apply; rewrite /honest List.mem_filter /= hj hjc.
      have := hgt'; rewrite /gtok => -[#] _ _ _ _ _ _ h6 *.
      have [w [hw [hrw hjw]]] := h6 _ _ hjl.
      exists w; rewrite hrw /=; move: hw hjw; rewrite mem_set get_setE.
      by case: (w = u) => [-> /= | hne /=]; [rewrite hu o1 | done].
    rewrite hw o6 /= fupdate_eq /=.
    done.
  have hVc : V \in cV by smt().
  have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h2 _]]; apply h2; left.
  have hw1 : wsV toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
               C xs' ix' V
           = wsV toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
               C xs ix V.
  - apply wsV_ext => [j hj hjc | k hk]; last exact (hxs k hk).
    split; first exact (hix3 V j hVr).
    have := hgd; rewrite /gdone => -[_ [_ [_ h4]]].
    by have [_ [hk _]] := h4 V j hVd hj hjc; rewrite hsx.
  have hw2 : wsV toks req C xs ix V
           = wsV toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
               C xs ix V.
  - apply wsV_frame => j hj hjc; split.
    + apply fun_ext => w /=; rewrite mem_set !get_setE.
      case: (w = u) => [-> /= | hne /=] //.
      have hru : req.[u] = None by move: hur; rewrite domE.
      by rewrite hru /=; smt().
    have [w hw] := good_opener _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hgt hgd hVd hj hjc.
    have [ho1 [ho2 _]] := tokofP toks req V j _; first by exists w.
    have hne : tokof toks req V j <> u by apply/negP => heq; move: hur; rewrite -heq domE ho2.
    by rewrite get_setE hne.
  have [hf hp] := h V hVc.
  rewrite hw1 -hw2 get_setE hVr /=.
  have hxne : xpt t (oget toks.[u]).`tk_msg
                (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                          ((oget toks.[u]).`tk_msg, T, cs))
                     (index (oget toks.[u]).`tk_i T) (popn s))
              <> xpt t V.`1 (wsV toks req C xs ix V).
  - by apply/negP => heq; move: hxp; rewrite heq hp.
  by rewrite fupdate_neq // hf hp.
have := hgr; rewrite /gresp => h V a hV; have [#] h1 h2 h3 h4 := h V a hV.
do !split => // hcv.
have hVr : V <> ((oget toks.[u]).`tk_msg, T, cs).
+ by apply/negP => heq; apply hnlr; exists a; rewrite -heq.
move: hcv; rewrite mem_set hVr /= => hcv.
have [h5 h6] := h4 hcv.
have hVd : V \in dn by have := hgd; rewrite /gdone => -[_ [h7 _]]; apply h7; left.
by rewrite !get_setE hVr /= h5 /= (hlopu V hVd) /=.
qed.

(* ---------- the submissions of a completion ---------- *)

(* The submission loop: the log grows, earlier entries stay, and each corrupt member of the
   request so far has its first message at its index *)
op [opaque] sinv (vr0 : request) (C0 : corrset) (ts0 : cmt list) (xs0 : h0in option list)
        (ix0 : (request * int, int) fmap) (k : int) (ts : cmt list) (xs : h0in option list)
        (ix : (request * int, int) fmap) : bool =
  0 <= k /\ size xs = size ts /\ size ts0 <= size ts
  /\ (forall k', 0 <= k' < size ts0 => nth witness ts k' = nth witness ts0 k')
  /\ (forall k', 0 <= k' < size xs0 => nth None xs k' = nth None xs0 k')
  /\ (forall (V : request) j, V <> vr0 => ix.[(V, j)] = ix0.[(V, j)])
  /\ (forall k', 0 <= k' < k => k' < size vr0.`2 => nth 0 vr0.`2 k' \in C0 =>
        (vr0, nth 0 vr0.`2 k') \in ix /\ 0 <= oget ix.[(vr0, nth 0 vr0.`2 k')] < size ts
        /\ nth witness ts (oget ix.[(vr0, nth 0 vr0.`2 k')]) = nth witness vr0.`3 k').

lemma sinv_init vr0 C0 (ts0 : cmt list) (xs0 : h0in option list) ix0 :
  size xs0 = size ts0 => sinv vr0 C0 ts0 xs0 ix0 0 ts0 xs0 ix0.
proof. by move=> hs; rewrite /sinv hs /=; smt(). qed.

lemma sinv_hon (vr0 : request) C0 (ts0 : cmt list) (xs0 : h0in option list) ix0 k ts xs ix :
  sinv vr0 C0 ts0 xs0 ix0 k ts xs ix => !(nth 0 vr0.`2 k \in C0) =>
  sinv vr0 C0 ts0 xs0 ix0 (k + 1) ts xs ix.
proof.
rewrite /sinv => -[#] h0 h1 h2 h3 h4 h5 h6 hc; do !split => //; first smt().
move=> k' hk' hks hkc; case: (k' < k) => hlt; first by apply h6 => /#.
have hkk : k' = k by smt().
by move: hkc; rewrite hkk hc.
qed.

lemma sinv_cor (vr0 : request) C0 (ts0 : cmt list) (xs0 : h0in option list) ix0 k (ts : cmt list)
               (xs : h0in option list) ix (r : h0in option) :
  uniq vr0.`2 => size xs0 = size ts0 =>
  sinv vr0 C0 ts0 xs0 ix0 k ts xs ix => k < size vr0.`2 => nth 0 vr0.`2 k \in C0 =>
  sinv vr0 C0 ts0 xs0 ix0 (k + 1) (rcons ts (nth witness vr0.`3 k)) (rcons xs r)
       ix.[(vr0, nth 0 vr0.`2 k) <- size ts].
proof.
rewrite /sinv => hu hs0 [#] h0 h1 h2 h3 h4 h5 h6 hk hc.
rewrite !size_rcons; do !split.
- smt().
- by rewrite h1.
- smt().
- by move=> k' hk'; rewrite nth_rcons (_ : k' < size ts) 1:/# /= h3.
- by move=> k' hk'; rewrite nth_rcons (_ : k' < size xs) 1:/# /= h4.
- by move=> V j hV; rewrite get_setE; smt().
move=> k' hk' hks hkc; case: (k' < k) => hlt.
- have [hin [hix hnt]] := h6 k' _ hks hkc; first smt().
  have hne : nth 0 vr0.`2 k' <> nth 0 vr0.`2 k.
  + apply/negP => heq.
    have := index_uniq 0 k' vr0.`2 _ hu; first smt().
    by rewrite heq index_uniq //; smt().
  rewrite mem_set get_setE.
  have -> /= : (vr0, nth 0 vr0.`2 k') <> (vr0, nth 0 vr0.`2 k) by smt().
  rewrite hin /=; split; first smt().
  by rewrite nth_rcons (_ : oget ix.[(vr0, nth 0 vr0.`2 k')] < size ts) 1:/# /= hnt.
have hkk : k' = k by smt().
rewrite hkk mem_set get_set_sameE /=.
by rewrite nth_rcons /=; smt(size_ge0).
qed.

lemma sinv_end (vr0 : request) C0 (ts0 : cmt list) (xs0 : h0in option list) ix0 k ts xs ix :
  uniq vr0.`2 => sinv vr0 C0 ts0 xs0 ix0 k ts xs ix => size vr0.`2 <= k =>
  forall j, j \in vr0.`2 => j \in C0 =>
    (vr0, j) \in ix /\ 0 <= oget ix.[(vr0, j)] < size ts
    /\ nth witness ts (oget ix.[(vr0, j)]) = owncmt vr0 j.
proof.
rewrite /sinv => hu [#] h0 h1 h2 h3 h4 h5 h6 hk j hj hjc.
have hi : 0 <= index j vr0.`2 < size vr0.`2 by rewrite index_ge0 index_mem.
have := h6 (index j vr0.`2) _ _ _; first smt().
- smt().
- by rewrite nth_index.
by rewrite nth_index // /owncmt.
qed.

lemma subm_spec (vr0 : request) (C0 : corrset) (dn0 : request list) (ts0 : cmt list)
                (xs0 : h0in option list) (ix0 : (request * int, int) fmap) :
  hoare [SOR(HCO.CQ, HCO.Rep).subm :
    V = vr0 /\ S.cs = C0 /\ Ex.dn = dn0 /\ H0C.ER.ts = ts0 /\ H0C.ER.xs = xs0 /\ Ex.ix = ix0
    /\ Ex.n = size ts0 /\ size xs0 = size ts0 /\ uniq vr0.`2 ==>
    Ex.dn = vr0 :: dn0 /\ S.cs = C0
    /\ size H0C.ER.xs = size H0C.ER.ts /\ Ex.n = size H0C.ER.ts /\ size ts0 <= size H0C.ER.ts
    /\ (forall k, 0 <= k < size ts0 => nth witness H0C.ER.ts k = nth witness ts0 k)
    /\ (forall k, 0 <= k < size xs0 => nth None H0C.ER.xs k = nth None xs0 k)
    /\ (forall (V : request) j, V <> vr0 => Ex.ix.[(V, j)] = ix0.[(V, j)])
    /\ (forall j, j \in vr0.`2 => j \in C0 =>
          (vr0, j) \in Ex.ix /\ 0 <= oget Ex.ix.[(vr0, j)] < size H0C.ER.ts
          /\ nth witness H0C.ER.ts (oget Ex.ix.[(vr0, j)]) = owncmt vr0 j)].
proof.
proc.
while (V = vr0 /\ S.cs = C0 /\ Ex.dn = vr0 :: dn0 /\ Ex.n = size H0C.ER.ts /\ uniq vr0.`2
       /\ size xs0 = size ts0 /\ sinv vr0 C0 ts0 xs0 ix0 k H0C.ER.ts H0C.ER.xs Ex.ix).
+ inline *; auto => /> &h hu hs0 hinv hk.
  have hcor : forall r, nth 0 vr0.`2 k{h} \in C0 =>
                sinv vr0 C0 ts0 xs0 ix0 (k{h} + 1) (rcons H0C.ER.ts{h} (nth witness vr0.`3 k{h}))
                     (rcons H0C.ER.xs{h} r) Ex.ix{h}.[(vr0, nth 0 vr0.`2 k{h}) <- size H0C.ER.ts{h}].
  - by move=> r hc; apply sinv_cor.
  have hhon := sinv_hon _ _ _ _ _ _ _ _ _ hinv.
  smt(size_rcons).
auto => /> hu hs0; split; first by apply sinv_init.
move=> ix ts xs k hk hinv.
have := hinv; rewrite /sinv => -[#] _ h1 h2 h3 h4 h5 _.
split; first exact h1.
split; first exact h2.
split; first by move=> k1 hk1 hk1'; apply h3.
split; first by move=> k1 hk1 hk1'; apply h4.
split; first exact h5.
move=> j hj hjc; have := sinv_end _ _ _ _ _ _ _ _ _ hs0 hinv _ j hj hjc; first smt().
smt().
qed.

(* ---------- the invariant of the game ---------- *)

op [opaque] cinv (toks : (int, token) fmap) (req : (int, request) fmap) (lo lr : alog) (C : corrset)
        (ctr : int) (sv : (int, vec * row) fmap) (dn : request list) (cV : (request, rq) fmap)
        (sV : (request, vec * row) fmap) (lop : (request, int) fmap) (ix : (request * int, int) fmap)
        (ts : cmt list) (xs : h0in option list) (cks : (int * h0in * cmt) list) (n : int)
        (pts : hcin list) (fhp : hcin -> rq) (t : row) (cz : (request * int, rq) fmap)
        (fz : (request * int, vec * vec) fmap) (dz : (request * int, vec) fmap)
        (lft bH b1 b2 b3 bP bC : bool) : bool =
  size xs = size ts /\ n = size ts /\ lft /\
  (flg b1 b2 b3 bP bC ts xs cks
   \/ (!bH /\ gtok toks req lo lr C ctr sv /\ gdone toks req lo C dn cV sV lop ix ts
       /\ gprog toks req C xs ix cV pts fhp t /\ gresp toks lr cV sV cz fz dz lop)).

lemma commit_lft (sv0 : (int, vec * row) fmap) :
  hoare [H0H.LC.commit : H0H.LC.lft /\ H0H.LC.sv = sv0 ==> H0H.LC.lft /\ H0H.LC.sv = sv0].
proof. proc; rcondt 1; first by auto. by inline *; sp; if; auto. qed.

lemma h0_cinv :
  hoare [CntH(HOP).h0 :
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC ==>
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC].
proof.
proc; inline *; sp; if; first by auto.
sp; if; [sp; if; auto | auto].
qed.

lemma h1_cinv :
  hoare [CntH(HOP).h1 :
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC ==>
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC].
proof. by proc; inline *; auto. qed.

lemma hc_cinv :
  hoare [CntH(HOP).hc :
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC ==>
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC].
proof. by proc; inline *; auto. qed.

(* A first round keeps the invariant *)
lemma cinv_o1 toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC
              (tk : token) :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  1 <= tk.`tk_i <= nmax => !(tk.`tk_i \in C) => tk.`tk_phase = 1 =>
  cinv toks.[ctr <- tk] req lo lr C (ctr + 1) sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1
       (b2 \/ dupc toks tk.`tk_cmt \/ seenc lr tk.`tk_cmt) b3 bP bC.
proof.
rewrite /cinv => -[#] h1 h2 h3 hd hi hic hph; do !split => //.
case: hd => [hf | [hb [hgt [hgd [hgp hgr]]]]]; first by left; move: hf; rewrite /flg; smt().
case: (dupc toks tk.`tk_cmt \/ seenc lr tk.`tk_cmt) => hds; first by left; rewrite /flg; smt().
right; rewrite hb /=.
have hd1 : !dupc toks tk.`tk_cmt by smt().
have hd2 : !seenc lr tk.`tk_cmt by smt().
exact (cons_o1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tk hgt hgd hgp hgr hi hic hph hd1 hd2).
qed.

lemma o1_cinv :
  hoare [CntO(SOP).o1 :
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC ==>
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC].
proof.
proc; inline SOP.o1; sp; if; last by auto.
seq 1 : (#pre /\ true).
+ ecall (commit_lft H0H.LC.sv); auto => /> &h; rewrite /cinv => -[#] *; smt().
auto => /> &h *.
by apply cinv_o1 => //; smt().
qed.

(* ---------- the invariant across a second round ---------- *)

lemma flg_ext b1 b2 b3 bP bC bP' bC' (ts ts' : cmt list) (xs xs' : h0in option list) cks :
  size xs = size ts => size ts <= size ts' =>
  (forall k, 0 <= k < size ts => nth witness ts' k = nth witness ts k) =>
  (forall k, 0 <= k < size xs => nth None xs' k = nth None xs k) =>
  (bP => bP') => (bC => bC') =>
  flg b1 b2 b3 bP bC ts xs cks => flg b1 b2 b3 bP' bC' ts' xs' cks.
proof.
move=> hs hle hts hxs hp hc; rewrite /flg.
have := extbad_ext ts ts' xs xs' cks hs hle hts hxs; smt().
qed.

(* An opening that completes no request *)
lemma cinv_open_new toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                    bP bC (u : int) (T : committee) (cs : cmt list) (s : vec * row) (tk' : token) :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  u \in toks => ok2 (oget toks.[u]) T cs => topen tk' (oget toks.[u]) s T =>
  !(complete ((oget toks.[u]).`tk_msg, T, cs) C
              ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo)
    /\ !(((oget toks.[u]).`tk_msg, T, cs) \in dn)) =>
  cinv toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
       ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) lr C ctr sv.[u <- s]
       dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC.
proof.
rewrite /cinv => -[#] h1 h2 h3 hd hu hok2 hto hnc; do !split => //.
case: hd => [hf | [hb [hgt [hgd [hgp hgr]]]]]; first by left.
right; rewrite hb /=.
exact (cons_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u T cs s tk' hgt hgd hgp hgr hu hok2 hto hnc).
qed.

(* An opening by a token that already holds a nonce raises a flag earlier *)
lemma cinv_open_old toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                    bP bC (u : int) (T : committee) (cs : cmt list) toks' req' lo' sv' :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  u \in toks => ok2 (oget toks.[u]) T cs => u \in sv =>
  cinv toks' req' lo' lr C ctr sv' dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC.
proof.
rewrite /cinv => -[#] h1 h2 h3 hd hu hok2 hsv; do !split => //.
case: hd => [hf | [hb [hgt _]]]; first by left.
have [hn _] := comp_nobh _ _ _ _ _ _ _ u T cs hgt hu hok2.
by move: hn; rewrite hsv.
qed.

(* A completion beyond the budget raises its flag *)
lemma cinv_bc toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC
              toks' req' lo' sv' dn' cV' sV' lop' ix' (ts' : cmt list) (xs' : h0in option list) n' pts'
              fhp' bH' :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  size xs' = size ts' => n' = size ts' =>
  cinv toks' req' lo' lr C ctr sv' dn' cV' sV' lop' ix' ts' xs' cks n' pts' fhp' t cz fz dz lft bH' b1 b2
       b3 bP true.
proof. by rewrite /cinv /flg => -[#] h1 h2 h3 hd hs hn; do !split => //; left. qed.

(* A completion by a token that already holds a nonce raises a flag earlier *)
lemma cinv_comp_old toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                    bP bC (u : int) (T : committee) (cs : cmt list) toks' req' lo' sv' dn' cV' sV' lop' ix'
                    (ts' : cmt list) (xs' : h0in option list) n' pts' fhp' bH' (bP' : bool) :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  u \in toks => ok2 (oget toks.[u]) T cs => u \in sv =>
  size xs' = size ts' => n' = size ts' => size ts <= size ts' =>
  (forall k, 0 <= k < size ts => nth witness ts' k = nth witness ts k) =>
  (forall k, 0 <= k < size xs => nth None xs' k = nth None xs k) =>
  (bP => bP') =>
  cinv toks' req' lo' lr C ctr sv' dn' cV' sV' lop' ix' ts' xs' cks n' pts' fhp' t cz fz dz lft bH' b1 b2
       b3 bP' bC.
proof.
rewrite /cinv => -[#] h1 h2 h3 hd hu hok2 hsv hs hn hle hts hxs hp; do !split => //.
case: hd => [hf | [hb [hgt _]]].
+ by left; apply (flg_ext b1 b2 b3 bP bC bP' bC ts ts' xs xs' cks).
have [hn' _] := comp_nobh _ _ _ _ _ _ _ u T cs hgt hu hok2.
by move: hn'; rewrite hsv.
qed.

(* A completion with a fresh programmed point *)
lemma cinv_comp_new toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                    bP bC (u : int) (T : committee) (cs : cmt list) (s : vec * row) (tk' : token)
                    (ts' : cmt list) (xs' : h0in option list) (ix' : (request * int, int) fmap) (n' : int)
                    (c : rq) :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  u \in toks => ok2 (oget toks.[u]) T cs => topen tk' (oget toks.[u]) s T =>
  complete ((oget toks.[u]).`tk_msg, T, cs) C
           ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) =>
  !(((oget toks.[u]).`tk_msg, T, cs) \in dn) =>
  size xs' = size ts' => n' = size ts' => size ts <= size ts' =>
  (forall k, 0 <= k < size ts => nth witness ts' k = nth witness ts k) =>
  (forall k, 0 <= k < size xs => nth None xs' k = nth None xs k) =>
  (forall (V : request) j, V <> ((oget toks.[u]).`tk_msg, T, cs) => ix'.[(V, j)] = ix.[(V, j)]) =>
  (forall j, j \in T => j \in C =>
     (((oget toks.[u]).`tk_msg, T, cs), j) \in ix'
     /\ 0 <= oget ix'.[(((oget toks.[u]).`tk_msg, T, cs), j)] < size ts'
     /\ nth witness ts' (oget ix'.[(((oget toks.[u]).`tk_msg, T, cs), j)])
        = owncmt ((oget toks.[u]).`tk_msg, T, cs) j) =>
  !(u \in sv) =>
  cinv toks.[u <- tk'] req.[u <- ((oget toks.[u]).`tk_msg, T, cs)]
       ((((oget toks.[u]).`tk_msg, T, cs), (oget toks.[u]).`tk_i) :: lo) lr C ctr sv.[u <- s]
       (((oget toks.[u]).`tk_msg, T, cs) :: dn) cV.[((oget toks.[u]).`tk_msg, T, cs) <- c]
       sV.[((oget toks.[u]).`tk_msg, T, cs) <- s] lop.[((oget toks.[u]).`tk_msg, T, cs) <- u] ix' ts' xs'
       cks n'
       (xpt t (oget toks.[u]).`tk_msg
          (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                    ((oget toks.[u]).`tk_msg, T, cs))
               (index (oget toks.[u]).`tk_i T) (popn s)) :: pts)
       fhp.[xpt t (oget toks.[u]).`tk_msg
              (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                        ((oget toks.[u]).`tk_msg, T, cs))
                   (index (oget toks.[u]).`tk_i T) (popn s)) <- c] t cz fz dz lft
       (bH \/ (exists a, (((oget toks.[u]).`tk_msg, T, cs), a) \in lr)) b1 b2 b3
       (bP \/ xpt t (oget toks.[u]).`tk_msg
                (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                          ((oget toks.[u]).`tk_msg, T, cs))
                     (index (oget toks.[u]).`tk_i T) (popn s)) \in pts) bC.
proof.
rewrite /cinv => -[#] h1 h2 h3 hd hu hok2 hto hcmp hndn hs hn hle hts hxs hix3 hix4 hsv.
do !split => //.
case: hd => [hf | [hb [hgt [hgd [hgp hgr]]]]].
+ left; apply (flg_ext b1 b2 b3 bP bC _ bC ts ts' xs xs' cks) => //; smt().
case: (xpt t (oget toks.[u]).`tk_msg
         (put (wsV toks req.[u <- ((oget toks.[u]).`tk_msg, T, cs)] C xs' ix'
                   ((oget toks.[u]).`tk_msg, T, cs))
              (index (oget toks.[u]).`tk_i T) (popn s)) \in pts) => hx.
+ by left; rewrite /flg.
right.
have [hn1 hn2] := comp_nobh _ _ _ _ _ _ _ u T cs hgt hu hok2.
rewrite hb hn2 /=.
exact (cons_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u T cs s tk' ts' xs' ix' c
         hgt hgd hgp hgr hu hok2 hto hcmp hndn h1 hle hts hxs hix3 hix4 hx).
qed.

lemma o2_cinv :
  hoare [CntO(SOP).o2 :
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC ==>
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC].
proof.
proc; inline SOP.o2; sp; if; last by auto.
sp; if; last by auto.
exlim S.req, S.lo, Ex.dn, H0C.ER.ts, H0C.ER.xs, Ex.ix, Ex.n => req0 lo0 dn0 ts0 xs0 ix0 n0.
seq 4 : (tok = oget S.toks.[u0] /\ u0 \in S.toks /\ ok2 tok T0 cs0 /\ vr = (tok.`tk_msg, T0, cs0)
         /\ d = H1O.QRO.fh (e1 S.t tok.`tk_msg T0 cs0)
         /\ S.req = req0.[u0 <- vr] /\ S.lo = (vr, tok.`tk_i) :: lo0
         /\ Ex.dn = dn0 /\ H0C.ER.ts = ts0 /\ H0C.ER.xs = xs0 /\ Ex.ix = ix0 /\ Ex.n = n0
         /\ cinv S.toks req0 lo0 S.lr S.cs S.ctr H0H.LC.sv dn0 Rp.cV Rp.sV Rx.lop ix0 ts0 xs0
                 H0C.ER.cks n0 Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2 Bd.b3
                 Rx.bP Rx.bC).
+ by auto => />.
if.
+ exlim vr, S.cs => vr0 C0.
  seq 1 : (tok = oget S.toks.[u0] /\ u0 \in S.toks /\ ok2 tok T0 cs0 /\ vr = (tok.`tk_msg, T0, cs0)
           /\ d = H1O.QRO.fh (e1 S.t tok.`tk_msg T0 cs0) /\ vr0 = vr /\ C0 = S.cs
           /\ S.req = req0.[u0 <- vr] /\ S.lo = (vr, tok.`tk_i) :: lo0
           /\ complete vr S.cs S.lo /\ !(vr \in dn0)
           /\ cinv S.toks req0 lo0 S.lr S.cs S.ctr H0H.LC.sv dn0 Rp.cV Rp.sV Rx.lop ix0 ts0 xs0
                   H0C.ER.cks n0 Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2 Bd.b3
                   Rx.bP Rx.bC
           /\ Ex.dn = vr0 :: dn0
           /\ size H0C.ER.xs = size H0C.ER.ts /\ Ex.n = size H0C.ER.ts /\ size ts0 <= size H0C.ER.ts
           /\ (forall k, 0 <= k < size ts0 => nth witness H0C.ER.ts k = nth witness ts0 k)
           /\ (forall k, 0 <= k < size xs0 => nth None H0C.ER.xs k = nth None xs0 k)
           /\ (forall (V : request) j, V <> vr0 => Ex.ix.[(V, j)] = ix0.[(V, j)])
           /\ (forall j, j \in vr0.`2 => j \in C0 =>
                 (vr0, j) \in Ex.ix /\ 0 <= oget Ex.ix.[(vr0, j)] < size H0C.ER.ts
                 /\ nth witness H0C.ER.ts (oget Ex.ix.[(vr0, j)]) = owncmt vr0 j)).
  + call (subm_spec vr0 C0 dn0 ts0 xs0 ix0); auto => /> &h hu hph huq hsz hin hiT hcs hown hinv hcmp hndn.
    by move: hinv; rewrite /cinv => -[#] -> -> *.
  sp 1; if.
  + auto => /> &h bH hu hph huq hsz hin hiT hcs hown hcmp hndn hinv hs hle hts hxs hix3 hix4 hnr s0 _ c0 _.
    have hok2 : ok2 (oget S.toks{h}.[u0{h}]) T0{h} cs0{h} by rewrite /ok2 /wf_committee.
    split => hsv.
    - apply (cinv_comp_new _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hu hok2 _ hcmp hndn hs _ hle hts hxs hix3 hix4 hsv) => //.
      by rewrite /topen get_set_sameE.
    apply (cinv_comp_old _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hu hok2 hsv hs _ hle hts hxs _) => //.
    by move=> ->.
  auto => /> &h bH hu hph huq hsz hin hiT hcs hown hcmp hndn hinv hs hle hts hxs hix3 hix4 hnr s0 _.
  by split => _; apply (cinv_bc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hs).
inline *; sp; if; auto => /> &h hu hph huq hsz hin hiT hcs hown hinv hnc hsv.
+ move=> s10 _.
  have hok2 : ok2 (oget S.toks{h}.[u0{h}]) T0{h} cs0{h} by rewrite /ok2 /wf_committee.
  apply (cinv_open_new _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hu hok2 _ hnc).
  by rewrite /topen get_set_sameE.
have hok2 : ok2 (oget S.toks{h}.[u0{h}]) T0{h} cs0{h} by rewrite /ok2 /wf_committee.
by apply (cinv_open_old _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hu hok2 hsv).
qed.

(* ---------- the invariant across a third round ---------- *)

(* The check loop: the invariant, and the checks so far agree with the openers *)
op [opaque] linv (toks : (int, token) fmap) (req : (int, request) fmap) (lo lr : alog) (C : corrset)
        (ctr : int) (sv : (int, vec * row) fmap) (dn : request list) (cV : (request, rq) fmap)
        (sV : (request, vec * row) fmap) (lop : (request, int) fmap) (ix : (request * int, int) fmap)
        (ts : cmt list) (xs : h0in option list) (cks : (int * h0in * cmt) list) (n : int)
        (pts : hcin list) (fhp : hcin -> rq) (t : row) (cz : (request * int, rq) fmap)
        (fz : (request * int, vec * vec) fmap) (dz : (request * int, vec) fmap)
        (lft bH b1 b2 b3 bP bC : bool) (V : request) (cs : cmt list) (ws : row list) (okk : bool)
        (k : int) : bool =
  size xs = size ts /\ n = size ts /\ lft /\
  (flg b1 b2 b3 bP bC ts xs cks
   \/ (!bH /\ gtok toks req lo lr C ctr sv /\ gdone toks req lo C dn cV sV lop ix ts
       /\ gprog toks req C xs ix cV pts fhp t /\ gresp toks lr cV sV cz fz dz lop
       /\ cs = V.`3 /\ (okk => chkok toks req C xs ix cV V V.`2 cs ws k))).

lemma linv_init toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                bP bC (u : int) (cs : cmt list) (ws : row list) :
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC =>
  linv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2
       (b3 \/ cs <> (oget req.[u]).`3) bP bC (oget req.[u]) cs ws true 0.
proof.
rewrite /cinv /linv => -[#] h1 h2 h3 hd; do !split => //.
case: hd => [hf | [hb [hgt [hgd [hgp hgr]]]]]; first by left; move: hf; rewrite /flg; smt().
case: (cs = (oget req.[u]).`3) => hcs; last by left; rewrite /flg; smt().
by right; rewrite hb hgt hgd hgp hgr /= chkok0.
qed.

lemma linv_cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                bP bC (V : request) (cs : cmt list) (ws : row list) (okk : bool) (k : int) :
  linv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC
       V cs ws okk k =>
  cinv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC.
proof. by rewrite /linv /cinv => -[#] h1 h2 h3 hd; do !split => //; smt(). qed.

(* One check of the loop *)
lemma linv_step toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                bP bC (u : int) (T : committee) (cs : cmt list) (ws : row list) (okk : bool) (k : int)
                (y : cmt) :
  linv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC
       (oget req.[u]) cs ws okk k =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 => T = (oget toks.[u]).`tk_T => 0 <= k < size T =>
  linv toks req lo lr C ctr sv dn cV sV lop ix ts xs
       (if PIdx.val (toidx (nth 0 T k)) \in C /\ (oget req.[u], PIdx.val (toidx (nth 0 T k))) \in ix
        then rcons cks (oget ix.[(oget req.[u], PIdx.val (toidx (nth 0 T k)))],
                        (((t, (oget toks.[u]).`tk_msg), toidx (nth 0 T k)), nth witness ws k), y)
        else cks)
       n pts fhp t cz fz dz lft bH
       (b1 \/ (!(nth 0 T k \in C) /\ y = nth witness cs k
               /\ incons toks (nth 0 T k) (oget toks.[u]).`tk_msg (nth witness cs k) (nth witness ws k)))
       b2 b3 bP bC (oget req.[u]) cs ws (okk /\ y = nth witness cs k) (k + 1).
proof.
rewrite /linv => -[#] h1 h2 h3 hd hu hph hT hk; do !split => //.
have hcks : forall e, H0C.extbad ts xs cks =>
  H0C.extbad ts xs (if PIdx.val (toidx (nth 0 T k)) \in C /\ (oget req.[u], PIdx.val (toidx (nth 0 T k))) \in ix
                    then rcons cks e else cks).
+ move=> e hb.
  case: (PIdx.val (toidx (nth 0 T k)) \in C /\ (oget req.[u], PIdx.val (toidx (nth 0 T k))) \in ix) => hc //.
  by apply extbad_cks.
case: hd => [hf | [hb [hgt [hgd [hgp [hgr [hcs hok]]]]]]].
+ by left; move: hf; rewrite /flg; smt().
have [hur hro] := resp_req _ _ _ _ _ _ _ _ hgt hu hph.
have hr : req.[u] = Some (oget req.[u]) by move: hur; rewrite domE; case: (req.[u]).
have := hro; rewrite /reqok => -[hTV [hmsg [hiV [hwf [hin [hsz [hown hlo]]]]]]].
have hTV' : T = (oget req.[u]).`2 by rewrite hT hTV.
have hu2 : uniq (oget req.[u]).`2 by move: hwf; rewrite /wf_committee.
have hkV : 0 <= k < size (oget req.[u]).`2 by rewrite -hTV'.
have hrng : 1 <= nth 0 T k <= nmax.
+ by move: hin; rewrite /inrange => /allP /(_ (nth 0 T k) _); [rewrite hTV' mem_nth | done].
have hj : PIdx.val (toidx (nth 0 T k)) = nth 0 T k by rewrite toidxK.
case: (okk /\ y = nth witness cs k) => hy; last by right; rewrite hb hgt hgd hgp hgr hcs.
have hok' := hok _; first by smt().
case: (nth 0 T k \in C) => hc.
+ have := chkok_cor _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (if PIdx.val (toidx (nth 0 T k)) \in C /\ (oget req.[u], PIdx.val (toidx (nth 0 T k))) \in ix
             then rcons cks (oget ix.[(oget req.[u], PIdx.val (toidx (nth 0 T k)))],
                             (((t, (oget toks.[u]).`tk_msg), toidx (nth 0 T k)), nth witness ws k), y)
             else cks)
            (oget req.[u]) cs ws k (((t, (oget toks.[u]).`tk_msg), toidx (nth 0 T k)), nth witness ws k) y
            hgt hgd hcs hu2 hkV _ _ _ _ hok'.
  - by rewrite -hTV'.
  - done.
  - smt().
  - move=> hcv.
    have hVd : oget req.[u] \in dn by have := hgd; rewrite /gdone => -[_ [h2' _]]; apply h2'; left.
    have := hgd; rewrite /gdone => -[_ [_ [_ hix]]].
    have [hin' _] := hix (oget req.[u]) (nth 0 T k) hVd _ hc; first by rewrite hTV' mem_nth.
    by rewrite hj hc hin' /= -hTV' mem_rcons.
  case => [hbad | hok2]; first by left; rewrite /flg hbad.
  by right; rewrite hb /=; do !split => //.
have := chkok_hon _ _ _ _ _ _ _ _ _ _ _ _ _ xs (oget req.[u]) cs ws k (oget toks.[u]).`tk_msg
          hgt hgd hcs hu2 hkV _ hok'; first by rewrite -hTV'.
case => [hinc | hok2].
+ by left; rewrite /flg; left; right; move: hinc; rewrite -hTV'; smt().
by right; rewrite hb /=; do !split => //.
qed.

(* A responding token has not responded before *)
lemma resp_nodup toks req lo lr C ctr sv (u : int) :
  gtok toks req lo lr C ctr sv => u \in toks => (oget toks.[u]).`tk_phase = 2 =>
  !((oget req.[u], (oget toks.[u]).`tk_i) \in lr).
proof.
move=> hgt hu hph; apply/negP => hin3.
have [hur _] := resp_req _ _ _ _ _ _ _ _ hgt hu hph.
have hr : req.[u] = Some (oget req.[u]) by move: hur; rewrite domE; case: (req.[u]).
have := hgt; rewrite /gtok => -[#] _ _ _ _ _ _ _ h7 _ _.
have [w [hw [hrw [hjw hpw]]]] := h7 _ _ hin3.
have heq := same_opener _ _ _ _ _ _ _ u w (oget req.[u]) hgt hu hw hr hrw _; first by rewrite hjw.
by move: hpw; rewrite -heq hph.
qed.

(* A duplicate response raises a flag earlier *)
lemma cinv_o3_dup toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                  bP bC (cs : cmt list) (ws : row list) (k : int) (u : int) toks' lr' cz' fz' dz' bH' :
  linv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC
       (oget req.[u]) cs ws true k =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 =>
  (oget req.[u], (oget toks.[u]).`tk_i) \in lr =>
  cinv toks' req lo lr' C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz' fz' dz' lft bH' b1 b2 b3 bP bC.
proof.
rewrite /linv /cinv => -[#] h1 h2 h3 hd hu hph hdup; do !split => //.
case: hd => [hf | [hb [hgt _]]]; first by left.
by have := resp_nodup _ _ _ _ _ _ _ u hgt hu hph; rewrite hdup.
qed.

(* A first response keeps the invariant *)
lemma cinv_o3_new toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3
                  bP bC (u : int) (T : committee) (cs : cmt list) (ws : row list) (z f : vec) (bH' : bool) :
  (forall T, wf_committee T => inrange T => wf_nodes T) =>
  linv toks req lo lr C ctr sv dn cV sV lop ix ts xs cks n pts fhp t cz fz dz lft bH b1 b2 b3 bP bC
       (oget req.[u]) cs ws true (size T) =>
  u \in toks => (oget toks.[u]).`tk_phase = 2 => T = (oget toks.[u]).`tk_T => size ws = size T =>
  !((oget req.[u], (oget toks.[u]).`tk_i) \in lr) =>
  (!bH =>
   !((oget req.[u], (oget toks.[u]).`tk_i) \in lr
     \/ (oget req.[u] \in cV /\ fhp (liftw (aggw ws), (t, (oget toks.[u]).`tk_msg)) <> oget cV.[oget req.[u]])
     \/ (filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                          /\ !((oget req.[u], j) \in lr)) T = [] /\ !(oget req.[u] \in cV))
     \/ (oget req.[u] \in lop /\ oget lop.[oget req.[u]] <> u
         /\ (oget toks.[oget lop.[oget req.[u]]]).`tk_i = (oget toks.[u]).`tk_i)
     \/ T <> (oget req.[u]).`2
     \/ (filter (fun j => j <> (oget toks.[u]).`tk_i /\ hpair C (oget toks.[u]).`tk_i j
                          /\ !((oget req.[u], j) \in lr)) T = []
         /\ !((oget req.[u], (oget toks.[u]).`tk_i) \in lr)
         /\ !okclose lop sV cV toks fz cz dz C (oget req.[u]) T (oget toks.[u]).`tk_i
                     (if lop.[oget req.[u]] = Some u then (oget toks.[u]).`tk_r else RqVec.Vector.zerov)))
   => !bH') =>
  cinv toks.[u <- erase (oget toks.[u])] req lo ((oget req.[u], (oget toks.[u]).`tk_i) :: lr) C ctr sv dn
       cV sV lop ix ts xs cks n pts fhp t
       cz.[(oget req.[u], (oget toks.[u]).`tk_i) <- fhp (liftw (aggw ws), (t, (oget toks.[u]).`tk_msg))]
       fz.[(oget req.[u], (oget toks.[u]).`tk_i) <- (z, f)]
       dz.[(oget req.[u], (oget toks.[u]).`tk_i) <- (if lop.[oget req.[u]] = Some u then (oget toks.[u]).`tk_r
                                                     else RqVec.Vector.zerov)]
       lft bH' b1 b2 b3 bP bC.
proof.
rewrite /linv /cinv => hsep -[#] h1 h2 h3 hd hu hph hT hws hnd hbh; do !split => //.
case: hd => [hf | [hb [hgt [hgd [hgp [hgr [hcs hok]]]]]]]; first by left.
have [hur hro] := resp_req _ _ _ _ _ _ _ _ hgt hu hph.
have hr : req.[u] = Some (oget req.[u]) by move: hur; rewrite domE; case: (req.[u]).
have := hro; rewrite /reqok => -[hTV _].
have hTV' : T = (oget req.[u]).`2 by rewrite hT hTV.
have hok' : chkok toks req C xs ix cV (oget req.[u]) (oget req.[u]).`2 cs ws (size (oget req.[u]).`2).
+ by move: hok; rewrite hTV'.
have hnoh := cons_noh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u (oget req.[u]) T cs ws
               (fhp (liftw (aggw ws), (t, (oget toks.[u]).`tk_msg)))
               hsep hgt hgd hgp hgr hu hph hr hT hcs hws hok' _; first done.
have hbh' := hbh hb hnoh.
right; rewrite hbh' /=.
apply (cons_o3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u (oget req.[u]) cs ws _ z f
         hgt hgd hgp hgr hu hph hr hcs hok' hnd).
by move=> hcv; move: hnoh; rewrite hcv /=; smt().
qed.

(* The checks of a response *)
lemma chk_spec (x0 : h0in) (cks0 : (int * h0in * cmt) list) (V0 : request)
               (ix0 : (request * int, int) fmap) (C0 : corrset) :
  hoare [SOE(H0C.ER).chk : x = x0 /\ H0C.ER.cks = cks0 /\ Ex.cur = V0 /\ Ex.ix = ix0 /\ S.cs = C0 ==>
    H0C.ER.cks = (if PIdx.val x0.`1.`2 \in C0 /\ (V0, PIdx.val x0.`1.`2) \in ix0
                  then rcons cks0 (oget ix0.[(V0, PIdx.val x0.`1.`2)], x0, res) else cks0)].
proof.
proc; sp; if.
+ if; inline *; auto => />; smt().
inline *; sp; if; [sp; if; auto => />; smt() | auto => />; smt()].
qed.

lemma o3_cinv :
  (forall T, wf_committee T => inrange T => wf_nodes T) =>
  hoare [CntO(SOP).o3 :
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC ==>
    cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
         H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
         Bd.b3 Rx.bP Rx.bC].
proof.
move=> hsep.
proc; inline SOP.o3; sp; if; last by auto.
sp; if; last by auto.
sp; if; last by auto.
seq 4 : (tok = oget S.toks.[u0] /\ u0 \in S.toks /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T
         /\ size cs0 = size T0 /\ size ws0 = size T0 /\ d = tok.`tk_dig /\ Ex.cur = oget S.req.[u0]
         /\ okk /\ k = 0
         /\ linv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
              H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
              Bd.b3 Rx.bP Rx.bC (oget S.req.[u0]) cs0 ws0 okk k).
+ auto => /> &h hinv *.
  exact (linv_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u{h} cs{h} ws{h} hinv).
seq 1 : (tok = oget S.toks.[u0] /\ u0 \in S.toks /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T
         /\ size cs0 = size T0 /\ size ws0 = size T0 /\ d = tok.`tk_dig /\ Ex.cur = oget S.req.[u0]
         /\ linv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
              H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
              Bd.b3 Rx.bP Rx.bC (oget S.req.[u0]) cs0 ws0 okk (size T0)).
+ while (tok = oget S.toks.[u0] /\ u0 \in S.toks /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T
         /\ size cs0 = size T0 /\ size ws0 = size T0 /\ d = tok.`tk_dig /\ Ex.cur = oget S.req.[u0]
         /\ 0 <= k <= size T0
         /\ linv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
              H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
              Bd.b3 Rx.bP Rx.bC (oget S.req.[u0]) cs0 ws0 okk k).
  - wp; ecall (chk_spec (((S.t, tok.`tk_msg), toidx (nth 0 T0 k)), nth witness ws0 k) H0C.ER.cks
                        Ex.cur Ex.ix S.cs).
    auto => /> &h hu hph hcs hws hk0 hk1 hinv hk y; split; first smt().
    exact (linv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hu hph _ _).
  auto => /> &h hu hph hcs hws hokk hinv; split; first smt(size_ge0).
  move=> b1 cks k0 okk0 hk0 hk1 hk2.
  by have -> : k0 = size (oget S.toks{h}.[u0{h}]).`tk_T by smt().
if; last first.
+ auto => /> &h hu hph hcs hws hinv.
  by move=> _; exact (linv_cinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv).
seq 5 : (tok = oget S.toks.[u0] /\ u0 \in S.toks /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T
         /\ size cs0 = size T0 /\ size ws0 = size T0 /\ d = tok.`tk_dig /\ Ex.cur = oget S.req.[u0]
         /\ linv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
              H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
              Bd.b3 Rx.bP Rx.bC (oget S.req.[u0]) cs0 ws0 true (size T0)
         /\ c = Rp.fhp (liftw (aggw ws0), (S.t, tok.`tk_msg))
         /\ ys = filter (fun (j0 : int) => j0 <> tok.`tk_i /\ hpair S.cs tok.`tk_i j0
                                           /\ !((oget S.req.[u0], j0) \in S.lr)) T0).
+ by auto => /> &h hu hph hcs hws hinv hokk; move: hinv; rewrite hokk.
seq 1 : (#pre).
+ by while (#pre); auto.
sp; if.
+ auto => /> &h bH hu hph hcs hws hinv hdup.
  exact (cinv_o3_dup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv hu hph hdup).
if.
+ auto => /> &h bH hu hph hcs hws hinv hnd hys z0 _.
  apply (cinv_o3_new _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsep hinv hu hph _ hws hnd _) => //.
  smt().
auto => /> &h bH hu hph hcs hws hinv hnd hys.
apply (cinv_o3_new _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsep hinv hu hph _ hws hnd _) => //.
smt().
qed.

(* ---------- the simulation flag is covered by the other flags ---------- *)

(* Evaluation points with unit differences give well formed nodes for every committee *)
lemma wf_of_sep :
  (forall i j, 1 <= i <= nmax => 1 <= j <= nmax => i <> j =>
     Rq.ComRingDflInv.unit (Rq.( + ) (alpha i) (Rq.([-]) (alpha j)))) =>
  forall T, wf_committee T => inrange T => wf_nodes T.
proof.
move=> hsep T [hu hs] hin.
have hr : forall j, j \in T => 1 <= j <= nmax by move: hin; rewrite /inrange => /allP.
rewrite /wf_nodes; split.
+ move=> a b; rewrite /nodesOf !mapP => -[i [hi ->]] [j [hj ->]] hne.
  apply hsep; [exact (hr i hi) | exact (hr j hj) | by apply/negP => heq; apply hne; rewrite heq].
split; last by rewrite size_nodesOf.
rewrite /nodesOf map_inj_in_uniq // => i j hi hj heq.
case: (i = j) => // hne.
have := hsep i j (hr i hi) (hr j hj) hne.
by rewrite heq Rq.ComRingDflInv.subrr Rq.ComRingDflInv.unitr0.
qed.

section Consistency.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER,
                         -HCO.CQ, -HCO.Rep}.

(* The evaluation points of distinct parties differ by a unit *)
declare axiom alpha_sep : forall i j, 1 <= i <= nmax => 1 <= j <= nmax => i <> j =>
  Rq.ComRingDflInv.unit (Rq.( + ) (alpha i) (Rq.([-]) (alpha j))).

(* A winning run that raises the simulation flag raises the flag of a point programmed twice or
   of a completion beyond the budget *)
lemma gp_cons : hoare [GP(A).main : true ==> res => Rp.bH => Rx.bP \/ Rx.bC].
proof.
proc.
wp.
call (_ : cinv S.toks S.req S.lo S.lr S.cs S.ctr H0H.LC.sv Ex.dn Rp.cV Rp.sV Rx.lop Ex.ix H0C.ER.ts
          H0C.ER.xs H0C.ER.cks Ex.n Rx.pts Rp.fhp S.t Rp.cz Fz.fz Rh.dz H0H.LC.lft Rp.bH Bd.b1 Bd.b2
          Bd.b3 Rx.bP Rx.bC).
+ exact o1_cinv.
+ exact o2_cinv.
+ exact (o3_cinv (wf_of_sep alpha_sep)).
+ exact h0_cinv.
+ exact h1_cinv.
+ exact hc_cinv.
auto.
call (_ : true).
inline *; auto => /> fh _ fh0 _ fh1 _ st _ fh2 _ C s _ e _ p _ sdc _.
have hinit : cinv empty empty [] [] C 0 empty [] empty empty empty empty [] [] [] 0 [] fh
                  (rndkey (mulA mA s + e)) empty empty empty true false false false false false false.
+ by rewrite /cinv /=; right; exact (good_init (rndkey (mulA mA s + e)) C fh).
split => // _ r ctr lo lr req toks dn ix n b1 b2 b3 dz bH cV cz fhp sV bC bP lop pts fz cks ts xs sv.
rewrite /cinv /flg => -[#] _ _ _ hd *.
smt().
qed.

(* The game with programmed challenges wins with the simulation flag down, or raises one of the
   flags of the programming *)
lemma gp_split &m :
  Pr[GP(A).main() @ &m : res]
  <= Pr[GP(A).main() @ &m : res /\ !Rp.bH] + Pr[GP(A).main() @ &m : Rx.bP \/ Rx.bC].
proof.
have h0 : Pr[GP(A).main() @ &m : res /\ Rp.bH /\ !(Rx.bP \/ Rx.bC)] = 0%r.
+ byphoare => //; hoare; conseq gp_cons; smt().
have h1 : Pr[GP(A).main() @ &m : res /\ Rp.bH]
          <= Pr[GP(A).main() @ &m : Rx.bP \/ Rx.bC]
             + Pr[GP(A).main() @ &m : res /\ Rp.bH /\ !(Rx.bP \/ Rx.bC)].
+ rewrite Pr[mu_split (Rx.bP \/ Rx.bC)].
  have : Pr[GP(A).main() @ &m : (res /\ Rp.bH) /\ (Rx.bP \/ Rx.bC)]
         <= Pr[GP(A).main() @ &m : Rx.bP \/ Rx.bC] by rewrite Pr[mu_sub].
  have -> : Pr[GP(A).main() @ &m : (res /\ Rp.bH) /\ !(Rx.bP \/ Rx.bC)]
          = Pr[GP(A).main() @ &m : res /\ Rp.bH /\ !(Rx.bP \/ Rx.bC)].
  - by rewrite Pr[mu_eq] => /#.
  smt().
rewrite Pr[mu_split Rp.bH]; smt().
qed.

end section Consistency.
