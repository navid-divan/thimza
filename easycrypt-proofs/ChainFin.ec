require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt ChainRep ChainProg ChainHint.
require import HintAlg ShamirHide.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* ---------- the assumption games with the distributions of the scheme ---------- *)

(* HintMLWE: a key (s, e), the vector b = A s + e or a uniform b, and at most qsig hints
   (c, c s + r, c e + e') with c a challenge and (r, e') a nonce, given on request *)
module type HMO = { proc gethint() : rq * vec * row }.

module HM : HMO = {
  var s : vec
  var e : row
  var n : int

  proc gethint() : rq * vec * row = {
    var c, rp, out;
    out <- witness;
    if (n < qsig) {
      c <$ dchal;
      rp <$ dnp;
      out <- (c, c ** s + rp.`1, rowZ c e + rp.`2);
      n <- n + 1;
    }
    return out;
  }
}.

module type HMAdv (O : HMO) = { proc guess(b : row) : bool }.

module HMLWE (B : HMAdv) = {
  proc main(real : bool) : bool = {
    var b, r;
    HM.s <$ dskey;
    HM.e <$ dekey;
    HM.n <- 0;
    if (real) { b <- mulA mA HM.s + HM.e; } else { b <$ drow; }
    r <@ B(HM).guess(b);
    return r;
  }
}.

(* SelfTargetMSIS for the challenge oracle: given b, find a short (z, c, u) and a message
   such that the oracle maps the image of (z, c, u) under [A | -t | I], with t = rndkey b,
   to c *)
module type STAdv2 (H : HCO.QRO_i) = { proc solve(b : row) : row * msg * vec * rq * row }.

module STM (B : STAdv2) = {
  proc main() : bool = {
    var b, vk, mu, z, c, u;
    HCO.QRO.init();
    b <$ drow;
    (vk, mu, z, c, u) <@ B(HCO.QRO).solve(b);
    return vk = rndkey b /\ HCO.QRO.fh (stimage vk z c u, (vk, mu)) = c /\ solnorm z c u <= bst;
  }
}.

(* ---------- the last game, written as the reductions run it ---------- *)

(* The secret that the last opener installs: a nonce whose opening is computed from a hint *)
op [opaque] hintw (zh : vec) (yh : row) (c : rq) (b : row) : vec * row =
  (RqVec.Vector.zerov, mulA mA zh + yh - rowZ c b).

(* The instance and the hint value y_V = c_V s + r_V of each programmed request *)
module Kb = {
  var b : row
}.

module Ry = {
  var yV : (request, vec) fmap
}.

(* The challenge oracle with its programmed points *)
module CH (HC : HCO.QRO_i) = {
  proc chal(x : hcin) : rq = {
    var r;
    if (x \in Rp.prog) { r <- oget Rp.prog.[x]; } else { r <@ HC.h(x); }
    return r;
  }
}.

module HOQ (HC : HCO.QRO_i) : HOr = {
  proc h0 = HOE(H0C.ER).h0
  proc h1(x : h1in) : view = { return H1O.QRO.fh x; }
  proc hc(x : hcin) : rq = { var r; r <@ CH(HC).chal(x); return r; }
}.

module SOQ (HS : HMO) (HC : HCO.QRO_i) : SOr = {
  proc o1 = SOA(H0H.LC).o1

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s, x, c, vr, zh, yh, k;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        vr <- (tok.`tk_msg, T, cs);
        S.req.[u] <- vr;
        S.lo <- (vr, tok.`tk_i) :: S.lo;
        if (complete vr S.cs S.lo /\ !(vr \in Ex.dn)) {
          Ex.dn <- vr :: Ex.dn;
          k <- 0;
          while (k < size vr.`2) {
            if (nth 0 vr.`2 k \in S.cs) {
              Ex.ix.[(vr, nth 0 vr.`2 k)] <- Ex.n;
              H0C.ER.submit(nth witness vr.`3 k);
              Ex.n <- Ex.n + 1;
            }
            k <- k + 1;
          }
          if (Rx.nr < qsig) {
            (c, zh, yh) <@ HS.gethint();
            s <- hintw zh yh c Kb.b;
            x <- xpt S.t vr.`1 (put (wsV S.toks S.req S.cs H0C.ER.xs Ex.ix vr)
                                    (index tok.`tk_i T) (popn s));
            Rx.bP <- Rx.bP \/ x \in Rx.pts;
            Rx.pts <- x :: Rx.pts;
            Rx.nr <- Rx.nr + 1;
            Rp.prog.[x] <- c;
            Rp.cV.[vr] <- c;
            Ry.yV.[vr] <- zh;
          } else {
            Rx.bC <- true;
            s <$ dnp;
          }
          if (u \notin H0H.LC.sv) { H0H.LC.sv.[u] <- s; }
          s <- oget H0H.LC.sv.[u];
          if (!(u \in H0H.LC.rv)) { H0H.LC.rv <- u :: H0H.LC.rv; }
          Rx.lop.[vr] <- u;
        } else {
          s <@ H0H.LC.reveal(u);
        }
        S.toks.[u] <- {| tok with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2;
                                  tk_T = T; tk_dig = d |};
        out <- Some (popn s);
      }
    }
    return out;
  }

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, g;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          Bd.b3 <- Bd.b3 \/ cs <> (oget S.req.[u]).`3;
          Ex.cur <- oget S.req.[u];
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ SOE(H0C.ER).chk((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
            okk <- okk /\ y = nth witness cs k;
            Bd.b1 <- Bd.b1 \/ (!(nth 0 T k \in S.cs) /\ y = nth witness cs k
                               /\ incons S.toks (nth 0 T k) tok.`tk_msg (nth witness cs k)
                                         (nth witness ws k));
            k <- k + 1;
          }
          if (okk) {
            c <@ CH(HC).chal((liftw (aggw ws), (S.t, tok.`tk_msg)));
            ys <- filter (fun j => j <> tok.`tk_i /\ hpair S.cs tok.`tk_i j
                                   /\ !((oget S.req.[u], j) \in S.lr)) T;
            mkh <- RqVec.Vector.zerov;
            mkc <- RqVec.Vector.zerov;
            k <- 0;
            while (k < size T) {
              j <- nth 0 T k;
              if (j <> tok.`tk_i /\ !(ys <> [] /\ j = head 0 ys)) {
                if (hpair S.cs tok.`tk_i j) {
                } else {
                  v <- prf (S.sdc (toidx (if tok.`tk_i < j then tok.`tk_i else j),
                                   toidx (if tok.`tk_i < j then j else tok.`tk_i))) d;
                  mkc <- mkc + (if tok.`tk_i < j then v else - v);
                }
              }
              k <- k + 1;
            }
            g <- (if Rx.lop.[oget S.req.[u]] = Some u then RqVec.Vector.zerov else tok.`tk_r) + mkc;
            if ((oget S.req.[u], tok.`tk_i) \in S.lr) {
              z <$ dvec;
            } else {
              if (ys <> []) {
                z <$ dvec;
              } else {
                if (oget S.req.[u] \in Rp.cV) {
                  z <- (oget Ry.yV.[oget S.req.[u]]
                        - vmap (fun j => (Rq.( * ) (oget Rp.cV.[oget S.req.[u]]) (lam_of T j))
                                         ** shr RqVec.Vector.zerov S.p j) (corrupted T S.cs))
                       + g + vmap (fun a => (oget Fz.fz.[(oget S.req.[u], a)]).`2
                                            - (oget Fz.fz.[(oget S.req.[u], a)]).`1)
                                  (filter (fun a => a <> tok.`tk_i) (honest T S.cs));
                } else {
                  z <- RqVec.Vector.zerov;
                }
              }
              Fz.fz.[(oget S.req.[u], tok.`tk_i)] <- (z, g);
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

module GQ (A : Adv) (HS : HMO) (HC : HCO.QRO_i) = {
  proc run() : msg * sig = {
    var mu, sg, sks, sds;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    H0C.QRO.init();
    H0C.Sim.init();
    H0C.ER.ts <- [];
    H0C.ER.xs <- [];
    H0C.ER.cks <- [];
    H0C.ER.simw <- true;
    H0C.CQ.n <- 0;
    H1O.QRO.init();
    S.cs <@ A(CntH(HOQ(HC)), CntO(SOQ(HS, HC))).corrupt();
    S.t <- rndkey Kb.b;
    mu <- witness;
    sg <- witness;
    if (admc S.cs) {
      S.p <$ dpoly;
      S.sdc <$ dseedf;
      S.toks <- empty;
      S.req <- empty;
      S.ctr <- 0;
      S.lo <- [];
      S.lr <- [];
      Fz.fz <- empty;
      Bd.b1 <- false;
      Bd.b2 <- false;
      Bd.b3 <- false;
      Ex.ix <- empty;
      Ex.n <- 0;
      Ex.dn <- [];
      Rx.nr <- 0;
      Rx.pts <- [];
      Rx.bP <- false;
      Rx.bC <- false;
      Rx.lop <- empty;
      Rp.prog <- empty;
      Rp.cV <- empty;
      Ry.yV <- empty;
      Cnt.c0 <- 0;
      Cnt.c1 <- 0;
      Cnt.cc <- 0;
      Cnt.cs <- 0;
      sks <- fun j => if j \in S.cs then shr RqVec.Vector.zerov S.p j else RqVec.Vector.zerov;
      sds <- fun (ab : pidx * pidx) =>
               if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
      (mu, sg) <@ A(CntH(HOQ(HC)), CntO(SOQ(HS, HC))).forge(S.t, sks, sds);
    }
    return (mu, sg);
  }
}.

(* The reduction to HintMLWE: it samples the challenge oracle and runs the game *)
module B2 (A : Adv) (O : HMO) = {
  proc guess(b : row) : bool = {
    var mu, sg, cv, ok;
    Kb.b <- b;
    HCO.QRO.init();
    (mu, sg) <@ GQ(A, O, HCO.QRO).run();
    cv <@ CH(HCO.QRO).chal((liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt S.t)) + sg.`3),
                            (S.t, mu)));
    ok <- (cv = sg.`1 /\ inbnd sg.`2 sg.`3) /\ admc S.cs;
    return win4 S.cs S.lo mu ok /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3
           /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks;
  }
}.

(* The reduction to SelfTargetMSIS: it samples the key and the hints itself *)
module B3 (A : Adv) (H : HCO.QRO_i) = {
  proc solve(b : row) : row * msg * vec * rq * row = {
    var mu, sg;
    Kb.b <- b;
    HM.s <$ dskey;
    HM.e <$ dekey;
    HM.n <- 0;
    (mu, sg) <@ GQ(A, HM, H).run();
    return (S.t, mu, sg.`2, sg.`1, uof S.t sg.`2 sg.`1 sg.`3);
  }
}.

(* ---------- relations between the hint game and the last game ---------- *)

(* A token without its nonce *)
op strip (t : token) : token = {| t with tk_r = RqVec.Vector.zerov; tk_e = RqRow.Vector.zerov |}.

(* The token u is the last opener of its request *)
op islop (lop : (request, int) fmap) (req : (int, request) fmap) (u : int) : bool =
  lop.[oget req.[u]] = Some u.

(* Tokens agree, except for the nonce of last openers *)
op [opaque] tokR (t1 t2 : (int, token) fmap) (lop : (request, int) fmap)
                 (req : (int, request) fmap) : bool =
  (forall u, u \in t1 <=> u \in t2)
  /\ (forall u, u \in t1 =>
        if islop lop req u then strip (oget t1.[u]) = strip (oget t2.[u])
        else t1.[u] = t2.[u]).

(* Revealed secrets agree, except for the nonce of last openers, which have the same opening *)
op [opaque] svR (s1 s2 : (int, vec * row) fmap) (lop : (request, int) fmap)
                (req : (int, request) fmap) : bool =
  (forall u, u \in s1 <=> u \in s2)
  /\ (forall u, u \in s1 => popn (oget s1.[u]) = popn (oget s2.[u])
                            /\ (!islop lop req u => s1.[u] = s2.[u])).

(* The hint value of a programmed request *)
op [opaque] yR (yV : (request, vec) fmap) (cV : (request, rq) fmap)
               (sV : (request, vec * row) fmap) (s : vec) : bool =
  forall V, V \in cV => yV.[V] = Some ((oget cV.[V]) ** s + (oget sV.[V]).`1).

(* Corrupt shares agree *)
op [opaque] shR (C : corrset) (s : vec) (p1 p2 : int -> vec) : bool =
  forall j, j \in C => shr s p1 j = shr RqVec.Vector.zerov p2 j.

(* Structural facts on tokens, secrets and last openers *)
op [opaque] stK (toks : (int, token) fmap) (req : (int, request) fmap)
                (sv : (int, vec * row) fmap) (lop : (request, int) fmap)
                (dn : request list) (ctr : int) : bool =
  0 <= ctr
  /\ (forall u, u \in toks => 0 <= u < ctr)
  /\ (forall u, u \in sv => u \in toks /\ (oget toks.[u]).`tk_phase <> 1)
  /\ (forall u, u \in req => u \in toks)
  /\ (forall V u, lop.[V] = Some u => u \in toks /\ (oget toks.[u]).`tk_phase <> 1)
  /\ (forall V, V \in lop => V \in dn).

op [opaque] stC (cV : (request, rq) fmap) (dn : request list) : bool =
  forall V, V \in cV => V \in dn.

(* ---------- facts about the relations ---------- *)

(* Tokens without nonce keep the public fields *)
lemma strip_fields (t1 t2 : token) :
  strip t1 = strip t2 =>
  t1.`tk_i = t2.`tk_i /\ t1.`tk_msg = t2.`tk_msg /\ t1.`tk_wbar = t2.`tk_wbar
  /\ t1.`tk_cmt = t2.`tk_cmt /\ t1.`tk_phase = t2.`tk_phase /\ t1.`tk_T = t2.`tk_T
  /\ t1.`tk_dig = t2.`tk_dig.
proof.
move=> h.
have h1 := congr1 (fun (t : token) => t.`tk_i) _ _ h.
have h2 := congr1 (fun (t : token) => t.`tk_msg) _ _ h.
have h3 := congr1 (fun (t : token) => t.`tk_wbar) _ _ h.
have h4 := congr1 (fun (t : token) => t.`tk_cmt) _ _ h.
have h5 := congr1 (fun (t : token) => t.`tk_phase) _ _ h.
have h6 := congr1 (fun (t : token) => t.`tk_T) _ _ h.
have h7 := congr1 (fun (t : token) => t.`tk_dig) _ _ h.
by move: h1 h2 h3 h4 h5 h6 h7; rewrite /strip /=.
qed.

(* Erasing forgets the nonce *)
lemma erase_strip (t1 t2 : token) : strip t1 = strip t2 => erase t1 = erase t2.
proof.
move=> h.
have -> : erase t1 = {| (strip t1) with tk_phase = 0 |} by rewrite /erase /strip.
have -> : erase t2 = {| (strip t2) with tk_phase = 0 |} by rewrite /erase /strip.
by rewrite h.
qed.

(* Tokens with the same fields have the same public fields *)
lemma tokR_mem t1 t2 lop req (u : int) : tokR t1 t2 lop req => (u \in t1 <=> u \in t2).
proof. by rewrite /tokR => -[h _]; exact (h u). qed.

lemma tokR_strip t1 t2 lop req (u : int) :
  tokR t1 t2 lop req => u \in t1 => strip (oget t1.[u]) = strip (oget t2.[u]).
proof.
rewrite /tokR => -[_ h] hu.
by have := h u hu; case: (islop lop req u) => _ //= ->.
qed.

lemma tokR_eq t1 t2 lop req (u : int) :
  tokR t1 t2 lop req => !islop lop req u => t1.[u] = t2.[u].
proof.
rewrite /tokR => -[hm h] hl.
case: (u \in t1) => hu; first by have := h u hu; rewrite hl.
have hu2 : !(u \in t2) by rewrite -hm.
by move: hu hu2; rewrite !domE; case: (t1.[u]) => //; case: (t2.[u]).
qed.

(* Setting the same token keeps the relation *)
lemma tokR_set t1 t2 lop req (k : int) (t : token) :
  tokR t1 t2 lop req => tokR t1.[k <- t] t2.[k <- t] lop req.
proof.
rewrite /tokR => -[hm h]; split.
+ by move=> u; rewrite !mem_set hm.
move=> u; rewrite mem_set !get_setE.
case: (u = k) => [-> /= | hne /= hu]; first by case: (islop lop req k).
exact (h u hu).
qed.

(* Setting tokens that agree up to the nonce at a last opener keeps the relation *)
lemma tokR_set_lop t1 t2 lop req (k : int) (ta tb : token) :
  tokR t1 t2 lop req => islop lop req k => strip ta = strip tb =>
  tokR t1.[k <- ta] t2.[k <- tb] lop req.
proof.
rewrite /tokR => -[hm h] hl hs; split.
+ by move=> u; rewrite !mem_set hm.
move=> u; rewrite mem_set !get_setE.
case: (u = k) => [-> /= | hne /= hu]; first by rewrite hl.
exact (h u hu).
qed.

(* A new last opener keeps the relation *)
lemma tokR_lop t1 t2 (lop : (request, int) fmap) req (V : request) (k : int) :
  tokR t1 t2 lop req => lop.[V] = None => tokR t1 t2 lop.[V <- k] req.
proof.
rewrite /tokR /islop => -[hm h] hV; split => // u hu.
rewrite get_setE.
have := h u hu.
case: (oget req.[u] = V) => [hreq | hne] /=; last done.
rewrite hreq hV /= => heq.
by case: (k = u) => hk //=; rewrite heq.
qed.

(* Opening a request at a token that is not a last opener keeps the relation *)
lemma tokR_req t1 t2 (lop : (request, int) fmap) (req : (int, request) fmap) (k : int) (V : request) :
  tokR t1 t2 lop req => t1.[k] = t2.[k] => lop.[V] <> Some k =>
  tokR t1 t2 lop req.[k <- V].
proof.
rewrite /tokR /islop => -[hm h] hk hV; split => // u hu.
rewrite get_setE; case: (u = k) => [-> /= | hne /=].
+ by rewrite hV /= hk.
exact (h u hu).
qed.

(* The same facts for the revealed secrets *)
lemma svR_mem s1 s2 lop req (u : int) : svR s1 s2 lop req => (u \in s1 <=> u \in s2).
proof. by rewrite /svR => -[h _]; exact (h u). qed.

lemma svR_popn s1 s2 lop req (u : int) :
  svR s1 s2 lop req => popn (oget s1.[u]) = popn (oget s2.[u]).
proof.
rewrite /svR => -[hm h]; case: (u \in s1) => hu; first by have [] := h u hu.
have hu2 : !(u \in s2) by rewrite -hm.
by move: hu hu2; rewrite !domE; case: (s1.[u]) => //; case: (s2.[u]).
qed.

lemma svR_eq s1 s2 lop req (u : int) :
  svR s1 s2 lop req => !islop lop req u => s1.[u] = s2.[u].
proof.
rewrite /svR => -[hm h] hl.
case: (u \in s1) => hu; first by have [] _ := h u hu; apply.
have hu2 : !(u \in s2) by rewrite -hm.
by move: hu hu2; rewrite !domE; case: (s1.[u]) => //; case: (s2.[u]).
qed.

lemma svR_set s1 s2 lop req (k : int) (v : vec * row) :
  svR s1 s2 lop req => svR s1.[k <- v] s2.[k <- v] lop req.
proof.
rewrite /svR => -[hm h]; split.
+ by move=> u; rewrite !mem_set hm.
move=> u; rewrite mem_set !get_setE.
by case: (u = k) => [-> /= | hne /= hu]; [done | exact (h u hu)].
qed.

lemma svR_set_lop s1 s2 lop req (k : int) (va vb : vec * row) :
  svR s1 s2 lop req => islop lop req k => popn va = popn vb =>
  svR s1.[k <- va] s2.[k <- vb] lop req.
proof.
rewrite /svR => -[hm h] hl hp; split.
+ by move=> u; rewrite !mem_set hm.
move=> u; rewrite mem_set !get_setE.
case: (u = k) => [-> /= | hne /= hu]; first by rewrite hp hl.
exact (h u hu).
qed.

lemma svR_lop s1 s2 (lop : (request, int) fmap) req (V : request) (k : int) :
  svR s1 s2 lop req => lop.[V] = None => svR s1 s2 lop.[V <- k] req.
proof.
rewrite /svR /islop => -[hm h] hV; split => // u hu.
have [hp he] := h u hu; split => //.
rewrite !get_setE; case: (oget req.[u] = V) => [hreq | hne] /=.
+ by move=> _; apply he; rewrite hreq hV.
exact he.
qed.

lemma svR_req s1 s2 (lop : (request, int) fmap) (req : (int, request) fmap) (k : int) (V : request) :
  svR s1 s2 lop req => s1.[k] = s2.[k] => lop.[V] <> Some k =>
  svR s1 s2 lop req.[k <- V].
proof.
rewrite /svR /islop => -[hm h] hk hV; split => // u hu.
have [hp he] := h u hu; split => //.
rewrite get_setE; case: (u = k) => [-> /= | hne /=]; first by rewrite hk.
exact he.
qed.

(* Commitment queries read revealed secrets only through their openings *)
lemma svR_filter s1 s2 lop req (l : int list) (w : row) :
  svR s1 s2 lop req =>
  filter (fun u => u \in s1 /\ popn (oget s1.[u]) = w) l
  = filter (fun u => u \in s2 /\ popn (oget s2.[u]) = w) l.
proof.
move=> h; apply List.eq_in_filter => u _ /=.
by rewrite (svR_mem _ _ _ _ u h) (svR_popn _ _ _ _ u h).
qed.

(* The flags and the openings read tokens only through their public fields *)
lemma tokR_incons t1 t2 lop req (j : int) (mu : msg) (c : cmt) (w : row) :
  tokR t1 t2 lop req => incons t1 j mu c w = incons t2 j mu c w.
proof.
move=> h; rewrite /incons /cmtok eq_iff; split.
+ move=> [u] [[hu [hi hc]] hr]; exists u.
  have hu2 : u \in t2 by rewrite -(tokR_mem _ _ _ _ u h).
  have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu).
  smt().
move=> [u] [[hu [hi hc]] hr]; exists u.
have hu1 : u \in t1 by rewrite (tokR_mem _ _ _ _ u h).
have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu1).
smt().
qed.

lemma tokR_dupc t1 t2 lop req (c : cmt) : tokR t1 t2 lop req => dupc t1 c = dupc t2 c.
proof.
move=> h; rewrite /dupc eq_iff; split.
+ move=> [u] [hu hc]; exists u.
  have hu2 : u \in t2 by rewrite -(tokR_mem _ _ _ _ u h).
  have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu).
  smt().
move=> [u] [hu hc]; exists u.
have hu1 : u \in t1 by rewrite (tokR_mem _ _ _ _ u h).
have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu1).
smt().
qed.

lemma tokR_tokof t1 t2 lop (req : (int, request) fmap) (V : request) (j : int) :
  tokR t1 t2 lop req => tokof t1 req V j = tokof t2 req V j.
proof.
move=> h; rewrite /tokof; congr; apply fun_ext => u /=.
rewrite eq_iff; split.
+ move=> [hu [hr hi]].
  have hu2 : u \in t2 by rewrite -(tokR_mem _ _ _ _ u h).
  have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu).
  smt().
move=> [hu [hr hi]].
have hu1 : u \in t1 by rewrite (tokR_mem _ _ _ _ u h).
have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu1).
smt().
qed.

lemma tokR_wbar t1 t2 lop req (u : int) :
  tokR t1 t2 lop req => (oget t1.[u]).`tk_wbar = (oget t2.[u]).`tk_wbar.
proof.
move=> h; case: (u \in t1) => hu.
+ by have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu); smt().
have hu2 : !(u \in t2) by rewrite -(tokR_mem _ _ _ _ u h).
by move: hu hu2; rewrite !domE; case: (t1.[u]) => //; case: (t2.[u]).
qed.

lemma tokR_wsV t1 t2 lop req (C : corrset) xs ix (V : request) :
  tokR t1 t2 lop req => wsV t1 req C xs ix V = wsV t2 req C xs ix V.
proof.
move=> h; rewrite /wsV; apply eq_in_map => j _ /=.
case: (j \in C) => // _.
by rewrite /hwbar (tokR_tokof _ _ _ _ V j h) (tokR_wbar _ _ _ _ _ h).
qed.

(* The programmed oracle is the oracle with its programmed points *)
lemma hcp_set (prog : (hcin, rq) fmap) (f : hcin -> rq) (x : hcin) (c : rq) :
  (hcp prog f).[x <- c] = hcp prog.[x <- c] f.
proof.
apply fun_ext => y; rewrite fupdateE /hcp mem_set get_setE.
case: (y = x) => [-> /= | hne] //=.
by have -> : x <> y by smt().
qed.

(* The opening computed from a hint is the opening of its nonce *)
lemma popn_hint (s : vec) (e : row) (c : rq) (rp : vec * row) :
  popn (hintw (c ** s + rp.`1) (rowZ c e + rp.`2) c (mulA mA s + e)) = popn rp.
proof.
rewrite /hintw /popn /commit /= hint_commit mulA0.
by rewrite RqRow.Vector.ZModule.add0r.
qed.

(* Hint values of programmed requests *)
lemma yR_set (yV : (request, vec) fmap) cV sV (s : vec) (V : request) (c : rq) (rp : vec * row) :
  yR yV cV sV s => yR yV.[V <- c ** s + rp.`1] cV.[V <- c] sV.[V <- rp] s.
proof.
rewrite /yR => h W; rewrite mem_set !get_setE.
by case: (W = V) => [-> | hne] /=; [done | exact (h W)].
qed.

lemma yR_sV (yV : (request, vec) fmap) cV (sV : (request, vec * row) fmap) (s : vec) (V : request) rp :
  yR yV cV sV s => !(V \in cV) => yR yV cV sV.[V <- rp] s.
proof.
rewrite /yR => h hV W hW; rewrite get_setE.
case: (W = V) => [heq | hne] /=; last exact (h W hW).
by move: hW; rewrite heq hV.
qed.

lemma yR_get yV cV sV (s : vec) (V : request) :
  yR yV cV sV s => V \in cV => oget yV.[V] = (oget cV.[V]) ** s + (oget sV.[V]).`1.
proof. by rewrite /yR => h hV; rewrite (h V hV). qed.

(* Corrupt Lagrange terms agree *)
lemma shR_corr (C : corrset) (s : vec) (p1 p2 : int -> vec) (T : committee) (c : rq) :
  shR C s p1 p2 =>
  vmap (fun j => (Rq.( * ) c (lam_of T j)) ** shr s p1 j) (corrupted T C)
  = vmap (fun j => (Rq.( * ) c (lam_of T j)) ** shr RqVec.Vector.zerov p2 j) (corrupted T C).
proof.
rewrite /shR => h; apply vmap_eq => j; rewrite /corrupted mem_filter => -[hj _] /=.
by rewrite (h j hj).
qed.

(* The shifted polynomial gives the corrupt shares *)
lemma shR_shift (C : corrset) (s : vec) (p : int -> vec) :
  (forall j, 1 <= j <= nmax => Rq.ComRingDflInv.unit (alpha j)) => admc C =>
  shR C s p (shiftp s C p).
proof.
move=> hu [hC [hs ha]]; rewrite /shR => j hj.
rewrite (shr_shift s C p j _ hs hj) //.
by move=> k hk; apply hu; move/allP: ha => /(_ k hk).
qed.

(* ---------- structural facts ---------- *)

lemma stK_fresh toks req sv lop dn (ctr : int) :
  stK toks req sv lop dn ctr =>
  !(ctr \in toks) /\ !(ctr \in sv) /\ !(ctr \in req) /\ (forall V, lop.[V] <> Some ctr).
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6.
have hc : !(ctr \in toks) by smt().
do !split => //; first 2 smt().
by move=> V; apply/negP => hV; have [] := h5 V ctr hV.
qed.

lemma stK_ph1 toks req sv lop dn (ctr u : int) :
  stK toks req sv lop dn ctr => u \in toks => (oget toks.[u]).`tk_phase = 1 =>
  !(u \in sv) /\ (forall V, lop.[V] <> Some u).
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6 hu hp.
split.
+ by apply/negP => /h2 [] _; rewrite hp.
by move=> V; apply/negP => hV; have [] _ := h5 V u hV; rewrite hp.
qed.

lemma stK_dn toks req sv (lop : (request, int) fmap) dn (ctr : int) (V : request) :
  stK toks req sv lop dn ctr => !(V \in dn) => lop.[V] = None.
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6 hV.
have : !(V \in lop) by apply/negP => /h6; exact hV.
by rewrite domE; case: (lop.[V]).
qed.

lemma stC_dn (cV : (request, rq) fmap) dn (V : request) :
  stC cV dn => !(V \in dn) => !(V \in cV).
proof. rewrite /stC => h hV; smt(). qed.

(* A new token keeps the structural facts *)
lemma stK_new toks req sv lop dn (ctr : int) (t : token) :
  stK toks req sv lop dn ctr => t.`tk_phase = 1 =>
  stK toks.[ctr <- t] req sv lop dn (ctr + 1).
proof.
move=> h ht; have [hc [hs [hr hl]]] := stK_fresh _ _ _ _ _ _ h.
move: h; rewrite /stK => -[#] h0 h1 h2 h4 h5 h6.
do !split.
+ smt().
+ by move=> u; rewrite mem_set; smt().
+ move=> u hu; have [] := h2 u hu => h7 h8.
  by rewrite mem_set get_setE h7 /=; smt().
+ by move=> u /h4 hu; rewrite mem_set hu.
+ move=> V u hV; have [] := h5 V u hV => h7 h8.
  rewrite mem_set get_setE h7 /=; smt().
exact h6.
qed.

(* Erasing a token keeps the structural facts *)
lemma stK_erase toks req sv lop dn (ctr u : int) (t : token) :
  stK toks req sv lop dn ctr => u \in toks => t.`tk_phase <> 1 =>
  stK toks.[u <- t] req sv lop dn ctr.
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6 hu ht.
do !split => //.
+ by move=> w; rewrite mem_set; smt().
+ move=> w hw; have [] := h2 w hw => h7 h8.
  by rewrite mem_set get_setE h7 /=; smt().
+ by move=> w /h4 hw; rewrite mem_set hw.
move=> V w hV; have [] := h5 V w hV => h7 h8.
rewrite mem_set get_setE h7 /=; smt().
qed.

(* An opening keeps the structural facts *)
lemma stK_open toks req sv lop dn sv' lop' dn' (ctr u : int) (t : token) :
  stK toks req sv lop dn ctr => u \in toks => t.`tk_phase <> 1 =>
  (forall w, w \in sv' => w \in sv \/ w = u) =>
  (forall V w, lop'.[V] = Some w => lop.[V] = Some w \/ w = u) =>
  (forall V, V \in lop' => V \in dn') =>
  stK toks.[u <- t] req sv' lop' dn' ctr.
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6 hu ht hs hl hd.
do !split => //.
+ by move=> w; rewrite mem_set; smt().
+ move=> w hw; rewrite mem_set get_setE.
  case: (hs w hw) => [hw' | ->] /=; last by rewrite ht.
  have [] := h2 w hw' => h7 h8; rewrite h7 /=; smt().
+ by move=> w hw; rewrite mem_set; left; apply h4.
move=> V w hV; rewrite mem_set get_setE.
case: (hl V w hV) => [hV' | ->] /=; last by rewrite ht.
have [] := h5 V w hV' => h7 h8; rewrite h7 /=; smt().
qed.

(* Recording the request of a token keeps the structural facts *)
lemma stK_req toks (req : (int, request) fmap) sv lop dn (ctr u : int) (vr : request) :
  stK toks req sv lop dn ctr => u \in toks => stK toks req.[u <- vr] sv lop dn ctr.
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6 hu.
do !split => //.
by move=> w; rewrite mem_set; case => [/h4 | ->].
qed.

(* Recording a complete request keeps the structural facts *)
lemma stK_dn_add toks req sv lop dn (ctr : int) (vr : request) :
  stK toks req sv lop dn ctr => stK toks req sv lop (vr :: dn) ctr.
proof.
rewrite /stK => -[#] h0 h1 h2 h4 h5 h6.
do !split => //.
by move=> V /h6 hV; rewrite in_cons hV.
qed.

lemma stC_add (cV : (request, rq) fmap) dn (V : request) :
  stC cV dn => stC cV (V :: dn).
proof. rewrite /stC => h W hW; rewrite in_cons; smt(). qed.

lemma stC_set (cV : (request, rq) fmap) dn (V : request) (c : rq) :
  stC cV dn => stC cV.[V <- c] (V :: dn).
proof. rewrite /stC => h W; rewrite mem_set in_cons; smt(). qed.

(* The second round succeeds on the same tokens *)
lemma ok2_strip (t1 t2 : token) (T : committee) (cs : cmt list) :
  strip t1 = strip t2 => ok2 t1 T cs = ok2 t2 T cs.
proof. by move=> /strip_fields [#] h1 h2 h3 h4 h5 h6 h7; rewrite /ok2 /own_cmt h1 h4 h5. qed.

(* A token in the first phase is not a last opener *)
lemma stK_nolop toks req sv (lop : (request, int) fmap) dn (ctr u : int) :
  stK toks req sv lop dn ctr => u \in toks => (oget toks.[u]).`tk_phase = 1 =>
  !islop lop req u.
proof.
move=> h hu hp; have [_ hl] := stK_ph1 _ _ _ _ _ _ _ h hu hp.
by rewrite /islop; apply hl.
qed.

(* ---------- the oracles of the hint game and of the last game agree ---------- *)

(* Commitment queries agree on related secrets *)
equiv lch_q : H0H.LC.h ~ H0H.LC.h :
  ={x, H0H.CQ.n, H0H.LC.fv, H0H.LC.lft, H0H.LC.rv, H0H.QRO.fh, Rx.lop, S.req}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  ==> ={res, H0H.CQ.n, H0H.LC.fv, H0H.LC.lft, H0H.LC.rv, H0H.QRO.fh, Rx.lop, S.req}
      /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}.
proof.
proc; inline H0H.LC.gf.
seq 2 2 : (={x, us, H0H.CQ.n, H0H.LC.fv, H0H.LC.lft, H0H.LC.rv, H0H.QRO.fh, Rx.lop, S.req}
           /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}).
+ by auto => /> &1 &2 h; exact (svR_filter _ _ _ _ _ _ h).
if => //.
+ by sp; if => //; auto.
by auto.
qed.

(* First messages agree *)
equiv commit_q (s1 s2 : (int, vec * row) fmap) : H0H.LC.commit ~ H0H.LC.commit :
  ={u, k, H0H.LC.fv, H0H.LC.lft} /\ H0H.LC.lft{1} /\ H0H.LC.sv{1} = s1 /\ H0H.LC.sv{2} = s2
  ==> ={res, H0H.LC.fv, H0H.LC.lft} /\ H0H.LC.sv{1} = s1 /\ H0H.LC.sv{2} = s2.
proof.
proc; rcondt{1} 1; first by auto.
rcondt{2} 1; first by auto => /> /#.
by inline *; sp; if => //; auto.
qed.

(* Revealing a token that is not a last opener agrees *)
equiv reveal_q : H0H.LC.reveal ~ H0H.LC.reveal :
  ={u, H0H.LC.rv, Rx.lop, S.req} /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ !islop Rx.lop{2} S.req{2} u{2}
  ==> ={res, H0H.LC.rv, Rx.lop, S.req} /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}.
proof.
proc; inline H0H.LC.gsec; sp.
if.
+ by move=> &1 &2 [#] -> -> -> _ _ _ h _; rewrite (svR_mem _ _ _ _ u{2} h).
+ auto => /> &1 &2 h hl hu s _.
  rewrite !get_set_sameE /=.
  by have := svR_set _ _ _ _ u{2} s h; smt().
auto => /> &1 &2 h hl hu.
by rewrite (svR_eq _ _ _ _ _ h hl).
qed.

(* Checks agree *)
equiv chk_q : SOE(H0C.ER).chk ~ SOE(H0C.ER).chk :
  ={x, S.cs, Ex.cur, Ex.ix, glob H0C.ER, glob H0C.Sim, glob H0C.CQ, glob H0C.QRO,
    H0H.CQ.n, H0H.LC.fv, H0H.LC.lft, H0H.LC.rv, H0H.QRO.fh, Rx.lop, S.req}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  ==> ={res, S.cs, Ex.cur, Ex.ix, glob H0C.ER, glob H0C.Sim, glob H0C.CQ, glob H0C.QRO,
        H0H.CQ.n, H0H.LC.fv, H0H.LC.lft, H0H.LC.rv, H0H.QRO.fh, Rx.lop, S.req}
      /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}.
proof.
proc; if => //.
+ by if => //; inline *; auto.
by call lch_q.
qed.

(* First rounds agree *)
equiv o1_q : CntO(SOH).o1 ~ CntO(SOQ(HM, HCO.QRO)).o1 :
  ={i, mu} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2} ==> ={res} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}.
proof.
proc; inline SOA(H0H.LC).o1.
sp; if => //; last by auto.
seq 1 1 : (={i, mu, out, i0, mu0, c} /\ (1 <= i0{1} <= nmax /\ !(i0{1} \in S.cs{1})) /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
+ by ecall (commit_q H0H.LC.sv{1} H0H.LC.sv{2}); auto.
auto => /> &1 &2 *.
have hS : stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2} by assumption.
do !split; 2..: smt(tokR_dupc tokR_set stK_new).
by congr; congr; apply (tokR_dupc _ _ Rx.lop{2} S.req{2}); assumption.
qed.

(* Hash queries agree *)
equiv h0_q : CntH(HOP).h0 ~ CntH(HOQ(HCO.QRO)).h0 : ={x} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2} ==> ={res} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}.
proof.
proc; inline HOE(H0C.ER).h0.
sp; if => //.
+ by inline *; auto.
by wp; call lch_q; auto.
qed.

equiv h1_q : CntH(HOP).h1 ~ CntH(HOQ(HCO.QRO)).h1 : ={x} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2} ==> ={res} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}.
proof. by proc; inline *; auto. qed.

equiv hc_q : CntH(HOP).hc ~ CntH(HOQ(HCO.QRO)).hc : ={x} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2} ==> ={res} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}.
proof.
proc; inline *; auto => /> &1 &2 *.
by rewrite /hcp; smt().
qed.

(* The token fields of related tokens *)
lemma tokR_flds t1 t2 lop req (u : int) :
  tokR t1 t2 lop req => u \in t1 =>
  (oget t1.[u]).`tk_i = (oget t2.[u]).`tk_i /\ (oget t1.[u]).`tk_msg = (oget t2.[u]).`tk_msg
  /\ (oget t1.[u]).`tk_T = (oget t2.[u]).`tk_T /\ (oget t1.[u]).`tk_wbar = (oget t2.[u]).`tk_wbar
  /\ (oget t1.[u]).`tk_phase = (oget t2.[u]).`tk_phase /\ (oget t1.[u]).`tk_dig = (oget t2.[u]).`tk_dig
  /\ (oget t1.[u]).`tk_cmt = (oget t2.[u]).`tk_cmt.
proof. by move=> h hu; have := strip_fields _ _ (tokR_strip _ _ _ _ u h hu). qed.

(* Erasing a token keeps the relations *)
lemma erase_inv t1 t2 lop req sv dn (ctr u : int) :
  tokR t1 t2 lop req => u \in t1 => stK t2 req sv lop dn ctr =>
  tokR t1.[u <- erase (oget t1.[u])] t2.[u <- erase (oget t2.[u])] lop req
  /\ stK t2.[u <- erase (oget t2.[u])] req sv lop dn ctr.
proof.
move=> h hu hs.
have -> : erase (oget t1.[u]) = erase (oget t2.[u]).
+ by apply erase_strip; apply (tokR_strip _ _ lop req).
split; first by apply tokR_set.
apply (stK_erase _ _ _ _ _ _ _ _ hs); first by rewrite -(tokR_mem _ _ _ _ u h).
by rewrite /erase.
qed.

(* The nonce part of a response of a token that is not a last opener *)
lemma g_eq t1 t2 (lop : (request, int) fmap) req (u : int) (m : vec) :
  tokR t1 t2 lop req =>
  (if lop.[oget req.[u]] = Some u then RqVec.Vector.zerov else (oget t1.[u]).`tk_r) + m
  = (if lop.[oget req.[u]] = Some u then RqVec.Vector.zerov else (oget t2.[u]).`tk_r) + m.
proof.
move=> h; case: (lop.[oget req.[u]] = Some u) => hl //=.
by rewrite (tokR_eq _ _ lop req u h _) // /islop hl.
qed.

(* The last response computed from the hint value *)
lemma close_eq yV cV sV (s : vec) (C : corrset) (p1 p2 : int -> vec) (V : request)
                (T : committee) (g w : vec) :
  yR yV cV sV s => shR C s p1 p2 => V \in cV =>
  ((oget cV.[V]) ** s + (oget sV.[V]).`1
    - vmap (fun j => (Rq.( * ) (oget cV.[V]) (lam_of T j)) ** shr s p1 j) (corrupted T C))
  + g + w
  = (oget yV.[V]
     - vmap (fun j => (Rq.( * ) (oget cV.[V]) (lam_of T j)) ** shr RqVec.Vector.zerov p2 j)
            (corrupted T C))
    + g + w.
proof. by move=> hy hs hV; rewrite (yR_get _ _ _ _ _ hy hV) (shR_corr _ _ _ _ _ _ hs). qed.

(* Third rounds agree *)
equiv o3_q : CntO(SOH).o3 ~ CntO(SOQ(HM, HCO.QRO)).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2} ==> ={res} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}.
proof.
proc; inline{1} SOH.o3; inline{2} SOQ(HM, HCO.QRO).o3.
sp.
if; first by move=> &1 &2 [#] *; smt(tokR_mem).
+ sp 1 1.
  if; first by move=> &1 &2 [#] *; smt(tokR_mem tokR_flds).
  + sp 1 1.
    if; first by move=> &1 &2 [#] *; smt(tokR_mem tokR_flds).
    + seq 4 4 : (={u0, T0, cs0, ws0, out, d, okk, k} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
      - by auto => /> &1 &2 *; smt(tokR_mem tokR_flds).
      seq 1 1 : (={u0, T0, cs0, ws0, out, d, okk, k} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
      - while (={u0, T0, cs0, ws0, out, d, okk, k} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}) => //.
        wp; call chk_q.
        auto => /> &1 &2 *.
        by rewrite (tokR_incons S.toks{1} S.toks{2} Rx.lop{2} S.req{2}); [assumption | smt()].
      if => //; last by auto.
      seq 1 1 : (={u0, T0, cs0, ws0, out, d, okk, c} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
      - by inline *; auto => /> &1 &2 *; rewrite /hcp; smt().
      seq 5 5 : (={u0, T0, cs0, ws0, out, d, okk, c, ys, mkh, mkc} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
      - while (={u0, T0, cs0, ws0, out, d, okk, c, ys, mkh, mkc, k} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
        + by auto => /> &1 &2 *; smt().
        by auto => /> &1 &2 hu hi *; rewrite hi.
      seq 4 1 : (={u0, T0, cs0, ws0, out, d, okk, c, ys, mkh, mkc, g} /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ tok{2} = oget S.toks{2}.[u0{2}]
  /\ tok{1}.`tk_i = tok{2}.`tk_i /\ tok{1}.`tk_msg = tok{2}.`tk_msg /\ tok{1}.`tk_T = tok{2}.`tk_T
  /\ tok{1}.`tk_wbar = tok{2}.`tk_wbar /\ tok{1}.`tk_phase = tok{2}.`tk_phase
  /\ tok{1}.`tk_dig = tok{2}.`tk_dig /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
      - auto => /> &1 &2 *.
        by apply (g_eq _ _ Rx.lop{2} S.req{2}); assumption.
      if; first by move=> &1 &2 [#] *; smt().
      - wp; rnd; auto => /> &1 &2 *.
        by apply (erase_inv _ _ Rx.lop{2} S.req{2} H0H.LC.sv{2} Ex.dn{2} S.ctr{2} u0{2}).
      if => //.
      - wp; rnd; auto => /> &1 &2 hu hi *; rewrite hi /=.
        by apply (erase_inv _ _ Rx.lop{2} S.req{2} H0H.LC.sv{2} Ex.dn{2} S.ctr{2} u0{2}).
      if => //.
      - auto => /> &1 &2 hu hi *; rewrite hi /=.
        rewrite (close_eq Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1} S.cs{2} S.p{1} S.p{2}); 1..3: by assumption.
        rewrite /=.
        by apply (erase_inv _ _ Rx.lop{2} S.req{2} H0H.LC.sv{2} Ex.dn{2} S.ctr{2} u0{2}).
      auto => /> &1 &2 hu hi *; rewrite hi /=.
      by apply (erase_inv _ _ Rx.lop{2} S.req{2} H0H.LC.sv{2} Ex.dn{2} S.ctr{2} u0{2}).
    by auto.
  by auto.
by auto.
qed.


lemma stC_in (cV : (request, rq) fmap) dn (V : request) (c : rq) :
  stC cV dn => V \in dn => stC cV.[V <- c] dn.
proof. by rewrite /stC => h hV W; rewrite mem_set; case => [/h | ->]. qed.

(* The last opener installs its secret *)
lemma install_step t1 t2 s1 s2 (lop : (request, int) fmap) (req : (int, request) fmap) dn
                   (ctr u : int) (vr : request) (tk1 tk2 : token) (va vb : vec * row) :
  tokR t1 t2 lop req => svR s1 s2 lop req => stK t2 req s2 lop dn ctr =>
  u \in t2 => req.[u] = Some vr => lop.[vr] = None => vr \in dn =>
  popn va = popn vb => strip tk1 = strip tk2 => tk2.`tk_phase <> 1 =>
  tokR t1.[u <- tk1] t2.[u <- tk2] lop.[vr <- u] req
  /\ svR s1.[u <- va] s2.[u <- vb] lop.[vr <- u] req
  /\ stK t2.[u <- tk2] req s2.[u <- vb] lop.[vr <- u] dn ctr.
proof.
move=> htR hsR hst hu hr hl hd hp hs hph.
have hil : islop lop.[vr <- u] req u by rewrite /islop hr /= get_set_sameE.
split.
+ by apply tokR_set_lop => //; apply tokR_lop.
split.
+ by apply svR_set_lop => //; apply svR_lop.
apply (stK_open _ _ _ _ _ _ _ _ _ _ _ hst hu hph).
+ by move=> w; rewrite mem_set; smt().
+ by move=> V w; rewrite get_setE; smt().
move=> V; rewrite mem_set; case => [hV | ->] //.
by move: hst; rewrite /stK; smt().
qed.


(* The last opener installs its secret: the structural facts *)
lemma stK_install toks req sv (lop : (request, int) fmap) dn (ctr u : int) (vr : request)
                  (t : token) (v : vec * row) :
  stK toks req sv lop dn ctr => u \in toks => vr \in dn => t.`tk_phase <> 1 =>
  stK toks.[u <- t] req sv.[u <- v] lop.[vr <- u] dn ctr.
proof.
move=> hst hu hd hph.
apply (stK_open _ _ _ _ _ _ _ _ _ _ _ hst hu hph).
+ by move=> w; rewrite mem_set; smt().
+ by move=> V w; rewrite get_setE; smt().
move=> V; rewrite mem_set; case => [hV | ->] //.
by move: hst; rewrite /stK; smt().
qed.

(* A revealed secret keeps the structural facts *)
lemma stK_reveal toks req sv (lop : (request, int) fmap) dn (ctr u : int) (t : token) (v : vec * row) :
  stK toks req sv lop dn ctr => u \in toks => t.`tk_phase <> 1 =>
  stK toks.[u <- t] req sv.[u <- v] lop dn ctr.
proof.
move=> hst hu hph.
apply (stK_open _ _ _ _ _ _ _ _ _ _ _ hst hu hph).
+ by move=> w; rewrite mem_set; smt().
+ by move=> V w ->; left.
by move: hst; rewrite /stK; smt().
qed.

(* Second rounds agree *)
equiv o2_q : CntO(SOH).o2 ~ CntO(SOQ(HM, HCO.QRO)).o2 :
  ={u, T, cs} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2} ==> ={res} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}.
proof.
proc; inline{1} SOP.o2; inline{2} SOQ(HM, HCO.QRO).o2.
inline{1} SOR(HCO.CQ, HCO.Rep).subm H0H.LC.reveal H0H.LC.gsec H0C.ER.submit.
inline{2} HM.gethint H0H.LC.reveal H0H.LC.gsec H0C.ER.submit.
sp.
if; first by move=> &1 &2 [#] *; smt(tokR_mem).
+ sp 1 1.
  if; first by move=> &1 &2 [#] *; smt(ok2_strip tokR_strip tokR_mem).
  + seq 4 4 : (={u0, T0, cs0, out, tok, d, vr} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}
  /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ ok2 tok{1} T0{1} cs0{1}
  /\ vr{1} = (tok{1}.`tk_msg, T0{1}, cs0{1}) /\ S.req{2}.[u0{2}] = Some vr{2}
  /\ !(u0{2} \in H0H.LC.sv{2}) /\ (forall V, Rx.lop{2}.[V] <> Some u0{2})
  /\ (!(vr{2} \in Ex.dn{2}) => Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}))).
    - auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hph *.
      have hu2 : u{2} \in S.toks{2} by rewrite -(tokR_mem _ _ _ _ u{2} htR).
      have hph2 : (oget S.toks{2}.[u{2}]).`tk_phase = 1.
      + by have := tokR_flds _ _ _ _ u{2} htR hu; smt().
      have [hnsv hnl] := stK_ph1 _ _ _ _ _ _ _ hst hu2 hph2.
      have hnl' : !islop Rx.lop{2} S.req{2} u{2} by rewrite /islop; apply hnl.
      have heq : S.toks{1}.[u{2}] = S.toks{2}.[u{2}] by apply (tokR_eq _ _ _ _ _ htR hnl').
      have hsv1 : !(u{2} \in H0H.LC.sv{1}) by rewrite (svR_mem _ _ _ _ u{2} hsR).
      rewrite heq /=.
      do !split.
      + exact (tokR_req _ _ _ _ _ _ htR heq (hnl _)).
      + apply (svR_req _ _ _ _ _ _ hsR _ (hnl _)).
        by move: hsv1 hnsv; rewrite !domE; case: (H0H.LC.sv{1}.[u{2}]); case: (H0H.LC.sv{2}.[u{2}]).
      + by apply stK_req.
      + by rewrite get_set_sameE.
      + exact hnsv.
      + exact hnl.
      move=> hdn; split; first by apply (stK_dn _ _ _ _ _ _ _ hst hdn).
      by apply (stC_dn _ _ _ hstC hdn).
    if => //.
    + seq 5 3 : (={u0, T0, cs0, out, tok, d, vr} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}
  /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ ok2 tok{1} T0{1} cs0{1}
  /\ vr{1} = (tok{1}.`tk_msg, T0{1}, cs0{1}) /\ S.req{2}.[u0{2}] = Some vr{2}
  /\ !(u0{2} \in H0H.LC.sv{2}) /\ (forall V, Rx.lop{2}.[V] <> Some u0{2})
  /\ (!(vr{2} \in Ex.dn{2}) => Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}))
  /\ Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}) /\ vr{2} \in Ex.dn{2}
  /\ !(u0{1} \in H0H.LC.sv{1})).
      - seq 3 2 : (={u0, T0, cs0, out, tok, d, vr} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}
  /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ ok2 tok{1} T0{1} cs0{1}
  /\ vr{1} = (tok{1}.`tk_msg, T0{1}, cs0{1}) /\ S.req{2}.[u0{2}] = Some vr{2}
  /\ !(u0{2} \in H0H.LC.sv{2}) /\ (forall V, Rx.lop{2}.[V] <> Some u0{2})
  /\ (!(vr{2} \in Ex.dn{2}) => Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}))
  /\ Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}) /\ vr{2} \in Ex.dn{2}
  /\ !(u0{1} \in H0H.LC.sv{1}) /\ V{1} = vr{2} /\ ={k}).
        + auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hph hT1 hT2 hT3 hT4 hT5 hT6 hreq hsv hnl himp hcomp hdn.
          have [h1 h2] := himp hdn.
          have hsv1 : !(u0{2} \in H0H.LC.sv{1}) by rewrite (svR_mem _ _ _ _ u0{2} hsR).
          by rewrite stK_dn_add // stC_add.
        wp.
        while (={u0, T0, cs0, out, tok, d, vr} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}
  /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ ok2 tok{1} T0{1} cs0{1}
  /\ vr{1} = (tok{1}.`tk_msg, T0{1}, cs0{1}) /\ S.req{2}.[u0{2}] = Some vr{2}
  /\ !(u0{2} \in H0H.LC.sv{2}) /\ (forall V, Rx.lop{2}.[V] <> Some u0{2})
  /\ (!(vr{2} \in Ex.dn{2}) => Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}))
  /\ Rx.lop{2}.[vr{2}] = None /\ !(vr{2} \in Rp.cV{2}) /\ vr{2} \in Ex.dn{2}
  /\ !(u0{1} \in H0H.LC.sv{1}) /\ V{1} = vr{2} /\ ={k}).
        + by inline *; auto.
        by auto.
      if => //.
      + rcondt{2} 2; first by auto => /> &2 *; smt().
        swap{1} 3 -2.
        seq 2 3 : (#pre /\ c{1} = c0{2} /\ s{1} = rp{2}).
        + rnd; rnd; wp; skip => &1 &2 h.
          split; first by move=> *.
          move=> _; split; first by move=> *.
          move=> _ cL hc.
          split; first exact hc.
          move=> _; split; first done.
          move=> _; split; first by move=> *.
          move=> _; split; first by move=> *.
          move=> _ sL hs.
          split; first exact hs.
          move=> _; split; first done.
          by move=> _; split.
        seq 1 5 : (={u0, T0, cs0, out, tok, d, vr, x} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} + 1 /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}
  /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ S.req{2}.[u0{2}] = Some vr{2}
  /\ !(u0{2} \in H0H.LC.sv{2}) /\ Rx.lop{2}.[vr{2}] = None /\ vr{2} \in Ex.dn{2}
  /\ !(vr{2} \in Rp.cV{2}) /\ Rx.nr{2} < qsig
  /\ popn s{1} = popn s{2} /\ !(u0{1} \in H0H.LC.sv{1}) /\ c{1} = c{2}
  /\ zh{2} = c{2} ** S.s{1} + s{1}.`1).
        + auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hph hT1 hT2 hT3 hT4 hT5 hT6 hreq hsv hnl himp hlv hcv hdnin hsv1 hnr.
          have hw := tokR_wsV S.toks{1} S.toks{2} Rx.lop{2} S.req{2} S.cs{2} H0C.ER.xs{2} Ex.ix{2}
                       ((oget S.toks{1}.[u0{2}]).`tk_msg, T0{2}, cs0{2}) htR.
          have hp := popn_hint S.s{1} S.e{1} c0{2} rp{2}.
          do !split => //.
          + by congr; congr; (apply/eq_sym; exact hp).
          by (apply/eq_sym; exact hp).
        seq 7 6 : (={u0, T0, cs0, out, tok, d, vr, x} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}
  /\ u0{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u0{1}] /\ S.req{2}.[u0{2}] = Some vr{2}
  /\ !(u0{2} \in H0H.LC.sv{2}) /\ Rx.lop{2}.[vr{2}] = None /\ vr{2} \in Ex.dn{2}
  /\ popn s{1} = popn s{2} /\ !(u0{1} \in H0H.LC.sv{1})).
        + auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hreq hsv hlv hdnin hcv hnr hp hsv1.
          split; first by rewrite hcp_set.
          split; first by apply yR_set.
          by apply stC_in.
        rcondt{1} 1; first by auto.
        rcondt{2} 1; first by auto.
        auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hreq hsv hlv hdnin hp hsv1.
        have hu2 : u0{2} \in S.toks{2} by rewrite -(tokR_mem _ _ _ _ u0{2} htR).
        rewrite !get_set_sameE !oget_some.
        split => _; (split; first exact hp);
          apply (install_step _ _ _ _ _ _ _ _ _ _ _ _ s{1} s{2} htR hsR hst hu2 hreq hlv hdnin hp) => //;
          rewrite /strip; congr; exact hp.
      rcondt{1} 4; first by auto.
      rcondt{2} 3; first by auto.
      auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hph hT1 hT2 hT3 hT4 hT5 hT6 hreq hsv hnl himp hlv hcv hdnin hsv1 hnr sL hs.
      have hu2 : u0{2} \in S.toks{2} by rewrite -(tokR_mem _ _ _ _ u0{2} htR).
      rewrite !get_set_sameE !oget_some.
      split => _; (split; first done);
        (split; first by apply tokR_set; apply tokR_lop);
        (split; first by apply svR_set; apply svR_lop);
        (split; first by apply yR_sV);
        by apply stK_install.
    sp 2 2.
    if; first by move=> &1 &2 [#] *; smt(svR_mem).
    + auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hph hT1 hT2 hT3 hT4 hT5 hT6 hreq hsv hnl himp hnc hsv1 sv1 hs.
      have hu2 : u0{2} \in S.toks{2} by rewrite -(tokR_mem _ _ _ _ u0{2} htR).
      rewrite !get_set_sameE !oget_some.
      split => _; (split; first done);
        (split; first by apply tokR_set);
        (split; first by apply svR_set);
        by apply stK_reveal.
    auto => /> &1 &2 htR hsR hyR hsh hlft hst hstC hu hph hT1 hT2 hT3 hT4 hT5 hT6 hreq hsv hnl himp hnc hin.
    by move: hin; rewrite (svR_mem _ _ _ _ u0{2} hsR) hsv.
  by auto.
by auto.
qed.

(* ---------- the final step ---------- *)

(* Programmed points belong to complete requests, and openers are honest members *)
op [opaque] invP (prog : (hcin, rq) fmap) (t : row) (C : corrset) (L : alog)
                 (toks : (int, token) fmap) : bool =
  (forall x, x \in prog => exists (V : request), x.`2 = (t, V.`1) /\ wf_committee V.`2
                                                 /\ complete V C L)
  /\ (forall (W : request) i, (W, i) \in L => i \in W.`2 /\ !(i \in C))
  /\ (forall u, u \in toks => !((oget toks.[u]).`tk_i \in C)).

lemma invP_empty (t : row) (C : corrset) : invP empty t C [] empty.
proof. by rewrite /invP; smt(mem_empty). qed.

lemma complete_cons (V : request) (C : corrset) (L : alog) e :
  complete V C L => complete V C (e :: L).
proof.
rewrite /complete => /allP h; apply/allP => j hj /=.
by right; apply (h j hj).
qed.

lemma invP_tok prog t C L (toks : (int, token) fmap) (k : int) (tk : token) :
  invP prog t C L toks => !(tk.`tk_i \in C) => invP prog t C L toks.[k <- tk].
proof.
rewrite /invP => -[h1 [h2 h3]] hi; do !split => //.
move=> u; rewrite mem_set get_setE; case: (u = k) => [-> /= | hne /=] //.
exact h3.
qed.

lemma invP_toki prog t C L (toks : (int, token) fmap) (u : int) :
  invP prog t C L toks => u \in toks => !((oget toks.[u]).`tk_i \in C).
proof. by rewrite /invP => -[_ [_ h3]]; apply h3. qed.

lemma invP_lo prog t C L toks (V : request) (i : int) :
  invP prog t C L toks => i \in V.`2 => !(i \in C) => invP prog t C ((V, i) :: L) toks.
proof.
rewrite /invP => -[h1 [h2 h3]] hi hc; do !split => //.
+ move=> x /h1 [W] [hx [hw hcp]]; exists W.
  split; first done.
  split; first done.
  by apply complete_cons.
by move=> W j; rewrite in_cons; case => [[-> ->] | /h2].
qed.

lemma invP_prog prog t C L toks (x : hcin) (c : rq) (V : request) :
  invP prog t C L toks => x.`2 = (t, V.`1) => wf_committee V.`2 => complete V C L =>
  invP prog.[x <- c] t C L toks.
proof.
rewrite /invP => -[h1 [h2 h3]] hx hw hc; do !split => //.
move=> y; rewrite mem_set; case => [/h1 // | ->].
by exists V.
qed.

(* A complete request makes every forgery on its message trivial *)
lemma complete_tf4 (V : request) (C : corrset) (L : alog) :
  wf_committee V.`2 => complete V C L =>
  (forall (W : request) i, (W, i) \in L => i \in W.`2 /\ !(i \in C)) =>
  tf4 C L V.
proof.
move=> [hu hs] hc hL.
have hmem : forall i, i \in S2 L V <=> i \in S4 C V.
+ move=> i; rewrite /S2 /S4 mem_undup; split.
  - move=> /mapP [e] [] /List.mem_filter [] /= he hin ->.
    have := hL e.`1 e.`2; rewrite -he /=.
    have -> : (e.`1, e.`2) = e by case: e he hin.
    move=> /(_ hin) [hi hnc].
    by rewrite /honest List.mem_filter.
  move=> hi; apply/mapP; exists (V, i) => /=.
  rewrite List.mem_filter /=; move: hc; rewrite /complete => /allP /(_ i hi).
  by move=> /=.
split => //.
rewrite /tf2.
have hsz : size (S2 L V) = size (honest V.`2 C).
+ apply perm_eq_size; apply uniq_perm_eq.
  - by rewrite /S2 undup_uniq.
  - by rewrite /honest; apply filter_uniq.
  by move=> i; rewrite (hmem i) /S4.
rewrite hsz /honest size_filter.
have hcount : count (fun i => i \in C) V.`2 <= size C.
+ rewrite -(size_filter (fun i => i \in C) V.`2).
  apply uniq_leq_size; first by apply filter_uniq.
  by move=> x; rewrite List.mem_filter => -[].
have hpc := count_predC (fun (i : int) => i \in C) V.`2.
have hcp : count (predC (fun (i : int) => i \in C)) V.`2 = count (fun i => !(i \in C)) V.`2.
+ by apply eq_count => x; rewrite /predC.
smt().
qed.

(* An accepted forgery that is not trivial solves SelfTargetMSIS *)
lemma final_step (prog : (hcin, rq) fmap) (f : hcin -> rq) (t : row) (C : corrset) (L : alog)
                 toks (mu : msg) (sg : sig) :
  rounding_fact => invP prog t C L toks =>
  win4 C L mu ((hcp prog f (liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt t)) + sg.`3), (t, mu))
                = sg.`1 /\ inbnd sg.`2 sg.`3) /\ admc C) =>
  f (stimage t sg.`2 sg.`1 (uof t sg.`2 sg.`1 sg.`3), (t, mu)) = sg.`1
  /\ solnorm sg.`2 sg.`1 (uof t sg.`2 sg.`1 sg.`3) <= bst.
proof.
move=> hr hinv; rewrite /win4 => -[[[hv hb] hC] hnt].
pose pt := (liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt t)) + sg.`3), (t, mu)).
have hnp : !(pt \in prog).
+ apply/negP => hp; move: hinv; rewrite /invP => -[h1 [h2 h3]].
  have [V [hx [hw hc]]] := h1 pt hp.
  apply hnt; exists V; split; first by move: hx; rewrite /pt /=; smt().
  exact (complete_tf4 V C L hw hc h2).
split; last exact (hr t sg.`2 sg.`1 sg.`3 hb).
rewrite stimage_uof.
by move: hv; rewrite /hcp -/pt hnp.
qed.

lemma invP_upd prog t C L (toks : (int, token) fmap) (u : int) (tk : token) :
  invP prog t C L toks => u \in toks => tk.`tk_i = (oget toks.[u]).`tk_i =>
  invP prog t C L toks.[u <- tk].
proof. by move=> h hu hi; apply invP_tok => //; rewrite hi; apply (invP_toki _ _ _ _ _ _ h hu). qed.

lemma invP_complete prog t C L (toks : (int, token) fmap) (u : int) (tk : token) (x : hcin) (c : rq)
                    (V : request) :
  invP prog t C L toks => u \in toks => tk.`tk_i = (oget toks.[u]).`tk_i =>
  x.`2 = (t, V.`1) => wf_committee V.`2 => complete V C L =>
  invP prog.[x <- c] t C L toks.[u <- tk].
proof.
move=> h hu hi hx hw hc; apply (invP_upd _ _ _ _ _ u) => //.
by apply (invP_prog _ _ _ _ _ _ _ V).
qed.


(* The checks keep the invariant of the final step *)
lemma chk_P : hoare [SOE(H0C.ER).chk : invP Rp.prog S.t S.cs S.lo S.toks
                                       ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto | auto].
qed.

lemma o1_P : hoare [CntO(SOQ(HM, HCO.QRO)).o1 : invP Rp.prog S.t S.cs S.lo S.toks
                                                ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof.
proc; inline SOA(H0H.LC).o1.
sp; if; last by auto.
seq 1 : (invP Rp.prog S.t S.cs S.lo S.toks /\ !(i0 \in S.cs)).
+ by inline *; sp; if; [sp; if; auto | sp; if; auto].
by auto => /> &hr h hi; apply invP_tok.
qed.

lemma o2_P : hoare [CntO(SOQ(HM, HCO.QRO)).o2 : invP Rp.prog S.t S.cs S.lo S.toks
                                                ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof.
proc; inline SOQ(HM, HCO.QRO).o2.
sp; if; last by auto.
sp; if; last by auto.
seq 4 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
         /\ wf_committee T0 /\ vr = (tok.`tk_msg, T0, cs0)).
+ auto => /> &hr h hu hph hU hS hI hT hcs hown.
  apply invP_lo => //.
  exact (invP_toki _ _ _ _ _ _ h hu).
if.
+ seq 3 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
           /\ wf_committee T0 /\ vr = (tok.`tk_msg, T0, cs0) /\ complete vr S.cs S.lo).
  - while (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
           /\ wf_committee T0 /\ vr = (tok.`tk_msg, T0, cs0) /\ complete vr S.cs S.lo).
    + by inline *; auto.
    by auto.
  if.
  - inline HM.gethint; sp; if.
    + auto => /> &hr h hu hU hS hc hn hm c _ rp _.
      by split => _; apply (invP_complete _ _ _ _ _ u0{hr} _ _ _ ((oget S.toks{hr}.[u0{hr}]).`tk_msg, T0{hr}, cs0{hr})).
    auto => /> &hr h hu hU hS hc hn hm.
    by split => _; apply (invP_complete _ _ _ _ _ u0{hr} _ _ _ ((oget S.toks{hr}.[u0{hr}]).`tk_msg, T0{hr}, cs0{hr})).
  seq 2 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]);
    first by auto.
  auto => /> &hr h hu.
  by split => _; apply (invP_upd _ _ _ _ _ u0{hr}).
inline *; sp; if.
+ auto => /> &hr h hu hU hS hc hsv s _.
  by apply (invP_upd _ _ _ _ _ u0{hr}).
auto => /> &hr h hu hU hS hc hs.
by apply (invP_upd _ _ _ _ _ u0{hr}).
qed.

lemma o3_P : hoare [CntO(SOQ(HM, HCO.QRO)).o3 : invP Rp.prog S.t S.cs S.lo S.toks
                                                ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof.
proc; inline SOQ(HM, HCO.QRO).o3.
sp; if; last by auto.
seq 1 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ by auto.
if; last by auto.
seq 1 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ by auto.
if; last by auto.
seq 5 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ while (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
  + by wp; call chk_P; auto.
  by auto.
if; last by auto.
seq 1 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ by inline *; auto.
seq 5 : (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ by while (invP Rp.prog S.t S.cs S.lo S.toks /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); auto.
sp; if.
+ auto => /> &hr h hu hd z _.
  by apply (invP_upd _ _ _ _ _ u0{hr}) => //; rewrite /erase.
if.
+ auto => /> &hr h hu hd hy z _.
  by apply (invP_upd _ _ _ _ _ u0{hr}) => //; rewrite /erase.
auto => /> &hr h hu hd.
by apply (invP_upd _ _ _ _ _ u0{hr}) => //; rewrite /erase.
qed.

lemma h0_P : hoare [CntH(HOQ(HCO.QRO)).h0 : invP Rp.prog S.t S.cs S.lo S.toks
                                            ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

lemma h1_P : hoare [CntH(HOQ(HCO.QRO)).h1 : invP Rp.prog S.t S.cs S.lo S.toks
                                            ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof. by proc; inline *; auto. qed.

lemma hc_P : hoare [CntH(HOQ(HCO.QRO)).hc : invP Rp.prog S.t S.cs S.lo S.toks
                                            ==> invP Rp.prog S.t S.cs S.lo S.toks].
proof. by proc; inline *; auto. qed.

section FinalHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -Rg, -Ry, -Kb, -HM,
                         -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ,
                         -H0C.Sim, -H0C.ER, -HCO.CQ, -HCO.Rep}.

(* In the last game the key comes from the instance, and programmed points belong to
   complete requests *)
lemma gq_inv :
  hoare [GQ(A, HM, HCO.QRO).run : true ==>
         S.t = rndkey Kb.b /\ (admc S.cs => invP Rp.prog S.t S.cs S.lo S.toks)].
proof.
proc.
seq 15 : true; first by call (_ : true); inline *; auto.
seq 3 : (S.t = rndkey Kb.b); first by auto.
if; last by auto.
call (_ : invP Rp.prog S.t S.cs S.lo S.toks).
+ exact o1_P.
+ exact o2_P.
+ exact o3_P.
+ exact h0_P.
+ exact h1_P.
+ exact hc_P.
by auto => /> &hr *; apply invP_empty.
qed.

lemma gq_spec :
  equiv [GQ(A, HM, HCO.QRO).run ~ GQ(A, HM, HCO.QRO).run :
         ={glob A, Ex.cur, HM.s, HM.e, HM.n, HCO.QRO.fh, Kb.b, Rp.prog, Bd.b1, Bd.b2, Bd.b3, S.lo}
         ==> ={res, S.t, S.cs, S.lo, Bd.b1, Bd.b2, Bd.b3, H0C.ER.ts, H0C.ER.xs, H0C.ER.cks,
               Rp.prog, HCO.QRO.fh, Kb.b}
             /\ S.t{2} = rndkey Kb.b{2}
             /\ (admc S.cs{2} => invP Rp.prog{2} S.t{2} S.cs{2} S.lo{2} S.toks{2})].
proof.
conseq (_ : ={glob A, Ex.cur, HM.s, HM.e, HM.n, HCO.QRO.fh, Kb.b, Rp.prog, Bd.b1, Bd.b2, Bd.b3, S.lo}
            ==> ={res, S.t, S.cs, S.lo, Bd.b1, Bd.b2, Bd.b3, H0C.ER.ts, H0C.ER.xs, H0C.ER.cks,
                  Rp.prog, HCO.QRO.fh, Kb.b}) _ gq_inv => //.
by proc; sim.
qed.

(* The ideal HintMLWE game is at most the success of the reduction to SelfTargetMSIS *)
lemma hm_stm &m :
  rounding_fact =>
  Pr[HMLWE(B2(A)).main(false) @ &m : res] <= Pr[STM(B3(A)).main() @ &m : res].
proof.
move=> hr.
byequiv (_ : ={glob A, Ex.cur, Rp.prog, Bd.b1, Bd.b2, Bd.b3, S.lo} /\ !real{1} ==> res{1} => res{2}) => //.
proc.
inline B2(A, HM).guess B3(A, HCO.QRO).solve HCO.QRO.init.
rcondf{1} 4; first by auto.
swap{1} 7 -3.
swap{2} [5..7] -4.
seq 7 7 : (={glob A, Ex.cur, HM.s, HM.e, HM.n, HCO.QRO.fh, Kb.b, Rp.prog, Bd.b1, Bd.b2, Bd.b3, S.lo} /\ Kb.b{2} = b{2}).
+ by auto.
seq 1 1 : (mu{1} = mu0{2} /\ ={sg, S.t, S.cs, S.lo, Bd.b1, Bd.b2, Bd.b3, H0C.ER.ts, H0C.ER.xs,
             H0C.ER.cks, Rp.prog, HCO.QRO.fh, Kb.b}
           /\ Kb.b{2} = b{2} /\ S.t{2} = rndkey Kb.b{2}
           /\ (admc S.cs{2} => invP Rp.prog{2} S.t{2} S.cs{2} S.lo{2} S.toks{2})).
+ by call gq_spec; auto.
inline *; auto => /> &1 hinv.
split => hp hv hb hU hS hA hnt *.
+ have hC : admc S.cs{1} by rewrite /admc.
  apply (final_step Rp.prog{1} HCO.QRO.fh{1} (rndkey b{1}) S.cs{1} S.lo{1} S.toks{1} mu0{1} sg{1}
                    hr (hinv hC)).
  by rewrite /win4 /hcp hp /=; do !split.
have hC : admc S.cs{1} by rewrite /admc.
apply (final_step Rp.prog{1} HCO.QRO.fh{1} (rndkey b{1}) S.cs{1} S.lo{1} S.toks{1} mu0{1} sg{1}
                  hr (hinv hC)).
by rewrite /win4 /hcp hp /=; do !split.
qed.

end section FinalHop.

(* The programmed oracle without programmed points *)
lemma hcp_empty (f : hcin -> rq) : hcp empty f = f.
proof. by apply fun_ext => x; rewrite /hcp mem_empty. qed.

(* The relations hold before any query *)
lemma inv_init (lop : (request, int) fmap) (req : (int, request) fmap) yV sV (s : vec) dn :
  req = empty =>
  tokR empty empty lop req /\ svR empty empty lop req /\ yR yV empty sV s
  /\ stK empty req empty empty dn 0 /\ stC empty dn.
proof.
move=> ->; rewrite /tokR /svR /yR /stK /stC; smt(mem_empty).
qed.

(* The corrupt shares given to the adversary agree *)
lemma sks_eq (C : corrset) (s : vec) (p1 p2 : int -> vec) :
  shR C s p1 p2 =>
  (fun j => if j \in C then shr s p1 j else RqVec.Vector.zerov)
  = (fun j => if j \in C then shr RqVec.Vector.zerov p2 j else RqVec.Vector.zerov).
proof. by rewrite /shR => h; apply fun_ext => j /=; case: (j \in C) => // hj; rewrite h. qed.

(* Seeds are lossless *)
lemma dseedf_ll : is_lossless dseedf.
proof. by rewrite /dseedf; apply PF.dfun_ll => x /=; exact dseed_ll. qed.

(* The oracles of the hint game terminate *)
lemma o1h_ll : islossless CntO(SOH).o1.
proof.
proc; inline *; sp; if; last by auto.
by sp; if; sp; if; auto => />; smt(dcmt_ll dnp_ll).
qed.

lemma o2h_ll : islossless CntO(SOH).o2.
proof. by proc; call sop_o2_ll; auto. qed.

lemma o3h_ll : islossless CntO(SOH).o3.
proof. by proc; call soh_o3_ll; auto. qed.

lemma h1h_ll : islossless CntH(HOP).h1.
proof. by proc; inline *; auto. qed.

lemma hch_ll : islossless CntH(HOP).hc.
proof. by proc; inline *; auto. qed.


(* Admissible reductions: a HintMLWE adversary does not read the secret of the game, and a
   SelfTargetMSIS adversary reaches the oracle only through its procedure *)
lemma hm_adv_ok (B <: HMAdv {-HM}) : true.
proof. by trivial. qed.

lemma stm_adv_ok (B <: STAdv2 {-HCO.QRO}) : true.
proof. by trivial. qed.

section FinHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -Rg, -Ry, -Kb, -HM,
                         -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ,
                         -H0C.Sim, -H0C.ER, -HCO.CQ, -HCO.Rep}.

declare axiom A_ll (H <: HOr {-A}) (O <: SOr {-A}) :
  islossless H.h0 => islossless H.h1 => islossless H.hc =>
  islossless O.o1 => islossless O.o2 => islossless O.o3 =>
  islossless A(H, O).forge.

declare axiom alpha_unit : forall j, 1 <= j <= nmax => Rq.ComRingDflInv.unit (alpha j).

(* The adversary terminates in the hint game *)
lemma forge_h_ll : islossless A(CntH(HOP), CntO(SOH)).forge.
proof.
exact (A_ll (CntH(HOP)) (CntO(SOH)) h0_ll h1h_ll hch_ll o1h_ll o2h_ll o3h_ll).
qed.

lemma gh_hm &m : Pr[GH(A).main() @ &m : res] = Pr[HMLWE(B2(A)).main(true) @ &m : res].
proof.
byequiv (_ : ={glob A, Ex.cur} /\ real{2} ==> ={res}) => //.
proc.
inline B2(A, HM).guess GQ(A, HM, HCO.QRO).run.
inline *.
rcondt{2} 4; first by auto.
swap{1} [18..19] -17.
seq 2 2 : (={glob A, Ex.cur} /\ real{2} /\ S.s{1} = HM.s{2} /\ S.e{1} = HM.e{2}); first by auto.
seq 16 19 : (={glob A, Ex.cur, HCO.QRO.fh, H0H.QRO.fh, H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft,
              H0H.CQ.n, H0C.QRO.fh, H0C.Sim.st, H0C.ER.ts, H0C.ER.xs, H0C.ER.cks, H0C.ER.simw,
              H0C.CQ.n, H1O.QRO.fh}
             /\ Rp.fhp{1} = HCO.QRO.fh{1} /\ S.s{1} = HM.s{2} /\ S.e{1} = HM.e{2}
             /\ HM.n{2} = 0 /\ Kb.b{2} = mulA mA HM.s{2} + HM.e{2}
             /\ H0H.LC.sv{1} = empty /\ H0H.LC.lft{1}).
+ by auto.
seq 1 1 : (={glob A, Ex.cur, S.cs, HCO.QRO.fh, H0H.QRO.fh, H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft,
             H0H.CQ.n, H0C.QRO.fh, H0C.Sim.st, H0C.ER.ts, H0C.ER.xs, H0C.ER.cks, H0C.ER.simw,
             H0C.CQ.n, H1O.QRO.fh}
            /\ Rp.fhp{1} = HCO.QRO.fh{1} /\ S.s{1} = HM.s{2} /\ S.e{1} = HM.e{2}
            /\ HM.n{2} = 0 /\ Kb.b{2} = mulA mA HM.s{2} + HM.e{2}
            /\ H0H.LC.sv{1} = empty /\ H0H.LC.lft{1}).
+ by call (_ : true).
case (admc S.cs{1}).
+ rcondt{2} 4; first by auto.
  swap{2} 4 -3.
  seq 1 1 : (={glob A, Ex.cur, S.cs, HCO.QRO.fh, H0H.QRO.fh, H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft,
               H0H.CQ.n, H0C.QRO.fh, H0C.Sim.st, H0C.ER.ts, H0C.ER.xs, H0C.ER.cks, H0C.ER.simw,
               H0C.CQ.n, H1O.QRO.fh}
              /\ Rp.fhp{1} = HCO.QRO.fh{1} /\ S.s{1} = HM.s{2} /\ S.e{1} = HM.e{2}
              /\ HM.n{2} = 0 /\ Kb.b{2} = mulA mA HM.s{2} + HM.e{2}
              /\ H0H.LC.sv{1} = empty /\ H0H.LC.lft{1} /\ admc S.cs{1}
              /\ shR S.cs{1} S.s{1} S.p{1} S.p{2}).
  + rnd (shiftp S.s{1} S.cs{1}) (unshiftp S.s{1} S.cs{1}).
    auto => /> &1 hlft hU hS hA.
    split; first by move=> p hp; rewrite unshiftpK.
    move=> _; split.
    - move=> p hp; apply dpoly_mu1; first by rewrite -dpoly_supp.
      by apply unshiftp_supp; rewrite -dpoly_supp.
    move=> _ p hp; split.
    - by rewrite dpoly_supp; apply shiftp_supp; rewrite -dpoly_supp.
    move=> _; split; first by rewrite shiftpK.
    move=> _; apply shR_shift; first exact alpha_unit.
    by rewrite /admc; do !split.
  seq 32 30 : (={glob A, S.t} /\ sks{1} = sks{2} /\ sds{1} = sds{2} /\ ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
  + auto => /> &1 &2 hlft hU hS hA hsh sdc hsdc.
    have [h1 [h2 [h3 [h4 h5]]]] := inv_init empty empty empty empty HM.s{2} [] _ => //.
    by rewrite hcp_empty (sks_eq _ _ _ _ hsh) h1 h2 h3 h4 h5.
  wp.
  call (_ : ={S.cs, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd, Ex.ix, Ex.n, Ex.dn, Ex.cur,
      H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, H0H.CQ.n, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.prog, Rp.cV, Fz.fz}
  /\ Rp.fhp{1} = hcp Rp.prog{2} HCO.QRO.fh{2}
  /\ tokR S.toks{1} S.toks{2} Rx.lop{2} S.req{2}
  /\ svR H0H.LC.sv{1} H0H.LC.sv{2} Rx.lop{2} S.req{2}
  /\ yR Ry.yV{2} Rp.cV{2} Rp.sV{1} S.s{1}
  /\ shR S.cs{2} S.s{1} S.p{1} S.p{2}
  /\ Kb.b{2} = mulA mA S.s{1} + S.e{1} /\ HM.s{2} = S.s{1} /\ HM.e{2} = S.e{1}
  /\ HM.n{2} = Rx.nr{2} /\ H0H.LC.lft{2}
  /\ stK S.toks{2} S.req{2} H0H.LC.sv{2} Rx.lop{2} Ex.dn{2} S.ctr{2}
  /\ stC Rp.cV{2} Ex.dn{2}).
  + exact o1_q.
  + exact o2_q.
  + exact o3_q.
  + exact h0_q.
  + exact h1_q.
  + exact hc_q.
  auto => /> &1 &2 *.
  by rewrite /hcp; smt().
rcondf{2} 4; first by auto.
wp.
call{1} forge_h_ll.
wp; rnd{1}; wp; rnd{1}.
auto => /> &1 &2 hC.
split; first exact dpoly_ll.
by move=> _ p _; exact dseedf_ll.
qed.


(* The hint game costs the HintMLWE advantage of B2 and the SelfTargetMSIS success of B3 *)
lemma gh_bound &m :
  rounding_fact =>
  Pr[GH(A).main() @ &m : res]
  <= `|Pr[HMLWE(B2(A)).main(true) @ &m : res] - Pr[HMLWE(B2(A)).main(false) @ &m : res]|
     + Pr[STM(B3(A)).main() @ &m : res].
proof.
move=> hr; rewrite (gh_hm &m).
have := hm_stm A &m hr.
smt().
qed.


(* The reductions are admissible adversaries of the assumption games *)
lemma b2_ok : true.
proof. by have := hm_adv_ok (B2(A)). qed.

lemma b3_ok : true.
proof. by have := stm_adv_ok (B3(A)). qed.

end section FinHop.
