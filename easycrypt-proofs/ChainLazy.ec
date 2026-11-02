require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim ChainDead.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op popn (s : vec * row) : row = rndc (commit s.`1 s.`2).

op pw : real.

module HOL (O : H0H.LC_i) : HOr = {
  proc h0(x : h0in) : cmt = {
    var y;
    if (PIdx.val x.`1.`2 \in S.cs) { y <- H0C.QRO.fh x; } else { y <@ O.h(x); }
    return y;
  }
  proc h1(x : h1in) : view = { return H1O.QRO.fh x; }
  proc hc(x : hcin) : rq = { return HCO.QRO.fh x; }
}.

module SOL (O : H0H.LC_i) : SOr = {
  proc h0any(x : h0in) : cmt = {
    var y;
    if (PIdx.val x.`1.`2 \in S.cs) { y <- H0C.QRO.fh x; } else { y <@ O.h(x); }
    return y;
  }

  proc o1(i : int, mu : msg) : (int * cmt) option = {
    var c, out;
    out <- None;
    if (1 <= i <= nmax /\ !(i \in S.cs)) {
      c <@ O.commit(S.ctr, ((S.t, mu), toidx i));
      S.toks.[S.ctr] <- {| tk_i = i; tk_msg = mu; tk_r = witness; tk_e = witness; tk_wbar = witness;
                           tk_cmt = c; tk_phase = 1; tk_T = []; tk_dig = witness |};
      out <- Some (S.ctr, c);
      S.ctr <- S.ctr + 1;
    }
    return out;
  }

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        s <@ O.reveal(u);
        S.toks.[u] <- {| tok with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2;
                                  tk_T = T; tk_dig = d |};
        S.req.[u] <- (tok.`tk_msg, T, cs);
        S.lo <- ((tok.`tk_msg, T, cs), tok.`tk_i) :: S.lo;
        out <- Some (popn s);
      }
    }
    return out;
  }

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ h0any((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
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
                z <$ dvec;
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

module GameL (A : Adv) (O : H0H.LC_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOL(O)), CntO(SOL(O))).corrupt();
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
    Fz.fz <- empty;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOL(O)), CntO(SOL(O))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

module BL (A : Adv) (O : H0H.LC_i) = {
  proc main() : bool = {
    var b;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameL(A, O).run();
    return b;
  }
}.

op [opaque] tokrel (t1 t2 : (int, token) fmap) (sv : (int, vec * row) fmap) (ctr : int) : bool =
  0 <= ctr
  /\ (forall u, u \in t1 <=> u \in t2)
  /\ (forall u, u \in t1 => 0 <= u < ctr)
  /\ (forall u, u \in sv => 0 <= u < ctr)
  /\ (forall u, u \in t1 => (oget t1.[u]).`tk_phase <> 1 => t1.[u] = t2.[u])
  /\ (forall u, u \in t1 => (oget t1.[u]).`tk_phase = 1 =>
        (oget t2.[u]).`tk_i = (oget t1.[u]).`tk_i
        /\ (oget t2.[u]).`tk_msg = (oget t1.[u]).`tk_msg
        /\ (oget t2.[u]).`tk_cmt = (oget t1.[u]).`tk_cmt
        /\ (oget t2.[u]).`tk_phase = 1
        /\ (oget t2.[u]).`tk_T = (oget t1.[u]).`tk_T
        /\ (oget t2.[u]).`tk_dig = (oget t1.[u]).`tk_dig
        /\ sv.[u] = Some ((oget t1.[u]).`tk_r, (oget t1.[u]).`tk_e)
        /\ (oget t1.[u]).`tk_wbar = popn ((oget t1.[u]).`tk_r, (oget t1.[u]).`tk_e)).

(* Second-round checks ignore the nonce fields *)
lemma ok2_fields (t1 t2 : token) (T : committee) (cs : cmt list) :
  t2.`tk_i = t1.`tk_i => t2.`tk_cmt = t1.`tk_cmt => t2.`tk_phase = t1.`tk_phase =>
  ok2 t2 T cs = ok2 t1 T cs.
proof. by rewrite /ok2 /own_cmt => -> -> ->. qed.

(* Fresh first rounds keep the token relation *)
lemma tokrel_o1 t1 t2 sv (ctr i : int) (mu : msg) (s : vec * row) (c : cmt) :
  tokrel t1 t2 sv ctr =>
  tokrel t1.[ctr <- {| tk_i = i; tk_msg = mu; tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s;
                       tk_cmt = c; tk_phase = 1; tk_T = []; tk_dig = witness |}]
         t2.[ctr <- {| tk_i = i; tk_msg = mu; tk_r = witness; tk_e = witness; tk_wbar = witness;
                       tk_cmt = c; tk_phase = 1; tk_T = []; tk_dig = witness |}]
         sv.[ctr <- s] (ctr + 1).
proof.
rewrite /tokrel => -[#] h0 h1 h2 h3 h4 h5; split; first smt().
split.
+ by move=> u; rewrite !mem_set h1.
split.
+ by move=> u; rewrite mem_set => -[/h2 | ->]; smt().
split.
+ by move=> u; rewrite mem_set => -[/h3 | ->]; smt().
split.
+ move=> u; rewrite mem_set !get_setE; case: (u = ctr) => [-> //= | hne /= hu hp].
  exact (h4 u hu hp).
move=> u; rewrite mem_set !get_setE; case: (u = ctr) => [-> /= | hne /= hu hp].
+ by case: s.
have [#] g1 g2 g3 g4 g5 g6 g7 g8 := h5 u hu hp.
by rewrite g1 g2 g3 g4 g5 g6 g8 /= g7.
qed.

(* Opening a token keeps the token relation *)
lemma tokrel_o2 t1 t2 sv (ctr u : int) (tok1 tok2 : token) (s : vec * row) (T : committee)
                (d d' : view) :
  tokrel t1 t2 sv ctr => u \in t1 => tok1 = oget t1.[u] => tok2 = oget t2.[u] =>
  s = oget sv.[u] => tok1.`tk_phase = 1 => d = d' =>
  tokrel t1.[u <- {| tok1 with tk_phase = 2; tk_T = T; tk_dig = d |}]
         t2.[u <- {| tok2 with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2;
                              tk_T = T; tk_dig = d' |}]
         sv ctr.
proof.
rewrite /tokrel => -[#] h0 h1 h2 h3 h4 h5 hu -> -> -> hp <-.
have [#] g1 g2 g3 g4 g5 g6 g7 g8 := h5 u hu hp.
split; first done.
split; first by move=> u'; rewrite !mem_set h1.
split; first by move=> u'; rewrite mem_set => -[/h2 // | ->]; exact (h2 u hu).
split; first exact h3.
split.
+ move=> u'; rewrite mem_set !get_setE; case: (u' = u) => [-> _ _ /= | hne /= hu' hp'].
  - by rewrite g1 g2 g3 g7 /= -g8.
  exact (h4 u' hu' hp').
move=> u'; rewrite mem_set !get_setE; case: (u' = u) => [-> //= | hne /= hu' hp'].
exact (h5 u' hu' hp').
qed.

(* Erasing an opened token keeps the token relation *)
lemma tokrel_erase t1 t2 sv (ctr u : int) :
  tokrel t1 t2 sv ctr => u \in t1 => (oget t1.[u]).`tk_phase = 2 =>
  tokrel t1.[u <- erase (oget t1.[u])] t2.[u <- erase (oget t2.[u])] sv ctr.
proof.
rewrite /tokrel => -[#] h0 h1 h2 h3 h4 h5 hu hp.
have heq := h4 u hu _; first by rewrite hp.
split; first done.
split; first by move=> u'; rewrite !mem_set h1.
split; first by move=> u'; rewrite mem_set => -[/h2 // | ->]; exact (h2 u hu).
split; first exact h3.
split.
+ move=> u'; rewrite mem_set !get_setE; case: (u' = u) => [-> _ _ /= | hne /= hu' hp'].
  - by rewrite heq.
  exact (h4 u' hu' hp').
move=> u'; rewrite mem_set !get_setE; case: (u' = u) => [-> //= | hne /= hu' hp'].
+ by rewrite /erase.
exact (h5 u' hu' hp').
qed.

(* Related token maps have the same domain *)
lemma tokrel_mem t1 t2 sv (ctr u : int) : tokrel t1 t2 sv ctr => (u \in t1 <=> u \in t2).
proof. by rewrite /tokrel => -[#] _ h1 *; exact (h1 u). qed.

(* Related tokens agree once opened *)
lemma tokrel_eq t1 t2 sv (ctr u : int) :
  tokrel t1 t2 sv ctr => u \in t1 => (oget t1.[u]).`tk_phase <> 1 => oget t1.[u] = oget t2.[u].
proof. by rewrite /tokrel => -[#] _ _ _ _ h4 _ hu hp; rewrite (h4 u hu hp). qed.

(* Related unopened tokens stay unopened *)
lemma tokrel_ph1 t1 t2 sv (ctr u : int) :
  tokrel t1 t2 sv ctr => u \in t1 => (oget t1.[u]).`tk_phase = 1 =>
  (oget t2.[u]).`tk_phase = 1.
proof. by rewrite /tokrel => -[#] _ _ _ _ _ h5 hu hp; have [#] := h5 u hu hp. qed.

(* The next token index is fresh *)
lemma tokrel_fresh t1 t2 sv (ctr : int) : tokrel t1 t2 sv ctr => !(ctr \in sv) /\ !(ctr \in t1).
proof. by rewrite /tokrel => -[#] _ _ h2 h3 *; split; [apply/negP => /h3 | apply/negP => /h2]. qed.

(* Related tokens pass the second-round checks together *)
lemma tokrel_ok2 t1 t2 sv (ctr u : int) (T : committee) (cs : cmt list) :
  tokrel t1 t2 sv ctr => u \in t1 => ok2 (oget t1.[u]) T cs = ok2 (oget t2.[u]) T cs.
proof.
move=> htr hu; case: ((oget t1.[u]).`tk_phase = 1) => hp.
+ move: htr; rewrite /tokrel => -[#] _ _ _ _ _ h5.
  have [#] g1 _ g3 g4 _ _ _ _ := h5 u hu hp.
  by rewrite (ok2_fields (oget t1.[u]) (oget t2.[u])) // g4 hp.
by rewrite (tokrel_eq _ _ _ _ _ htr hu hp).
qed.

(* Unopened related tokens hold their nonce in the secrets *)
lemma tokrel_sec t1 t2 sv (ctr u : int) :
  tokrel t1 t2 sv ctr => u \in t1 => (oget t1.[u]).`tk_phase = 1 =>
  u \in sv /\ oget sv.[u] = ((oget t1.[u]).`tk_r, (oget t1.[u]).`tk_e)
  /\ (oget t1.[u]).`tk_wbar = popn (oget sv.[u]).
proof.
rewrite /tokrel => -[#] _ _ _ _ _ h5 hu hp.
have [#] _ _ _ _ _ _ g7 g8 := h5 u hu hp.
by rewrite domE g7 /= g8.
qed.

(* Unopened related tokens share their public fields *)
lemma tokrel_flds t1 t2 sv (ctr u : int) :
  tokrel t1 t2 sv ctr => u \in t1 => (oget t1.[u]).`tk_phase = 1 =>
  (oget t2.[u]).`tk_i = (oget t1.[u]).`tk_i /\ (oget t2.[u]).`tk_msg = (oget t1.[u]).`tk_msg
  /\ (oget t2.[u]).`tk_cmt = (oget t1.[u]).`tk_cmt.
proof.
rewrite /tokrel => -[#] _ _ _ _ _ h5 hu hp.
by have [#] -> -> -> *:= h5 u hu hp.
qed.

section LazyHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO,
                          -H0H.CQ, -H1O.CQ, -H0H.LC}.

(* Eager commitment checks agree with the commitment oracle *)
equiv h0any_l0 :
  SOF(MPI, H0H.QRO, H1O.QRO).h0any ~ SOL(H0H.LC).h0any :
  ={x, S.cs, H0H.QRO.fh, H0C.QRO.fh} /\ !H0H.LC.lft{2} ==> ={res}.
proof.
proc; if => //; first by auto.
inline *; sp; if{2}; first by exfalso => /#.
by auto.
qed.

(* Eager third rounds agree with the commitment oracle *)
equiv o3_l0 :
  SOFt(H0H.QRO, H1O.QRO).o3 ~ SOL(H0H.LC).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz,
                       H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz,
                  H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}.
proof.
proc; sp; if; first by move=> /> &1 &2 *; smt(tokrel_mem).
+ sp; case (tok{1}.`tk_phase = 1).
  + rcondf{1} 1; first by move=> &2; auto => /> /#.
    rcondf{2} 1; first by move=> &1; auto => /> *; smt(tokrel_ph1 tokrel_mem).
    by auto.
  seq 0 0 : (#pre /\ ={tok}); first by auto => /> *; smt(tokrel_eq).
  if; first by move=> &1 &2 [#]; smt().
  + seq 1 1 : (={u, T, cs, ws, tok, d, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr,
             S.lo, S.lr, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
           /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
           /\ u{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u{1}] /\ tok{1}.`tk_phase = 2).
    + by inline *; auto => />; smt().
    if; first by move=> &1 &2 [#]; smt().
    + seq 3 3 : (={u, T, cs, ws, tok, d, out, okk} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr,
             S.lo, S.lr, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
           /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
           /\ u{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u{1}] /\ tok{1}.`tk_phase = 2).
      + while (={k, u, T, cs, ws, tok, d, out, okk} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr,
             S.lo, S.lr, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
           /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
           /\ u{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u{1}] /\ tok{1}.`tk_phase = 2).
        + by wp; call h0any_l0; auto.
        by auto.
      if; first by move=> &1 &2 [#]; smt().
      + seq 6 6 : (={u, T, cs, ws, tok, d, out, okk, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr,
             S.lo, S.lr, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
           /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
           /\ u{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u{1}] /\ tok{1}.`tk_phase = 2).
        + while (={k, u, T, cs, ws, tok, d, out, okk, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr,
             S.lo, S.lr, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
           /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
           /\ u{1} \in S.toks{1} /\ tok{1} = oget S.toks{1}.[u{1}] /\ tok{1}.`tk_phase = 2); last by auto.
          by auto.
        sp; if; first by move=> /> *.
        + auto => /> &1 &2 htr hlft hu hph *.
          have heq : oget S.toks{1}.[u{2}] = oget S.toks{2}.[u{2}].
          - by apply (tokrel_eq _ _ _ _ _ htr hu); rewrite hph.
          by rewrite {2}heq; exact (tokrel_erase _ _ _ _ _ htr hu hph).
        if; first by move=> /> *.
        + wp; rnd; auto => /> &1 &2 htr hlft hu hph *.
          have heq : oget S.toks{1}.[u{2}] = oget S.toks{2}.[u{2}].
          - by apply (tokrel_eq _ _ _ _ _ htr hu); rewrite hph.
          by rewrite {2}heq; exact (tokrel_erase _ _ _ _ _ htr hu hph).
        auto => /> &1 &2 htr hlft hu hph *.
        have heq : oget S.toks{1}.[u{2}] = oget S.toks{2}.[u{2}].
        - by apply (tokrel_eq _ _ _ _ _ htr hu); rewrite hph.
        by rewrite {2}heq; exact (tokrel_erase _ _ _ _ _ htr hu hph).
      by auto.
    by auto.
  by auto.
by auto.
qed.

(* Eager first rounds agree with the commitment oracle *)
equiv o1_l0 :
  SOFt(H0H.QRO, H1O.QRO).o1 ~ SOL(H0H.LC).o1 :
  ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz,
            H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz,
            H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}.
proof.
proc; sp; if; first by move=> /> *.
+ inline *; sp.
  rcondf{2} 1; first by move=> &1; auto.
  sp; rcondt{2} 1; first by move=> &1; auto => /> *; smt(tokrel_fresh).
  wp; rnd; auto => /> &1 &2 htr hlft *.
  rewrite get_set_sameE /=.
  exact (tokrel_o1 _ _ _ _ _ _ _ _ htr).
by auto.
qed.

(* Eager second rounds agree with the commitment oracle *)
equiv o2_l0 :
  SOFt(H0H.QRO, H1O.QRO).o2 ~ SOL(H0H.LC).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz,
            H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz,
            H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}.
proof.
proc; sp; if; first by move=> /> *; smt(tokrel_mem).
+ sp; if; first by move=> /> &1 &2 *; smt(tokrel_ok2).
  + inline *; sp.
    rcondf{2} 1.
    + move=> &1; auto => /> *; smt(tokrel_sec).
    seq 0 1 : (#pre /\ s0{2} = oget H0H.LC.sv{2}.[u1{2}]); first by auto.
    if{2}; auto => /> &2 toks_L htr hlft hu hph *.
    + have [_ [_ hw]] := tokrel_sec _ _ _ _ _ htr hu hph.
      have [hi [hm hc]] := tokrel_flds _ _ _ _ _ htr hu hph.
      split; first exact hw.
      split; first by rewrite hm hi.
      apply (tokrel_o2 _ _ _ _ _ (oget toks_L.[u{2}]) (oget S.toks{2}.[u{2}])
                       (oget H0H.LC.sv{2}.[u{2}])) => //.
      by rewrite hm.
    have [_ [_ hw]] := tokrel_sec _ _ _ _ _ htr hu hph.
    have [hi [hm hc]] := tokrel_flds _ _ _ _ _ htr hu hph.
    split; first exact hw.
    split; first by rewrite hm hi.
    apply (tokrel_o2 _ _ _ _ _ (oget toks_L.[u{2}]) (oget S.toks{2}.[u{2}])
                     (oget H0H.LC.sv{2}.[u{2}])) => //.
    by rewrite hm.
  by auto.
by auto.
qed.


(* Eager commitments through the interface give the previous game *)
lemma g1t_lazy0 &m :
  Pr[G1t(A).main() @ &m : res] = Pr[H0H.LCG(BL(A)).main(false) @ &m : res].
proof.
byequiv => //; proc.
inline G1t(A).main BL(A, H0H.LC).main GameFt(A, H0H.QRO, H1O.QRO).run GameL(A, H0H.LC).run.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.req, S.ctr, S.lo, S.lr, Fz.fz, Cnt.c0, Cnt.c1,
            Cnt.cc, Cnt.cs, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
          /\ tokrel S.toks{1} S.toks{2} H0H.LC.sv{2} S.ctr{2} /\ !H0H.LC.lft{2}).
+ by proc; wp; call o1_l0; auto.
+ by proc; wp; call o2_l0; auto.
+ by proc; wp; call o3_l0; auto.
+ proc; sp 1 1; inline HOF(H0H.QRO, H1O.QRO).h0 HOL(H0H.LC).h0; sp 1 1.
  if => //; first by auto.
  by inline *; sp; if{2}; [exfalso => /# | auto].
+ by proc; inline *; auto.
+ by proc; inline *; auto.
inline *; auto; call (_ : true); auto => />.
by rewrite /tokrel; smt(mem_empty).
qed.

(* Secrets indexed below a bound are at most that many *)
lemma card_sv (sv : (int, vec * row) fmap) (n : int) :
  0 <= n => (forall u, u \in sv => 0 <= u < n) => card (fdom sv) <= n.
proof.
move=> hn hk.
have hsub : fdom sv \subset oflist (range 0 n).
+ by move=> u; rewrite mem_fdom mem_oflist mem_range => /hk.
have := subset_leq_fcard _ _ hsub.
have := fcard_oflist (range 0 n).
by rewrite size_range; smt().
qed.

op [opaque] lzs (cs ctr : int) (sv : (int, vec * row) fmap) (toks : (int, token) fmap) : bool =
  0 <= ctr <= cs /\ (forall u, u \in sv => 0 <= u < ctr)
  /\ (forall u, u \in toks => 0 <= u < ctr) /\ tokinv toks.

declare axiom reg_open :
  forall (w : row), mu (dnonce `*` dnoiser) (fun (s : vec * row) => rndc (commit s.`1 s.`2) = w) <= pw.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

(* Structural facts survive a refused call *)
lemma lzs_mono (cs ctr : int) sv toks : lzs (cs - 1) ctr sv toks => lzs cs ctr sv toks.
proof. by rewrite /lzs => -[#] *; smt(). qed.

(* Structural facts survive a new token *)
lemma lzs_new (cs ctr : int) sv toks (tok : token) (s : vec * row) (b : bool) :
  lzs (cs - 1) ctr sv toks => size tok.`tk_T <= tthr =>
  lzs cs (ctr + 1) (if b then sv.[ctr <- s] else sv) toks.[ctr <- tok].
proof.
rewrite /lzs => -[#] h2 h3 h4 h5 h6 ht.
split; first smt().
split; first by move=> u; case: b => _; rewrite ?mem_set; smt().
split; first by move=> u; rewrite mem_set; smt().
rewrite /tokinv => u; rewrite mem_set get_setE; case: (u = ctr) => [-> /= | hne /= hu].
+ exact ht.
by move: h6; rewrite /tokinv => /(_ u hu).
qed.

(* Structural facts survive an update of a known token *)
lemma lzs_upd (cs ctr : int) sv toks (u : int) (tok : token) (s : vec * row) (b : bool) :
  lzs (cs - 1) ctr sv toks => u \in toks => size tok.`tk_T <= tthr =>
  lzs cs ctr (if b then sv.[u <- s] else sv) toks.[u <- tok].
proof.
rewrite /lzs => -[#] h2 h3 h4 h5 h6 hu ht.
split; first smt().
split; first by move=> u'; case: b => _; rewrite ?mem_set; smt().
split; first by move=> u'; rewrite mem_set; smt().
rewrite /tokinv => u'; rewrite mem_set get_setE; case: (u' = u) => [-> /= | hne /= hu'].
+ exact ht.
by move: h6; rewrite /tokinv => /(_ u' hu').
qed.

(* Structural facts survive a new token without a secret *)
lemma lzs_new0 (cs ctr : int) sv toks (tok : token) :
  lzs (cs - 1) ctr sv toks => size tok.`tk_T <= tthr => lzs cs (ctr + 1) sv toks.[ctr <- tok].
proof. by move=> h ht; have /= := lzs_new cs ctr sv toks tok witness false h ht. qed.

(* Structural facts survive a new token with its secret *)
lemma lzs_new1 (cs ctr : int) sv toks (tok : token) (s : vec * row) :
  lzs (cs - 1) ctr sv toks => size tok.`tk_T <= tthr =>
  lzs cs (ctr + 1) sv.[ctr <- s] toks.[ctr <- tok].
proof. by move=> h ht; have /= := lzs_new cs ctr sv toks tok s true h ht. qed.

(* Structural facts survive an update without a secret *)
lemma lzs_upd0 (cs ctr : int) sv toks (u : int) (tok : token) :
  lzs (cs - 1) ctr sv toks => u \in toks => size tok.`tk_T <= tthr =>
  lzs cs ctr sv toks.[u <- tok].
proof. by move=> h hu ht; have /= := lzs_upd cs ctr sv toks u tok witness false h hu ht. qed.

(* Structural facts survive an update with a secret *)
lemma lzs_upd1 (cs ctr : int) sv toks (u : int) (tok : token) (s : vec * row) :
  lzs (cs - 1) ctr sv toks => u \in toks => size tok.`tk_T <= tthr =>
  lzs cs ctr sv.[u <- s] toks.[u <- tok].
proof. by move=> h hu ht; have /= := lzs_upd cs ctr sv toks u tok s true h hu ht. qed.

(* Tokens have bounded committees *)
lemma lzs_size (cs ctr : int) sv toks (u : int) :
  lzs cs ctr sv toks => u \in toks => size (oget toks.[u]).`tk_T <= tthr.
proof. by rewrite /lzs => -[#] _ _ _ _ h6 hu; move: h6; rewrite /tokinv => /(_ u hu). qed.

(* Lazy first rounds keep the counting invariant *)
lemma o1_lz (n : int) :
  hoare [SOL(H0H.LC).o1 : H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks ==>
                          H0H.CQ.n <= n /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks].
proof.
proc; sp; if; last by auto => &hr [[_ [hn h]] _]; rewrite hn /=; exact (lzs_mono _ _ _ _ h).
inline *; sp; if.
+ sp; if; auto => /> *.
  - by apply lzs_new0 => //=; smt(thr_range).
  by apply lzs_new0 => //=; smt(thr_range).
sp; if; auto => /> *.
+ by apply lzs_new1 => //=; smt(thr_range).
by apply lzs_new0 => //=; smt(thr_range).
qed.

(* Lazy second rounds keep the counting invariant *)
lemma o2_lz (n : int) :
  hoare [SOL(H0H.LC).o2 : H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks ==>
                          H0H.CQ.n <= n /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks].
proof.
proc; sp; if; last by auto => &hr [[_ [hn h]] _]; rewrite hn /=; exact (lzs_mono _ _ _ _ h).
sp; if; last by auto => &hr [#] _ _ hn h *; rewrite hn /=; exact (lzs_mono _ _ _ _ h).
inline *; sp; if; auto => /> *.
+ by apply lzs_upd1 => //=; smt().
by apply lzs_upd0 => //=; smt().
qed.

(* Commitment checks query the commitment oracle at most once *)
lemma h0any_lz (m : int) :
  hoare [SOL(H0H.LC).h0any : H0H.CQ.n <= m ==> H0H.CQ.n <= m + 1].
proof.
proc; inline *; sp; if; first by auto => /#.
by sp; if; [sp; if; auto => /# | auto => /#].
qed.

(* Lazy third rounds keep the counting invariant *)
lemma o3_lz (n : int) :
  hoare [SOL(H0H.LC).o3 : H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks ==>
                          H0H.CQ.n <= n + tthr /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks].
proof.
proc; seq 1 : (H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks); first by auto.
if; last by auto => &hr [[hn h] _]; split; [smt(thr_range) | exact (lzs_mono _ _ _ _ h)].
seq 1 : (H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks); first by auto.
if; last by auto => &hr [[hn [h _]] _]; split; [smt(thr_range) | exact (lzs_mono _ _ _ _ h)].
seq 1 : (H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T); first by auto => /> /#.
if; last by auto => &hr [[hn [h _]] _]; split; [smt(thr_range) | exact (lzs_mono _ _ _ _ h)].
seq 2 : (H0H.CQ.n <= n /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T /\ k = 0); first by auto.
seq 1 : (H0H.CQ.n <= n + tthr /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T).
+ while (H0H.CQ.n <= n + k /\ 0 <= k <= size T /\ size T <= tthr
         /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T).
  + by wp; ecall (h0any_lz H0H.CQ.n); auto => /#.
  auto => /> &hr hn h hu; split; first by rewrite size_ge0 /=; exact (lzs_size _ _ _ _ _ h hu).
  smt().
if; last by auto => &hr [[hn [h _]] _]; split; [smt(thr_range) | exact (lzs_mono _ _ _ _ h)].
seq 6 : (H0H.CQ.n <= n + tthr /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T).
+ by while (H0H.CQ.n <= n + tthr /\ lzs (Cnt.cs - 1) S.ctr H0H.LC.sv S.toks
            /\ tok = oget S.toks.[u] /\ u \in S.toks /\ T = tok.`tk_T); auto.
sp; if.
+ auto => /> &hr hn h hu *.
  by apply lzs_upd0 => //; rewrite /erase /=; exact (lzs_size _ _ _ _ _ h hu).
if.
+ auto => /> &hr hn h hu *.
  by apply lzs_upd0 => //; rewrite /erase /=; exact (lzs_size _ _ _ _ _ h hu).
auto => /> &hr hn h hu *.
by apply lzs_upd0 => //; rewrite /erase /=; exact (lzs_size _ _ _ _ _ h hu).
qed.

(* Structural facts bound the number of secrets *)
lemma lzs_card (cs ctr : int) sv toks : lzs cs ctr sv toks => card (fdom sv) <= cs.
proof. by rewrite /lzs => -[#] h0 h1 h2 *; have := card_sv sv ctr h0 h2; smt(). qed.

(* Commitment queries and secrets stay within the budget *)
lemma bl_cnt :
  hoare [BL(A, H0H.LC).main : H0H.CQ.n = 0 /\ H0H.LC.sv = empty ==>
         H0H.CQ.n <= qh0 + tthr * qsig /\ card (fdom H0H.LC.sv) <= qsig].
proof.
proc; inline GameL(A, H0H.LC).run; wp.
conseq (_ : _ ==> H0H.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks
                  /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig).
+ move=> &hr _ n0 c0 cs ctr sv toks [#] h1 h2 h3 h4.
  have := lzs_card _ _ _ _ h2.
  have : tthr * cs <= tthr * qsig by apply StdOrder.IntOrder.ler_wpmul2l; smt(thr_range).
  smt().
call (_ : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ H0H.CQ.n = 0
          /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks ==>
          H0H.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks
          /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig).
+ conseq (A_bnd (HOL(H0H.LC)) (SOL(H0H.LC)))
         (_ : H0H.CQ.n = 0 /\ Cnt.c0 = 0 /\ Cnt.cs = 0 /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks ==>
              H0H.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks) => //.
  proc (H0H.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ lzs Cnt.cs S.ctr H0H.LC.sv S.toks) => //.
  + proc; sp; ecall (o1_lz H0H.CQ.n); auto => /#.
  + proc; sp; ecall (o2_lz H0H.CQ.n); auto => /#.
  + proc; sp; ecall (o3_lz H0H.CQ.n); auto => /#.
  + proc; inline *; sp; if; first by auto => /#.
    by sp; if; [sp; if; auto => /# | auto => /#].
  + by proc; inline *; auto.
  + by proc; inline *; auto.
auto; call (_ : true); inline *; auto => />.
by rewrite /lzs; smt(mem_empty).
qed.

(* Lazily sampled commitments cost the hidden point bound *)
lemma lazy_hop &m :
  `|Pr[H0H.LCG(BL(A)).main(true) @ &m : res] - Pr[H0H.LCG(BL(A)).main(false) @ &m : res]|
  <= 2%r * (qh0 + tthr * qsig)%r * sqrt (qsig%r * pw) + (qsig * qsig)%r * pw.
proof.
have hpw : 0%r <= pw.
+ have := reg_open witness; smt(mu_bounded).
apply (H0H.o2h_lazy (BL(A)) &m (qh0 + tthr * qsig) qsig pw _ _ hpw _ bl_cnt).
+ smt(ge0_qh0 ge0_qsig thr_range).
+ exact ge0_qsig.
exact reg_open.
qed.

(* The game with lazy commitments is close to the previous game *)
lemma g1t_lazy &m :
  Pr[G1t(A).main() @ &m : res]
  <= Pr[H0H.LCG(BL(A)).main(true) @ &m : res]
     + 2%r * (qh0 + tthr * qsig)%r * sqrt (qsig%r * pw) + (qsig * qsig)%r * pw.
proof. by have := lazy_hop &m; rewrite -g1t_lazy0; smt(). qed.

end section LazyHop.
