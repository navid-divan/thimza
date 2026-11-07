require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop FelTactic.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.
import Bigreal.BRA.

(* ---------- the lazy game with flags, written as one procedure ----------

   GAf runs the code of H0H.LCG(BA(A)).main(true) in one procedure, so that the failure event
   lemma applies to its adversary calls.  The second flag (a fresh first message equal to an
   existing one) is bounded by a birthday argument on the lazily sampled first messages. *)

module GAf (A : Adv) = {
  proc main() : bool = {
    var mu, sg, ok, sks, sds;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    S.cs <@ A(CntH(HOL(H0H.LC)), CntO(SOA(H0H.LC))).corrupt();
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
    Bd.b1 <- false;
    Bd.b2 <- false;
    Bd.b3 <- false;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOL(H0H.LC)), CntO(SOA(H0H.LC))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

(* The signing oracles with the first message of a new token sampled directly (the lazy
   commitment oracle samples a fresh value for a new token index) *)
module SOA2 : SOr = {
  proc h0any = SOA(H0H.LC).h0any

  proc o1(i : int, mu : msg) : (int * cmt) option = {
    var c, out;
    out <- None;
    if (1 <= i <= nmax /\ !(i \in S.cs)) {
      c <$ dcmt;
      H0H.LC.fv.[(S.ctr, ((S.t, mu), toidx i))] <- c;
      Bd.b2 <- Bd.b2 \/ dupc S.toks c \/ seenc S.lr c;
      S.toks.[S.ctr] <- {| tk_i = i; tk_msg = mu; tk_r = witness; tk_e = witness; tk_wbar = witness;
                           tk_cmt = c; tk_phase = 1; tk_T = []; tk_dig = witness |};
      out <- Some (S.ctr, c);
      S.ctr <- S.ctr + 1;
    }
    return out;
  }

  proc o2 = SOA(H0H.LC).o2
  proc o3 = SOA(H0H.LC).o3
}.

module GAg (A : Adv) = {
  proc main() : bool = {
    var mu, sg, ok, sks, sds;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    S.cs <@ A(CntH(HOL(H0H.LC)), CntO(SOA2)).corrupt();
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
    Bd.b1 <- false;
    Bd.b2 <- false;
    Bd.b3 <- false;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOL(H0H.LC)), CntO(SOA2)).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

(* The keys of the lazy first messages and the revealed nonces belong to issued tokens *)
op lzk (fv : (int * h0key, cmt) fmap) (sv : (int, vec * row) fmap) (toks : (int, token) fmap)
       (ctr : int) (lft : bool) : bool =
  (forall u k, (u, k) \in fv => u < ctr) /\ (forall u, u \in sv => u < ctr)
  /\ (forall u, u \in toks => u < ctr) /\ lft.

(* The head of a nonempty filtered list satisfies the filter *)
lemma head_filter (P : 'a -> bool) (l : 'a list) (x0 : 'a) :
  List.filter P l <> [] => P (head x0 (List.filter P l)).
proof. by elim: l => //= x l ih; case: (P x). qed.

(* A fresh value hits a list of values with probability at most their number times p_max *)
lemma flatten_size (f : 'a -> 'b list) (l : 'a list) (k : int) :
  (forall x, x \in l => size (f x) <= k) => size (flatten (map f l)) <= k * size l.
proof.
elim: l => [| x l ih] h /=; first by rewrite flatten_nil.
rewrite flatten_cons size_cat.
have := h x _; first by left.
have := ih _; first by move=> y hy; apply h; right.
smt().
qed.

(* The lazy commitment oracle keeps the keys below the token counter *)
lemma lch_lzk :
  hoare [H0H.LC.h : lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft ==>
                    lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft].
proof.
proc; sp; if; last by auto.
inline *; sp; if; last by auto.
auto => /> &h hf hs ht hl hus hnf y0 _ u0 k0.
rewrite mem_set => -[h | heq]; first by apply (hf u0 k0 h).
have [hm _] := head_filter _ _ 0 hus.
by move: heq => [-> _]; apply hs.
qed.

lemma h0_lzk :
  hoare [CntH(HOL(H0H.LC)).h0 : lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft ==>
                                lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft].
proof. by proc; inline HOL(H0H.LC).h0; sp; if; [auto | wp; call lch_lzk; auto]. qed.

lemma o2_lzk :
  hoare [CntO(SOA(H0H.LC)).o2 : lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft ==>
                                lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft].
proof.
proc; inline SOA(H0H.LC).o2; sp; if; last by auto.
sp; if; last by auto.
by inline *; sp; if; auto => />; smt(mem_set).
qed.

lemma o3_lzk :
  hoare [CntO(SOA(H0H.LC)).o3 : lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft ==> lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft].
proof.
proc; inline SOA(H0H.LC).o3; sp; if; last by auto.
sp; if; last by auto.
sp; if; last by auto.
seq 3 : (lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft /\ u0 \in S.toks); first by auto.
seq 1 : (lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft /\ u0 \in S.toks).
+ while (lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft /\ u0 \in S.toks); last by auto.
  wp; call (_ : lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft); last by auto.
  by sp; if; [auto | wp; call lch_lzk; auto].
if; last by auto.
seq 6 : (lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft /\ u0 \in S.toks); first by while (lzk H0H.LC.fv H0H.LC.sv S.toks S.ctr H0H.LC.lft /\ u0 \in S.toks); auto.
by sp; if; [auto => />; smt(mem_set) | if; auto => />; smt(mem_set)].
qed.

(* The direct sampling of a new first message does not change the game *)
equiv o1_gag :
  CntO(SOA(H0H.LC)).o1 ~ CntO(SOA2).o1 :
  ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1}.
proof.
proc; inline SOA(H0H.LC).o1 SOA2.o1; sp; if; [by auto | | by auto].
inline H0H.LC.commit; sp; rcondt{1} 1; first by auto => />.
inline H0H.LC.gf; sp; rcondt{1} 1.
+ by auto => />; smt().
by auto => />; smt(mem_set get_set_sameE).
qed.

equiv o2_gag :
  CntO(SOA(H0H.LC)).o2 ~ CntO(SOA2).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1}.
proof.
conseq (_ : ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO}) o2_lzk _ => //.
by proc; inline *; sim.
qed.

equiv o3_gag :
  CntO(SOA(H0H.LC)).o3 ~ CntO(SOA2).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1}.
proof.
conseq (_ : ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO}) o3_lzk _ => //.
by proc; inline *; sim.
qed.

equiv h0_gag :
  CntH(HOL(H0H.LC)).h0 ~ CntH(HOL(H0H.LC)).h0 :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1}.
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO}) h0_lzk _ => //.
by proc; inline *; sim.
qed.

section GAflat.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ}.

(* The flattened game is the lazy game with flags *)
lemma ga_gaf &m (E : bool -> (glob A) -> bool -> bool -> bool -> int -> int -> int -> int -> bool) :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : E res (glob A) Bd.b1 Bd.b2 Bd.b3 Cnt.c0 Cnt.c1 Cnt.cc Cnt.cs]
  = Pr[GAf(A).main() @ &m : E res (glob A) Bd.b1 Bd.b2 Bd.b3 Cnt.c0 Cnt.c1 Cnt.cc Cnt.cs].
proof.
byequiv => //; proc.
inline BA(A, H0H.LC).main GameA(A, H0H.LC).run.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt,
            glob Fz, glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO,
            glob HCO.QRO}).
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
by inline *; auto; call (_ : true); auto.
qed.

(* The direct sampling of new first messages does not change the flattened game *)
lemma gaf_gag &m (E : bool -> (glob A) -> bool -> bool -> bool -> int -> int -> int -> int -> bool) :
  Pr[GAf(A).main() @ &m : E res (glob A) Bd.b1 Bd.b2 Bd.b3 Cnt.c0 Cnt.c1 Cnt.cc Cnt.cs]
  = Pr[GAg(A).main() @ &m : E res (glob A) Bd.b1 Bd.b2 Bd.b3 Cnt.c0 Cnt.c1 Cnt.cc Cnt.cs].
proof.
byequiv => //; proc.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO, glob HCO.QRO} /\ lzk H0H.LC.fv{1} H0H.LC.sv{1} S.toks{1} S.ctr{1} H0H.LC.lft{1}).
+ exact o1_gag.
+ exact o2_gag.
+ exact o3_gag.
+ exact h0_gag.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
by inline *; auto; call (_ : true); auto => />; smt(mem_empty).
qed.

end section GAflat.
