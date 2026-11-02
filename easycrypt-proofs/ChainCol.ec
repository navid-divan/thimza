require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op findcol ['a 'b] (l : ('a * 'b) list) : 'a * 'a =
  choiceb (fun (p : 'a * 'a) => exists y, (p.`1, y) \in l /\ (p.`2, y) \in l /\ p.`1 <> p.`2)
          (witness, witness).

(* A logged collision is found *)
lemma findcolP ['a 'b] (l : ('a * 'b) list) (f : 'a -> 'b) :
  (forall x y, (x, y) \in l => y = f x) =>
  hascol l => (findcol l).`1 <> (findcol l).`2 /\ f (findcol l).`1 = f (findcol l).`2.
proof.
move=> hl [x x' y] [#] hx hx' hne.
have := choicebP (fun (p : 'a * 'a) => exists y, (p.`1, y) \in l /\ (p.`2, y) \in l /\ p.`1 <> p.`2)
          (witness, witness) _.
+ by exists (x, x') => /=; exists y.
rewrite -/(findcol l) => -[y'] [#] h1 h2 h3.
by split => //; rewrite -(hl _ _ h1) -(hl _ _ h2).
qed.

module Bc1 (A : Adv) (H : H1O.QRO_i) = {
  proc main() : h1in * h1in = {
    var b;
    MPI.init();
    H0H.QRO.init();
    H0C.QRO.init();
    HCO.QRO.init();
    b <@ GameF(A, MPI, H0H.QRO, H).run();
    return findcol Lg.l1;
  }
}.

module Bc0 (A : Adv) (H : H0H.QRO_i) = {
  proc main() : h0in * h0in = {
    var b;
    MPI.init();
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameF(A, MPI, H, H1O.QRO).run();
    return findcol Lg.l0;
  }
}.

section ColHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO,
                          -H0H.CQ, -H1O.CQ}.

(* Digest logging keeps digests correct *)
lemma h1hon_l1 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).h1hon :
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x].
proof. by proc; inline *; auto => />; smt(). qed.

(* Commitment checks keep digests correct *)
lemma h0any_l1 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).h0any :
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x].
proof. by proc; inline *; auto. qed.

(* Mask values keep digests correct *)
lemma mpi_l1 :
  hoare [MPI.f : forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x ==>
                 forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x].
proof. by proc; sp; if; auto. qed.

(* Third rounds keep digests correct *)
lemma o3_l1 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).o3 :
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x].
proof.
proc.
seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); first by auto.
if => //.
seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); first by auto.
if => //.
seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); first by call h1hon_l1.
if => //.
seq 2 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); first by auto.
seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x).
+ while (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); last by auto.
  by wp; call h0any_l1; auto.
if => //.
seq 5 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); first by auto.
seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x).
+ while (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); last by auto.
  seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x); first by auto.
  if; last by auto.
  if; last by auto.
  by wp; call mpi_l1; auto.
seq 1 : (forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x).
+ if; last by auto.
  by wp; call mpi_l1; auto.
by auto.
qed.

(* Logged digests are oracle values *)
lemma log1_ok :
  hoare [GameF(A, MPI, H0H.QRO, H1O.QRO).run : true ==>
         forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x].
proof.
proc; wp.
call (_ : forall x y, (x, y) \in Lg.l1 => y = H1O.QRO.fh x).
+ by proc; inline *; sp; if; auto.
+ by proc; inline *; auto => />; smt().
+ by proc; call o3_l1; auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
auto => />; call (_ : true) => //; auto => /> /#.
qed.

(* Commitment logging keeps commitments correct *)
lemma h0hon_l0 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).h0hon :
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof. by proc; inline *; auto => />; smt(). qed.

(* Commitment checks keep commitments correct *)
lemma h0any_l0 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).h0any :
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof. by proc; if; [auto | call h0hon_l0; auto]. qed.

(* Digest logging keeps commitments correct *)
lemma h1hon_l0 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).h1hon :
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof. by proc; inline *; auto. qed.

(* Mask values keep commitments correct *)
lemma mpi_l0 :
  hoare [MPI.f : forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x ==>
                 forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof. by proc; sp; if; auto. qed.

(* Third rounds keep commitments correct *)
lemma o3_l0 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).o3 :
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof.
proc.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by auto.
if => //.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by auto.
if => //.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by call h1hon_l0.
if => //.
seq 2 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by auto.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x).
+ while (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); last by auto.
  by wp; call h0any_l0; auto.
if => //.
seq 5 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by auto.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x).
+ while (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); last by auto.
  seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by auto.
  if; last by auto.
  if; last by auto.
  by wp; call mpi_l0; auto.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x).
+ if; last by auto.
  by wp; call mpi_l0; auto.
by auto.
qed.

(* First rounds keep commitments correct *)
lemma o1_l0 :
  hoare [SOF(MPI, H0H.QRO, H1O.QRO).o1 :
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x ==>
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof.
proc.
seq 1 : (forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x); first by auto.
if; last by auto.
by wp; call h0hon_l0; auto.
qed.

(* Logged commitments are oracle values *)
lemma log0_ok :
  hoare [GameF(A, MPI, H0H.QRO, H1O.QRO).run : true ==>
         forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x].
proof.
proc; wp.
call (_ : forall x y, (x, y) \in Lg.l0 => y = H0H.QRO.fh x).
+ by proc; call o1_l0; auto.
+ by proc; inline *; auto.
+ by proc; call o3_l0; auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
auto => />; call (_ : true) => //; auto => /> /#.
qed.

(* Digest collisions yield oracle collisions *)
lemma col1_red &m :
  Pr[G1(A).main() @ &m : hascol Lg.l1] <= Pr[H1O.Col(Bc1(A)).main() @ &m : res].
proof.
byequiv => //; proc; inline H1O.QRO.init Bc1(A, H1O.CQ).main G1(A).main.
seq 5 6 : (={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}).
+ by inline *; swap{2} 1 4; auto.
wp; call (_ : ={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh} ==>
              ={res, Lg.l1, H1O.QRO.fh}
              /\ forall x y, (x, y) \in Lg.l1{1} => y = H1O.QRO.fh{1} x).
+ conseq (_ : ={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh} ==>
              ={res, Lg.l1, H1O.QRO.fh}) log1_ok _ => //.
  by proc; inline *; sim.
auto => /> &2 l h x x' y h1 h2 hne.
by apply (findcolP l H1O.QRO.fh{2} h); exists x x' y.
qed.

(* Commitment collisions yield oracle collisions *)
lemma col0_red &m :
  Pr[G1(A).main() @ &m : hascol Lg.l0] <= Pr[H0H.Col(Bc0(A)).main() @ &m : res].
proof.
byequiv => //; proc; inline H0H.QRO.init Bc0(A, H0H.CQ).main G1(A).main.
seq 5 6 : (={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}).
+ by inline *; swap{2} 1 2; auto.
wp; call (_ : ={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh} ==>
              ={res, Lg.l0, H0H.QRO.fh}
              /\ forall x y, (x, y) \in Lg.l0{1} => y = H0H.QRO.fh{1} x).
+ conseq (_ : ={glob A, MPI.m, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh} ==>
              ={res, Lg.l0, H0H.QRO.fh}) log0_ok _ => //.
  by proc; inline *; sim.
auto => /> &2 l h x x' y h1 h2 hne.
by apply (findcolP l H0H.QRO.fh{2} h); exists x x' y.
qed.

end section ColHop.

section ColBound.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO,
                          -H0H.CQ, -H1O.CQ}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

(* Second rounds query the digest oracle once *)
lemma o2_cnt1 (n : int) :
  hoare [SOF(MPI, H0H.QRO, H1O.CQ).o2 : H1O.CQ.n <= n ==> H1O.CQ.n <= n + 1].
proof.
proc; seq 1 : (H1O.CQ.n <= n); first by auto.
if; last by auto => /#.
seq 1 : (H1O.CQ.n <= n); first by auto.
if; last by auto => /#.
by inline *; auto => /#.
qed.

(* Third rounds query the digest oracle once *)
lemma o3_cnt1 (n : int) :
  hoare [SOF(MPI, H0H.QRO, H1O.CQ).o3 : H1O.CQ.n <= n ==> H1O.CQ.n <= n + 1].
proof.
proc; seq 1 : (H1O.CQ.n <= n); first by auto.
if; last by auto => /#.
seq 1 : (H1O.CQ.n <= n); first by auto.
if; last by auto => /#.
seq 1 : (H1O.CQ.n <= n + 1); first by inline *; auto => /#.
if; last by auto.
seq 2 : (H1O.CQ.n <= n + 1); first by auto.
seq 1 : (H1O.CQ.n <= n + 1).
+ while (H1O.CQ.n <= n + 1); last by auto.
  by inline *; auto.
if; last by auto.
seq 5 : (H1O.CQ.n <= n + 1); first by auto.
seq 1 : (H1O.CQ.n <= n + 1).
+ while (H1O.CQ.n <= n + 1); last by auto.
  seq 1 : (H1O.CQ.n <= n + 1); first by auto.
  if; last by auto.
  if; last by auto.
  by inline *; wp; sp; if; auto.
seq 1 : (H1O.CQ.n <= n + 1).
+ if; last by auto.
  by inline *; wp; sp; if; auto.
by auto.
qed.

(* Digest queries stay within the budget *)
lemma bc1_cnt :
  hoare [Bc1(A, H1O.CQ).main : H1O.CQ.n = 0 ==> H1O.CQ.n <= qh1 + 2 * qsig].
proof.
proc; inline GameF(A, MPI, H0H.QRO, H1O.CQ).run; wp.
conseq (_ : _ ==> H1O.CQ.n <= Cnt.c1 + 2 * Cnt.cs /\ Cnt.c1 <= qh1 /\ Cnt.cs <= qsig) => //.
+ smt().
call (_ : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ H1O.CQ.n = 0 ==>
          H1O.CQ.n <= Cnt.c1 + 2 * Cnt.cs /\ Cnt.c1 <= qh1 /\ Cnt.cs <= qsig).
+ conseq (A_bnd (HOF(H0H.QRO, H1O.CQ)) (SOF(MPI, H0H.QRO, H1O.CQ)))
         (_ : H1O.CQ.n = 0 /\ Cnt.c1 = 0 /\ Cnt.cs = 0 ==> H1O.CQ.n <= Cnt.c1 + 2 * Cnt.cs) => //.
  proc (H1O.CQ.n <= Cnt.c1 + 2 * Cnt.cs) => //.
  + by proc; inline *; sp; if; auto => /#.
  + proc; sp; ecall (o2_cnt1 H1O.CQ.n); auto => /#.
  + proc; sp; ecall (o3_cnt1 H1O.CQ.n); auto => /#.
  + by proc; inline *; auto.
  + by proc; inline *; auto => /#.
  + by proc; inline *; auto.
auto; call (_ : true); inline *; auto.
qed.

(* Digest collisions are improbable *)
lemma col1_bound &m :
  Pr[G1(A).main() @ &m : hascol Lg.l1] <= 27%r * (qh1 + 2 * qsig + 2)%r ^ 3 * p_max dview.
proof.
have h1 := col1_red A &m.
have h2 := H1O.pr_col (Bc1(A)) &m (qh1 + 2 * qsig) bc1_cnt.
smt().
qed.

op tokinv (m : (int, token) fmap) : bool =
  forall u, u \in m => size (oget m.[u]).`tk_T <= tthr.

(* Updates within the size bound keep the invariant *)
lemma tokinv_set (m : (int, token) fmap) (k : int) (tok : token) :
  tokinv m => size tok.`tk_T <= tthr => tokinv m.[k <- tok].
proof.
move=> hm ht u; rewrite mem_set get_setE.
by case: (u = k) => /= [_ | hne hu]; [exact ht | exact (hm u hu)].
qed.

(* Checks query the commitment oracle at most once *)
lemma h0any_cnt0 (n : int) :
  hoare [SOF(MPI, H0H.CQ, H1O.QRO).h0any : H0H.CQ.n <= n ==> H0H.CQ.n <= n + 1].
proof. by proc; inline *; auto => /#. qed.

(* First rounds query the commitment oracle once *)
lemma o1_cnt0 (n : int) :
  hoare [SOF(MPI, H0H.CQ, H1O.QRO).o1 :
         H0H.CQ.n <= n /\ tokinv S.toks ==> H0H.CQ.n <= n + 1 /\ tokinv S.toks].
proof.
proc; seq 1 : (H0H.CQ.n <= n /\ tokinv S.toks); first by auto.
if; last by auto => /#.
inline *; auto => /> &hr hn ht *; split; first by smt().
by apply tokinv_set => //=; smt(thr_range).
qed.

(* Second rounds keep committee sizes *)
lemma o2_cnt0 (n : int) :
  hoare [SOF(MPI, H0H.CQ, H1O.QRO).o2 :
         H0H.CQ.n <= n /\ tokinv S.toks ==> H0H.CQ.n <= n /\ tokinv S.toks].
proof.
proc; seq 1 : (H0H.CQ.n <= n /\ tokinv S.toks); first by auto.
if; last by auto.
seq 1 : (H0H.CQ.n <= n /\ tokinv S.toks); first by auto.
if; last by auto.
inline *; auto => /> &hr hn ht *.
by apply tokinv_set => //=; smt().
qed.

(* Third rounds query the commitment oracle per member *)
lemma o3_cnt0 (n : int) :
  hoare [SOF(MPI, H0H.CQ, H1O.QRO).o3 :
         H0H.CQ.n <= n /\ tokinv S.toks ==> H0H.CQ.n <= n + tthr /\ tokinv S.toks].
proof.
proc; seq 1 : (H0H.CQ.n <= n /\ tokinv S.toks); first by auto.
if; last by auto; smt(thr_range).
seq 1 : (H0H.CQ.n <= n /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks).
+ by auto.
if; last by auto; smt(thr_range).
seq 1 : (H0H.CQ.n <= n /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T).
+ by inline *; auto.
if; last by auto; smt(thr_range).
seq 2 : (H0H.CQ.n <= n /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T /\ k = 0).
+ by auto.
seq 1 : (H0H.CQ.n <= n + tthr /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T).
+ while (H0H.CQ.n <= n + k /\ 0 <= k <= size T /\ size T <= tthr /\ tokinv S.toks
         /\ tok = oget S.toks.[u] /\ u \in S.toks /\ T = tok.`tk_T).
  + wp; ecall (h0any_cnt0 H0H.CQ.n); auto; smt().
  auto => /> &hr hn ht hu; split; first by split; [exact size_ge0 | exact (ht _ hu)].
  smt().
if; last by auto.
seq 5 : (H0H.CQ.n <= n + tthr /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T).
+ by auto.
seq 1 : (H0H.CQ.n <= n + tthr /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T).
+ while (H0H.CQ.n <= n + tthr /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T); last by auto.
  seq 1 : (H0H.CQ.n <= n + tthr /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
           /\ T = tok.`tk_T); first by auto.
  if; last by auto.
  if; last by auto.
  by inline *; wp; sp; if; auto.
seq 1 : (H0H.CQ.n <= n + tthr /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks
         /\ T = tok.`tk_T).
+ if; last by auto.
  by inline *; wp; sp; if; auto.
auto => /> &hr hn ht hu *.
by apply tokinv_set => //; rewrite /erase /=; apply ht.
qed.

(* Commitment queries stay within the budget *)
lemma bc0_cnt :
  hoare [Bc0(A, H0H.CQ).main : H0H.CQ.n = 0 ==> H0H.CQ.n <= qh0 + (tthr + 1) * qsig].
proof.
proc; inline GameF(A, MPI, H0H.CQ, H1O.QRO).run; wp.
conseq (_ : _ ==> H0H.CQ.n <= Cnt.c0 + (tthr + 1) * Cnt.cs /\ Cnt.c0 <= qh0
                  /\ Cnt.cs <= qsig) => //.
+ move=> &hr _ c0 cs n [#] h1 h2 h3.
  have : (tthr + 1) * cs <= (tthr + 1) * qsig.
  - by apply StdOrder.IntOrder.ler_wpmul2l; smt(thr_range).
  smt().
call (_ : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ H0H.CQ.n = 0
          /\ tokinv S.toks ==>
          H0H.CQ.n <= Cnt.c0 + (tthr + 1) * Cnt.cs /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig).
+ conseq (A_bnd (HOF(H0H.CQ, H1O.QRO)) (SOF(MPI, H0H.CQ, H1O.QRO)))
         (_ : H0H.CQ.n = 0 /\ Cnt.c0 = 0 /\ Cnt.cs = 0 /\ tokinv S.toks ==>
              H0H.CQ.n <= Cnt.c0 + (tthr + 1) * Cnt.cs) => //.
  proc (H0H.CQ.n <= Cnt.c0 + (tthr + 1) * Cnt.cs /\ tokinv S.toks) => //.
  + proc; sp; ecall (o1_cnt0 H0H.CQ.n); auto => /#.
  + proc; sp; ecall (o2_cnt0 H0H.CQ.n); auto => /#.
  + proc; sp; ecall (o3_cnt0 H0H.CQ.n); auto => /#.
  + by proc; inline *; auto => /#.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
auto; call (_ : true); inline *; auto => />; smt(mem_empty).
qed.

(* Commitment collisions are improbable *)
lemma col0_bound &m :
  Pr[G1(A).main() @ &m : hascol Lg.l0] <= 27%r * (qh0 + (tthr + 1) * qsig + 2)%r ^ 3 * p_max dcmt.
proof.
have h1 := col0_red A &m.
have h2 := H0H.pr_col (Bc0(A)) &m (qh0 + (tthr + 1) * qsig) bc0_cnt.
smt().
qed.

end section ColBound.
