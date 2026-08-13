require import AllCore Int List Distr.
require import Params BigOps PolyList.
import Rq.ComRingDflInv.

(* Removal under uniqueness excludes the removed element *)
lemma rem_mem_neq (x y : 'a) (s : 'a list) : uniq s => y \in rem x s => y <> x.
proof. by move=> hu; rewrite (rem_filter x s hu) mem_filter /predC1 => -[]. qed.

(* The monic product of linear factors over a node list *)
op nodepoly (ns : rq list) : poly =
  with ns = "[]"     => [oner]
  with ns = (::) a l => linmul a (nodepoly l).

(* The node polynomial is never the empty list *)
lemma nodepoly_nonnil (ns : rq list) : nodepoly ns <> [].
proof.
elim ns => [| a l ih] //=.
by rewrite /linmul /padd /pshift; smt(size_ge0 size_eq0 size_padd size_pshift).
qed.

(* The node polynomial has one coefficient per node, plus one *)
lemma size_nodepoly (ns : rq list) : size (nodepoly ns) = size ns + 1.
proof.
elim ns => [| a l ih] //=.
by rewrite (size_linmul a (nodepoly l) (nodepoly_nonnil l)) ih; smt().
qed.

(* The node polynomial is the product of its linear factors *)
lemma peval_nodepoly (ns : rq list) (x : rq) :
  peval (nodepoly ns) x = rprod (fun a => x - a) ns.
proof.
elim ns => [| a l ih] /=.
+ by rewrite rprod_nil; smt(mulr0 addr0 add0r).
by rewrite peval_linmul ih rprod_cons.
qed.

(* The node polynomial vanishes at each of its nodes *)
lemma nodepoly_root (ns : rq list) (a : rq) :
  a \in ns => peval (nodepoly ns) a = zeror.
proof.
move=> ha; rewrite peval_nodepoly.
by apply (rprod_zero (fun b => a - b) ns a ha); smt(subrr).
qed.

(* The Lagrange denominator of one node against the others *)
op lagden (ns : rq list) (i : rq) : rq = rprod (fun b => i - b) (rem i ns).

(* The Lagrange basis polynomial of one node *)
op lagbasis (ns : rq list) (i : rq) : poly =
  pscale (invr (lagden ns i)) (nodepoly (rem i ns)).

(* A separated node list has invertible Lagrange denominators *)
lemma lagden_unit (ns : rq list) (i : rq) :
  sep ns => uniq ns => i \in ns => unit (lagden ns i).
proof.
move=> hsep huniq hi; rewrite /lagden.
apply rprod_unit => b hb => /=.
have hbns : b \in ns by smt(mem_rem).
have hbi : i <> b by smt(rem_mem_neq).
by apply hsep.
qed.

(* The basis polynomial has one coefficient per node *)
lemma size_lagbasis (ns : rq list) (i : rq) :
  i \in ns => size (lagbasis ns i) = size ns.
proof.
move=> hi; rewrite /lagbasis size_pscale size_nodepoly.
by smt(size_rem).
qed.

(* The basis polynomial is one at its own node *)
lemma lagbasis_self (ns : rq list) (i : rq) :
  sep ns => uniq ns => i \in ns => peval (lagbasis ns i) i = oner.
proof.
move=> hsep huniq hi.
have hu := lagden_unit ns i hsep huniq hi.
rewrite /lagbasis peval_scale peval_nodepoly.
have -> : rprod (fun a => i - a) (rem i ns) = lagden ns i by rewrite /lagden.
smt(Rq.ComRingDflInv.mulVr).
qed.

(* The basis polynomial vanishes at every other node *)
lemma lagbasis_other (ns : rq list) (i k : rq) :
  uniq ns => i \in ns => k \in ns => k <> i =>
  peval (lagbasis ns i) k = zeror.
proof.
move=> huniq hi hk hki.
rewrite /lagbasis peval_scale.
have hkrem : k \in rem i ns by rewrite (mem_rem_neq i ns k _) 1:/#.
rewrite (nodepoly_root (rem i ns) k hkrem). smt(mulr0).
qed.

(* The reconstruction coefficient of one node *)
op lagcoef (ns : rq list) (i : rq) : rq = peval (lagbasis ns i) zeror.

(* The interpolant of a value family over the nodes *)
(* The Lagrange identities that define a reconstruction family *)
lemma lagrange_identity (ns : rq list) (f : poly) :
  sep ns => uniq ns => size f <= size ns =>
  rmap (fun i => lagcoef ns i * peval f i) ns = peval f zeror.
proof.
move=> hsep huniq hsz.
pose P := padd (pscale (-oner) f)
               (foldr (fun i acc => padd (pscale (peval f i) (lagbasis ns i)) acc)
                      [] ns).
have hPeval : forall x, peval P x
            = rmap (fun i => peval f i * peval (lagbasis ns i) x) ns - peval f x.
+ move=> x; rewrite /P peval_add peval_scale.
  have hfold : forall (L : rq list),
      peval (foldr (fun i acc => padd (pscale (peval f i) (lagbasis ns i)) acc) [] L) x
      = rmap (fun i => peval f i * peval (lagbasis ns i) x) L.
  - elim => [| a L ihL] /=; first by rewrite rmap_nil.
    by rewrite peval_add peval_scale ihL rmap_cons.
  by rewrite hfold; smt(mulNr mul1r addrC).
have hPsize : size P <= size ns.
+ rewrite /P size_padd size_pscale.
  have hfoldsz : forall (L : rq list),
      (forall i, i \in L => i \in ns) =>
      size (foldr (fun i acc => padd (pscale (peval f i) (lagbasis ns i)) acc) [] L)
      <= size ns.
  - elim => [| a L ihL] h /=; first by smt(size_ge0).
    rewrite size_padd size_pscale (size_lagbasis ns a).
    * by apply h; rewrite mem_head.
    by have := ihL _; smt(in_cons).
  by have := hfoldsz ns _; smt().
have hProot : forall k, k \in ns => peval P k = zeror.
+ move=> k hk; rewrite hPeval.
  have -> : rmap (fun i => peval f i * peval (lagbasis ns i) k) ns
          = rmap (fun i => if i = k then peval f k else zeror) ns.
  - apply rmap_eq => i hi /=.
    case: (i = k) => hik.
    * rewrite ?hik (lagbasis_self ns k hsep huniq hk). smt(mulr1).
    rewrite (lagbasis_other ns i k huniq hi hk _) 1:/#. smt(mulr0).
  have -> : rmap (fun i => if i = k then peval f k else zeror) ns = peval f k.
  - have := rmap_rem (fun i => if i = k then peval f k else zeror) k ns hk.
    move=> /= ->.
    have -> : rmap (fun i => if i = k then peval f k else zeror) (rem k ns) = zeror.
    * rewrite (rmap_eq (fun i => if i = k then peval f k else zeror)
                        (fun (_ : rq) => zeror) (rem k ns) _).
      - move=> i hi /=; have hik2 : i <> k by smt(rem_mem_neq).
        by rewrite hik2.
      exact rmap0.
    by smt(addr0).
  by smt(subrr).
have hPzero := peval_many_roots P ns hsep huniq hPsize hProot zeror.
move: hPzero; rewrite hPeval => hz.
have -> : rmap (fun i => lagcoef ns i * peval f i) ns
        = rmap (fun i => peval f i * peval (lagbasis ns i) zeror) ns.
+ by apply rmap_eq => i _ /=; rewrite /lagcoef; smt(mulrC).
by smt(subr_eq0 subrr addrC add0r).
qed.

(* The reconstruction coefficients sum to the ring unit *)
lemma lagcoef_sum_one (ns : rq list) :
  sep ns => uniq ns => 0 < size ns =>
  rmap (fun i => lagcoef ns i) ns = oner.
proof.
move=> hsep huniq hsz.
have hone : forall (x : rq), peval [oner] x = oner.
+ by move=> x /=; smt(mulr0 addr0).
have h := lagrange_identity ns [oner] hsep huniq _; first by smt(size_ge0).
have heq : rmap (fun i => lagcoef ns i) ns
         = rmap (fun i => lagcoef ns i * peval [oner] i) ns.
+ apply rmap_eq => i _ /=.
  have hi := hone i.
  by smt(mulr1).
rewrite heq h.
by have := hone zeror.
qed.

(* The reconstruction coefficients annihilate the higher powers *)
lemma lagcoef_annihilates (ns : rq list) (f : poly) :
  sep ns => uniq ns => size f <= size ns => peval f zeror = zeror =>
  rmap (fun i => lagcoef ns i * peval f i) ns = zeror.
proof.
move=> hsep huniq hsz h0.
by rewrite (lagrange_identity ns f hsep huniq hsz) h0.
qed.

(* The powers of a node, as a polynomial of that degree *)
op monomial (u : int) : poly = nseq u zeror ++ [oner].

(* A monomial has one coefficient per degree, plus one *)
lemma size_monomial (u : int) : 0 <= u => size (monomial u) = u + 1.
proof. by move=> hu; rewrite /monomial size_cat size_nseq /=; smt(). qed.

(* A monomial evaluates to the corresponding power *)
lemma peval_monomial (u : int) (x : rq) :
  0 <= u => peval (monomial u) x = exp x u.
proof.
elim/natind: u => [n hn hu | n hn ih hu].
+ have -> : n = 0 by smt().
  by rewrite /monomial nseq0 /=; smt(expr0 mulr0 addr0 add0r).
rewrite /monomial nseqS // cat_cons peval_cons.
have -> : peval (nseq n zeror ++ [oner]) x = exp x n by rewrite -/(monomial n) ih; smt().
by rewrite exprS //; smt(add0r mulrC).
qed.

(* A positive monomial vanishes at the ring zero *)
lemma peval_monomial_zero (u : int) : 0 < u => peval (monomial u) zeror = zeror.
proof. by move=> hu; rewrite peval_monomial 1:/#; smt(expr0z). qed.

(* Reconstruction coefficients sum to one over the committee *)
lemma lagcoef_id0 (ns : rq list) :
  sep ns => uniq ns => 0 < size ns =>
  rmap (fun i => lagcoef ns i) ns = oner.
proof. exact lagcoef_sum_one. qed.

(* Reconstruction coefficients kill every positive power *)
lemma lagcoef_idu (ns : rq list) (u : int) :
  sep ns => uniq ns => 0 < u => u < size ns =>
  rmap (fun i => lagcoef ns i * exp i u) ns = zeror.
proof.
move=> hsep huniq hu husz.
have hsz : size (monomial u) <= size ns by rewrite size_monomial 1:/#; smt().
have h := lagcoef_annihilates ns (monomial u) hsep huniq hsz _.
+ exact (peval_monomial_zero u hu).
rewrite -h; apply rmap_eq => i _ /=.
by rewrite (peval_monomial u i _) 1:/#.
qed.
