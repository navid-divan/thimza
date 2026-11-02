require import AllCore Int List Distr Finite.
require import Params Types.

(* Product enumerations count each pair once *)
lemma enum_pair ['a 'b] (la : 'a list) (lb : 'b list) :
  (forall x, count (pred1 x) la = 1) =>
  (forall y, count (pred1 y) lb = 1) =>
  forall z, count (pred1 z) (allpairs (fun a b => (a, b)) la lb) = 1.
proof.
move=> ha hb z.
have ua : uniq la.
+ apply count_mem_uniq => x; rewrite ha.
  by have -> : x \in la by rewrite -has_pred1 has_count ha.
have ub : uniq lb.
+ apply count_mem_uniq => y; rewrite hb.
  by have -> : y \in lb by rewrite -has_pred1 has_count hb.
have hu : uniq (allpairs (fun a b => (a, b)) la lb).
+ by apply allpairs_uniq => // x1 x2 y1 y2 /= _ _ _ _ [] -> ->.
rewrite count_uniq_mem // allpairsP.
have -> // : exists (p : 'a * 'b), p.`1 \in la /\ p.`2 \in lb /\ z = (p.`1, p.`2).
exists z; split; first by rewrite -has_pred1 has_count ha.
by split; [rewrite -has_pred1 has_count hb | case: z].
qed.

op enum_row : row list = to_seq (support drow).

(* Rows are enumerated once each *)
lemma enum_row_spec : forall (x : row), count (pred1 x) enum_row = 1.
proof.
move=> x; have hfin : is_finite (support drow).
+ by apply uniform_finite; apply funi_uni; exact drow_funi.
rewrite count_uniq_mem 1:uniq_to_seq (mem_to_seq _ _ hfin).
by have := drow_fu x; rewrite /support => ->.
qed.

subtype pidx as PIdx = { i : int | 1 <= i <= nmax }.

realize inhabited.
proof. by exists 1; smt(ge1_nmax). qed.

op toidx (i : int) : pidx = PIdx.insubd i.

op enum_pidx : pidx list = map toidx (range 1 (nmax + 1)).

(* Party indices are enumerated once each *)
lemma enum_pidx_spec : forall (x : pidx), count (pred1 x) enum_pidx = 1.
proof.
move=> x; rewrite count_uniq_mem.
+ have hinj : forall a b, a \in range 1 (nmax + 1) => b \in range 1 (nmax + 1) =>
                toidx a = toidx b => a = b.
  - move=> a b ha hb hab.
    have := congr1 PIdx.val _ _ hab; rewrite /toidx.
    rewrite PIdx.insubdK; first by smt(mem_range).
    by rewrite PIdx.insubdK; smt(mem_range).
  by rewrite (map_inj_in_uniq _ _ hinj) range_uniq.
rewrite b2i_eq1; apply/mapP; exists (PIdx.val x).
rewrite mem_range /toidx PIdx.valKd /=.
by have := PIdx.valP x; smt().
qed.

(* Valid indices survive the conversion *)
lemma toidxK (i : int) : 1 <= i <= nmax => PIdx.val (toidx i) = i.
proof. by move=> hi; rewrite /toidx PIdx.insubdK. qed.
