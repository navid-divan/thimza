require import AllCore Int List Distr.
require import Params.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

op rprod (f : 'a -> rq) (L : 'a list) : rq =
  foldr (fun x acc => Rq.( * ) (f x) acc) Rq.oner L.

(* Empty ring product is the unit *)
lemma rprod_nil (f : 'a -> rq) : rprod f [] = Rq.oner.
proof. by rewrite /rprod. qed.

(* Ring product peels off its head *)
lemma rprod_cons (f : 'a -> rq) (a : 'a) (L : 'a list) :
  rprod f (a :: L) = Rq.( * ) (f a) (rprod f L).
proof. by rewrite /rprod. qed.

(* Pointwise equal families have equal products *)
lemma rprod_eq (f g : 'a -> rq) (L : 'a list) :
  (forall x, x \in L => f x = g x) => rprod f L = rprod g L.
proof.
elim L => [| a L ih] h; first by rewrite !rprod_nil.
rewrite !rprod_cons h 1:mem_head ih // => x hx.
by apply h; rewrite in_cons hx.
qed.

(* A product with a zero factor vanishes *)
lemma rprod_zero (f : 'a -> rq) (L : 'a list) (a : 'a) :
  a \in L => f a = Rq.zeror => rprod f L = Rq.zeror.
proof.
elim L => [| b L ih] //= ha hfa.
rewrite rprod_cons.
case: (b = a) => hb.
+ by rewrite hb hfa Rq.ComRingDflInv.mul0r.
have haL : a \in L by smt().
by rewrite (ih haL hfa) Rq.ComRingDflInv.mulr0.
qed.

(* A product of units is a unit *)
lemma rprod_unit (f : 'a -> rq) (L : 'a list) :
  (forall x, x \in L => Rq.ComRingDflInv.unit (f x)) =>
  Rq.ComRingDflInv.unit (rprod f L).
proof.
elim L => [| a L ih] h.
+ by rewrite rprod_nil; exact Rq.ComRingDflInv.unitr1.
rewrite rprod_cons; apply Rq.ComRingDflInv.unitrM; split.
+ by apply h; rewrite mem_head.
by apply ih => x hx; apply h; rewrite in_cons hx.
qed.

(* Vector sums add over list concatenation *)
lemma vmap_cat (f : 'a -> vec) (L1 L2 : 'a list) :
  vmap f (L1 ++ L2) = vmap f L1 + vmap f L2.
proof.
elim L1 => [| a L1 ih].
+ by rewrite cat0s vmap_nil RqVec.Vector.ZModule.add0r.
rewrite cat_cons !vmap_cons ih.
by rewrite (RqVec.Vector.ZModule.addrA (f a) (vmap f L1) (vmap f L2)).
qed.

(* Ring sums add over list concatenation *)
lemma rmap_cat (f : 'a -> rq) (L1 L2 : 'a list) :
  rmap f (L1 ++ L2) = Rq.( + ) (rmap f L1) (rmap f L2).
proof.
elim L1 => [| a L1 ih].
+ by rewrite cat0s rmap_nil Rq.ComRingDflInv.add0r.
rewrite cat_cons !rmap_cons ih.
by rewrite (Rq.ComRingDflInv.addrA (f a) (rmap f L1) (rmap f L2)).
qed.

(* Ring products multiply over list concatenation *)
lemma rprod_cat (f : 'a -> rq) (L1 L2 : 'a list) :
  rprod f (L1 ++ L2) = Rq.( * ) (rprod f L1) (rprod f L2).
proof.
elim L1 => [| a L1 ih].
+ by rewrite cat0s rprod_nil Rq.ComRingDflInv.mul1r.
rewrite cat_cons !rprod_cons ih.
by rewrite (Rq.ComRingDflInv.mulrA (f a) (rprod f L1) (rprod f L2)).
qed.

(* A member may be pulled to the front of a ring sum *)
lemma rmap_rem (f : 'a -> rq) (a : 'a) (L : 'a list) :
  a \in L => rmap f L = Rq.( + ) (f a) (rmap f (rem a L)).
proof.
elim L => [| b L ih] //= hmem.
case: (b = a) => hb.
+ by rewrite ?hb /= ?rmap_cons.
have haL : a \in L by smt().
rewrite ?hb /= !rmap_cons (ih haL).
by rewrite !Rq.ComRingDflInv.addrA (Rq.ComRingDflInv.addrC (f b) (f a)).
qed.

(* Ring sums are invariant under permutation *)
lemma rmap_perm (f : 'a -> rq) (L1 L2 : 'a list) :
  perm_eq L1 L2 => rmap f L1 = rmap f L2.
proof.
move: L2; elim L1 => [| a L1 ih] L2 hp.
+ have -> //: L2 = [].
  by apply perm_eq_small => //; apply perm_eq_sym.
have ha : a \in L2 by rewrite -(perm_eq_mem _ _ hp) mem_head.
have hp2 : perm_eq L1 (rem a L2).
+ have h1 : perm_eq (a :: L1) (a :: rem a L2).
  - by apply (perm_eq_trans L2) => //; exact (perm_to_rem a L2 ha).
  by move: h1; apply perm_cons.
by rewrite rmap_cons (ih (rem a L2) hp2) -(rmap_rem f a L2 ha).
qed.

(* A scalar factors out of a ring sum *)
lemma rmap_mull (c : rq) (f : 'a -> rq) (L : 'a list) :
  Rq.( * ) c (rmap f L) = rmap (fun x => Rq.( * ) c (f x)) L.
proof.
elim L => [| a L ih]; first by rewrite !rmap_nil Rq.ComRingDflInv.mulr0.
by rewrite !rmap_cons -ih Rq.ComRingDflInv.mulrDr.
qed.

(* Double ring sums may be exchanged *)
lemma rmap_exchange (f : 'a -> 'b -> rq) (L1 : 'a list) (L2 : 'b list) :
  rmap (fun x => rmap (f x) L2) L1 = rmap (fun y => rmap (fun x => f x y) L1) L2.
proof.
elim L1 => [| a L1 ih].
+ rewrite rmap_nil.
  have -> : rmap (fun y => rmap (fun (x : 'a) => f x y) []) L2
          = rmap (fun (_ : 'b) => Rq.zeror) L2.
  - by apply rmap_eq => y _ /=; exact rmap_nil.
  by rewrite rmap0.
rewrite rmap_cons /= ih.
have -> : rmap (fun y => rmap (fun x => f x y) (a :: L1)) L2
        = rmap (fun y => Rq.( + ) (f a y) (rmap (fun x => f x y) L1)) L2.
+ by apply rmap_eq => y _ /=; rewrite rmap_cons.
rewrite rmap_split.
have -> : rmap (fun y => f a y) L2 = rmap (f a) L2 by apply rmap_eq.
done.
qed.

(* A vector sum over a singleton is its only term *)
lemma vmap_single (f : 'a -> vec) (a : 'a) : vmap f [a] = f a.
proof. by rewrite vmap_cons vmap_nil RqVec.Vector.ZModule.addr0. qed.

(* A ring sum over a singleton is its only term *)
lemma rmap_single (f : 'a -> rq) (a : 'a) : rmap f [a] = f a.
proof. by rewrite rmap_cons rmap_nil Rq.ComRingDflInv.addr0. qed.

(* A ring product over a singleton is its only factor *)
lemma rprod_single (f : 'a -> rq) (a : 'a) : rprod f [a] = f a.
proof. by rewrite rprod_cons rprod_nil Rq.ComRingDflInv.mulr1. qed.

(* Vector sums over a filtered list drop the rejected terms *)
lemma vmap_filter_zero (f : 'a -> vec) (p : 'a -> bool) (L : 'a list) :
  (forall x, x \in L => !p x => f x = zerov) =>
  vmap f (filter p L) = vmap f L.
proof.
elim L => [| a L ih] h //=.
case: (p a) => hp.
+ rewrite !vmap_cons ih // => x hx hnp.
  by apply h => //; rewrite in_cons hx.
rewrite ih.
+ by move=> x hx hnp; apply h => //; rewrite in_cons hx.
rewrite vmap_cons.
have -> : f a = zerov by apply h; [rewrite mem_head | exact hp].
by rewrite RqVec.Vector.ZModule.add0r.
qed.
