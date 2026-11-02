require import AllCore Int List Distr DList.
require import Params Types BigOps Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

op pairv (u : int -> int -> vec) (a b : int) : vec =
  if a < b then u a b else if b < a then - u b a else zerov.

op cmask (u : int -> int -> vec) (m a : int) : vec = vmap (pairv u a) (range 0 m).

(* A member does not mask against itself *)
lemma pairv_diag (u : int -> int -> vec) a : pairv u a a = zerov.
proof. by rewrite /pairv. qed.

(* Pair values seen from both ends cancel *)
lemma pairv_anti (u : int -> int -> vec) a b : pairv u a b + pairv u b a = zerov.
proof.
rewrite /pairv.
case: (a < b) => hab.
+ have hba : !(b < a) by smt().
  by rewrite hba /= RqVec.Vector.ZModule.addrN.
case: (b < a) => hba.
+ by rewrite /= RqVec.Vector.ZModule.addNr.
by rewrite /= RqVec.Vector.ZModule.addr0.
qed.

(* Class masks sum to zero *)
lemma cmask_sum (u : int -> int -> vec) m : vmap (cmask u m) (range 0 m) = zerov.
proof.
have -> : vmap (cmask u m) (range 0 m) = vmap (fun a => vmap (pairv u a) (range 0 m)) (range 0 m).
+ by apply vmap_eq.
by apply dsum_anti; [exact (pairv_diag u) | exact (pairv_anti u)].
qed.

op mixu (inner : int -> int -> vec) (lst : vec list) (m : int) : int -> int -> vec =
  fun a b => if b = m - 1 then nth zerov lst a else inner a b.

op cst (f : int -> vec) (inner : int -> int -> vec) (m a : int) : vec =
  f a + vmap (pairv inner a) (range 0 (m - 1)).

op shiftk (c : int -> vec) (k : int) (l : vec list) : vec list =
  map (fun a => c a + nth zerov l a) (range 0 k).

op unshiftk (c : int -> vec) (k : int) (l : vec list) : vec list =
  map (fun a => nth zerov l a - c a) (range 0 k).

(* Translation keeps the length *)
lemma size_shiftk c k l : 0 <= k => size (shiftk c k l) = k.
proof. by move=> hk; rewrite /shiftk size_map size_range; smt(). qed.

(* Inverse translation keeps the length *)
lemma size_unshiftk c k l : 0 <= k => size (unshiftk c k l) = k.
proof. by move=> hk; rewrite /unshiftk size_map size_range; smt(). qed.

(* Translating back and forth is the identity *)
lemma shift_unshift c k l : size l = k => shiftk c k (unshiftk c k l) = l.
proof.
move=> hs; apply (eq_from_nth zerov).
+ by rewrite size_shiftk; smt(size_ge0).
move=> i; rewrite size_shiftk; 1: smt(size_ge0).
move=> hi; rewrite /shiftk /unshiftk (nth_map 0) ?size_range; 1: smt().
rewrite nth_range //= (nth_map 0) ?size_range; 1: smt().
rewrite nth_range //=.
by rewrite RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.subrK.
qed.

(* Translating forth and back is the identity *)
lemma unshift_shift c k l : size l = k => unshiftk c k (shiftk c k l) = l.
proof.
move=> hs; apply (eq_from_nth zerov).
+ by rewrite size_unshiftk; smt(size_ge0).
move=> i; rewrite size_unshiftk; 1: smt(size_ge0).
move=> hi; rewrite /shiftk /unshiftk (nth_map 0) ?size_range; 1: smt().
rewrite nth_range //= (nth_map 0) ?size_range; 1: smt().
rewrite nth_range //=.
by rewrite RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.addKr.
qed.

(* Early masks split into two parts *)
lemma cmask_early (inner : int -> int -> vec) (lst : vec list) m a :
  0 <= a < m - 1 =>
  cmask (mixu inner lst m) m a
  = vmap (pairv inner a) (range 0 (m - 1)) + nth zerov lst a.
proof.
move=> ha; rewrite /cmask (rangeSr 0 (m - 1)) 1:/# -cats1.
have -> : vmap (pairv (mixu inner lst m) a) (range 0 (m - 1) ++ [m - 1])
        = vmap (pairv (mixu inner lst m) a) (range 0 (m - 1))
          + vmap (pairv (mixu inner lst m) a) [m - 1].
+ by rewrite vmap_cat.
congr.
+ apply vmap_eq => b hb; rewrite /pairv /mixu.
  have hb' : b <> m - 1 by smt(mem_range).
  have ha' : a <> m - 1 by smt().
  by rewrite hb' ha'.
rewrite vmap_cons vmap_nil RqVec.Vector.ZModule.addr0 /pairv /mixu.
by have -> /= : a < m - 1 by smt().
qed.

(* Class responses via last pair values *)
lemma class_form (f : int -> vec) (inner : int -> int -> vec) (lst : vec list) m :
  1 <= m =>
  map (fun a => f a + cmask (mixu inner lst m) m a) (range 0 m)
  = shiftk (cst f inner m) (m - 1) lst
    ++ [vmap f (range 0 m) - vsum (shiftk (cst f inner m) (m - 1) lst)].
proof.
move=> hm.
pose g := fun a => f a + cmask (mixu inner lst m) m a.
have hpre : map g (range 0 (m - 1)) = shiftk (cst f inner m) (m - 1) lst.
+ rewrite /shiftk; apply eq_in_map => a /mem_range ha.
  by rewrite /g /cst (cmask_early inner lst m a) // RqVec.Vector.ZModule.addrA.
have hsum : vmap g (range 0 m) = vmap f (range 0 m).
+ have -> : vmap g (range 0 m)
          = vmap f (range 0 m) + vmap (cmask (mixu inner lst m) m) (range 0 m).
  - by rewrite /g -vmap_split.
  by rewrite cmask_sum RqVec.Vector.ZModule.addr0.
have hr : range 0 m = range 0 (m - 1) ++ [m - 1].
+ by rewrite cats1 -rangeSr 1:/#.
have hsplit : vmap g (range 0 m) = vsum (shiftk (cst f inner m) (m - 1) lst) + g (m - 1).
+ rewrite {1}hr vmap_cat vmap_cons vmap_nil (RqVec.Vector.ZModule.addr0 (g (m - 1))).
  have -> : vmap g (range 0 (m - 1)) = vsum (map g (range 0 (m - 1))) by done.
  by rewrite hpre.
rewrite {1}hr map_cat hpre /= .
congr; congr.
rewrite -hsum hsplit.
by rewrite (RqVec.Vector.ZModule.addrC (vsum (shiftk (cst f inner m) (m - 1) lst)) (g (m - 1)))
           (RqVec.Vector.ZModule.addrK (vsum (shiftk (cst f inner m) (m - 1) lst)) (g (m - 1))).
qed.

module Class = {
  proc real(m : int, f : int -> vec, inner : int -> int -> vec) : vec list = {
    var lst;
    lst <$ dlist dvec (m - 1);
    return map (fun a => f a + cmask (mixu inner lst m) m a) (range 0 m);
  }

  proc ideal(m : int, f : int -> vec) : vec list = {
    var zs0;
    zs0 <$ dlist dvec (m - 1);
    return zs0 ++ [vmap f (range 0 m) - vsum zs0];
  }
}.

(* Class responses are simulated without the key *)
equiv class_sim : Class.real ~ Class.ideal : ={m, f} /\ 1 <= m{1} ==> ={res}.
proof.
proc.
rnd (shiftk (cst f{1} inner{1} m{1}) (m{1} - 1)) (unshiftk (cst f{1} inner{1} m{1}) (m{1} - 1)).
skip => /> &1 &2 hm; split.
+ move=> zs hzs; apply/eq_sym; apply shift_unshift.
  by move: hzs; rewrite supp_dlist; smt().
move=> h1; split.
+ move=> zs hzs; apply (dlist_uni dvec (m{2} - 1) dvec_uni); first exact hzs.
  rewrite supp_dlist; 1: smt().
  split; first by rewrite size_unshiftk; smt().
  by apply/allP => x _; exact dvec_fu.
move=> h2 lst hlast; split.
+ rewrite supp_dlist; 1: smt().
  split; first by rewrite size_shiftk; smt().
  by apply/allP => x _; exact dvec_fu.
move=> h3; split.
+ by apply/eq_sym; apply unshift_shift; move: hlast; rewrite supp_dlist; smt().
by move=> _; rewrite (class_form f{2} inner{1} lst m{2} hm).
qed.

module ClassPart = {
  proc real(m k : int, f : int -> vec, inner : int -> int -> vec) : vec list = {
    var zs;
    zs <@ Class.real(m, f, inner);
    return take k zs;
  }

  proc ideal(m k : int) : vec list = {
    var zs0;
    zs0 <$ dlist dvec (m - 1);
    return take k zs0;
  }
}.

(* Early class responses are uniform *)
equiv class_prefix :
  ClassPart.real ~ ClassPart.ideal : ={m, k} /\ 1 <= m{1} /\ 0 <= k{1} < m{1} ==> ={res}.
proof.
proc.
transitivity{1} { zs <@ Class.ideal(m, f); }
  (={m, k, f} /\ 1 <= m{1} ==> ={zs, k, m})
  (={m, k} /\ 1 <= m{1} /\ 0 <= k{1} < m{1} ==> take k{1} zs{1} = take k{2} zs0{2}).
+ by move=> &1 &2 /= [#] h1 h2 hm hk1 hk2; exists f{1} k{1} m{1}; smt().
+ done.
+ by wp; call class_sim; auto.
inline Class.ideal; wp; rnd; wp; skip => /> &1 &2 hm hk0 hk zs0 hzs0.
have hs : size zs0 = m{2} - 1 by move: hzs0; rewrite supp_dlist; smt().
rewrite take_cat hs.
case: (k{2} < m{2} - 1) => // hlt.
have -> : k{2} = m{2} - 1 by smt().
have -> : m{2} - 1 - (m{2} - 1) <= 0 by smt().
by rewrite /= cats0 -hs take_size.
qed.
