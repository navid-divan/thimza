require import AllCore Int List Distr.
require import Params BigOps.
import Rq.ComRingDflInv.

(* A polynomial is its coefficient list, constant term first *)
type poly = rq list.

op peval (f : poly) (x : rq) : rq =
  with f = "[]"     => zeror
  with f = (::) c g => c + x * (peval g x).

op padd (f g : poly) : poly =
  with f = "[]"     , g = "[]"      => []
  with f = "[]"     , g = (::) d g' => d :: g'
  with f = (::) c f', g = "[]"      => c :: f'
  with f = (::) c f', g = (::) d g' => (c + d) :: padd f' g'.

op pscale (c : rq) (f : poly) : poly = map (fun d => c * d) f.

op pshift (f : poly) : poly = zeror :: f.

(* The zero polynomial evaluates to zero *)
lemma peval_nil (x : rq) : peval [] x = zeror.
proof. done. qed.

(* Evaluation peels off the constant term *)
lemma peval_cons (c : rq) (f : poly) (x : rq) :
  peval (c :: f) x = c + x * (peval f x).
proof. done. qed.

(* Evaluation is additive over polynomial addition *)
lemma peval_add (f g : poly) (x : rq) :
  peval (padd f g) x = peval f x + peval g x.
proof.
move: g; elim f => [| c f ih] g.
+ case g => [| d g] /=; first by smt(addr0).
  by smt(add0r).
case g => [| d g] /=; first by smt(addr0).
rewrite ih.
smt(mulrDr addrACA).
qed.

(* Evaluation scales with the polynomial *)
lemma peval_scale (c : rq) (f : poly) (x : rq) :
  peval (pscale c f) x = c * peval f x.
proof.
elim f => [| d f ih]; first by rewrite /pscale /=; smt(mulr0).
rewrite /pscale map_cons -/(pscale c f) !peval_cons ih.
smt(mulrDr mulrCA).
qed.

(* Shifting a polynomial multiplies its value by the point *)
lemma peval_shift (f : poly) (x : rq) : peval (pshift f) x = x * peval f x.
proof. rewrite /pshift peval_cons. smt(add0r). qed.

(* Addition of polynomials preserves the coefficient count *)
lemma size_padd (f g : poly) : size (padd f g) = max (size f) (size g).
proof.
move: g; elim f => [| c f ih] g.
+ by case g => [| d g] //=; smt(size_ge0).
case g => [| d g] /=; first smt(size_ge0).
by rewrite ih; smt().
qed.

(* Scaling preserves the coefficient count *)
lemma size_pscale (c : rq) (f : poly) : size (pscale c f) = size f.
proof. by rewrite /pscale size_map. qed.

(* Shifting adds one coefficient *)
lemma size_pshift (f : poly) : size (pshift f) = size f + 1.
proof. by rewrite /pshift /=; smt(). qed.

op linmul (a : rq) (f : poly) : poly = padd (pshift f) (pscale (-a) f).

(* Multiplying by a linear factor acts as expected on values *)
lemma peval_linmul (a : rq) (f : poly) (x : rq) :
  peval (linmul a f) x = (x - a) * peval f x.
proof.
rewrite /linmul peval_add peval_shift peval_scale.
smt(mulrDl mulNr).
qed.

(* A linear factor adds one coefficient *)
lemma size_linmul (a : rq) (f : poly) :
  f <> [] => size (linmul a f) = size f + 1.
proof.
move=> hf; rewrite /linmul size_padd size_pshift size_pscale.
by smt(size_ge0 size_eq0).
qed.

op syndiv (f : poly) (a : rq) : poly =
  with f = "[]"     => []
  with f = (::) c g => if g = [] then [] else peval g a :: syndiv g a.

(* Synthetic division loses exactly one coefficient *)
lemma size_syndiv (f : poly) (a : rq) :
  f <> [] => size (syndiv f a) = size f - 1.
proof.
elim f => [| c f ih] //=.
case: (f = []) => hf; first by smt(size_ge0).
rewrite ?hf /= (ih hf); smt(size_ge0 size_eq0).
qed.

(* The factor theorem, as synthetic division *)
lemma peval_syndiv (f : poly) (a x : rq) :
  peval f x - peval f a = (x - a) * peval (syndiv f a) x.
proof.
elim f => [| c f ih] /=.
+ smt(subrr mulr0).
case: (f = []) => hf.
+ rewrite ?hf /=. smt(mulr0 addr0 subrr).
rewrite ?hf /=.
have hstep : c + x * peval f x - (c + a * peval f a)
           = x * peval f x - a * peval f a.
+ smt(opprD addrACA subrr add0r).
rewrite hstep.
have hsplit : x * peval f x - a * peval f a
            = x * (peval f x - peval f a) + (x - a) * peval f a.
+ smt(mulrBr mulrBl addrA addKr).
rewrite hsplit ih.
smt(mulrCA mulrDr mulrA mulrC addrC).
qed.

(* A root splits off a linear factor *)
lemma peval_root_factor (f : poly) (a x : rq) :
  peval f a = zeror =>
  peval f x = (x - a) * peval (syndiv f a) x.
proof.
move=> ha; have := peval_syndiv f a x.
smt(subr0).
qed.

(* Distinct nodes have invertible pairwise differences *)
pred sep (ns : rq list) =
  forall a b, a \in ns => b \in ns => a <> b => unit (a - b).

(* A separated node list stays separated after removing a head *)
lemma sep_cons (a : rq) (ns : rq list) : sep (a :: ns) => sep ns.
proof. by move=> h b c hb hc hbc; apply h => //; rewrite in_cons ?hb ?hc. qed.

(* A polynomial with more roots than coefficients vanishes *)
lemma peval_many_roots (f : poly) (ns : rq list) :
  sep ns => uniq ns => size f <= size ns =>
  (forall a, a \in ns => peval f a = zeror) =>
  forall x, peval f x = zeror.
proof.
move: f; elim ns => [| a ns ih] f hsep huniq hsz hroot x.
+ by have -> : f = [] by smt(size_eq0 size_ge0).
case: (f = []) => hf; first by rewrite hf.
have hfa : peval f a = zeror by apply hroot; rewrite mem_head.
pose g := syndiv f a.
have hsizeg : size g <= size ns by rewrite /g (size_syndiv f a hf); smt().
have hrootg : forall b, b \in ns => peval g b = zeror.
+ move=> b hb.
  have hfb : peval f b = zeror by apply hroot; rewrite in_cons hb.
  have hba : b <> a by smt(mem_head).
  have hu : unit (b - a).
  - by apply hsep; [rewrite in_cons hb | rewrite mem_head | exact hba].
  have heq : (b - a) * peval g b = zeror.
  - by rewrite /g -(peval_root_factor f a b hfa).
  have hz : (b - a) * peval g b = (b - a) * zeror by smt(mulr0).
  by have := mulrI (b - a) hu (peval g b) zeror hz.
have hg := ih g (sep_cons a ns hsep) _ hsizeg hrootg x; first by smt().
rewrite (peval_root_factor f a x hfa) hg. smt(mulr0).
qed.
