require import AllCore Int List Real.
require import Params Types Protocol.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op liftw : row -> row.

op solnorm : vec -> rq -> row -> real.

op bst : real.

op hc_of (g : row -> row * msg -> rq) : hcfun = fun vk w mu => g (liftw w) (vk, mu).

op stimage (vk : row) (z : vec) (c : rq) (u : row) : row =
  mulA mA z - rowZ c (liftt vk) + u.

op uof (vk : row) (z : vec) (c : rq) (h : row) : row =
  liftw (rndw (mulA mA z - rowZ c (liftt vk)) + h) - (mulA mA z - rowZ c (liftt vk)).

(* Extracted solutions map to lifted commitments *)
lemma stimage_uof vk z c h :
  stimage vk z c (uof vk z c h) = liftw (rndw (mulA mA z - rowZ c (liftt vk)) + h).
proof.
rewrite /stimage /uof.
by rewrite RqRow.Vector.ZModule.addrC RqRow.Vector.ZModule.subrK.
qed.

pred rounding_fact =
  forall vk z c h, inbnd z h => solnorm z c (uof vk z c h) <= bst.

(* Forgeries solve self-target MSIS *)
lemma forgery_solves (g : row -> row * msg -> rq) vk mu (sg : sig) :
  rounding_fact =>
  verify (hc_of g) vk mu sg =>
  g (stimage vk sg.`2 sg.`1 (uof vk sg.`2 sg.`1 sg.`3)) (vk, mu) = sg.`1
  /\ solnorm sg.`2 sg.`1 (uof vk sg.`2 sg.`1 sg.`3) <= bst.
proof.
move=> hr [] hc hb; split.
+ by rewrite stimage_uof; move: hc; rewrite /hc_of.
exact (hr vk sg.`2 sg.`1 sg.`3 hb).
qed.

(* Unprogrammed forgeries solve self-target MSIS *)
lemma unprogrammed (g : row -> row * msg -> rq) (prog : row * (row * msg) -> bool)
                   (cv : row * (row * msg) -> rq) vk mu (sg : sig) :
  rounding_fact =>
  verify (fun vk' w mu' => if prog (liftw w, (vk', mu')) then cv (liftw w, (vk', mu'))
                           else g (liftw w) (vk', mu')) vk mu sg =>
  !prog (liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt vk)) + sg.`3), (vk, mu)) =>
  g (stimage vk sg.`2 sg.`1 (uof vk sg.`2 sg.`1 sg.`3)) (vk, mu) = sg.`1
  /\ solnorm sg.`2 sg.`1 (uof vk sg.`2 sg.`1 sg.`3) <= bst.
proof.
move=> hr [] hc hb hnp; split.
+ rewrite stimage_uof.
  move: hc; rewrite (negbTE _ hnp) /=.
  done.
exact (hr vk sg.`2 sg.`1 sg.`3 hb).
qed.
