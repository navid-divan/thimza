require import AllCore Int List Distr Real.
require import Params Types Protocol Extract Assumptions.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op hcprog (g : row -> row * msg -> rq) (pts : (row * (row * msg)) list) (vals : rq list)
  : hcfun =
  fun vk w mu =>
    if (liftw w, (vk, mu)) \in pts then nth witness vals (index (liftw w, (vk, mu)) pts)
    else g (liftw w) (vk, mu).

op chkpt (vk : row) (mu : msg) (sg : sig) : row * (row * msg) =
  (liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt vk)) + sg.`3), (vk, mu)).

module type FinalSim (G : GOracle) = {
  proc run(b : row) : row * msg * sig * (row * (row * msg)) list * rq list
}.

module Final (S : FinalSim) = {
  proc main() : bool = {
    var b, vk, mu, sg, pts, vals;
    GO.init();
    b <$ drow;
    (vk, mu, sg, pts, vals) <@ S(GO).run(b);
    return verify (hcprog GO.g pts vals) vk mu sg /\ !(chkpt vk mu sg \in pts);
  }
}.

module Red (S : FinalSim) (G : GOracle) = {
  proc solve(b : row) : row * msg * vec * rq * row = {
    var vk, mu, sg, pts, vals;
    (vk, mu, sg, pts, vals) <@ S(G).run(b);
    return (vk, mu, sg.`2, sg.`1, uof vk sg.`2 sg.`1 sg.`3);
  }
}.

(* Unprogrammed forgeries solve self-target MSIS *)
lemma final_reduction (S <: FinalSim {-GO}) &m :
  rounding_fact =>
  Pr[Final(S).main() @ &m : res] <= Pr[STMSIS(Red(S)).main() @ &m : res].
proof.
move=> hr; byequiv => //.
proc; inline Red(S, GO).solve; wp.
call (_ : ={GO.g}); first by proc; auto.
wp; rnd; inline GO.init; wp; rnd; skip => /> g _ b _ [vk mu sg pts vals] /= hv hb hnp.
have hver : verify (fun vk' w mu' => if (fun x => x \in pts) (liftw w, (vk', mu'))
                                     then (fun x => nth witness vals (index x pts)) (liftw w, (vk', mu'))
                                     else g (liftw w) (vk', mu')) vk mu sg.
+ by rewrite /verify /=; split => //; move: hv; rewrite /hcprog.
have := unprogrammed g (fun x => x \in pts) (fun x => nth witness vals (index x pts))
          vk mu sg hr hver _.
+ by move: hnp; rewrite /chkpt.
by move=> [] -> ->.
qed.
