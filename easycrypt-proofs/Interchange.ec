require import AllCore Int List.
require import Params Types BigOps PolyList Sharing ShamirLagrange Masking Protocol Privacy.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op raccoon_verify (hc : hcfun) (vk : row) (mu : msg) (sg : sig) : bool =
  hc vk (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt vk)) + sg.`3) mu = sg.`1
  /\ inbnd sg.`2 sg.`3.

(* The threshold verifier is the Raccoon verifier *)
lemma verify_is_raccoon hc vk mu sg : verify hc vk mu sg = raccoon_verify hc vk mu sg.
proof. by rewrite /verify /raccoon_verify. qed.

op raccoon_sign (hc : hcfun) (vk : row) (s : vec) (mu : msg) (r : vec) (e : row) : sig =
  let w = aggw [rndc (commit r e)] in
  let c = hc vk w mu in
  (c, c ** s + r, mkhint vk c w (c ** s + r)).

(* One element sums are the element *)
lemma vsum1 (x : vec) : vsum [x] = x.
proof. by rewrite /vsum /= (RqVec.Vector.ZModule.addr0 x). qed.

(* A single node is separated *)
lemma sep_single (a : rq) : sep [a].
proof. by move=> x y; rewrite !mem_seq1 => -> ->. qed.

(* One signer computes Raccoon signing *)
lemma single_signer h0 h1 hc vk s p mu (i : int) (r : vec) (e : row) :
  tthr = 1 => 1 <= i <= nmax =>
  honest_sig h0 h1 hc vk s p mu [i] [r] [e] = raccoon_sign hc vk s mu r e.
proof.
move=> ht hi.
have hok : okset [i].
+ rewrite /okset /wf_committee /inrange /wf_nodes /nodesOf /= ht /=.
  by rewrite hi /= sep_single.
rewrite (honest_ideal h0 h1 hc vk s p mu [i] [r] [e] hok) 1:/# //.
rewrite /ideal_sig /raccoon_sign /=.
by rewrite vsum1.
qed.

(* Raccoon signatures verify under norm bounds *)
lemma single_signer_verifies hc vk s mu r e :
  raccoon_verify hc vk mu (raccoon_sign hc vk s mu r e)
  = inbnd ((raccoon_sign hc vk s mu r e).`2) ((raccoon_sign hc vk s mu r e).`3).
proof.
rewrite /raccoon_verify /raccoon_sign /=.
by rewrite hint_correct.
qed.
