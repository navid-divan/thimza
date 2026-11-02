require import AllCore Int List Distr DList.
require import Params Types BigOps Sharing ShamirLagrange Masking Protocol.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op dnonce : vec distr.

op dnoiser : row distr.

op pick (T : committee) (xs : 'a list) (j : int) : 'a = nth witness xs (index j T).

(* Committee reading returns the list *)
lemma map_pick (T : committee) (xs : 'a list) :
  uniq T => size xs = size T => map (pick T xs) T = xs.
proof.
elim: T xs => [| a T ih] xs.
+ by move=> _ /= hs; smt(size_eq0).
move=> /= [] ha hu.
case: xs => [| x xs].
+ by move=> /=; smt(size_ge0).
move=> /= hs.
split; first by rewrite /pick /= index_cons.
have -> : map (pick (a :: T) (x :: xs)) T = map (pick T xs) T.
+ apply eq_in_map => j hj; rewrite /pick index_cons.
  have -> /= : j <> a by smt().
  smt(index_ge0).
by apply ih => //; smt().
qed.

(* Pair maps are zipped maps *)
lemma map_pair (f : 'a -> 'b) (g : 'a -> 'c) (L : 'a list) :
  map (fun x => (f x, g x)) L = zip (map f L) (map g L).
proof. by elim: L => //= a L ->. qed.

op tokf (h0 : h0fun) (vk : row) (mu : msg) (T : committee) (rs : vec list)
        (es : row list) (j : int) : token =
  sign1 h0 vk j mu (pick T rs j) (pick T es j).

op cmtsOf h0 vk mu T rs es : cmt list = map (fun j => (tokf h0 vk mu T rs es j).`tk_cmt) T.

op opensOf h0 vk mu T rs es : row list = map (fun j => (tokf h0 vk mu T rs es j).`tk_wbar) T.

op tok2f (h0 : h0fun) (h1 : h1fun) vk mu T rs es (j : int) : token =
  (oget (sign2 h1 vk (tokf h0 vk mu T rs es j) T (cmtsOf h0 vk mu T rs es))).`1.

op respsOf (h0 : h0fun) (h1 : h1fun) (hc : hcfun) vk (s : vec) (p : int -> vec) mu T rs es
  : vec list =
  map (fun j => resp hc vk (shr s p j) (tok2f h0 h1 vk mu T rs es j) T (opensOf h0 vk mu T rs es)) T.

op honest_sig (h0 : h0fun) (h1 : h1fun) (hc : hcfun) vk s p mu T rs es : sig =
  combine vk (chal hc vk mu (opensOf h0 vk mu T rs es)) (aggw (opensOf h0 vk mu T rs es))
          (respsOf h0 h1 hc vk s p mu T rs es).

op ideal_sig (hc : hcfun) (vk : row) (s : vec) (mu : msg) (rs : vec list) (es : row list) : sig =
  let ws = map (fun (x : vec * row) => rndc (commit x.`1 x.`2)) (zip rs es) in
  let c = hc vk (aggw ws) mu in
  (c, c ** s + vsum rs, mkhint vk c (aggw ws) (c ** s + vsum rs)).

pred okset (T : committee) = wf_committee T /\ inrange T /\ wf_nodes T.

(* Honest members pass round two checks *)
lemma honest_ok2 h0 vk mu T rs es j :
  okset T => j \in T =>
  ok2 (tokf h0 vk mu T rs es j) T (cmtsOf h0 vk mu T rs es).
proof.
rewrite /okset => -[hwf [hr _]] hj; rewrite /ok2 /own_cmt /cmtsOf /tokf /sign1 /=.
rewrite hwf hr hj size_map /=.
rewrite (nth_map witness) /=; first by smt(index_ge0 index_mem).
by rewrite nth_index.
qed.

(* Honest openings are nonce commitments *)
lemma opensOf_zip h0 vk mu T rs es :
  uniq T => size rs = size T => size es = size T =>
  opensOf h0 vk mu T rs es = map (fun (x : vec * row) => rndc (commit x.`1 x.`2)) (zip rs es).
proof.
move=> hu hr he.
have -> : opensOf h0 vk mu T rs es
        = map (fun (x : vec * row) => rndc (commit x.`1 x.`2))
              (map (fun j => (pick T rs j, pick T es j)) T).
+ rewrite /opensOf -map_comp; apply eq_map => j @/(\o) /=.
  by rewrite /tokf /sign1.
congr.
have -> : map (fun j => (pick T rs j, pick T es j)) T = zip (map (pick T rs) T) (map (pick T es) T).
+ by apply map_pair.
by rewrite (map_pick T rs) // (map_pick T es).
qed.

(* Honest second rounds succeed *)
lemma honest_sign2 h0 h1 vk mu T rs es j :
  okset T => j \in T =>
  sign2 h1 vk (tokf h0 vk mu T rs es j) T (cmtsOf h0 vk mu T rs es)
  = Some (tok2f h0 h1 vk mu T rs es j, (tokf h0 vk mu T rs es j).`tk_wbar).
proof.
move=> hok hj; rewrite /tok2f /sign2 (honest_ok2 h0 vk mu T rs es j hok hj) /=.
done.
qed.

(* Round two tokens keep nonces, bind digests *)
lemma tok2f_fields h0 h1 vk mu T rs es j :
  okset T => j \in T =>
  (tok2f h0 h1 vk mu T rs es j).`tk_i = j
  /\ (tok2f h0 h1 vk mu T rs es j).`tk_msg = mu
  /\ (tok2f h0 h1 vk mu T rs es j).`tk_dig = h1 vk mu T (cmtsOf h0 vk mu T rs es)
  /\ (tok2f h0 h1 vk mu T rs es j).`tk_r = pick T rs j
  /\ (tok2f h0 h1 vk mu T rs es j).`tk_phase = 2
  /\ (tok2f h0 h1 vk mu T rs es j).`tk_T = T
  /\ (tok2f h0 h1 vk mu T rs es j).`tk_wbar = (tokf h0 vk mu T rs es j).`tk_wbar.
proof.
move=> hok hj.
have := sign2_some h1 vk (tokf h0 vk mu T rs es j) T (cmtsOf h0 vk mu T rs es)
          (tok2f h0 h1 vk mu T rs es j, (tokf h0 vk mu T rs es j).`tk_wbar)
          (honest_sign2 h0 h1 vk mu T rs es j hok hj).
move=> [#] _ hph hT hdig _ hi hmsg hr _ hw _.
by rewrite hph hT hdig hi hmsg hr hw /tokf /sign1.
qed.

(* Recomputed commitments pass opening checks *)
lemma opens_all (h0 : h0fun) vk mu (g : int -> token) (L : int list) :
  (forall j, (g j).`tk_cmt = h0 vk mu j (g j).`tk_wbar) =>
  all (fun (p : int * (cmt * row)) => h0 vk mu p.`1 p.`2.`2 = p.`2.`1)
      (zip L (zip (map (fun j => (g j).`tk_cmt) L) (map (fun j => (g j).`tk_wbar) L))).
proof. by move=> hg; elim: L => //= a L ->; rewrite hg. qed.

(* Honest openings match commitments *)
lemma honest_opens h0 vk mu T rs es :
  opens_ok h0 vk mu T (cmtsOf h0 vk mu T rs es) (opensOf h0 vk mu T rs es).
proof.
rewrite /opens_ok /cmtsOf /opensOf !size_map /=.
by apply opens_all => j; rewrite /tokf /sign1.
qed.

(* Honest members pass round three checks *)
lemma honest_ok3 h0 h1 vk mu T rs es j :
  okset T => j \in T =>
  ok3 h0 h1 vk (tok2f h0 h1 vk mu T rs es j) T
      (cmtsOf h0 vk mu T rs es) (opensOf h0 vk mu T rs es).
proof.
move=> hok hj.
have [#] hi hmsg hdig hr hph hT hw := tok2f_fields h0 h1 vk mu T rs es j hok hj.
rewrite /ok3 hph hT hmsg hdig hw hi /= honest_opens /=.
rewrite /opensOf (nth_map witness) /=; first by smt(index_ge0 index_mem).
by rewrite nth_index.
qed.

(* Honest third rounds return responses *)
lemma honest_sign3 h0 h1 hc vk s p mu T rs es j :
  okset T => j \in T =>
  sign3 h0 h1 hc vk (shr s p j) (tok2f h0 h1 vk mu T rs es j) T
        (cmtsOf h0 vk mu T rs es) (opensOf h0 vk mu T rs es)
  = Some (erase (tok2f h0 h1 vk mu T rs es j),
          resp hc vk (shr s p j) (tok2f h0 h1 vk mu T rs es j) T (opensOf h0 vk mu T rs es)).
proof. by move=> hok hj; rewrite /sign3 (honest_ok3 h0 h1 vk mu T rs es j hok hj). qed.

(* Honest sessions output ideal signatures *)
lemma honest_ideal h0 h1 hc vk s p mu T rs es :
  okset T => 0 < tthr => size rs = size T => size es = size T =>
  honest_sig h0 h1 hc vk s p mu T rs es = ideal_sig hc vk s mu rs es.
proof.
move=> hok ht hr he.
have [[hu hsz] [hrg hwn]] := hok.
have hsum : vsum (respsOf h0 h1 hc vk s p mu T rs es)
          = (chal hc vk mu (opensOf h0 vk mu T rs es)) ** s + vsum rs.
+ have := resp_sum hc vk mu T (h1 vk mu T (cmtsOf h0 vk mu T rs es))
            (opensOf h0 vk mu T rs es) s p (tok2f h0 h1 vk mu T rs es) hwn ht _.
  - move=> j hj; have [#] hi hmsg hdig _ _ _ _ := tok2f_fields h0 h1 vk mu T rs es j hok hj.
    by rewrite hi hmsg hdig.
  rewrite /respsOf /vmap => ->; congr.
  have -> : map (fun j => (tok2f h0 h1 vk mu T rs es j).`tk_r) T = map (pick T rs) T.
  - apply eq_in_map => j hj /=.
    by have [#] _ _ _ -> _ _ _ := tok2f_fields h0 h1 vk mu T rs es j hok hj.
  by rewrite (map_pick T rs).
rewrite /honest_sig /ideal_sig /combine /= hsum /chal (opensOf_zip h0 vk mu T rs es hu hr he).
done.
qed.

module Priv = {
  proc honest(h0 : h0fun, h1 : h1fun, hc : hcfun, vk : row, s : vec, p : int -> vec,
              mu : msg, T : committee) : sig = {
    var n, rs, es;
    n <- size T;
    rs <$ dlist dnonce n;
    es <$ dlist dnoiser n;
    return honest_sig h0 h1 hc vk s p mu T rs es;
  }
}.

(* Signatures ignore the signer set *)
equiv signer_set_privacy :
  Priv.honest ~ Priv.honest :
  ={h0, h1, hc, vk, s, p, mu} /\ size T{1} = size T{2} /\ okset T{1} /\ okset T{2}
  /\ 0 < tthr ==> ={res}.
proof.
proc.
seq 1 1 : (={h0, h1, hc, vk, s, p, mu, n} /\ n{1} = size T{1} /\ n{2} = size T{2}
           /\ okset T{1} /\ okset T{2} /\ 0 < tthr).
+ by auto => /> &1 &2 hsz.
auto => /> &1 &2 hsz hu1 hs1 hr1 hp1 hn1 hm1 hu2 hs2 hr2 hp2 hn2 hm2 ht rs hrs es hes.
have hok1 : okset T{1} by rewrite /okset /wf_committee /wf_nodes.
have hok2 : okset T{2} by rewrite /okset /wf_committee /wf_nodes.
have hr : size rs = size T{1} by smt(supp_dlist size_ge0).
have he : size es = size T{1} by smt(supp_dlist size_ge0).
rewrite (honest_ideal h0{2} h1{2} hc{2} vk{2} s{2} p{2} mu{2} T{1} rs es) //.
by rewrite (honest_ideal h0{2} h1{2} hc{2} vk{2} s{2} p{2} mu{2} T{2} rs es) // -hsz.
qed.
