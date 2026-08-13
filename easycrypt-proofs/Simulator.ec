require import AllCore Int List Distr DList.
require import Params Types BigOps Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Translating a list of vectors pointwise by a fixed family *)
op shiftl (f : int -> vec) (H : committee) (ms : vec list) : vec list =
  map (fun (p : int * vec) => f p.`1 + p.`2) (zip H ms).

(* Translation preserves the length of the response list *)
lemma size_shiftl (f : int -> vec) (H : committee) (ms : vec list) :
  size ms = size H => size (shiftl f H ms) = size H.
proof. by move=> h; rewrite /shiftl size_map size_zip; smt(). qed.

(* The masks of the honest signers, with the last one closing the sum *)
op closeSum (ms : vec list) : vec = - (vsum ms).

(* A list of uniform vectors, one per honest signer but the last *)
op dmasks (k : int) : vec list distr = dlist dvec k.

(* The mask list distribution is lossless *)
lemma dmasks_ll (k : int) : is_lossless (dmasks k).
proof. by rewrite /dmasks; apply dlist_ll; exact dvec_ll. qed.

module ShareGen = {
  proc real(H : committee, f : int -> vec) : vec list = {
    var ms : vec list;
    var zs : vec list;
    ms <$ dmasks (size H - 1);
    zs <- shiftl f H (ms ++ [closeSum ms]);
    return zs;
  }

  proc ideal(H : committee, f : int -> vec) : vec list = {
    var zs0 : vec list;
    var zs : vec list;
    zs0 <$ dmasks (size H - 1);
    zs <- zs0 ++ [vmap f H - vsum zs0];
    return zs;
  }
}.

(* Translating a uniform vector keeps it uniform *)
equiv shift_one_uniform :
  Masking.OTP.masked ~ Masking.OTP.uniform : true ==> ={res}.
proof. exact Masking.otp_perfect. qed.

(* Empty vector list sums to zero *)
lemma vsum_nil : vsum [] = zerov.
proof. by rewrite /vsum. qed.

(* A vector list sum peels off its head *)
lemma vsum_cons (a : vec) (l : vec list) : vsum (a :: l) = a + vsum l.
proof. by rewrite /vsum. qed.

(* Vector list sums add over concatenation *)
lemma vsum_cat (l1 l2 : vec list) : vsum (l1 ++ l2) = vsum l1 + vsum l2.
proof.
elim l1 => [| a l1 ih].
+ by rewrite cat0s vsum_nil; smt(RqVec.Vector.ZModule.add0r).
rewrite cat_cons !vsum_cons ih.
exact RqVec.Vector.ZModule.addrA.
qed.

(* The sum of a translated list splits into the two parts *)
lemma vsum_shiftl (f : int -> vec) (H : committee) (ms : vec list) :
  size ms = size H =>
  vsum (shiftl f H ms) = vmap f H + vsum ms.
proof.
rewrite /shiftl /vsum /vmap.
move: ms; elim H => [| a H ih] ms hs.
+ have hnil : ms = [] by smt(size_eq0 size_ge0).
  by rewrite hnil /=; smt(RqVec.Vector.ZModule.addr0).
case: ms hs => [| m ms] hs //=; first by smt(size_ge0).
rewrite ih 1:/#.
exact RqVec.Vector.ZModule.addrACA.
qed.

(* Closing the sum makes the masks cancel *)
lemma vsum_close (ms : vec list) : vsum (ms ++ [closeSum ms]) = zerov.
proof.
rewrite vsum_cat vsum_cons vsum_nil /closeSum.
have -> : - vsum ms + zerov = - vsum ms by smt(RqVec.Vector.ZModule.addr0).
exact RqVec.Vector.ZModule.addrN.
qed.

(* The honest responses of a session sum to the unmasked aggregate *)
lemma shareGen_sum (f : int -> vec) (H : committee) (ms : vec list) :
  size ms = size H - 1 => 0 < size H =>
  vsum (shiftl f H (ms ++ [closeSum ms])) = vmap f H.
proof.
move=> hsz hpos.
rewrite vsum_shiftl.
+ by rewrite size_cat /=; smt().
by rewrite vsum_close RqVec.Vector.ZModule.addr0.
qed.

(* The simulated responses sum to the same aggregate *)
lemma ideal_sum (f : int -> vec) (H : committee) (zs0 : vec list) :
  vsum (zs0 ++ [vmap f H - vsum zs0]) = vmap f H.
proof.
rewrite vsum_cat vsum_cons vsum_nil.
have -> : vmap f H - vsum zs0 + zerov = vmap f H - vsum zs0.
+ by smt(RqVec.Vector.ZModule.addr0).
rewrite RqVec.Vector.ZModule.addrC.
exact RqVec.Vector.ZModule.subrK.
qed.

(* Real and simulated share generation agree on the aggregate *)
lemma shareGen_agree (f : int -> vec) (H : committee) (ms zs0 : vec list) :
  size ms = size H - 1 => 0 < size H =>
  vsum (shiftl f H (ms ++ [closeSum ms])) = vsum (zs0 ++ [vmap f H - vsum zs0]).
proof.
move=> hsz hpos.
by rewrite (shareGen_sum f H ms hsz hpos) (ideal_sum f H zs0).
qed.
