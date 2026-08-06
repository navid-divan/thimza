require import AllCore Int List Distr.
require import Params Types.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Pairwise masking pseudorandom function *)
op prf : seed -> view -> vec.

(* Per unordered pair pseudorandom masking seeds *)
op pairseed : int -> int -> seed.

(* Masking term of one partner *)
op term (T : committee) (vw : view) (i j : int) : vec =
  if i = j then zerov
  else if i < j then prf (pairseed i j) vw
  else - (prf (pairseed j i) vw).

(* Total antisymmetric mask received by a signer *)
op mask (T : committee) (vw : view) (i : int) : vec =
  vmap (term T vw i) T.

(* Partners of a signer inside a committee *)
op partners (T : committee) (i : int) : committee = filter (predC1 i) T.

(* Self masking terms are zero *)
lemma term_diag (T : committee) (vw : view) (i : int) : term T vw i i = zerov.
proof. by rewrite /term. qed.

(* Paired masking terms are additive inverses *)
lemma term_anti (T : committee) (vw : view) (i j : int) :
  term T vw i j + term T vw j i = zerov.
proof.
rewrite /term; case (i = j) => [->|hne] /=.
+ exact RqVec.Vector.ZModule.add0r.
have hne' : j <> i by smt().
rewrite hne' /=; case (i < j) => hlt.
+ have -> /=: !(j < i) by smt().
  exact RqVec.Vector.ZModule.addrN.
have -> /=: j < i by smt().
exact RqVec.Vector.ZModule.addNr.
qed.

(* Antisymmetric double sums vanish *)
lemma dsum_anti (g : int -> int -> vec) (S : committee) :
  (forall i, g i i = zerov) =>
  (forall i j, g i j + g j i = zerov) =>
  vmap (fun i => vmap (g i) S) S = zerov.
proof.
move=> hd ha; elim S => [| a S ih]; first exact vmap_nil.
rewrite vmap_cons /= vmap_cons.
have -> : g a a + vmap (g a) S = vmap (g a) S.
+ by rewrite hd; exact RqVec.Vector.ZModule.add0r.
have -> : vmap (fun i => vmap (g i) (a :: S)) S
        = vmap (fun i => g i a + vmap (g i) S) S.
+ by apply vmap_eq => i _ /=; rewrite vmap_cons.
rewrite vmap_split ih.
have -> : vmap (fun i => g i a) S + zerov = vmap (fun i => g i a) S.
+ exact RqVec.Vector.ZModule.addr0.
rewrite -vmap_split.
have -> : vmap (fun x => g a x + g x a) S = vmap (fun (_ : int) => zerov) S.
+ by apply vmap_eq => i _ /=; exact ha.
exact vmap0.
qed.

(* Committee masks sum to zero *)
lemma mask_sum_zero (T : committee) (vw : view) :
  vmap (mask T vw) T = zerov.
proof.
have -> : vmap (mask T vw) T = vmap (fun i => vmap (term T vw i) T) T.
+ by apply vmap_eq => i _; rewrite /mask.
by apply dsum_anti; [exact (term_diag T vw) | exact (term_anti T vw)].
qed.

(* Masking preserves the aggregate response *)
lemma mask_agg (T : committee) (vw : view) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) T = vmap g T.
proof.
rewrite vmap_split.
have -> : vmap (fun i => mask T vw i) T = vmap (mask T vw) T.
+ by apply vmap_eq.
by rewrite mask_sum_zero; exact RqVec.Vector.ZModule.addr0.
qed.

(* Each signer stores one seed per partner *)
lemma partners_size (T : committee) (i : int) :
  uniq T => i \in T => size (partners T i) = size T - 1.
proof.
move=> hu hin; rewrite /partners size_filter.
have hc : predC1 i = predC (pred1 i).
+ by apply fun_ext => y; rewrite /predC1 /predC /pred1.
have h1 : count (pred1 i) T = 1 by rewrite count_uniq_mem // hin.
by rewrite hc; have := count_predC (pred1 i) T; smt().
qed.

(* No signer masks against itself *)
lemma partners_mem (T : committee) (i j : int) :
  j \in partners T i => j <> i.
proof. by rewrite /partners mem_filter /predC1 => -[]. qed.

(* Masking involves partners only *)
lemma mask_partners (T : committee) (vw : view) (i : int) :
  mask T vw i = vmap (term T vw i) (partners T i).
proof.
rewrite /mask /partners.
elim T => [| a T ih]; first by rewrite !vmap_nil.
rewrite filter_cons /predC1 /= vmap_cons.
case: (a = i) => ha.
+ by rewrite ?ha /= ?term_diag ih; exact RqVec.Vector.ZModule.add0r.
by rewrite ?ha /= ?vmap_cons ih.
qed.

(* Partner count matches the committee *)
lemma partners_wf (T : committee) (i : int) :
  wf_committee T => i \in T => size (partners T i) = tthr - 1.
proof. by move=> [hu hs] hin; rewrite (partners_size T i hu hin) hs. qed.

module OTP = {
  proc masked(u : vec) : vec = {
    var m : vec;
    m <$ dvec;
    return u + m;
  }

  proc uniform() : vec = {
    var z : vec;
    z <$ dvec;
    return z;
  }
}.

(* One time masking yields a uniform response *)
equiv otp_perfect : OTP.masked ~ OTP.uniform : true ==> ={res}.
proof.
proc.
rnd (fun (m : vec) => u{1} + m) (fun (z : vec) => z - u{1}).
skip => &1 &2 _ /=; split.
+ by move=> z hz; rewrite vaddS.
move=> _; split.
+ by move=> z hz; apply dvec_funi.
move=> _ m hm; split; first exact dvec_fu.
by move=> _; rewrite vsubK.
qed.

(* A uniform partner term perfectly masks *)
module OTPFromPartner = {
  proc masked(u : vec, T : committee, vw : view, i j : int) : vec = {
    var m, r : vec;
    if (i < j) {
      m <$ dvec;
      r <- u + m;
    } else {
      m <$ dvec;
      r <- u + (-m);
    }
    return r;
  }

  proc uniform() : vec = {
    var z : vec;
    z <$ dvec;
    return z;
  }
}.

(* Uniform masking term hides any vector *)
equiv otp_from_partner : OTPFromPartner.masked ~ OTPFromPartner.uniform : true ==> ={res}.
proof.
proc.
if{1}.
+ wp.
  rnd (fun (m : vec) => u{1} + m) (fun (z : vec) => z - u{1}).
  skip => &1 &2 _ /=; split.
  - by move=> z hz; rewrite vaddS.
  move=> _; split.
  - by move=> z hz; apply dvec_funi.
  move=> _ m hm; split; first exact dvec_fu.
  by move=> _; rewrite vsubK.
wp.
rnd (fun (m : vec) => u{1} + (-m)) (fun (z : vec) => u{1} - z).
skip => &1 &2 _ /=; split.
+ move=> z hz.
  have hstep : u{1} + - (u{1} - z) = z + (u{1} + - u{1}).
  - by rewrite RqVec.Vector.ZModule.opprB RqVec.Vector.ZModule.addrCA.
  rewrite hstep.
  have hz2 : u{1} + - u{1} = zerov by exact (RqVec.Vector.ZModule.addrN u{1}).
  rewrite hz2.
  by rewrite RqVec.Vector.ZModule.addr0.
move=> _; split.
+ by move=> z hz; apply dvec_funi.
move=> _ m hm; split; first exact dvec_fu.
move=> _.
have hstep2 : u{1} - (u{1} + - m) = (u{1} + - u{1}) + m.
+ by rewrite RqVec.Vector.ZModule.opprD RqVec.Vector.ZModule.opprK
    (RqVec.Vector.ZModule.addrA u{1} (- u{1}) m).
rewrite hstep2.
have hz3 : u{1} + - u{1} = zerov by exact (RqVec.Vector.ZModule.addrN u{1}).
rewrite hz3.
by rewrite RqVec.Vector.ZModule.add0r.
qed.
