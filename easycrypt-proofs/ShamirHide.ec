require import AllCore Int List Distr DList StdBigop.
require import Params Types BigOps PolyList Lagrange Sharing ChainBase.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The functions on which the sharing polynomial distribution puts mass *)
op suppc (p : int -> vec) : bool = forall u, !(1 <= u < tthr) => p u = zerov.

op fpoly (l : vec list) : int -> vec =
  fun u => if 1 <= u < tthr then nth zerov l (u - 1) else zerov.

op gpoly (p : int -> vec) : vec list = mkseq (fun i => p (i + 1)) (tthr - 1).

(* The sharing polynomial is the image of a list of coefficients *)
lemma dpoly_def : dpoly = dmap (dlist dvec (tthr - 1)) fpoly.
proof. by rewrite /dpoly /fpoly. qed.

(* Coefficients determine the polynomial *)
lemma fpoly_gpoly (p : int -> vec) : suppc p => fpoly (gpoly p) = p.
proof.
move=> hp; apply fun_ext => u; rewrite /fpoly /gpoly.
case: (1 <= u < tthr) => hu.
+ by rewrite nth_mkseq /=; smt().
by rewrite hp.
qed.

(* The polynomial determines its coefficients *)
lemma gpoly_fpoly (l : vec list) : size l = tthr - 1 => gpoly (fpoly l) = l.
proof.
move=> hs; rewrite /gpoly /fpoly.
apply (eq_from_nth zerov); first by rewrite size_mkseq; smt(thr_range).
move=> i; rewrite size_mkseq => hi.
rewrite nth_mkseq /=; first smt().
by have -> /= : 1 <= i + 1 < tthr by smt().
qed.

(* The support of the sharing polynomial *)
lemma dpoly_supp (p : int -> vec) : p \in dpoly <=> suppc p.
proof.
rewrite dpoly_def supp_dmap; split.
+ by move=> [l] [hl ->] u hu; rewrite /fpoly hu.
move=> hp; exists (gpoly p); split; last by rewrite fpoly_gpoly.
rewrite supp_dlist; first smt(thr_range).
split; first by rewrite /gpoly size_mkseq; smt(thr_range).
by apply/allP => x _; apply dvec_fu.
qed.

(* Lists of vectors of the same size are equally likely *)
lemma dlist_mu1_eq (l l' : vec list) :
  size l = size l' => mu1 (dlist dvec (tthr - 1)) l = mu1 (dlist dvec (tthr - 1)) l'.
proof.
move=> hs; rewrite !dlist1E; 1,2: smt(thr_range).
rewrite hs; case: (tthr - 1 = size l') => // _.
have e : forall (m : vec list), Bigreal.BRM.big predT (fun x => mu1 dvec x) m
                               = Bigreal.BRM.big predT (fun _ => mu1 dvec zerov) m.
+ move=> m; apply Bigreal.BRM.eq_bigr => x _ /=.
  by apply dvec_funi.
by rewrite !e !Bigreal.BRM.big_const !count_predT hs.
qed.

(* Every polynomial of the support is equally likely *)
lemma dpoly_mu1 (p q : int -> vec) : suppc p => suppc q => mu1 dpoly p = mu1 dpoly q.
proof.
move=> hp hq.
have e : forall (r : int -> vec), suppc r =>
           mu1 dpoly r = mu1 (dlist dvec (tthr - 1)) (gpoly r).
+ move=> r hr.
  have h1 : fpoly (gpoly r) = r by apply fpoly_gpoly.
  have h2 : forall l, l \in dlist dvec (tthr - 1) => fpoly l = r => l = gpoly r.
  - move=> l hl <-; rewrite gpoly_fpoly //.
    by apply (supp_dlist_size dvec (tthr - 1) l _ hl); smt(thr_range).
  by rewrite dpoly_def (in_dmap1E_can _ _ gpoly r h1 h2).
rewrite (e p hp) (e q hq); apply dlist_mu1_eq.
by rewrite /gpoly !size_mkseq.
qed.

(* The sharing polynomial distribution is lossless *)
lemma dpoly_ll : is_lossless dpoly.
proof. by rewrite dpoly_def; apply dmap_ll; apply dlist_ll; exact dvec_ll. qed.

(* ---------- a polynomial with constant term one vanishing at the corrupt nodes ---------- *)

op npol (C : int list) : poly = nodepoly (map alpha C).

op qpol (C : int list) : poly =
  pscale (Rq.ComRingDflInv.invr (peval (npol C) Rq.zeror)) (npol C).

op qco (C : int list) (u : int) : rq = nth Rq.zeror (qpol C) u.

(* The node polynomial at zero is a unit when the nodes are *)
lemma npol0_unit (C : int list) :
  (forall j, j \in C => Rq.ComRingDflInv.unit (alpha j)) =>
  Rq.ComRingDflInv.unit (peval (npol C) Rq.zeror).
proof.
move=> hu; rewrite /npol peval_nodepoly; apply rprod_unit => a.
rewrite mapP => -[j] [hj ->] /=.
rewrite Rq.ComRingDflInv.add0r Rq.ComRingDflInv.unitrN.
exact (hu j hj).
qed.

(* The polynomial vanishes at the corrupt nodes *)
lemma qpol_root (C : int list) (j : int) : j \in C => peval (qpol C) (alpha j) = Rq.zeror.
proof.
move=> hj; rewrite /qpol peval_scale /npol.
have -> : peval (nodepoly (map alpha C)) (alpha j) = Rq.zeror.
+ by apply nodepoly_root; apply map_f.
smt(Rq.ComRingDflInv.mulr0).
qed.

(* The polynomial has constant term one *)
lemma qpol_zero (C : int list) :
  (forall j, j \in C => Rq.ComRingDflInv.unit (alpha j)) =>
  peval (qpol C) Rq.zeror = Rq.oner.
proof.
move=> hu; rewrite /qpol peval_scale.
have hn := npol0_unit C hu.
have := Rq.ComRingDflInv.mulVr (peval (npol C) Rq.zeror) hn.
smt().
qed.

(* The polynomial has one coefficient more than the corrupt set *)
lemma size_qpol (C : int list) : size (qpol C) = size C + 1.
proof. by rewrite /qpol /pscale size_map /npol size_nodepoly size_map. qed.

(* The constant coefficient is the value at zero *)
lemma nth0_peval (f : poly) : nth Rq.zeror f 0 = peval f Rq.zeror.
proof.
case: f => [| c g] //=.
smt(Rq.ComRingDflInv.mul0r Rq.ComRingDflInv.addr0).
qed.

(* Ring sums over a shifted range *)
lemma rmap_map (f : 'b -> rq) (g : 'a -> 'b) (L : 'a list) :
  rmap f (map g L) = rmap (fun x => f (g x)) L.
proof. by rewrite /rmap -map_comp. qed.

(* Evaluation unfolds in the operations of the ring *)
lemma peval_nilR (x : rq) : peval [] x = Rq.zeror.
proof. done. qed.

lemma peval_consR (c : rq) (g : poly) (x : rq) :
  peval (c :: g) x = Rq.( + ) c (Rq.( * ) x (peval g x)).
proof. done. qed.

(* Evaluation is the sum of the coefficients times the powers *)
lemma peval_coef (f : poly) (x : rq) (n : int) :
  size f <= n =>
  peval f x = rmap (fun u => Rq.( * ) (nth Rq.zeror f u) (Rq.ComRingDflInv.exp x u)) (range 0 n).
proof.
elim: f n => [| c g ih] n hn.
+ rewrite peval_nilR.
  have -> : rmap (fun u => Rq.( * ) (nth Rq.zeror [] u) (Rq.ComRingDflInv.exp x u)) (range 0 n)
          = rmap (fun _ => Rq.zeror) (range 0 n).
  - by apply rmap_eq => u _ /=; rewrite Rq.ComRingDflInv.mul0r.
  by rewrite rmap0.
have hn1 : 0 < n by smt(size_ge0).
have er : range 1 n = map (Int.( + ) 1) (range 0 (n - 1)).
+ by have := range_addl 0 n 1.
rewrite peval_consR (range_ltn 0 n hn1) rmap_cons /=.
rewrite Rq.ComRingDflInv.expr0 Rq.ComRingDflInv.mulr1.
congr.
rewrite er rmap_map /=.
rewrite (ih (n - 1)); first smt().
rewrite rmap_mull; apply rmap_eq => v hv /=.
have hv0 : 0 <= v by smt(mem_range).
have -> /= : 1 + v <> 0 by smt().
have -> : 1 + v = v + 1 by ring.
by rewrite Rq.ComRingDflInv.exprS // Rq.ComRingDflInv.mulrCA.
qed.

(* A sum that completes one to zero is minus one *)
lemma ring_neg1 (R : rq) : Rq.zeror = Rq.( + ) Rq.oner R => R = Rq.([-]) Rq.oner.
proof.
move=> h.
have h1 := Rq.ComRingDflInv.addKr Rq.oner R.
have h2 := Rq.ComRingDflInv.addr0 (Rq.([-]) Rq.oner).
smt().
qed.

(* The higher coefficients sum to minus one at a corrupt node *)
lemma qco_sum (C : int list) (j : int) :
  (forall k, k \in C => Rq.ComRingDflInv.unit (alpha k)) =>
  size C <= tthr - 1 => j \in C =>
  rmap (fun u => Rq.( * ) (qco C u) (Rq.ComRingDflInv.exp (alpha j) u)) (range 1 tthr)
  = Rq.([-]) Rq.oner.
proof.
move=> hu hs hj.
have h := peval_coef (qpol C) (alpha j) tthr _.
+ by rewrite size_qpol; smt().
rewrite (qpol_root C j hj) (range_ltn 0 tthr _) in h; first smt(thr_range).
rewrite rmap_cons /= Rq.ComRingDflInv.expr0 Rq.ComRingDflInv.mulr1 nth0_peval in h.
rewrite (qpol_zero C hu) in h.
have -> : rmap (fun u => Rq.( * ) (qco C u) (Rq.ComRingDflInv.exp (alpha j) u)) (range 1 tthr)
        = rmap (fun u => Rq.( * ) (nth Rq.zeror (qpol C) u) (Rq.ComRingDflInv.exp (alpha j) u))
               (range 1 tthr) by done.
by apply ring_neg1.
qed.

(* ---------- shifting the polynomial by the secret ---------- *)

op dsh (s : vec) (C : int list) (u : int) : vec =
  if 1 <= u < tthr then qco C u ** s else zerov.

op shiftp (s : vec) (C : int list) (p : int -> vec) : int -> vec = fun u => p u - dsh s C u.

op unshiftp (s : vec) (C : int list) (p : int -> vec) : int -> vec = fun u => p u + dsh s C u.

(* The shift is invertible *)
lemma shiftpK (s : vec) (C : int list) (p : int -> vec) : unshiftp s C (shiftp s C p) = p.
proof. by apply fun_ext => u; rewrite /unshiftp /shiftp /= RqVec.Vector.ZModule.subrK. qed.

lemma unshiftpK (s : vec) (C : int list) (p : int -> vec) : shiftp s C (unshiftp s C p) = p.
proof. by apply fun_ext => u; rewrite /unshiftp /shiftp /= RqVec.Vector.ZModule.addrK. qed.

(* The shift stays in the support *)
lemma shiftp_supp (s : vec) (C : int list) (p : int -> vec) : suppc p => suppc (shiftp s C p).
proof.
move=> hp u hu; rewrite /shiftp /dsh /= hu /= hp //.
by rewrite RqVec.Vector.ZModule.subrr.
qed.

lemma unshiftp_supp (s : vec) (C : int list) (p : int -> vec) : suppc p => suppc (unshiftp s C p).
proof.
move=> hp u hu; rewrite /unshiftp /dsh /= hu /= hp //.
by rewrite RqVec.Vector.ZModule.addr0.
qed.

(* Vector sums of differences *)
lemma vmap_sub (f g : 'a -> vec) (L : 'a list) :
  vmap (fun x => f x - g x) L = vmap f L - vmap g L.
proof.
elim: L => [| a L ih].
+ by rewrite !vmap_nil RqVec.Vector.ZModule.subrr.
rewrite !vmap_cons ih /=.
by rewrite RqVec.Vector.ZModule.opprD RqVec.Vector.ZModule.addrACA.
qed.

(* Scaling commutes with negation of the vector *)
lemma vscalevN (a : rq) (v : vec) : a ** (- v) = - (a ** v).
proof.
apply (RqVec.Vector.ZModule.addrI (a ** v)).
rewrite -vscaleDr !RqVec.Vector.ZModule.addrN.
exact vscaler0.
qed.

(* The corrupt shares of the shifted polynomial do not depend on the secret *)
lemma shr_shift (s : vec) (C : int list) (p : int -> vec) (j : int) :
  (forall k, k \in C => Rq.ComRingDflInv.unit (alpha k)) =>
  size C <= tthr - 1 => j \in C =>
  shr zerov (shiftp s C p) j = shr s p j.
proof.
move=> hu hs hj; rewrite /shr RqVec.Vector.ZModule.add0r.
have -> : vmap (fun u => ipow (alpha j) u ** shiftp s C p u) (range 1 tthr)
        = vmap (fun u => ipow (alpha j) u ** p u
                         - (Rq.( * ) (qco C u) (ipow (alpha j) u)) ** s) (range 1 tthr).
+ apply vmap_eq => u hu' /=.
  have hr : 1 <= u < tthr by smt(mem_range).
  rewrite /shiftp /dsh hr.
  rewrite (_ : (if true then qco C u ** s else zerov) = qco C u ** s) 1://.
  rewrite vscaleDr vscalevN -vscaleA.
  by rewrite (Rq.ComRingDflInv.mulrC (ipow (alpha j) u) (qco C u)).
rewrite vmap_sub -rmap_scale.
have -> : rmap (fun u => Rq.( * ) (qco C u) (ipow (alpha j) u)) (range 1 tthr)
        = Rq.([-]) Rq.oner by rewrite /ipow; exact (qco_sum C j hu hs hj).
rewrite vscaleN vscale1 RqVec.Vector.ZModule.opprK.
by rewrite RqVec.Vector.ZModule.addrC.
qed.
