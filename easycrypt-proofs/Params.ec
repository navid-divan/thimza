require import AllCore Int IntDiv List Distr.
require import Ring.
require PolyReduce Matrix Bigalg.

op qmod : { int | 2 <= qmod } as ge2_qmod.

op phi  : { int | 0 < phi  } as gt0_phi.

op krow : { int | 0 < krow } as gt0_krow.

op ell  : { int | 0 < ell  } as gt0_ell.

clone PolyReduce.PolyReduceZp as Rq with
  op p <= qmod,
  op n <= phi
  proof ge2_p by exact ge2_qmod
  proof gt0_n by exact gt0_phi
  proof *.

type rq = Rq.polyXnD1.

op prevecl (f : int -> rq) = forall i, !(0 <= i < ell) => f i = Rq.zeror.
op prevech (f : int -> rq) = forall i, !(0 <= i < krow) => f i = Rq.zeror.
op prematl (f : int -> int -> rq) =
  forall i j, !(0 <= i < ell /\ 0 <= j < ell) => f i j = Rq.zeror.
op premath (f : int -> int -> rq) =
  forall i j, !(0 <= i < krow /\ 0 <= j < krow) => f i j = Rq.zeror.

subtype vecl as VL = { f : int -> rq | prevecl f }.
realize inhabited. proof. by exists (fun _ => Rq.zeror). qed.

subtype vech as VH = { f : int -> rq | prevech f }.
realize inhabited. proof. by exists (fun _ => Rq.zeror). qed.

subtype matl as ML = { f : int -> int -> rq | prematl f }.
realize inhabited. proof. by exists (fun _ _ => Rq.zeror). qed.

subtype math as MH = { f : int -> int -> rq | premath f }.
realize inhabited. proof. by exists (fun _ _ => Rq.zeror). qed.

op clampl (f : int -> rq) = fun i => if 0 <= i < ell then f i else Rq.zeror.
op clamph (f : int -> rq) = fun i => if 0 <= i < krow then f i else Rq.zeror.
op mclampl (f : int -> int -> rq) =
  fun i j => if 0 <= i < ell /\ 0 <= j < ell then f i j else Rq.zeror.
op mclamph (f : int -> int -> rq) =
  fun i j => if 0 <= i < krow /\ 0 <= j < krow then f i j else Rq.zeror.

(* Clamping fixes vectors of length ell *)
lemma vl_tofunvK : cancel VL.val (fun f => VL.insubd (clampl f)).
proof.
move=> v /=; rewrite -{2}(VL.valKd v); congr.
apply fun_ext => i; rewrite /clampl /=; case (0 <= i < ell) => // hi.
have h := VL.valP v; rewrite /prevecl in h; by rewrite (h i hi).
qed.

(* Clamped functions are vectors of length ell *)
lemma vl_offunvK (f : int -> rq) : VL.val (VL.insubd (clampl f)) = clampl f.
proof. by rewrite VL.insubdK // /prevecl /clampl => i ->. qed.

(* Clamping fixes vectors of length krow *)
lemma vh_tofunvK : cancel VH.val (fun f => VH.insubd (clamph f)).
proof.
move=> v /=; rewrite -{2}(VH.valKd v); congr.
apply fun_ext => i; rewrite /clamph /=; case (0 <= i < krow) => // hi.
have h := VH.valP v; rewrite /prevech in h; by rewrite (h i hi).
qed.

(* Clamped functions are vectors of length krow *)
lemma vh_offunvK (f : int -> rq) : VH.val (VH.insubd (clamph f)) = clamph f.
proof. by rewrite VH.insubdK // /prevech /clamph => i ->. qed.

(* Clamping fixes square matrices of size ell *)
lemma ml_tofunmK : cancel ML.val (fun f => ML.insubd (mclampl f)).
proof.
move=> m /=; rewrite -{2}(ML.valKd m); congr.
apply fun_ext => i; apply fun_ext => j; rewrite /mclampl /=.
case (0 <= i < ell /\ 0 <= j < ell) => // hij.
have h := ML.valP m; rewrite /prematl in h; by rewrite (h i j hij).
qed.

(* Clamped functions are matrices of size ell *)
lemma ml_offunmK (f : int -> int -> rq) : ML.val (ML.insubd (mclampl f)) = mclampl f.
proof. by rewrite ML.insubdK // /prematl /mclampl => i j ->. qed.

(* Clamping fixes square matrices of size krow *)
lemma mh_tofunmK : cancel MH.val (fun f => MH.insubd (mclamph f)).
proof.
move=> m /=; rewrite -{2}(MH.valKd m); congr.
apply fun_ext => i; apply fun_ext => j; rewrite /mclamph /=.
case (0 <= i < krow /\ 0 <= j < krow) => // hij.
have h := MH.valP m; rewrite /premath in h; by rewrite (h i j hij).
qed.

(* Clamped functions are matrices of size krow *)
lemma mh_offunmK (f : int -> int -> rq) : MH.val (MH.insubd (mclamph f)) = mclamph f.
proof. by rewrite MH.insubdK // /premath /mclamph => i j ->. qed.

clone Matrix as RqVec with
  type ZR.t     <- rq,
  op   ZR.zeror <- Rq.zeror,
  op   ZR.oner  <- Rq.oner,
  op   ZR.( + ) <- Rq.( + ),
  op   ZR.([-]) <- Rq.([-]),
  op   ZR.( * ) <- Rq.( * ),
  op   ZR.invr  <- Rq.ComRingDflInv.invr,
  pred ZR.unit  <- Rq.ComRingDflInv.unit,
  op   size     <- ell,
  type vector   <- vecl,
  op   Vector.tofunv <= VL.val,
  op   Vector.offunv <= (fun f => VL.insubd (clampl f)),
  type Matrix.matrix <- matl,
  op   Matrix.tofunm <= ML.val,
  op   Matrix.offunm <= (fun f => ML.insubd (mclampl f))
  proof ZR.addrA     by exact Rq.ComRingDflInv.addrA
  proof ZR.addrC     by exact Rq.ComRingDflInv.addrC
  proof ZR.add0r     by exact Rq.ComRingDflInv.add0r
  proof ZR.addNr     by exact Rq.ComRingDflInv.addNr
  proof ZR.oner_neq0 by exact Rq.ComRingDflInv.oner_neq0
  proof ZR.mulrA     by exact Rq.ComRingDflInv.mulrA
  proof ZR.mulrC     by exact Rq.ComRingDflInv.mulrC
  proof ZR.mul1r     by exact Rq.ComRingDflInv.mul1r
  proof ZR.mulrDl    by exact Rq.ComRingDflInv.mulrDl
  proof ZR.mulVr     by exact Rq.ComRingDflInv.mulVr
  proof ZR.unitP     by exact Rq.ComRingDflInv.unitP
  proof ZR.unitout   by exact Rq.ComRingDflInv.unitout
  proof ge0_size     by smt(gt0_ell)
  proof Vector.tofunv_prevector by exact VL.valP
  proof Vector.tofunvK by exact vl_tofunvK
  proof Vector.offunvK by exact vl_offunvK
  proof Matrix.tofunm_prematrix by exact ML.valP
  proof Matrix.tofunmK by exact ml_tofunmK
  proof Matrix.offunmK by exact ml_offunmK
  proof *.

clone Matrix as RqRow with
  type ZR.t     <- rq,
  op   ZR.zeror <- Rq.zeror,
  op   ZR.oner  <- Rq.oner,
  op   ZR.( + ) <- Rq.( + ),
  op   ZR.([-]) <- Rq.([-]),
  op   ZR.( * ) <- Rq.( * ),
  op   ZR.invr  <- Rq.ComRingDflInv.invr,
  pred ZR.unit  <- Rq.ComRingDflInv.unit,
  op   size     <- krow,
  type vector   <- vech,
  op   Vector.tofunv <= VH.val,
  op   Vector.offunv <= (fun f => VH.insubd (clamph f)),
  type Matrix.matrix <- math,
  op   Matrix.tofunm <= MH.val,
  op   Matrix.offunm <= (fun f => MH.insubd (mclamph f))
  proof ZR.addrA     by exact Rq.ComRingDflInv.addrA
  proof ZR.addrC     by exact Rq.ComRingDflInv.addrC
  proof ZR.add0r     by exact Rq.ComRingDflInv.add0r
  proof ZR.addNr     by exact Rq.ComRingDflInv.addNr
  proof ZR.oner_neq0 by exact Rq.ComRingDflInv.oner_neq0
  proof ZR.mulrA     by exact Rq.ComRingDflInv.mulrA
  proof ZR.mulrC     by exact Rq.ComRingDflInv.mulrC
  proof ZR.mul1r     by exact Rq.ComRingDflInv.mul1r
  proof ZR.mulrDl    by exact Rq.ComRingDflInv.mulrDl
  proof ZR.mulVr     by exact Rq.ComRingDflInv.mulVr
  proof ZR.unitP     by exact Rq.ComRingDflInv.unitP
  proof ZR.unitout   by exact Rq.ComRingDflInv.unitout
  proof ge0_size     by smt(gt0_krow)
  proof Vector.tofunv_prevector by exact VH.valP
  proof Vector.tofunvK by exact vh_tofunvK
  proof Vector.offunvK by exact vh_offunvK
  proof Matrix.tofunm_prematrix by exact MH.valP
  proof Matrix.tofunmK by exact mh_tofunmK
  proof Matrix.offunmK by exact mh_offunmK
  proof *.

import RqVec RqVec.Vector RqVec.Vector.ZModule.

type vec = vecl.

type row = vech.

type mx = matl.

clone Bigalg.BigZModule as BigV with
  type ZM.t     <- vec,
  op   ZM.zeror <- RqVec.Vector.zerov,
  op   ZM.( + ) <- RqVec.Vector.( + ),
  op   ZM.([-]) <- RqVec.Vector.([-])
  proof ZM.addrA by exact RqVec.Vector.ZModule.addrA
  proof ZM.addrC by exact RqVec.Vector.ZModule.addrC
  proof ZM.add0r by exact RqVec.Vector.ZModule.add0r
  proof ZM.addNr by exact RqVec.Vector.ZModule.addNr
  proof *.

op dRq : rq distr = Rq.dpolyXnD1.

op dvec : vec distr = RqVec.Matrix.dvector dRq.

op drow : row distr = RqRow.Matrix.dvector dRq.

(* Uniform ring distribution is lossless *)
lemma dRq_ll : is_lossless dRq.
proof. exact Rq.dpolyXnD1_ll. qed.

(* Uniform ring distribution is full *)
lemma dRq_fu : is_full dRq.
proof. exact Rq.dpolyXnD1_full. qed.

(* Uniform ring distribution is uniform *)
lemma dRq_uni : is_uniform dRq.
proof. exact Rq.dpolyXnD1_uni. qed.

(* Uniform vector distribution is lossless *)
lemma dvec_ll : is_lossless dvec.
proof. by apply RqVec.Matrix.dvector_ll; exact dRq_ll. qed.

(* Uniform vector distribution is full *)
lemma dvec_fu : is_full dvec.
proof. by apply RqVec.Matrix.dvector_fu; exact dRq_fu. qed.

(* Uniform vector distribution is uniform *)
lemma dvec_uni : is_uniform dvec.
proof. by apply RqVec.Matrix.dvector_uni; exact dRq_uni. qed.

(* Uniform vector distribution is functionally uniform *)
lemma dvec_funi : is_funiform dvec.
proof. by apply RqVec.Matrix.dvector_funi; [exact dRq_fu | exact dRq_uni]. qed.

(* Uniform row distribution is lossless *)
lemma drow_ll : is_lossless drow.
proof. by apply RqRow.Matrix.dvector_ll; exact dRq_ll. qed.

(* Uniform row distribution is full *)
lemma drow_fu : is_full drow.
proof. by apply RqRow.Matrix.dvector_fu; exact dRq_fu. qed.

(* Uniform row distribution is functionally uniform *)
lemma drow_funi : is_funiform drow.
proof. by apply RqRow.Matrix.dvector_funi; [exact dRq_fu | exact dRq_uni]. qed.

(* Translation by a fixed vector is injective *)
lemma vaddI (u : vec) : injective (fun v => u + v).
proof. by move=> v w /=; exact RqVec.Vector.ZModule.addrI. qed.

(* Translation by a fixed vector is surjective *)
lemma vaddS (u w : vec) : u + (w - u) = w.
proof. by rewrite RqVec.Vector.ZModule.addrC; exact RqVec.Vector.ZModule.subrK. qed.

(* Translation is inverted by the opposite translation *)
lemma vsubK (u w : vec) : (u + w) - u = w.
proof. by apply (RqVec.Vector.ZModule.addrI u); exact (vaddS u (u+w)). qed.

(* Common left addends cancel *)
lemma vcancelL (x y w : vec) : (w + x) - (w + y) = x - y.
proof.
apply (RqVec.Vector.ZModule.addrI (w + y)).
rewrite (vaddS (w + y) (w + x)).
rewrite -(RqVec.Vector.ZModule.addrA w y (x - y)).
by rewrite (vaddS y x).
qed.

(* Scaling distributes over vector addition *)
lemma vscaleDr (a : rq) (v w : vec) : a ** (v + w) = a ** v + a ** w.
proof. exact RqVec.Vector.scalevDr. qed.

(* Scaling distributes over ring addition *)
lemma vscaleDl (a b : rq) (v : vec) : (Rq.( + ) a b) ** v = a ** v + b ** v.
proof. exact RqVec.Vector.scalevDl. qed.

(* Scaling is compatible with ring multiplication *)
lemma vscaleA (a b : rq) (v : vec) : (Rq.( * ) a b) ** v = a ** (b ** v).
proof. exact RqVec.Vector.scalevA. qed.

(* Zero scalar yields the zero vector *)
lemma vscale0 (v : vec) : Rq.zeror ** v = zerov.
proof.
apply RqVec.Vector.eq_vectorP => i hi.
by rewrite RqVec.Vector.scalevE RqVec.Vector.offunCE // Rq.ComRingDflInv.mul0r.
qed.

(* Scaling the zero vector gives zero *)
lemma vscaler0 (a : rq) : a ** zerov = zerov.
proof.
apply RqVec.Vector.eq_vectorP => i hi.
by rewrite RqVec.Vector.scalevE RqVec.Vector.offunCE // Rq.ComRingDflInv.mulr0.
qed.

(* Unit scalar acts as identity *)
lemma vscale1 (v : vec) : Rq.oner ** v = v.
proof.
apply RqVec.Vector.eq_vectorP => i hi.
by rewrite RqVec.Vector.scalevE Rq.ComRingDflInv.mul1r.
qed.

(* Scaling distributes over vector subtraction *)
lemma vscaleN (a : rq) (v : vec) : (Rq.([-]) a) ** v = - (a ** v).
proof.
apply RqVec.Vector.eq_vectorP => i hi.
by rewrite RqVec.Vector.offunN !RqVec.Vector.scalevE Rq.ComRingDflInv.mulNr.
qed.

(* Unit scaling is inverted by its inverse *)
lemma vscaleK (a : rq) (v : vec) :
  Rq.ComRingDflInv.unit a => a ** (Rq.ComRingDflInv.invr a ** v) = v.
proof. by move=> hu; rewrite -vscaleA Rq.ComRingDflInv.mulrV // vscale1. qed.

(* Inverse scaling is inverted by unit *)
lemma vscaleKV (a : rq) (v : vec) :
  Rq.ComRingDflInv.unit a => Rq.ComRingDflInv.invr a ** (a ** v) = v.
proof. by move=> hu; rewrite -vscaleA Rq.ComRingDflInv.mulVr // vscale1. qed.

op vsum (xs : vec list) : vec = foldr RqVec.Vector.( + ) zerov xs.

op vmap (f : 'a -> vec) (L : 'a list) : vec = vsum (map f L).

op rsum (xs : rq list) : rq = foldr Rq.( + ) Rq.zeror xs.

op rmap (f : 'a -> rq) (L : 'a list) : rq = rsum (map f L).

(* Empty vector sum is zero *)
lemma vmap_nil (f : 'a -> vec) : vmap f [] = zerov.
proof. by rewrite /vmap /vsum. qed.

(* Vector sum peels off its head *)
lemma vmap_cons (f : 'a -> vec) (a : 'a) (L : 'a list) :
  vmap f (a :: L) = f a + vmap f L.
proof. by rewrite /vmap /vsum. qed.

(* Empty ring sum is zero *)
lemma rmap_nil (f : 'a -> rq) : rmap f [] = Rq.zeror.
proof. by rewrite /rmap /rsum. qed.

(* Ring sum peels off its head *)
lemma rmap_cons (f : 'a -> rq) (a : 'a) (L : 'a list) :
  rmap f (a :: L) = Rq.( + ) (f a) (rmap f L).
proof. by rewrite /rmap /rsum. qed.

(* Pointwise equal families have equal vector sums *)
lemma vmap_eq (f g : 'a -> vec) (L : 'a list) :
  (forall x, x \in L => f x = g x) => vmap f L = vmap g L.
proof.
elim L => [| a L ih] h; first by rewrite !vmap_nil.
rewrite !vmap_cons h 1:mem_head ih // => x hx.
by apply h; rewrite in_cons hx.
qed.

(* Pointwise equal families have equal ring sums *)
lemma rmap_eq (f g : 'a -> rq) (L : 'a list) :
  (forall x, x \in L => f x = g x) => rmap f L = rmap g L.
proof.
elim L => [| a L ih] h; first by rewrite !rmap_nil.
rewrite !rmap_cons h 1:mem_head ih // => x hx.
by apply h; rewrite in_cons hx.
qed.

(* Vector sum of zeros is zero *)
lemma vmap0 (L : 'a list) : vmap (fun _ => zerov) L = zerov.
proof.
elim L => [| a L ih]; first exact vmap_nil.
rewrite vmap_cons ih /=; exact RqVec.Vector.ZModule.add0r.
qed.

(* Ring sum of zeros is zero *)
lemma rmap0 (L : 'a list) : rmap (fun _ => Rq.zeror) L = Rq.zeror.
proof.
elim L => [| a L ih]; first exact rmap_nil.
rewrite rmap_cons ih /=; exact Rq.ComRingDflInv.add0r.
qed.

(* Vector sums split over pointwise addition *)
lemma vmap_split (f g : 'a -> vec) (L : 'a list) :
  vmap (fun x => f x + g x) L = vmap f L + vmap g L.
proof.
elim L => [| a L ih].
+ by rewrite !vmap_nil RqVec.Vector.ZModule.add0r.
rewrite !vmap_cons ih /=; exact RqVec.Vector.ZModule.addrACA.
qed.

(* Ring sums split over pointwise addition *)
lemma rmap_split (f g : 'a -> rq) (L : 'a list) :
  rmap (fun x => Rq.( + ) (f x) (g x)) L = Rq.( + ) (rmap f L) (rmap g L).
proof.
elim L => [| a L ih].
+ by rewrite !rmap_nil Rq.ComRingDflInv.add0r.
rewrite !rmap_cons ih /=; exact Rq.ComRingDflInv.addrACA.
qed.

(* Linear maps commute with ring scaling *)
lemma mulmxvZ (m : mx) (a : rq) (v : vec) : m *^ (a ** v) = a ** (m *^ v).
proof.
apply RqVec.Vector.eq_vectorP => i hi.
rewrite RqVec.Matrix.mulmxvE RqVec.Vector.scalevE RqVec.Matrix.mulmxvE.
rewrite RqVec.Big.BAdd.mulr_sumr.
apply RqVec.Big.BAdd.eq_bigr => j _ /=.
by rewrite RqVec.Vector.scalevE Rq.ComRingDflInv.mulrCA.
qed.

(* Linear maps commute with finite vector sums *)
lemma mulmxv_vmap (m : mx) (f : 'a -> vec) (L : 'a list) :
  m *^ (vmap f L) = vmap (fun x => m *^ f x) L.
proof.
elim L => [| a L ih]; first by rewrite !vmap_nil RqVec.Matrix.mulmxv0.
by rewrite !vmap_cons RqVec.Matrix.mulmxvDr ih.
qed.

(* Scaling commutes with finite vector sums *)
lemma scalev_vmap (a : rq) (f : 'b -> vec) (L : 'b list) :
  a ** (vmap f L) = vmap (fun x => a ** f x) L.
proof.
elim L => [| x L ih]; first by rewrite !vmap_nil vscaler0.
by rewrite !vmap_cons vscaleDr ih.
qed.

(* Ring sums factor over a vector *)
lemma rmap_scale (f : 'a -> rq) (L : 'a list) (v : vec) :
  (rmap f L) ** v = vmap (fun x => f x ** v) L.
proof.
elim L => [| x L ih]; first by rewrite rmap_nil vmap_nil vscale0.
by rewrite rmap_cons vmap_cons vscaleDl ih.
qed.

(* Negation is scaling by minus one *)
lemma vneg_scale (v : vec) : - v = (Rq.([-]) Rq.oner) ** v.
proof. by rewrite vscaleN vscale1. qed.

(* Linear maps commute with vector negation *)
lemma mulmxvN (m : mx) (v : vec) : m *^ (- v) = - (m *^ v).
proof. by rewrite vneg_scale mulmxvZ vscaleN vscale1. qed.

(* Linear maps commute with subtraction *)
lemma mulmxvB (m : mx) (v w : vec) : m *^ (v - w) = m *^ v - m *^ w.
proof. by rewrite RqVec.Matrix.mulmxvDr mulmxvN. qed.

type mat = int -> vec.

op mulA (a : mat) (v : vec) : row =
  RqRow.Vector.offunv (fun i => RqVec.Vector.dotp (a i) v).

op rowZ (c : rq) (x : row) : row = RqRow.Vector.scalev c x.

(* Inner products are linear when scaled *)
lemma dotpZr (u v : vec) (c : rq) :
  RqVec.Vector.dotp u (c ** v) = Rq.( * ) c (RqVec.Vector.dotp u v).
proof.
rewrite /RqVec.Vector.dotp RqVec.Big.BAdd.mulr_sumr.
apply RqVec.Big.BAdd.eq_bigr => j _ /=.
by rewrite RqVec.Vector.scalevE Rq.ComRingDflInv.mulrCA.
qed.

(* The matrix product is additive *)
lemma mulAD (a : mat) (v w : vec) :
  mulA a (v + w) = RqRow.Vector.( + ) (mulA a v) (mulA a w).
proof.
apply RqRow.Vector.eq_vectorP => i hi.
by rewrite RqRow.Vector.offunD !RqRow.Vector.offunvE //= RqVec.Vector.dotpDr.
qed.

(* The matrix product commutes with ring scaling *)
lemma mulAZ (a : mat) (c : rq) (v : vec) :
  mulA a (c ** v) = rowZ c (mulA a v).
proof.
apply RqRow.Vector.eq_vectorP => i hi.
by rewrite /rowZ RqRow.Vector.scalevE !RqRow.Vector.offunvE //= dotpZr.
qed.

(* The matrix product maps zero to zero *)
lemma mulA0 (a : mat) : mulA a zerov = RqRow.Vector.zerov.
proof.
have h := mulAD a zerov zerov.
rewrite RqVec.Vector.ZModule.addr0 in h.
have := RqRow.Vector.ZModule.addrI (mulA a zerov) (mulA a zerov) RqRow.Vector.zerov.
by rewrite RqRow.Vector.ZModule.addr0 -h.
qed.

(* The matrix product commutes with negation *)
lemma mulAN (a : mat) (v : vec) : mulA a (- v) = RqRow.Vector.([-]) (mulA a v).
proof.
apply (RqRow.Vector.ZModule.addrI (mulA a v)).
by rewrite -mulAD RqVec.Vector.ZModule.addrN mulA0 RqRow.Vector.ZModule.addrN.
qed.

(* The matrix product commutes with subtraction *)
lemma mulAB (a : mat) (v w : vec) :
  mulA a (v - w) = RqRow.Vector.( + ) (mulA a v) (RqRow.Vector.([-]) (mulA a w)).
proof. by rewrite mulAD mulAN. qed.

op rsumv (xs : row list) : row = foldr RqRow.Vector.( + ) RqRow.Vector.zerov xs.

op rowmap (f : 'a -> row) (L : 'a list) : row = rsumv (map f L).

(* Empty row sum is zero *)
lemma rowmap_nil (f : 'a -> row) : rowmap f [] = RqRow.Vector.zerov.
proof. by rewrite /rowmap /rsumv. qed.

(* Row sum peels off its head *)
lemma rowmap_cons (f : 'a -> row) (x : 'a) (L : 'a list) :
  rowmap f (x :: L) = RqRow.Vector.( + ) (f x) (rowmap f L).
proof. by rewrite /rowmap /rsumv. qed.

(* The matrix product commutes with finite sums *)
lemma mulA_vmap (a : mat) (f : 'a -> vec) (L : 'a list) :
  mulA a (vmap f L) = rowmap (fun x => mulA a (f x)) L.
proof.
elim L => [| x L ih]; first by rewrite vmap_nil rowmap_nil mulA0.
by rewrite vmap_cons rowmap_cons mulAD ih.
qed.

(* Row scaling distributes over row addition *)
lemma rowZD (c : rq) (x y : row) :
  rowZ c (RqRow.Vector.( + ) x y) = RqRow.Vector.( + ) (rowZ c x) (rowZ c y).
proof. exact RqRow.Vector.scalevDr. qed.
