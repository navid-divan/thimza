require import AllCore Int List Distr.
require import Params Types.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

op ipow (x : rq) (u : int) : rq = Rq.ComRingDflInv.exp x u.

(* A Shamir share of the secret *)
op shr (s : vec) (p : int -> vec) (i : int) : vec =
  s + vmap (fun u => (ipow (alpha i) u) ** p u) (range 1 tthr).

(* Lagrange reconstruction coefficient predicate *)
pred recons (T : committee) (lam : int -> rq) =
  rmap lam T = Rq.oner /\
  forall u, 1 <= u < tthr =>
    rmap (fun i => Rq.( * ) (lam i) (ipow (alpha i) u)) T = Rq.zeror.

(* Double vector sums may be exchanged *)
lemma vmap_exchange (f : 'a -> 'b -> vec) (L1 : 'a list) (L2 : 'b list) :
  vmap (fun x => vmap (f x) L2) L1 = vmap (fun y => vmap (fun x => f x y) L1) L2.
proof.
elim L1 => [| a L1 ih].
+ rewrite vmap_nil.
  have -> : vmap (fun y => vmap (fun (x : 'a) => f x y) []) L2
          = vmap (fun (_ : 'b) => zerov) L2.
  - by apply vmap_eq => y _ /=; exact vmap_nil.
  by rewrite vmap0.
rewrite vmap_cons /= ih.
have -> : vmap (fun y => vmap (fun x => f x y) (a :: L1)) L2
        = vmap (fun y => f a y + vmap (fun x => f x y) L1) L2.
+ by apply vmap_eq => y _ /=; rewrite vmap_cons.
rewrite vmap_split.
have -> : vmap (fun y => f a y) L2 = vmap (f a) L2.
+ by apply vmap_eq.
done.
qed.

(* Lagrange combination of shares recovers the secret *)
lemma shr_recons (T : committee) (lam : int -> rq) (s : vec) (p : int -> vec) :
  recons T lam => vmap (fun i => lam i ** shr s p i) T = s.
proof.
move=> [h0 h1].
have -> : vmap (fun i => lam i ** shr s p i) T
        = vmap (fun i => lam i ** s + lam i ** (vmap (fun u => (ipow (alpha i) u) ** p u) (range 1 tthr))) T.
+ by apply vmap_eq => i _ /=; rewrite /shr vscaleDr.
rewrite vmap_split.
have -> : vmap (fun i => lam i ** s) T = (rmap lam T) ** s.
+ by rewrite rmap_scale.
rewrite h0 vscale1.
have -> : vmap (fun i => lam i ** (vmap (fun u => (ipow (alpha i) u) ** p u) (range 1 tthr))) T
        = vmap (fun i => vmap (fun u => (Rq.( * ) (lam i) (ipow (alpha i) u)) ** p u) (range 1 tthr)) T.
+ apply vmap_eq => i _ /=; rewrite scalev_vmap.
  by apply vmap_eq => u _ /=; rewrite vscaleA.
rewrite vmap_exchange.
have -> : vmap (fun (u : int) => vmap (fun (i : int) => (Rq.( * ) (lam i) (ipow (alpha i) u)) ** p u) T) (range 1 tthr)
        = vmap (fun (_ : int) => zerov) (range 1 tthr).
+ apply vmap_eq => u hu /=.
  have hu' : 1 <= u < tthr by smt(mem_range).
  by rewrite -rmap_scale (h1 u hu') vscale0.
rewrite vmap0; exact RqVec.Vector.ZModule.addr0.
qed.

(* Reconstruction coefficients agree on shares *)
lemma recons_unique (T : committee) (lam1 lam2 : int -> rq) (s : vec) (p : int -> vec) :
  recons T lam1 => recons T lam2 =>
  vmap (fun i => lam1 i ** shr s p i) T = vmap (fun i => lam2 i ** shr s p i) T.
proof. by move=> h1 h2; rewrite (shr_recons T lam1 s p h1) (shr_recons T lam2 s p h2). qed.

(* One point committees use unit coefficients *)
lemma recons_single (i : int) : tthr = 1 => recons [i] (fun _ => Rq.oner).
proof.
move=> ht; split.
+ by rewrite /rmap /rsum /= Rq.ComRingDflInv.addr0.
by move=> u hu; smt().
qed.

(* Threshold one shares the secret directly *)
lemma shr_share0 (s : vec) (p : int -> vec) (i : int) : tthr = 1 => shr s p i = s.
proof.
move=> ht; rewrite /shr ht.
have -> : range 1 1 = [] by rewrite range_geq.
by rewrite vmap_nil RqVec.Vector.ZModule.addr0.
qed.

module SHR = {
  proc share(s : vec, a : rq) : vec = {
    var p1 : vec;
    p1 <$ dvec;
    return s + a ** p1;
  }

  proc uniform() : vec = {
    var z : vec;
    z <$ dvec;
    return z;
  }
}.

(* A single share hides the secret perfectly *)
equiv shr_hiding : SHR.share ~ SHR.uniform :
  Rq.ComRingDflInv.unit a{1} ==> ={res}.
proof.
proc.
rnd (fun (v : vec) => s{1} + a{1} ** v)
    (fun (w : vec) => Rq.ComRingDflInv.invr a{1} ** (w - s{1})).
skip => &1 &2 hu /=; split.
+ by move=> w hw; rewrite vscaleK // vaddS.
move=> _; split.
+ by move=> w hw; apply dvec_funi.
move=> _ v hv; split; first exact dvec_fu.
by move=> _; rewrite vsubK vscaleKV.
qed.

