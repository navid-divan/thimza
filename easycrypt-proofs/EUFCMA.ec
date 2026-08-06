require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions Protocol Combine Verify Hierarchy.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Non threshold signing procedure *)
module PlainSign = {
  proc sign(t : vec, mu : msg, s0 : vec) : sig = {
    var r, er, w, wr, z, h : vec;
    var c : rq;
    r  <$ dvec;
    er <$ dvec;
    w  <- mA *^ r + er;
    wr <- rndw w;
    c  <- Hchal t wr mu;
    z  <- c ** s0 + r;
    h  <- wr - rndw (mA *^ z - c ** liftt t);
    return (c, z, h);
  }
}.

(* Threshold protocol on a singleton committee *)
module SingletonSign = {
  proc sign(t : vec, mu : msg, s0 : vec, i : int) : sig = {
    var r, er, w, wr, z, h : vec;
    var c : rq;
    r  <$ dvec;
    er <$ dvec;
    w  <- mA *^ r + er;
    wr <- rndw w;
    c  <- Hchal t wr mu;
    z  <- zcomb (singleton i)
            (fun j => (Rq.( * ) c (lamSingle j)) ** shr s0 (fun _ => zerov) j
                      + (if j = i then r else zerov) + mask (singleton i) witness j);
    h  <- wr - rndw (mA *^ z - c ** liftt t);
    return (c, z, h);
  }
}.

(* Singleton protocol matches plain signing *)
equiv singleton_is_plain (i0 : int) :
  SingletonSign.sign ~ PlainSign.sign :
    t{1} = t{2} /\ mu{1} = mu{2} /\ s0{1} = s0{2} /\ i{1} = i0 /\ tthr = 1
    ==> ={res}.
proof.
proc.
seq 2 2 : (t{1} = t{2} /\ mu{1} = mu{2} /\ s0{1} = s0{2} /\ i{1} = i0
           /\ tthr = 1 /\ r{1} = r{2} /\ er{1} = er{2}).
+ by auto.
wp; skip => &1 &2 [#] ht hmu hs0 hi htt hr her.
have e1 : shr s0{1} (fun _ => zerov) i{1} = s0{1}
  by exact (shr_share0 s0{1} (fun _ => zerov) i{1} htt).
have e2 : mask (singleton i{1}) witness i{1} = zerov
  by exact (singleton_mask_zero witness i{1}).
have ez : zcomb (singleton i{1})
    (fun j => (Rq.( * ) (Hchal t{1} (rndw (mA *^ r{1} + er{1})) mu{1}) (lamSingle j))
              ** shr s0{1} (fun _ => zerov) j
              + (if j = i{1} then r{1} else zerov) + mask (singleton i{1}) witness j)
    = (Hchal t{1} (rndw (mA *^ r{1} + er{1})) mu{1}) ** s0{1} + r{1}.
+ rewrite /zcomb /singleton vmap_cons vmap_nil /= e1 e2 /lamSingle /=.
  by smt(RqVec.Vector.ZModule.addr0).
by smt().
qed.
