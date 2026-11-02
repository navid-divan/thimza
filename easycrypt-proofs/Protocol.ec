require import AllCore Int List Distr.
require import Params Types BigOps Sharing ShamirLagrange Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op mA : mat.

op rndc : row -> row.

op liftc : row -> row.

op rndw : row -> row.

op liftt : row -> row.

op inbnd : vec -> row -> bool.

type sig = rq * vec * row.

type h0fun = row -> msg -> int -> row -> cmt.

type h1fun = row -> msg -> committee -> cmt list -> view.

type hcfun = row -> row -> msg -> rq.

type token = {
  tk_i     : int;
  tk_msg   : msg;
  tk_r     : vec;
  tk_e     : row;
  tk_wbar  : row;
  tk_cmt   : cmt;
  tk_phase : int;
  tk_T     : committee;
  tk_dig   : view;
}.

op commit (r : vec) (e : row) : row = mulA mA r + e.

op sign1 (h0 : h0fun) (vk : row) (i : int) (mu : msg) (r : vec) (e : row) : token =
  {| tk_i = i; tk_msg = mu; tk_r = r; tk_e = e; tk_wbar = rndc (commit r e);
     tk_cmt = h0 vk mu i (rndc (commit r e)); tk_phase = 1; tk_T = [];
     tk_dig = witness |}.

op inrange (T : committee) : bool = all (fun j => 1 <= j <= nmax) T.

op own_cmt (tok : token) (T : committee) (cs : cmt list) : bool =
  nth witness cs (index tok.`tk_i T) = tok.`tk_cmt.

op ok2 (tok : token) (T : committee) (cs : cmt list) : bool =
  tok.`tk_phase = 1 /\ wf_committee T /\ inrange T /\ tok.`tk_i \in T
  /\ size cs = size T /\ own_cmt tok T cs.

op sign2 (h1 : h1fun) (vk : row) (tok : token) (T : committee) (cs : cmt list)
  : (token * row) option =
  if ok2 tok T cs
  then Some ({| tok with tk_phase = 2; tk_T = T; tk_dig = h1 vk tok.`tk_msg T cs |},
             tok.`tk_wbar)
  else None.

op opens_ok (h0 : h0fun) (vk : row) (mu : msg) (T : committee) (cs : cmt list)
            (ws : row list) : bool =
  size cs = size T /\ size ws = size T /\
  all (fun (p : int * (cmt * row)) => h0 vk mu p.`1 p.`2.`2 = p.`2.`1)
      (zip T (zip cs ws)).

op ok3 (h0 : h0fun) (h1 : h1fun) (vk : row) (tok : token) (T : committee)
       (cs : cmt list) (ws : row list) : bool =
  tok.`tk_phase = 2 /\ T = tok.`tk_T /\ h1 vk tok.`tk_msg T cs = tok.`tk_dig
  /\ opens_ok h0 vk tok.`tk_msg T cs ws
  /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar.

op aggw (ws : row list) : row = rndw (rowmap liftc ws).

op chal (hc : hcfun) (vk : row) (mu : msg) (ws : row list) : rq = hc vk (aggw ws) mu.

op resp (hc : hcfun) (vk : row) (sk : vec) (tok : token) (T : committee)
        (ws : row list) : vec =
  (Rq.( * ) (chal hc vk tok.`tk_msg ws) (lam_of T tok.`tk_i)) ** sk
  + tok.`tk_r + mask T tok.`tk_dig tok.`tk_i.

op erase (tok : token) : token =
  {| tok with tk_phase = 0; tk_r = RqVec.Vector.zerov; tk_e = RqRow.Vector.zerov |}.

op sign3 (h0 : h0fun) (h1 : h1fun) (hc : hcfun) (vk : row) (sk : vec) (tok : token)
         (T : committee) (cs : cmt list) (ws : row list) : (token * vec) option =
  if ok3 h0 h1 vk tok T cs ws then Some (erase tok, resp hc vk sk tok T ws) else None.

op mkhint (vk : row) (c : rq) (w : row) (z : vec) : row =
  w - rndw (mulA mA z - rowZ c (liftt vk)).

op combine (vk : row) (c : rq) (w : row) (zs : vec list) : sig =
  (c, vsum zs, mkhint vk c w (vsum zs)).

op verify (hc : hcfun) (vk : row) (mu : msg) (sg : sig) : bool =
  hc vk (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt vk)) + sg.`3) mu = sg.`1
  /\ inbnd sg.`2 sg.`3.

(* Fresh tokens start in phase one *)
lemma sign1_phase h0 vk i mu r e : (sign1 h0 vk i mu r e).`tk_phase = 1.
proof. by rewrite /sign1. qed.

(* Fresh tokens commit truncated commitments *)
lemma sign1_cmt h0 vk i mu r e :
  (sign1 h0 vk i mu r e).`tk_cmt = h0 vk mu i (sign1 h0 vk i mu r e).`tk_wbar.
proof. by rewrite /sign1. qed.

(* Round two succeeds under its checks *)
lemma sign2_some h1 vk tok T cs x :
  sign2 h1 vk tok T cs = Some x =>
  ok2 tok T cs /\ x.`1.`tk_phase = 2 /\ x.`1.`tk_T = T
  /\ x.`1.`tk_dig = h1 vk tok.`tk_msg T cs /\ x.`2 = tok.`tk_wbar
  /\ x.`1.`tk_i = tok.`tk_i /\ x.`1.`tk_msg = tok.`tk_msg /\ x.`1.`tk_r = tok.`tk_r
  /\ x.`1.`tk_e = tok.`tk_e /\ x.`1.`tk_wbar = tok.`tk_wbar /\ x.`1.`tk_cmt = tok.`tk_cmt.
proof. by rewrite /sign2; case: (ok2 tok T cs) => // h [] <-. qed.

(* The second round answers only fresh tokens *)
lemma sign2_fresh h1 vk tok T cs :
  tok.`tk_phase <> 1 => sign2 h1 vk tok T cs = None.
proof. by move=> h; rewrite /sign2 /ok2 h. qed.

(* An answered request contains the own commitment *)
lemma sign2_own h1 vk tok T cs x :
  sign2 h1 vk tok T cs = Some x => tok.`tk_i \in T /\ own_cmt tok T cs.
proof. by move=> /sign2_some [#] /> _ _ _ hin _ hown. qed.

(* Round three succeeds under its checks *)
lemma sign3_some h0 h1 hc vk sk tok T cs ws x :
  sign3 h0 h1 hc vk sk tok T cs ws = Some x =>
  ok3 h0 h1 vk tok T cs ws /\ x.`1 = erase tok /\ x.`2 = resp hc vk sk tok T ws.
proof. by rewrite /sign3; case: (ok3 h0 h1 vk tok T cs ws) => // h [] <-. qed.

(* The third round answers only opened tokens *)
lemma sign3_opened h0 h1 hc vk sk tok T cs ws :
  tok.`tk_phase <> 2 => sign3 h0 h1 hc vk sk tok T cs ws = None.
proof. by move=> h; rewrite /sign3 /ok3 h. qed.

(* An erased token is never used again *)
lemma erase_dead h0 h1 hc vk sk tok T cs ws :
  sign2 h1 vk (erase tok) T cs = None
  /\ sign3 h0 h1 hc vk sk (erase tok) T cs ws = None.
proof. by split; [apply sign2_fresh | apply sign3_opened]; rewrite /erase. qed.

(* An erased token holds no nonce *)
lemma erase_nonce tok : (erase tok).`tk_r = RqVec.Vector.zerov.
proof. by rewrite /erase. qed.

(* Responses bind the opened request *)
lemma sign3_request h0 h1 hc vk sk tok T cs ws x :
  sign3 h0 h1 hc vk sk tok T cs ws = Some x =>
  T = tok.`tk_T /\ h1 vk tok.`tk_msg T cs = tok.`tk_dig.
proof.
move=> /sign3_some [] hok _; move: hok; rewrite /ok3 => [#] _ hT hd _ _.
by split.
qed.

(* A response checks every opening *)
lemma sign3_openings h0 h1 hc vk sk tok T cs ws x :
  sign3 h0 h1 hc vk sk tok T cs ws = Some x => opens_ok h0 vk tok.`tk_msg T cs ws.
proof.
move=> /sign3_some [] hok _; move: hok; rewrite /ok3 => [#] _ _ _ hop _.
exact hop.
qed.

(* The combiner hint recovers the aggregate *)
lemma hint_correct vk c w z :
  rndw (mulA mA z - rowZ c (liftt vk)) + mkhint vk c w z = w.
proof.
rewrite /mkhint RqRow.Vector.ZModule.addrC.
exact RqRow.Vector.ZModule.subrK.
qed.

(* A combined signature passes the hash test *)
lemma combine_hash hc vk mu c w zs :
  c = hc vk w mu =>
  verify hc vk mu (combine vk c w zs) = inbnd (vsum zs) (mkhint vk c w (vsum zs)).
proof. by move=> hc0; rewrite /verify /combine /= hint_correct -hc0. qed.

(* Honest responses sum to the aggregate *)
lemma resp_sum (hc : hcfun) (vk : row) (mu : msg) (T : committee) (vw : view)
               (ws : row list) (s : vec) (p : int -> vec) (tok : int -> token) :
  wf_nodes T => 0 < tthr =>
  (forall j, j \in T => (tok j).`tk_i = j /\ (tok j).`tk_msg = mu /\ (tok j).`tk_dig = vw) =>
  vmap (fun j => resp hc vk (shr s p j) (tok j) T ws) T
  = (chal hc vk mu ws) ** s + vmap (fun j => (tok j).`tk_r) T.
proof.
move=> hwf ht htok.
have e1 : vmap (fun j => resp hc vk (shr s p j) (tok j) T ws) T
        = vmap (fun j => (Rq.( * ) (chal hc vk mu ws) (lam_of T j)) ** shr s p j
                         + (tok j).`tk_r + mask T vw j) T.
+ apply vmap_eq => j hj /=; rewrite /resp.
  by have [#] -> -> -> := htok j hj.
rewrite e1.
have e2 := vmap_split (fun j => (Rq.( * ) (chal hc vk mu ws) (lam_of T j)) ** shr s p j
                                + (tok j).`tk_r) (mask T vw) T.
rewrite /= in e2; rewrite e2 mask_sum_zero RqVec.Vector.ZModule.addr0.
have e3 := vmap_split (fun j => (Rq.( * ) (chal hc vk mu ws) (lam_of T j)) ** shr s p j)
                      (fun j => (tok j).`tk_r) T.
rewrite /= in e3; rewrite e3.
congr.
have -> : vmap (fun j => (Rq.( * ) (chal hc vk mu ws) (lam_of T j)) ** shr s p j) T
        = vmap (fun j => (chal hc vk mu ws) ** (lam_of T j ** shr s p j)) T.
+ by apply vmap_eq => j _ /=; rewrite vscaleA.
by rewrite -scalev_vmap (shr_recons_constructed T s p hwf ht).
qed.

(* Honest executions verify within the bound *)
lemma correctness (hc : hcfun) (vk : row) (mu : msg) (T : committee) (vw : view)
                  (ws : row list) (s : vec) (p : int -> vec) (tok : int -> token) :
  wf_nodes T => 0 < tthr =>
  (forall j, j \in T => (tok j).`tk_i = j /\ (tok j).`tk_msg = mu /\ (tok j).`tk_dig = vw) =>
  let zs = map (fun j => resp hc vk (shr s p j) (tok j) T ws) T in
  let c = chal hc vk mu ws in
  vsum zs = c ** s + vmap (fun j => (tok j).`tk_r) T
  /\ verify hc vk mu (combine vk c (aggw ws) zs)
     = inbnd (vsum zs) (mkhint vk c (aggw ws) (vsum zs)).
proof.
move=> hwf ht htok /=; split.
+ by rewrite -(resp_sum hc vk mu T vw ws s p tok hwf ht htok) /vmap.
by apply combine_hash; rewrite /chal.
qed.

(* Public image of honest aggregates *)
lemma resp_image (c : rq) (s : vec) (rs : int -> vec) (T : committee) :
  mulA mA (c ** s + vmap rs T)
  = rowZ c (mulA mA s) + rowmap (fun j => mulA mA (rs j)) T.
proof. by rewrite mulAD mulAZ mulA_vmap. qed.
