require import AllCore Int List.
require import Params Types Corruption.

type request = msg * committee * cmt list.

type alog = (request * int) list.

op S1 (L : alog) (mu : msg) : int list =
  undup (map snd (filter (fun (e : request * int) => e.`1.`1 = mu) L)).

op S2 (L : alog) (V : request) : int list =
  undup (map snd (filter (fun (e : request * int) => e.`1 = V) L)).

op S3 (tokOK : int -> request -> bool) (C : corrset) (V : request) : int list =
  filter (fun i => !(i \in C) /\ tokOK i V) V.`2.

op S4 (C : corrset) (V : request) : int list = honest V.`2 C.

op tf0 (L : alog) (mu : msg) : bool = S1 L mu <> [].

op tf1 (C : corrset) (L : alog) (mu : msg) : bool = tthr - size C <= size (S1 L mu).

op tf2 (C : corrset) (L : alog) (V : request) : bool = tthr - size C <= size (S2 L V).

op tf3 (tokOK : int -> request -> bool) (C : corrset) (L : alog) (V : request) : bool =
  tf2 C L V /\ (forall i, i \in S2 L V <=> i \in S3 tokOK C V).

op tf4 (C : corrset) (L : alog) (V : request) : bool =
  tf2 C L V /\ (forall i, i \in S2 L V <=> i \in S4 C V).

op win0 (L : alog) (mu : msg) (ok : bool) : bool = ok /\ !tf0 L mu.

op win1 (C : corrset) (L : alog) (mu : msg) (ok : bool) : bool = ok /\ !tf1 C L mu.

op win2 (C : corrset) (L : alog) (mu : msg) (ok : bool) : bool =
  ok /\ !(exists (V : request), V.`1 = mu /\ tf2 C L V).

op win3 (tokOK : int -> request -> bool) (C : corrset) (L : alog) (mu : msg) (ok : bool) : bool =
  ok /\ !(exists (V : request), V.`1 = mu /\ tf3 tokOK C L V).

op win4 (C : corrset) (L : alog) (mu : msg) (ok : bool) : bool =
  ok /\ !(exists (V : request), V.`1 = mu /\ tf4 C L V).

pred loggood (tokOK : int -> request -> bool) (C : corrset) (L : alog) =
  forall V i, (V, i) \in L => !(i \in C) /\ i \in V.`2 /\ tokOK i V.

(* Request answers are message answers *)
lemma S2_sub_S1 (L : alog) (V : request) i : i \in S2 L V => i \in S1 L V.`1.
proof.
rewrite /S2 /S1 mem_undup => /mapP [e] [] /mem_filter [] /= he hL ->.
rewrite mem_undup; apply/mapP; exists e; rewrite mem_filter /=.
by rewrite he hL.
qed.

(* Good logs hold valid honest tokens *)
lemma S2_sub_S3 tokOK C L V i :
  loggood tokOK C L => i \in S2 L V => i \in S3 tokOK C V.
proof.
move=> hg; rewrite /S2 mem_undup => /mapP [e] [] /mem_filter [] /= heq hin ->.
have := hg e.`1 e.`2; rewrite heq.
have -> : (V, e.`2) = e by rewrite -heq; case: e heq hin.
move=> /(_ hin) [#] hC hT hok.
by rewrite /S3 mem_filter /= hC hok hT.
qed.

(* Valid honest tokens belong to honest members *)
lemma S3_sub_S4 tokOK C V i : i \in S3 tokOK C V => i \in S4 C V.
proof. by rewrite /S3 /S4 /honest !mem_filter => -[] [] h _ hin. qed.

(* The fourth trivial condition implies the third *)
lemma tf4_tf3 tokOK C L V : loggood tokOK C L => tf4 C L V => tf3 tokOK C L V.
proof.
move=> hg [] h2 heq; split => // i; split.
+ by apply (S2_sub_S3 tokOK C L V i hg).
by move=> /(S3_sub_S4 tokOK C V i) /heq.
qed.

(* The third trivial condition implies the second *)
lemma tf3_tf2 tokOK C L V : tf3 tokOK C L V => tf2 C L V.
proof. by move=> []. qed.

(* The second trivial condition implies the first *)
lemma tf2_tf1 C L V : tf2 C L V => tf1 C L V.`1.
proof.
rewrite /tf2 /tf1 => h.
have : size (S2 L V) <= size (S1 L V.`1).
+ apply uniq_leq_size; first by rewrite /S2 undup_uniq.
  by move=> i; apply S2_sub_S1.
smt().
qed.

(* First trivial condition implies the zeroth *)
lemma tf1_tf0 C L mu : size C < tthr => tf1 C L mu => tf0 L mu.
proof.
rewrite /tf1 /tf0 => hc h; apply/negP => h0.
by move: h; rewrite h0 /=; smt().
qed.

(* Winning the zeroth game wins the first *)
lemma win0_win1 C L mu ok : size C < tthr => win0 L mu ok => win1 C L mu ok.
proof.
move=> hc; rewrite /win0 /win1 => -[] hok h0; split => //.
apply/negP => h1; apply h0; exact (tf1_tf0 C L mu hc h1).
qed.

(* Winning the first game wins the second *)
lemma win1_win2 C L mu ok : win1 C L mu ok => win2 C L mu ok.
proof.
rewrite /win1 /win2 => -[] hok h1; split => //.
apply/negP => -[V] [] hm h2; apply h1; rewrite -hm; exact (tf2_tf1 C L V h2).
qed.

(* Winning the second game wins the third *)
lemma win2_win3 tokOK C L mu ok : win2 C L mu ok => win3 tokOK C L mu ok.
proof.
rewrite /win2 /win3 => -[] hok h2; split => //.
apply/negP => -[V] [] hm h3; apply h2; exists V; split => //.
exact (tf3_tf2 tokOK C L V h3).
qed.

(* Winning the third game wins the fourth *)
lemma win3_win4 tokOK C L mu ok :
  loggood tokOK C L => win3 tokOK C L mu ok => win4 C L mu ok.
proof.
move=> hg; rewrite /win3 /win4 => -[] hok h3; split => //.
apply/negP => -[V] [] hm h4; apply h3; exists V; split => //.
exact (tf4_tf3 tokOK C L V hg h4).
qed.

(* Winning the zeroth game wins the fourth *)
lemma win0_win4 tokOK C L mu ok :
  size C < tthr => loggood tokOK C L => win0 L mu ok => win4 C L mu ok.
proof.
move=> hc hg h0.
apply (win3_win4 tokOK) => //; apply win2_win3; apply win1_win2.
by apply win0_win1.
qed.

pred sublog (Lr Lo : alog) = forall e, e \in Lr => e \in Lo.

(* Fewer answers give fewer trivial forgeries *)
lemma tf2_sub C Lr Lo V : sublog Lr Lo => tf2 C Lr V => tf2 C Lo V.
proof.
rewrite /tf2 => hs h.
have : size (S2 Lr V) <= size (S2 Lo V).
+ apply uniq_leq_size; first by rewrite /S2 undup_uniq.
  move=> i; rewrite /S2 mem_undup => /mapP [e] [] /mem_filter [] /= he hL ->.
  rewrite mem_undup; apply/mapP; exists e; rewrite mem_filter /=.
  by rewrite he (hs e hL).
smt().
qed.

(* Response trivial forgeries are opening ones *)
lemma tf4_sub tokOK C Lr Lo V :
  sublog Lr Lo => loggood tokOK C Lo => tf4 C Lr V => tf4 C Lo V.
proof.
move=> hs hg [] h2 heq; split; first by apply (tf2_sub C Lr Lo V).
move=> i; split.
+ by move=> /(S2_sub_S3 tokOK C Lo V i hg) /(S3_sub_S4 tokOK C V i).
move=> /heq; rewrite /S2 mem_undup => /mapP [e] [] /mem_filter [] /= he hL ->.
rewrite mem_undup; apply/mapP; exists e; rewrite mem_filter /=.
by rewrite he (hs e hL).
qed.

(* Opening semantics wins are response semantics wins *)
lemma win4_o_r tokOK C Lr Lo mu ok :
  sublog Lr Lo => loggood tokOK C Lo => win4 C Lo mu ok => win4 C Lr mu ok.
proof.
move=> hs hg; rewrite /win4 => -[] hok h4; split => //.
apply/negP => -[V] [] hm hr; apply h4; exists V; split => //.
exact (tf4_sub tokOK C Lr Lo V hs hg hr).
qed.
