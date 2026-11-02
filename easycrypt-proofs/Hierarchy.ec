require import AllCore Int List Distr FMap.
require import Params Types Corruption Protocol Notions Games.

(* The first oracle keeps opened tokens recorded *)
lemma o1_reqinv : hoare [O.o1 : reqinv St.toks St.req ==> reqinv St.toks St.req].
proof.
proc; sp; if; last by skip.
wp; rnd; rnd; skip => &m [[_ hri] hc] r _ e _ /=.
move: hri; rewrite /reqinv => hri u; rewrite mem_set get_setE; case: (u = St.ctr{m}) => [-> /= | hne /=].
+ by rewrite /sign1.
by move=> hu hp; exact (hri u hu hp).
qed.

(* The second oracle keeps opened tokens recorded *)
lemma o2_reqinv : hoare [O.o2 : reqinv St.toks St.req ==> reqinv St.toks St.req].
proof.
proc; wp; skip => &m hri.
case: (u{m} \in St.toks{m}) => hu //=.
case: (sign2 St.h1{m} St.vk{m} (oget St.toks{m}.[u{m}]) T{m} cs{m} <> None) => hx //=.
move: hri; rewrite /reqinv => hri u'; rewrite !mem_set get_setE; case: (u' = u{m}) => [-> //= | hne /=].
by move=> hu' hp; rewrite (hri u' hu' hp).
qed.

section.

declare module A <: Adv {-St, -Game}.

(* Oracle invariants hold after every game *)
lemma game_inv :
  hoare [Game(A).main : true ==> inv St.cs St.toks St.req St.ctr St.lo St.lr
                                  /\ reqinv St.toks St.req /\ (Game.ok => cadm St.cs)].
proof.
proc; wp.
call (_ : inv St.cs St.toks St.req St.ctr St.lo St.lr /\ reqinv St.toks St.req).
+ by conseq o1_inv o1_reqinv.
+ by conseq o2_inv o2_reqinv.
+ by conseq o3_inv.
+ by proc; skip.
+ by proc; skip.
+ by proc; skip.
wp; rnd; rnd; rnd; call (_ : true); rnd; rnd; rnd; skip => /> *.
split; first split.
+ by move=> u; rewrite mem_empty.
+ by move=> u; rewrite mem_empty.
by rewrite /reqinv => u; rewrite mem_empty.
qed.

(* Opening semantics forgeries are response semantics forgeries *)
lemma uf4_o_r &m :
  Pr[Game(A).main() @ &m : win4 St.cs St.lo Game.mu Game.ok]
  <= Pr[Game(A).main() @ &m : win4 St.cs St.lr Game.mu Game.ok].
proof.
byequiv => //.
conseq (_ : ={glob A} ==> ={St.cs, St.lo, St.lr, St.toks, Game.mu, Game.ok}) game_inv _ => //.
+ move=> &1 &2 _ muL okL csL ctrL loL lrL reqL toksL muR okR csR loR lrR toksR.
  move=> [[#] e1 e2 e3 e4 e5 e6] [[hinv [_ hadm]] _] hw.
  rewrite -e1 -e3 -e5 -e6.
  have [_ [hlo [_ [hlr _]]]] := hinv.
  apply (win4_o_r (tokOK toksL) csL lrL loL muL okL) => //.
  by move=> V i /hlo [] hni [] hin hok; split => //; split => //; split.
by sim.
qed.

(* Unforgeability notions form a hierarchy *)
lemma uf_hierarchy &m :
  Pr[Game(A).main() @ &m : win0 St.lo Game.mu Game.ok]
  <= Pr[Game(A).main() @ &m : win4 St.cs St.lo Game.mu Game.ok].
proof.
byequiv => //.
conseq (_ : ={glob A} ==> ={St.cs, St.lo, St.lr, St.toks, Game.mu, Game.ok}) game_inv _ => //.
+ move=> &1 &2 _ muL okL csL ctrL loL lrL reqL toksL muR okR csR loR lrR toksR.
  move=> [[#] e1 e2 e3 e4 e5 e6] [[hinv [_ hadm]] _] hw.
  rewrite -e1 -e2 -e5 -e6.
  have [_ [hlo _]] := hinv.
  have hc : size csL < tthr.
  - by move: hw; rewrite /win0 => -[] /hadm; rewrite /cadm; smt().
  apply (win0_win4 (tokOK toksL) csL loL muL okL hc) => //.
  by move=> V i /hlo [] hni [] hin hok; split => //; split => //; split.
by sim.
qed.

end section.
