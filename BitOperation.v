Require Export VPHL.
Require Setoid.
Check aid.

Inductive bit : Type :=
  |bitTrue  :bit
  |bitFalse :bit.

Definition probBit (a: bit):= match a with |bitTrue => true| _ => false end.

Example bitUnitTrue: Pr probBit in (Unit bitTrue) =1.
Proof. reflexivity. Qed.

Example bitUnitFalse: Pr probBit in (Unit bitFalse) =0.
Proof. reflexivity. Qed.

Lemma bitUnit: forall (a:bit), Pr probBit in (Unit a) = 0 \/ Pr probBit in (Unit a) = 1.
Proof. intros.
       destruct a.
       - right. apply bitUnitTrue.
       - left. apply bitUnitFalse.
         Qed.

Lemma bitCombineTrueFalse: forall (d1 d2 : dist bit) p v , (d1 = Unit bitTrue)->
                                                           (d2 = Unit bitFalse) -> Pr probBit in (Combine p v d1 d2) = p.
Proof. intros. simpl. rewrite H, H0. simpl. lra. Qed.

Definition coin := fun p =>  fun v => Combine p v (Unit bitTrue) (Unit bitFalse).

Lemma bitCombineTrueTrue: forall (d1 d2 : dist bit) p v, (d1 = Unit bitTrue) -> (d2 = Unit bitTrue) ->
                                                           Pr probBit in (Combine p v d1 d2 ) = 1.
  Proof. intros. simpl. rewrite H, H0. simpl. lra. Qed.

Inductive dist2 (T:Type) : Type :=
| ret : T -> dist2 T
| comb : forall p, 0<p<1 -> dist2 T -> dist2 T -> dist2 T
| mlet : forall T1, dist2 T1 -> (T1 -> dist2 T) -> dist2 T.

Example foo := (coin (1/2)).
Check Unit (bitTrue, bitFalse).


Example coinEx:forall v,  Pr probBit in (foo v) = (1/2).
Proof. intros. simpl. lra. Qed.


Definition X :aid := Aid 1.
Definition Y :aid := Aid 0.

Definition initialState :dstate := dist_update (dist_update empty_dstate X (ANum 0)) Y (ANum 0).
Check initialState.
Print initialState.



Definition coinPair p1 p2 u v :dist (nat * nat):=

                                        Combine p1 u (Combine p2 v (Unit (1%nat , 1%nat)) (Unit (1%nat, 0%nat)))

                                                   (Combine p2 v (Unit (0%nat ,1%nat)) (Unit (0%nat, 0%nat))).


Definition probPairHeadTail (t : nat * nat) := match t with| (a  ,b ) =>
                                               match a, b with | 0, 1 => true | _,_ => false end end.
                                            

Check probPairHeadTail.

Lemma coinPairProbTailHead : forall p1 p2 u v , Pr probPairHeadTail in (coinPair p1 p2 u v) = ((1-p1) * p2).
Proof. intros. simpl. lra. Qed.

Definition probPairTailTail t : bool := match t with | (a ,b) =>
                                                     match a,b with | 0,0 => true | _,_=>false
                                        end end.




Definition probPair (x: nat) (y: nat) (t: nat*nat) := match t with| (a,b) =>
                                                                    if (beq_nat a x) then
                                                                    if (beq_nat b y) then true else false  
                                                                    else false end.


Lemma coinPairProbHeadHead : forall p1 p2 u v, Pr (probPair 1 1) in (coinPair p1 p2 u v) >= (p1)*p2.
Proof. intros. simpl. lra. Qed.

Lemma coinPairProbHeadTail : forall p1 p2 u v, Pr (probPair 1 0) in (coinPair p1 p2 u v) >= p1 * (1-p2).
  Proof. intros. simpl. lra. Qed.

Lemma coinPairProbTailTail : forall p1 p2 u v, Pr (probPair 0 0) in (coinPair p1 p2 u v) >= ((1-p1)*(1-p2)).
  Proof. intros. simpl. lra. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity).
  
Definition bitSum sum t:= match t with | (a,b)=> (beq_nat (a+b) sum) end.
Compute (bitSum 1%nat (1%nat,1%nat)).

Lemma bitSumPairImpossible: forall p1 p2 u v, Pr (bitSum 3%nat) in (coinPair p1 p2 u v) = 0.
Proof. intros. simpl. lra. Qed.

Lemma bitSumPair0: forall p1 p2 u v, Pr (bitSum 0%nat) in (coinPair p1 p2 u v) >= (1-p1) * (1-p2).
Proof. intros. simpl. lra. Qed.

Lemma bitSumPair2: forall p1 p2 u v, Pr (bitSum 2%nat) in (coinPair p1 p2 u v) >= p1*p2.
Proof. intros. simpl. lra. Qed.

Lemma bitSumPair1: forall p1 p2 u v, Pr (bitSum 1%nat) in (coinPair p1 p2 u v) >= p1 + p2 - 2 * p1 *p2.
Proof. intros. simpl. lra. Qed.  
  