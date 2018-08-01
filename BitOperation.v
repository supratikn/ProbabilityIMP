Require Export VPHL.

Check aid.

Inductive bit : Type :=
  |bitTrue : bit
  |bitFalse :  bit.

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




Definition coinPair  := fun p => fun v =>  Combine p v (Combine p v (Unit (bitTrue , bitTrue)) (Unit (bitTrue, bitFalse)))

                                                   (Combine p v (Unit (bitFalse , bitTrue)) (Unit (bitFalse, bitFalse))).


Definition probPair t:= match t with| (a,b) =>
                                      match a with| bitTrue => match b with |bitTrue =>true | _ =>false end
                                           | _=> false
                                      end
end.
Check probPair.

Lemma coinPairProb : forall p v , Pr probPair in (coinPair p v) = (p * p).
  Proof. intros. simpl. lra. Qed.
