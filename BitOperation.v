Require Export VPHL.
Require Setoid.
Require Import Field.
Require Import Fourier.
Check aid.

Inductive bit : Type :=
  |bitTrue  :bit
  |bitFalse :bit.

Definition probBit (a: bit):bool:= match a with |bitTrue => true| _ => false end.

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


Definition ideal_coin: dist bit.
  apply (coin (1/2)). split;fourier. Defined.

Definition coin_third: dist bit.
  apply (coin (1/3)). split;fourier. Defined.


Check ideal_coin.

Check (Pr probBit in ideal_coin).

Definition extract_bias (c: dist bit) : R :=
Pr probBit in c.

Compute (extract_bias ideal_coin).

Example coinEx: Pr probBit in ideal_coin = (1/2).
Proof. simpl. lra. Qed.


Lemma bitCombineTrueTrue: forall (d1 d2 : dist bit) p v, (d1 = Unit bitTrue) -> (d2 = Unit bitTrue) ->
                                                           Pr probBit in (Combine p v d1 d2 ) = 1.
  Proof. intros. simpl. rewrite H, H0. simpl. lra. Qed.

Inductive dist2 (T:Type) : Type :=
| ret : T -> dist2 T
| comb : forall p, 0<p<1 -> dist2 T -> dist2 T -> dist2 T
| mlet : forall T1, dist2 T1 -> (T1 -> dist2 T) -> dist2 T.

Example foo := (coin (1/2)).
Check Unit (bitTrue, bitFalse).


(*Example coinEx:forall v,  Pr probBit in (foo v) = (1/2).
Proof. intros. simpl. lra. Qed.
*)

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

Fixpoint sumList (l: natlist) (sum:nat) := match l with| [] => sum |x::y => sumList y (sum+x) end.

Definition bitSum sum t:= beq_nat (sumList t 0) sum.
Compute (bitSum 1%nat (1%nat::1%nat::[])).

Definition coinPairL := fun p1 => fun p2=> fun u => fun v =>
                         Combine p1 u (Combine p2 v (Unit (1%nat::1%nat::[])) (Unit (1%nat::0%nat::[])))
                                      (Combine p2 v (Unit (0%nat::1%nat::[])) (Unit (0%nat::0%nat::[]))).

Lemma bitSumPairImpossible: forall p1 p2 u v, Pr (bitSum 3%nat) in (coinPairL p1 p2 u v) = 0.
Proof. intros. simpl. lra. Qed.

Lemma bitSumPair0: forall p1 p2 u v, Pr (bitSum 0%nat) in (coinPairL p1 p2 u v) >= (1-p1) * (1-p2).
Proof. intros. simpl. lra. Qed.

Lemma bitSumPair2: forall p1 p2 u v, Pr (bitSum 2%nat) in (coinPairL p1 p2 u v) >= p1*p2.
Proof. intros. simpl. lra. Qed.

Lemma bitSumPair1: forall p1 p2 u v, Pr (bitSum 1%nat) in (coinPairL p1 p2 u v) >= p1 + p2 - 2 * p1 *p2.
Proof. intros. simpl. lra. Qed.

Definition coinThree := fun p1 => fun p2 => fun p3 => fun u => fun v => fun w => Combine p1 w
    (Combine p2 v (Combine p3 u (Unit (1%nat::1%nat::1%nat::[])) (Unit (1%nat::1%nat::0%nat::[]))) (Combine p3 u (Unit (1%nat::0%nat::1%nat::[])) (Unit (1%nat::0%nat::0%nat::[]))))
    (Combine p2 v (Combine p3 u (Unit (0%nat::1%nat::1%nat::[])) (Unit (0%nat::1%nat::0%nat::[]))) (Combine p3 u (Unit (0%nat::0%nat::1%nat::[])) (Unit (0%nat::0%nat::0%nat::[])))).

Lemma bitSumThreeImpossible : forall p1 p2 p3 u v w, Pr (bitSum 4%nat) in (coinThree p1 p2 p3 u v w) =0.
Proof. intros. simpl. lra. Qed.

Lemma bitSumThree3: forall p1 p2 p3 u v w, Pr (bitSum 3%nat) in (coinThree p1 p2 p3 u v w) >= p1 * p2 * p3.
Proof. intros. simpl. lra. Qed.

Lemma bitSumThree0: forall p1 p2 p3 u v w, Pr (bitSum 0%nat) in (coinThree p1 p2 p3 u v w) >= (1-p1) * (1-p2) * (1-p3).
Proof. intros. simpl. lra. Qed.

Lemma bitSumThree1: forall p1 p2 p3 u v w, Pr (bitSum 1%nat) in (coinThree p1 p2 p3 u v w) >=
                                                       p1 * (1-p2) * (1-p3) + p2 * (1-p1) * (1- p3) + p3 * (1-p1) * (1-p2).
Proof. intros. simpl. lra. Qed.

Lemma bitSumThree2: forall p1 p2 p3 u v w, Pr (bitSum 2%nat) in (coinThree p1 p2 p3 u v w) >=
                                                                (1 - p1) * p2 * p3 + p1 * (1 - p2) * p3 + p1 * p2 * (1 - p3).
Proof. intros. simpl. lra. Qed.

Definition coinFour:= fun p1 => fun p2 => fun p3 => fun p4 => fun u v w x =>
                                                                Combine p1 u (
                Combine p2 v (Combine p3 w (Combine p4 x (Unit (1%nat::1%nat::1%nat::1%nat::[]))
                                                   (Unit (1%nat::1%nat::1%nat::0%nat::[])))
                                       (Combine p4 x (Unit (1%nat::1%nat::0%nat::1%nat::[]))
                                                    (Unit (1%nat::1%nat::0%nat::0%nat::[]))))
                            (Combine p3 w (Combine p4 x (Unit (1%nat::0%nat::1%nat::1%nat::[]))
                                                    (Unit (1%nat::0%nat::1%nat::0%nat::[])))
                                        (Combine p4 x (Unit (1%nat::0%nat::0%nat::1%nat::[]))
                                                    (Unit (1%nat::0%nat::0%nat::0%nat::[])))))
                (Combine p2 v (Combine p3 w (Combine p4 x (Unit (0%nat::1%nat::1%nat::1%nat::[]))
                                                    (Unit (0%nat::1%nat::1%nat::0%nat::[])))
                                        (Combine p4 x (Unit (0%nat::1%nat::0%nat::1%nat::[]))
                                                    (Unit (0%nat::1%nat::0%nat::0%nat::[]))))
                            (Combine p3 w (Combine p4 x (Unit (0%nat::0%nat::1%nat::1%nat::[]))
                                                    (Unit (0%nat::0%nat::1%nat::0%nat::[])))
                                        (Combine p4 x (Unit (0%nat::0%nat::0%nat::1%nat::[]))
                                                 (Unit (0%nat::0%nat::0%nat::0%nat::[]))))).
Check coinFour.

Lemma coinFourSumImpossible: forall p1 p2 p3 p4 u v w x, Pr (bitSum 5%nat) in (coinFour p1 p2 p3 p4 u v w x) =0.
Proof. intros. simpl. lra. Qed.

Lemma coinFourSum0: forall p1 p2 p3 p4 u v w x, Pr (bitSum 0%nat) in (coinFour p1 p2 p3 p4 u v w x) >=
                                                                     (1-p1) * (1-p2) * (1-p3) * (1-p4).
Proof. intros. simpl. lra. Qed.

Lemma coinFourSum4: forall p1 p2 p3 p4 u v w x, Pr (bitSum 4%nat) in (coinFour p1 p2 p3 p4 u v w x) >= p1*p2*p3*p4.
Proof. intros. simpl. lra. Qed.

Lemma coinFourSum1: forall p1 p2 p3 p4 u v w x, Pr (bitSum 1%nat) in (coinFour p1 p2 p3 p4 u v w x) >=
p1 * (1-p2) * (1-p3) * (1-p4) +  (1-p1) * p2 * (1-p3) * (1-p4) +  (1-p1) * (1-p2) * p3 * (1-p4) + (1-p1) * (1-p2) * (1-p3) * p4.
Proof. intros. simpl. lra. Qed.

 Lemma coinFourSum2: forall p1 p2 p3 p4 u v w x, Pr (bitSum 2%nat) in (coinFour p1 p2 p3 p4 u v w x) >=
 (1-p1) * (1-p2) * p3 * p4 +
 (1-p1) * p2 * (1-p3) * p4 +
 (1-p1) * p2 * p3 * (1-p4) +
 p1 * (1-p2) * (1-p3) * p4 +
 p1 * (1-p2) * p3 * (1-p4) +
 p1 * p2 * (1-p3) * (1-p4).
Proof. intros. simpl. lra. Qed.

 Lemma coinFourSum3 : forall p1 p2 p3 p4 u v w x, Pr (bitSum 3%nat) in (coinFour p1 p2 p3 p4 u v w x) >=
 (1-p1) * p2 * p3 * p4 +
 p1 * (1-p2) * p3 * p4 +
 p1 * p2 * (1-p3) * p4 +
 p1 * p2 * p3 * (1-p4).
 Proof. intros. simpl. lra. Qed.

 Lemma fooo : 0 < 1/2 < 1.
 Proof. lra. Qed.

 Fixpoint build l := match l with | nil  => (coin (1/2) fooo)
                             | cons a b  => (coin (1/2) fooo) end.

 Check build.


 Inductive list (X:Type) : Type :=
  | nil :  list X
  | cons : X-> list X  -> list X.

 Check sig.

 Inductive bound  (p:R) : Type :=
   | boundP :  0 < p < 1 -> bound p.

Lemma range_half: 0 < 1/2 < 1.
Proof. nra. Qed.



(*Marco: this is a way to define lists of real numbers between 0 and 1 *)
 
Definition l1 : (list {x : R | 0 < x < 1}).
  apply cons. exists (1/2).  nra. apply nil.
Defined.

(*Marco: this is another way which uses existential variables and the tactic
nra to fulfill the proof obligations *)
Obligation Tactic := nra.

Program Definition l2 : list {x : R | 0 < x < 1}:=
  cons _ (exist _  (1/3) _) (cons _ (exist _  (1/2) _)  (nil _)).

Check proj2_sig (exist (fun x => 0 <= x <= 1)  (1/2) _) .

(*Marco: I tried to fix the build *)

Program Fixpoint build1 (l:list {x : R | 0 < x < 1})  (k:natlist) := match l  with
  | nil _  => Unit(k)
  | cons _ x xs  => (Combine (proj1_sig x) (proj2_sig x)  (build1 xs ((1%nat)::k)) (build1 xs ((0%nat)::k))) end.

(*Marco: An example of evaluation *)
  Eval simpl in build1 l1.

(*Marco: I stopped here *)
  
  Axiom boundProof  : forall (x:R), 0<x<1.

  Check boundProof.

  Definition bias:Type := R * (forall (x:R), (0<x<1)).

  Infix ":::" := cons (at level 60, right associativity).

Compute (build1 (cons _ (1/2,boundProof) (cons _ (1/2,boundProof) (nil _))) []).


Definition l1 : (list (exists (x:R), (0<x<1))).
  apply cons. intro. split. apply (1/2).

Defined.

    := cons _ (1/2, boundProof) (cons _ (1/2, boundProof) (nil bias)).
