Require Export HoTT Ch09.

Inductive acc {A : hSet} {L : A -> A -> hProp} : A -> Type :=
  | accL : forall a : A, (forall b : A, (L b a) -> acc b) -> acc a.

Lemma hprop_acc `{Funext} {A : hSet} {L : A -> A -> hProp} 
  : forall a, IsHProp (@acc _ L a).
Proof.
  intro a. apply hprop_allpath. intros s1 s2.
  induction s1 as [a1 h1 k1]. 
  induction s2 as [a2 h2 k2]. apply (ap (accL a2)).
  apply path_forall; intro b. apply path_forall; intro l.
  apply k1.
Defined.

Definition well_founded {A : hSet} (L : A -> A -> hProp) := 
  forall a : A, @acc A L a.


Lemma wf_irreflexive {A : hSet} (L : A -> A -> hProp) (HL : well_founded L)
  : forall a : A, ~ (L a a).
Proof.
  intro a. induction (HL a) as [a f g].
  intro H. contradiction (g a H).
Defined.


Definition set_sum (A B : hSet) := @BuildhSet (A + B) hset_sum.

(* This is misdefined in HoTT/HoTT *)
Definition False_hp : hProp := (BuildhProp Empty).

Definition sum_order {A B : hSet} (LA : A -> A -> hProp) 
           (LB : B -> B -> hProp) (z z' : set_sum A B)
  : hProp
  := match z with
       | inl a => match z' with
                    | inl a' => LA a a'
                    | inr b' => Unit_hp
                  end
       | inr b => match z' with
                    | inl a' => False_hp
                    | inr b' => LB b b'
                  end
     end.

Lemma sum_order_wf {A B : hSet} (LA : A -> A -> hProp) (LB : B -> B -> hProp)
  : (well_founded LA) -> (well_founded LB) -> well_founded (sum_order LA LB).
Proof.
  intros HLA HLB.
  transparent assert (HA : (
    forall a : A, @acc A LA a -> @acc _ (sum_order LA LB) (inl a)
  )).
  intros a s. induction s as [a f g]. constructor.
  intros z' L. destruct z' as [a' | b']; simpl in *.
  apply g. apply L.
  contradiction.

  transparent assert (HB : (
    forall b : B, @acc B LB b -> @acc _ (sum_order LA LB) (inr b)
  )).
  intros b s. induction s as [b f g]. constructor.
  intros z' L. destruct z' as [a' | b']; simpl in *.
  apply HA. apply HLA.
  apply g. apply L.

  intro z. destruct z as [a | b].
  apply HA. apply HLA.
  apply HB. apply HLB.
Defined.
  

Definition extensional {A : hSet} (L : A -> A -> hProp) {HL : well_founded L}
  := forall a a', (forall c, (L c a) <-> (L c a')) -> (a = a').

Lemma sum_order_ext {A B : hSet} (LA : A -> A -> hProp) (LB : B -> B -> hProp)
      (HwfA : well_founded LA) (HwfB : well_founded LB)
  : (@extensional A LA HwfA) 
    -> (@extensional B LB HwfB) 
    -> @extensional _ (sum_order LA LB) (sum_order_wf LA LB HwfA HwfB).
Proof.
  intros HeA HeB.
  intros z z' Heq. destruct z as [a | b], z' as [a' | b']; apply path_sum.
  apply HeA. intro a''. apply (Heq (inl a'')).
  apply (wf_irreflexive LA HwfA a), ((snd (Heq (inl a))) tt).
  apply (wf_irreflexive LA HwfA a'), ((fst (Heq (inl a'))) tt).
  apply HeB. intro b''. apply (Heq (inr b'')).
Defined.

Class Ord 
  := BuildOrd {
       o_set :> hSet ;
       o_rel :> o_set -> o_set -> hProp ;
       o_wf :> @well_founded o_set o_rel ;
       o_ext :> @extensional o_set o_rel o_wf ;
       o_trans : forall a b c : o_set, (o_rel a b) -> (o_rel b c) -> (o_rel a c)
     }.

Definition ord_sum (A B : Ord) : Ord.
Proof.
  destruct A as [A LA LAw LAe LAt], B as [B LB LBw LBe LBt].
  refine (BuildOrd (set_sum A B) 
                   (sum_order LA LB)
                   (sum_order_wf LA LB LAw LBw)
                   (sum_order_ext LA LB LAw LBw LAe LBe)
                   _).
  intros z z' z'' Hzz' Hz'z''.
  destruct z as [a | b], z' as [a' | b'], z'' as [a'' | b'']; simpl in *.
  apply (LAt a a' a'' Hzz' Hz'z''). 
  apply Hz'z''. contradiction. apply Hzz'.
  contradiction. contradiction. contradiction.
  apply (LBt b b' b'' Hzz' Hz'z'').
Defined.



Definition heyting_ord `{Funext} (P Q : hProp) 
  : hProp
  := BuildhProp ((P -> Q) * (Q <> P)).
