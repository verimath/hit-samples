Require Export HoTT Ch04.

Module Ex1.

  Section Ex1. 
    Variable A : Type.
    Variable P : list A -> Type.
    Hypothesis d : P nil 
                   -> (forall h t, P t -> P (cons h t))
                   -> forall l, P l.
    Variable p_n : P nil.
    Variable p_c : forall h t, P t -> P (cons h t).

    Fixpoint f (l : list A) : P l :=
      match l with
        | nil => p_n
        | cons h t => p_c h t (f t)
      end.
    End Ex1.
End Ex1.


Module Ex2.
Section Ex2.
  Variables (C : Type) (c : C).

  Definition f (n : nat) := c.
  Fixpoint f' (n : nat) :=
    match n with
      | O => c
      | S n' => f' n'
    end.

  Theorem ex5_2_O : f O = f' O.
  Proof.
    reflexivity.
  Qed.
  
  Theorem ex5_2_S : forall n, f (S n) = f' (S n).
  Proof.
    intros. unfold f, f'.
    induction n. reflexivity. apply IHn.
  Qed.
End Ex2.
End Ex2.


Module Ex3.
Section Ex3.
  Variables (C : Type) (c c' : C) (p : ~ (c = c')).
  
  Definition ez := c.
  Definition es (n : nat) (x : C) := x.
  Definition ez' := c.
  Definition es' (n : nat) := fun (x : C) => c.
  
  Theorem f_O : Ex2.f C c O = ez.
  Proof.
    reflexivity.
  Defined.
  Theorem f_S : forall n, Ex2.f C c (S n) = es n (Ex2.f C c n).
  Proof.
    reflexivity.
  Defined.
    
  Theorem f_O' : Ex2.f C c O = ez'.
  Proof.
    reflexivity.
  Defined.
  Theorem f_S' : forall n, Ex2.f C c (S n) = es' n (Ex2.f C c n).
  Proof.
    reflexivity.
  Defined.

  Theorem ex5_3 : ~ ((ez, es) = (ez', es')).
  Proof.
    intro q. apply (ap snd) in q. simpl in q. unfold es, es' in q.
    assert (idmap = fun x:C => c) as r.
    apply (apD10 q O).
    assert (c' = c) as s.
    apply (apD10 r). 
    symmetry in s.
    contradiction p.
  Defined.

End Ex3.
End Ex3.



Definition Bool_rect_uncurried (E : Bool -> Type) : 
  (E false) * (E true) -> (forall b, E b).
  intros p b. destruct b; [apply (snd p) | apply (fst p)].
Defined.

Definition Bool_rect_uncurried_inv (E : Bool -> Type) : 
  (forall b, E b) -> (E false) * (E true).
  intro f. split; [apply (f false) | apply (f true)].
Defined.

Theorem ex5_4 `{Funext} (E : Bool -> Type) : IsEquiv (Bool_rect_uncurried E).
Proof.
  refine (isequiv_adjointify _ (Bool_rect_uncurried_inv E) _ _);
    unfold Bool_rect_uncurried, Bool_rect_uncurried_inv.
  intro f. apply path_forall; intro b. destruct b; reflexivity.
  intro p. apply eta_prod.
Qed.


Definition nat_rect_uncurried (E : nat -> Type) :
  (E O) * (forall n, E n -> E (S n)) -> forall n, E n.
  intros p n. induction n. apply (fst p). apply (snd p). apply IHn.
Defined.

Theorem ex5_5 `{Funext} : ~ IsEquiv (nat_rect_uncurried (fun _ => Bool)).
Proof.
  intro e. destruct e.
  set (ez := (Ex3.ez Bool true)).
  set (es := (Ex3.es Bool)).
  set (ez' := (Ex3.ez' Bool true)).
  set (es' := (Ex3.es' Bool true)).
  assert ((ez, es) = (ez', es')) as H'.
  transitivity (equiv_inv (nat_rect_uncurried (fun _ => Bool) (ez, es))).
  symmetry. apply eissect.
  transitivity (equiv_inv (nat_rect_uncurried (fun _ => Bool) (ez', es'))).
  apply (ap equiv_inv). apply path_forall; intro n. induction n.
    reflexivity.
    simpl. rewrite IHn. unfold Ex3.es, Ex3.es'. induction n; reflexivity.
  apply eissect.
  assert (~ ((ez, es) = (ez', es'))) as nH.
    apply (Ex3.ex5_3 Bool true false). apply true_ne_false.
    contradiction nH.
Qed.

Section Ex7.

Variable (C : Type) (g : (C -> Empty) -> C).
Variable (rec : forall P, ((C -> Empty) -> (P -> Empty) -> P) -> C -> P).

Theorem ex7 : Empty.
Proof.
  set (h := (fun k i => k (g k)): ((C -> Empty) -> (Empty -> Empty) -> Empty)).
  apply (rec Empty h).
  apply g. apply (rec Empty h).
Defined.

End Ex7.

Section Ex8.

Variable (D : Type) (scott : (D -> D) -> D).
Hypothesis (rec : forall P, ((D -> D) -> (D -> P) -> P) -> D -> P).

Theorem ex8 : Empty.
Proof.
  set (h := (fun f g => g (scott f)) : (D -> D) -> (D -> Empty) -> Empty).
  apply (h idmap). intro d.
  apply (rec Empty h d).
Defined.
 

End Ex8.

Definition onto {X Y} (f : X -> Y) := forall y : Y, {x : X & f x = y}.

Lemma LawvereFP {X Y} (phi : X -> (X -> Y)) : 
  onto phi -> forall (f : Y -> Y), {y : Y & f y = y}.
Proof.
  intros Hphi f.
  set (q := fun x => f (phi x x)).
  set (p := Hphi q). destruct p as [p Hp].
  exists (phi p p).
  change (f (phi p p)) with ((fun x => f (phi x x)) p).
  change (fun x => f (phi x x)) with q.
  symmetry. apply (apD10 Hp).
Defined.

Module Ex9.
Section Ex9.

Variable (L A : Type).
Variable lawvere : (L -> A) -> L.
Variable rec : forall P, ((L -> A) -> P) -> L -> P.
Hypothesis rec_comp : forall P h alpha, rec P h (lawvere alpha) = h alpha.

Definition phi : (L -> A) -> ((L -> A) -> A) :=
  fun f alpha => f (lawvere alpha).

Theorem ex5_9 `{Funext} : forall (f : A -> A), {a : A & f a = a}.
Proof.
  intro f. apply (LawvereFP phi).
  intro q. exists (rec A q). unfold phi.
  change q with (fun alpha => q alpha).
  apply path_forall; intro alpha. apply rec_comp.
Defined.

End Ex9.
End Ex9.


Module Ex10.
Section Ex10.

Variable L : Type.
Variable lawvere : (L -> Unit) -> L.

Variable indL : forall P, (forall alpha, P (lawvere alpha)) -> forall l, P l.
Hypothesis ind_comp : forall P f alpha, indL P f (lawvere alpha) = f alpha.

Theorem ex5_10 `{Funext} : Contr L.
Proof.
  apply (BuildContr L (lawvere (fun _ => tt))).
  apply indL; intro alpha.
  apply (ap lawvere).
  apply path_ishprop.
Defined.

End Ex10.
End Ex10.


Theorem not_equiv_empty (A : Type) : ~ A -> (A <~> Empty).
Proof.
  intro nA. refine (equiv_adjointify nA (Empty_rect (fun _ => A)) _ _);
  intro; contradiction.
Defined.

Module Ex11.

Inductive lost (A : Type) := cons : A -> lost A -> lost A.

Theorem ex5_11 (A : Type) : lost A <~> Empty.
Proof.
  apply not_equiv_empty.
  intro l.
  apply (lost_rect A). auto. apply l.
Defined.

End Ex11.

