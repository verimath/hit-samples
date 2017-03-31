Require Export HoTT.
Module Ex1.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).

Lemma compose_assoc (A B C D : Type) (f : A -> B) (g : B-> C) (h : C -> D)
  : compose h (compose g f) = compose (compose h g) f.
Proof.
  reflexivity.
Defined.

End Ex1.
Module Ex2.

Section Ex2a.
Context (A B : Type).

Definition prod_rect (C : Type) (g : A -> B -> C) (p : A * B)
  := g (fst p) (snd p).

Theorem prod_rect_correct : forall (C : Type) (g : A -> B -> C) (a : A) (b : B),
    prod_rect C g (a, b) = g a b. 
Proof.
  reflexivity.
Defined.

End Ex2a.


Section Ex2b.

Context (A : Type).
Context (B : A -> Type).


Definition sigma_rect (C : Type) (g : forall (x : A), B x -> C) (p : {x:A & B x})
  := g (p.1) (p.2).

Theorem sigma_rect_correct : forall (C:Type) (g : forall x, B x -> C) (a:A) (b:B a),
  sigma_rect C g (a; b) = g a b. 
Proof.
  reflexivity.
Defined.

End Ex2b.

End Ex2.

Module Ex3.
Section Ex3a.
Context (A B : Type).


Definition prod_rect (C : A * B -> Type) (g : forall (x:A) (y:B), C (x, y)) (z : A * B) 
  := (eta_prod z) # (g (fst z) (snd z)).


Theorem prod_rect_correct :
  forall (C : A * B -> Type) (g : forall (x:A) (y:B), C (x, y)) (a:A) (b:B),
    prod_rect C g (a, b) = g a b.
Proof.
  reflexivity.
Defined.

End Ex3a.

Section Ex3b.
Context (A : Type).
Context (B : A -> Type).

Definition sigma_rect (C : {x:A & B x} -> Type)
           (g : forall (a:A) (b:B a), C (a; b)) (p : {x:A & B x})
  := (eta_sigma p) # (g (p.1) (p.2)).

Theorem sigma_rect_correct :
      forall (C : {x:A & B x} -> Type)
             (g : forall (a:A) (b:B a), C (a; b)) (a : A) (b : B a),
        sigma_rect C g (a; b) = g a b.
Proof.
  reflexivity.
Defined.

End Ex3b.

End Ex3.

Section Ex4.

Variable C : Type.
Variable c0 : C.
Variable cs : nat -> C -> C.

Fixpoint iter (C : Type) (c0 : C) (cs : C -> C) (n : nat) : C :=
  match n with
    | O => c0
    | S n' => cs(iter C c0 cs n')
  end.

Definition Phi (C : Type) (c0 : C) (cs: nat -> C -> C) (n : nat) :=
  snd (iter (nat * C)
            (O, c0)
            (fun x => (S (fst x), cs (fst x) (snd x)))
            n).

Definition Phi' (n : nat) :=
  iter (nat * C) (O, c0) (fun x => (S (fst x), cs (fst x) (snd x))) n.


Theorem Phi'_correct1 : snd (Phi' 0) = c0.
Proof.
  reflexivity.
Defined.

Theorem Phi'_correct2 : forall n, Phi'(S n) = (S n, cs n (snd (Phi' n))).
Proof.
  intros. induction n. reflexivity.
  transitivity ((S (fst (Phi' (S n))), cs (fst (Phi' (S n))) (snd (Phi' (S n))))).
  reflexivity.
  rewrite IHn. reflexivity.
Defined.

End Ex4.


Module Ex5.
Section Ex5.

Context (A B : Type).

Definition sum := {x:Bool & if x then B else A}.
Definition inl (a : A) := existT (fun x:Bool => if x then B else A) false a.
Definition inr (b : B) := existT (fun x:Bool => if x then B else A) true b.

Definition sum_rect (C : sum -> Type)
           (g0 : forall a : A, C (inl a))
           (g1 : forall b : B, C (inr b))
           (x : sum)
  :=
  sigT_rect C
            (Bool_ind (fun x:Bool => forall (y : if x then B else A), C (x; y))
                      g1
                      g0)
            x.

Theorem sum_rect_correct1 :
  forall C g0 g1 a, sum_rect C g0 g1 (inl a) = g0 a.
Proof.
  reflexivity.
Qed.

Theorem sum_rect_correct2 :
  forall C g0 g1 a, sum_rect C g0 g1 (inr a) = g1 a.
Proof.
  reflexivity.
Qed.

End Ex5.
End Ex5.


Module Ex6.
Section Ex6.
Context (A B : Type).


Definition prod := forall x : Bool, if x then B else A.

Definition pair (a : A) (b : B) 
  := Bool_ind (fun x : Bool => if x then B else A) b a.


Definition fst (p : prod) := p false.
Definition snd (p : prod) := p true.


Definition eta_prod `{Funext} (p : prod) : pair (fst p) (snd p) = p.
  apply path_forall.
  unfold pointwise_paths; apply Bool_ind; reflexivity.
Defined.

Definition prod_rect `{Funext} (C : prod -> Type) 
           (g : forall (x:A) (y:B), C (pair x y)) (z : prod) 
  := (eta_prod z) # (g (fst z) (snd z)).

Lemma prod_rect_correct `{Funext} C g a b
  : prod_rect C g (pair a b) = g a b.
Proof.
  unfold prod_rect.
  path_via (transport C 1 (g (fst (pair a b)) (snd (pair a b)))). f_ap.
  unfold eta_prod.
  path_via (path_forall (pair (fst (pair a b)) (snd (pair a b))) (pair a b) 
                        (fun _ => idpath)).
  f_ap. apply path_forall; intro x. destruct x; reflexivity.
  apply path_forall_1.
Defined.

End Ex6.
End Ex6.



Module Ex7.

Section ex7.

Definition ind (A : Type) : forall (C : forall (x y : A), x = y -> Type),
                              (forall (x:A), C x x idpath) -> 
                              forall (x y : A) (p : x = y), C x y p.
Proof.
  path_induction. apply X.
Defined.

Definition Lemma231 {A} (P : A -> Type) (x y : A) (p : x = y) : P(x) -> P(y).
Proof.
  intro. rewrite <- p. apply X.
Defined.

Definition Lemma3118 : forall (A : Type) (a:A), Contr {x:A & a=x}.
Proof.
  intros A a. exists (a; idpath).
  intro x. destruct x as [x p]. path_induction. reflexivity.
Defined.

Definition ind' (A : Type) : forall (a : A) (C : forall (x:A), a = x -> Type),
                               C a idpath -> forall (x:A) (p:a=x), C x p.
Proof.
  intros.
  assert (H : (Contr {x:A & a=x})). apply Lemma3118.
  change (C x p) with ((fun c => C c.1 c.2) (x; p)).
  apply (Lemma231 _ (a; idpath) (x; p)).
  transitivity (center {x : A & a = x}). destruct H as [[a' p'] z]. simpl. 
  rewrite <- p'. reflexivity.
  destruct H as [[a' p'] z]. simpl. rewrite <- p'. rewrite <- p. reflexivity.
  apply X.
Defined.


End ex7.
End Ex7.


Local Open Scope nat_scope.


Fixpoint plus (n m : nat) : nat :=
  match n with
    | 0 => m
    | S p => S (p + m)
  end

    where "n + m" := (plus n m) : nat_scope.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + (p * m)
  end

    where "n * m" := (mult n m) : nat_scope.

Fixpoint myexp (e b : nat) :=
  match e with
    | 0 => S 0
    | S e' => b * (myexp e' b)
  end.


Theorem plus_O_r : forall (n : nat), n = plus n 0.
Proof.
  induction n. reflexivity. apply (ap S IHn).
Defined.

Theorem ex1_8_i : forall (n : nat), 
                    (0 + n = n) /\ (n = n + 0) /\ (0 + n = n + 0).
Proof.
  split; [| split; rewrite <- plus_O_r]; reflexivity.
Qed.

Theorem mult_0_r : forall (n : nat), 0 = n * 0.
Proof.
  induction n; [| simpl; rewrite <- IHn]; reflexivity.
Qed. 

Theorem ex1_8_ii : forall (n : nat),
                     (0 * n = 0) /\ (0 = n * 0) /\ (0 * n = n * 0).
Proof.
  split; [| split; rewrite <- mult_0_r]; reflexivity.
Qed.

Theorem mult_1_r : forall (n : nat), n = n * 1.
Proof.
  induction n; [| simpl; rewrite <- IHn]; reflexivity.
Qed.

Theorem mult_1_l : forall (n : nat), 1 * n = n.
Proof.
  simpl; intro n; rewrite <- plus_O_r; reflexivity.
Qed.

Theorem ex1_8_iii : forall (n : nat),
                      (1 * n = n) /\ (n = n * 1) /\ (1 * n = n * 1).
Proof.
  split; [rewrite mult_1_l
         | split; rewrite <- mult_1_r; 
           [| rewrite mult_1_l]];
  reflexivity.
Qed.

Theorem plus_n_Sm : forall (n m : nat), S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n. reflexivity.
  simpl. apply (ap S). apply IHn.
Defined.

Theorem plus_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  induction n. apply plus_O_r.
  refine (_ @ (plus_n_Sm _ _)). apply (ap S IHn).
Defined.
  

Theorem plus_assoc : forall (n m k : nat),
                    (n + m) + k = n + (m + k).
Proof.
  intros n m k.
  induction n; [| simpl; rewrite IHn]; reflexivity.
Qed.

Theorem ex1_8_viii : forall (n m k : nat),
                       (n + m) * k = (n * k) + (m * k).
Proof.
  intros n m k.
  induction n. reflexivity. simpl. 
  refine (_ @ (plus_assoc _ _ _)^).
  apply (ap (plus k) IHn).
Defined.

Theorem ex1_8_vi : forall (n m k : nat),
                     (n * m) * k = n * (m * k).
Proof.
  intros n m k.
  induction n; [| simpl; rewrite <- IHn; rewrite <- ex1_8_viii]; reflexivity.
Qed.

Theorem ex1_8_vii : forall (n m k : nat),
                      n * (m + k) = (n * m) + (n * k).
Proof.
  intros n m k.
  induction n. reflexivity.
  simpl.
  refine (_ @ (plus_assoc _ _ _)^).
  refine ((plus_assoc _ _ _) @ _). apply (ap (plus m)).
  refine (_ @ (plus_comm _ _)).
  refine (_ @ (plus_assoc _ _ _)^).
  apply (ap (plus k)). refine (IHn @ _). apply plus_comm.
Defined.

Local Close Scope nat_scope.


Local Open Scope nat_scope.

Definition le (n m : nat) : Type := {k:nat & n + k = m}.
Notation "n <= m" := (le n m)%nat (at level 70) : nat_scope.

Definition lt (n m : nat) : Type := {k : nat & n + S k = m}.
Notation "n < m" := (lt n m)%nat (at level 70) : nat_scope.

Definition Fin (n:nat) : Type := {m:nat & m < n}.

Definition fmax (n:nat) : Fin(n+1) := (n; (0; idpath)).


Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Theorem S_inj : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  change n with (pred (S n)). change m with (pred (S m)).
  apply (ap pred). apply H.
Defined.

Theorem plus_1_r : forall n, S n = n + 1.
Proof.
  intros. rewrite plus_comm. reflexivity.
Qed.

Theorem fmax_correct : forall (n:nat) (m:Fin(n+1)),
                         m .1 <= (fmax n) .1.
Proof.
  unfold Fin, lt, le. intros. simpl.
  exists m.2.1.
  apply S_inj. rewrite plus_n_Sm.
  rewrite m.2.2.
  symmetry.
  apply plus_1_r.
Qed.

Local Close Scope nat_scope.


Definition ack : nat -> nat -> nat :=
  nat_rect (fun _ => nat -> nat)
           S
           (fun m r => nat_rect (fun _ => nat)
                                (r (S 0))
                                (fun n s => (r s))).



Goal forall n, ack 0 n = S n. auto. Qed.
Goal forall m, ack (S m) 0 = ack m (S 0). auto. Qed.
Goal forall m n, ack (S m) (S n) = ack m (ack (S m) n). auto. Qed.

Close Scope nat_scope.

  Goal forall A, ~ ~ ~ A -> ~A. auto. Qed.

Section Ex12.
  Context (A B : Type).

  Goal A -> B -> A. trivial. Qed.

  Goal A -> ~ ~ A. auto. Qed.

  Goal (~ A + ~ B) -> ~ (A * B).
  Proof.
    unfold not.
    intros H x.
    apply H.
    destruct x.
    constructor.
    exact fst.
  Qed.

End Ex12.

Section Ex13.
  Context (P : Type).

  Goal ~ ~ (P + ~P).
  Proof.
    unfold not.
    intro H.
    apply H.
    right.
    intro p.
    apply H.
    left.
    apply p.
  Qed.

End Ex13.

