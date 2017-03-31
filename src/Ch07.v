Require Export HoTT Ch06.

Inductive W_tree (A : Type) (B : A -> Type) : Type :=
  | sup : forall a : A, (B a -> W_tree A B) -> W_tree A B.

Lemma ap11_V {A B : Type} {f g : A -> B} (p : f = g) (h : forall x y : A, x = y)
      (x y : A)
  : ap11 p^ (h x y)^ = (ap11 p (h x y))^.
Proof.
  induction p.
  induction (h x y).
  reflexivity.
Defined.

