Require Export HoTT Ch07.

Lemma equiv_functor_Trunc (n : trunc_index) (A B : Type) 
  : (A <~> B) -> (Trunc n A) <~> (Trunc n B).
Proof.
  intro e.
  simple refine (equiv_adjointify _ _ _ _).
  apply Trunc_rec. intro a. apply (tr (e a)).
  apply Trunc_rec. intro b. apply (tr (e^-1 b)).
  refine (Trunc_ind _ _).
  intro b. simpl. apply (ap tr). apply eisretr.
  refine (Trunc_ind _ _).
  intro a. simpl. apply (ap tr). apply eissect.
Defined.
