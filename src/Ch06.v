Require Export HoTT Ch05 HIT.TwoSphere.

Definition concatD {A} {P : A -> Type} {x y z : A} 
           {u : P x} {v : P y} {w : P z}
           {p : x = y} {q : y = z} :
  (p # u = v) -> (q # v = w) -> ((p @ q) # u = w).
  by path_induction.
Defined.

Notation "p @D q" := (concatD p q)%path (at level 20) : path_scope.


Theorem apD_pp {A} {P : A -> Type} (f : forall x : A, P x) 
        {x y z : A} (p : x = y) (q : y = z) :
  apD f (p @ q) = (apD f p) @D (apD f q).
Proof.
  by path_induction.
Defined.


Definition concat2D {A : Type} {P : A -> Type} 
           {x y z : A} {p : x = y} {q : y = z} 
           {u : P x} {v : P y} {w : P z}
           {r r' : p # u = v} {s s' : q # v = w} :
  (r = r') -> (s = s') -> (r @D s = r' @D s').
  by path_induction.
Defined.

Notation "p @@D q" := (concat2D p q)%path (at level 20) : path_scope.

Module Torus_ex.

Private Inductive T2 : Type :=
| Tb : T2.

Axiom Tp : Tb = Tb.
Axiom Tq : Tb = Tb.
Axiom Tt : Tp @ Tq = Tq @ Tp.

Definition T2_rect (P : T2 -> Type) 
           (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
           (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p'))
  : forall (x : T2), P x :=
  fun x => match x with Tb => fun _ _ _ => b' end p' q' t'.

Axiom T2_rect_beta_Tp :
  forall (P : T2 -> Type)
         (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
         (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p')),
    apD (T2_rect P b' p' q' t') Tp = p'.

Axiom T2_rect_beta_Tq :
  forall (P : T2 -> Type)
         (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
         (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p')),
    apD (T2_rect P b' p' q' t') Tq = q'.

Axiom T2_rect_beta_Tt :
  forall (P : T2 -> Type)
         (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
         (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p')),
    (T2_rect_beta_Tp P b' p' q' t' @@D T2_rect_beta_Tq P b' p' q' t')^
    @ (apD_pp (T2_rect P b' p' q' t') Tp Tq)^ 
    @ (apD02 (T2_rect P b' p' q' t') Tt)
    @ (whiskerL (transport2 P Tt (T2_rect P b' p' q' t' Tb))
                (apD_pp (T2_rect P b' p' q' t') Tq Tp))
    @ (whiskerL (transport2 P Tt (T2_rect P b' p' q' t' Tb))
                (T2_rect_beta_Tq P b' p' q' t' @@D T2_rect_beta_Tp P b' p' q' t'))
    = t'.

End Torus_ex.


Definition equiv_functor_susp {A B : Type} (f : A -> B) `{IsEquiv A B f}
: Susp A <~> Susp B.
Proof.
  refine (equiv_adjointify (Susp_rec North South (merid o f))
                           (Susp_rec North South (merid o f^-1)) _ _);
  refine (Susp_ind _ 1 1 _);
  intro b; refine ((transport_paths_FFlr _ _) @ _);
  refine ((concat_pp_p _ _ _) @ _); apply moveR_Vp; symmetry;
  refine ((concat_p1 _) @ _);
  (* [Susp_rec_beta_merid] is called [Susp_comp_merid] in HoTT/master.  This
     uses the branch [jdoughertyii:spheres_with_S2], PR 782 *)
  refine ((ap (ap _) (Susp_rec_beta_merid b)) @ _);
  refine ((Susp_rec_beta_merid _) @ _);
  refine (_ @ (concat_1p _)^);
  f_ap; [apply eisretr | apply eissect]. 
Defined.
      
Definition ex6_2 : Susp S1 <~> S2.
Proof.
  equiv_via (Sphere 2).
  - apply equiv_inverse.
    refine (equiv_functor_susp Sph1_to_S1).
  - refine (BuildEquiv _ _ Sph2_to_S2 _).
Defined.



Definition Phi {A : Type} {x x' y y' : A} (alpha : x = x') (alpha' : y = y') 
: ((path_prod (x, y) (x, y') 1 alpha') @ (path_prod (x, y') (x', y') alpha 1)) 
  = ((path_prod (x, y) (x', y) alpha 1) @ (path_prod (x', y) (x', y') 1 alpha')). 
  induction alpha.
  induction alpha'. 
  reflexivity.
Defined.


Class IsMonoid (A : hSet) (m : A -> A -> A) (e : A) 
  := BuildIsMonoid {
         m_unitr : forall a : A, m a e = a ;
         m_unitl : forall a : A, m e a = a ;
         m_assoc : forall x y z : A, m x (m y z) = m (m x y) z
       }.

Record Monoid 
  := BuildMonoid {
         m_set :> hSet ;
         m_mult :> m_set -> m_set -> m_set ;
         m_unit :> m_set ;
         m_ismonoid :> IsMonoid m_set m_mult m_unit
       }.

Theorem hprop_inverse_exists (G : hSet) (m : G -> G -> G) (e : G) 
        (HG : IsMonoid G m e)
: forall x, IsHProp {y : G & (m x y = e) * (m y x = e)}.
Proof.
  intro x.
  (* reduce to uniqueness of inverse *)
  assert (forall y : G, IsHProp ((m x y = e) * (m y x = e))). intro y.
  apply hprop_prod; intros p q; apply G.
  apply hprop_inhabited_contr. intro u. exists u.
  intro v. apply path_sigma_hprop.

  (* inverse is unique *)
  destruct HG.
  refine ((m_unitr0 _)^ @ _).
  refine (_ @ (m_unitl0 _)). 
  path_via (m u.1 (m x v.1)). f_ap. symmetry. apply (fst v.2).
  path_via (m (m u.1 x) v.1). f_ap. apply (snd u.2).
Defined.


Class IsGroup (A : Monoid) (i : A -> A) 
  := BuildIsGroup {
         g_invr : forall a : A, (m_mult A) a (i a) = (m_unit A) ;
         g_invl : forall a : A, (m_mult A) (i a) a = (m_unit A)
       }.

Record Group 
  := BuildGroup {
         g_monoid :> Monoid ;
         g_inv :> (m_set g_monoid) -> (m_set g_monoid) ;
         g_isgroup :> IsGroup g_monoid g_inv
       }.

Theorem issig_group `{Funext} : 
  {G : Monoid & {i : G -> G & forall a, (G a (i a) = G) * (G (i a) a = G)}} 
    <~>
    Group.
Proof.
  apply (@equiv_compose' _ {G : Monoid & {i : G -> G & IsGroup G i}} _).
  issig BuildGroup g_monoid g_inv g_isgroup.
  apply equiv_functor_sigma_id. intro G.
  apply equiv_functor_sigma_id. intro i.
  apply (@equiv_compose' _
                         {_ : forall a, (G a (i a) = G)
                                & (forall a : G, G (i a) a = G)}
                         _).
  issig (BuildIsGroup G i) (@g_invr G i) (@g_invl G i).
  simple refine (equiv_adjointify _ _ _ _); intro z.
    apply (fun a => fst (z a); fun a => snd (z a)).
    apply (fun a => (z.1 a, z.2 a)).
    destruct z as [g h]. apply path_sigma_uncurried. exists 1. reflexivity.
    apply path_forall; intro a. apply eta_prod.
Defined.
  
Theorem ex6_7 `{Funext} :
  {G : Monoid & forall x, Brck {y : G & (G x y = G) * (G y x = G)}}
  <~>
  Group.
Proof.
  apply (@equiv_compose' _
                         {G : Monoid & 
                          forall x : G, {y : G & (G x y = G) * (G y x = G)}} 
                         _).
  apply (@equiv_compose' _
                         {G : Monoid & 
                         {i : G -> G & 
                          forall a, (G a (i a) = G) * (G (i a) a = G)}} 
                         _).
  apply issig_group. 
  apply equiv_functor_sigma_id. intro G.
  apply equiv_inverse. refine (equiv_sigT_coind _ _).
  apply equiv_functor_sigma_id. intro G.
  apply equiv_functor_forall_id. intro x.
  apply equiv_inverse.
  apply ex3_21.
  destruct G as [G m e HG]. simpl in *.
  apply hprop_inverse_exists.
  apply HG.
Defined.


Local Open Scope list_scope.

Fixpoint list_code {A : Type} (l l' : list A) : Type :=
  match l with
    | nil => match l' with
               | nil => Unit
               | h' :: t' => Empty
             end
    | h :: t => match l' with
                    | nil => Empty
                    | h' :: t' => (h = h') * (list_code t t')
                  end
  end.

Fixpoint list_r {A : Type} (l : list A) : list_code l l :=
  match l with
    | nil => tt
    | h :: t => (1, list_r t)
  end.

Definition list_encode {A : Type} (l l' : list A) (p : l = l') := 
  transport (fun x => list_code l x) p (list_r l).

Definition list_decode {A : Type} : 
  forall (l l' : list A) (z : list_code l l'), l = l'.
  induction l as [| h t]; destruct l' as [| h' t']; intros.
    reflexivity. contradiction. contradiction.
    apply (@ap _ _ (fun x => cons (fst x) (snd x)) (h, t) (h', t')).
    apply path_prod. apply (fst z). apply IHt. apply (snd z).
Defined.

Definition path_list {A : Type} : forall (h h' : A) (t t' : list A),
  h = h' -> t = t' -> h :: t = h' :: t'.
Proof.
  intros h h' t t' ph pt.
  apply (list_decode _ _). split. 
    apply ph.
    apply (list_encode _ _). apply pt.
Defined.

Theorem equiv_path_list {A : Type} {H : IsHSet A} (l l' : list A) : 
  (list_code l l') <~> (l = l').
Proof.
  refine (equiv_adjointify (list_decode l l') (list_encode l l') _ _).

  (* lst_decode o lst_encode == id *)
  intro p. induction p. 
  induction l as [|h t]. reflexivity. simpl in *.
  refine (_ @ (ap_1 _ _)). f_ap.
  transitivity (path_prod (h, t) (h, t) 1 1). f_ap. reflexivity.

  (* lst_encode o lst_decode == id *)
  generalize dependent l'.
  induction l as [|h t], l' as [|h' t']; intro z.
    apply contr_unit. contradiction. contradiction.
    simpl. unfold list_encode.
    refine ((transport_compose _ _ _ _)^ @ _).
    refine ((transport_prod 
               (path_prod (h, t) (h', t') (fst z) (list_decode t t' (snd z)))
               (1, list_r t)) @ _).
    destruct z as [p c].
    apply path_prod. apply H.
    refine ((transport_path_prod _ _ _ _) @ _).
    induction p. apply (IHt t').
Defined.


Theorem app_nil_r {A : Type} : forall l : list A, l ++ nil = l.
Proof. induction l. reflexivity. simpl. f_ap. Defined.

Theorem app_assoc {A : Type} : forall x y z : list A,
  x ++ (y ++ z) = (x ++ y) ++ z.
Proof. 
  intros x y z. induction x. reflexivity.
  simpl. apply path_list. reflexivity. apply IHx.
Defined.


Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Class IsMonoidHom {A B : Monoid} (f : A -> B) :=
  BuildIsMonoidHom {
      hunit : f (m_unit A) = m_unit B ;
      hmult : forall a a' : A, f ((m_mult A) a a') = (m_mult B) (f a) (f a')
    }.

Record MonoidHom (A B : Monoid) := 
  BuildMonoidHom {
      mhom_fun :> A -> B ;
      mhom_ismhom :> IsMonoidHom mhom_fun
    }.


Theorem isprod_ismonoidhom {A B : Monoid} (f : A -> B) :
  (f (m_unit A) = m_unit B) 
  * (forall a a', f ((m_mult A) a a') = (m_mult B) (f a) (f a'))
  <~>
  IsMonoidHom f.
Proof.
  (* I think this should be a judgemental equality, but it's not *)
  etransitivity {_ : f A = B & forall a a' : A, f (A a a') = B (f a) (f a')}.
  simple refine (equiv_adjointify _ _ _ _); intro z.
    exists (fst z). apply (snd z). apply (z.1, z.2). 
    apply eta_sigma. apply eta_prod.
    
  issig (BuildIsMonoidHom A B f) (@hunit A B f) (@hmult A B f).
Defined.

Module Exercise6_10.

Module Interval.

Private Inductive interval : Type :=
  | zero : interval
  | one : interval.

Axiom seg : zero = one.

Definition interval_rect (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b)
  : forall x : interval, P x
  := fun x => (match x return _ -> P x with
                 | zero => fun _ => a
                 | one => fun _ => b
               end) p.

Axiom interval_rect_beta_seg : forall (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b),
  apD (interval_rect P a b p) seg = p.

End Interval.

  
 
End Exercise6_10.


Theorem univ_prop_susp `{Funext} {A B : Type} :
  (Susp A -> B) <~> {bn : B & {bs : B & A -> (bn = bs)}}.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  intro f. exists (f North). exists (f South). intro a. apply (ap f (merid a)).
  intro w. destruct w as [bn [bs f]]. apply (Susp_rec bn bs f).

  intro w. destruct w as [bn [bs f]]. 
  apply path_sigma_uncurried. exists 1. 
  apply path_sigma_uncurried. exists 1. 
  apply path_forall; intro a. simpl.
  apply Susp_rec_beta_merid.

  intro f. apply path_forall.
  refine (Susp_ind _ 1 1 _).
  intro a. 
  simpl.
  refine ((@transport_paths_FlFr _ _ _ f _ _ _ _) @ _).
  apply moveR_pM.
  refine ((concat_p1 _) @ _). refine (_ @ (concat_1p _)^). apply inverse2.
  refine ((Susp_rec_beta_merid _) @ _).
  reflexivity.
Defined.
  



Lemma hset_prod : forall A, IsHSet A -> forall B, IsHSet B -> IsHSet (A * B).
Proof.
  intros A HA B HB.
  intros z z'. apply hprop_allpath. apply path_ishprop.
Defined.

Module Exercise6_12.


Fixpoint monus n m :=
  match m with
    | O => n
    | S m' => pred (monus n m')
  end.

Lemma monus_O_n : forall n, monus O n = O.
Proof. induction n. reflexivity. simpl. change O with (pred O). f_ap. Defined.

Lemma n_le_Sn : forall n, le n (S n).
Proof. intro n. exists (S O). apply (plus_1_r n)^. Defined.

Lemma monus_eq_O__n_le_m : forall n m, (monus n m = O) -> (le n m).
Admitted.

Lemma monus_self : forall n, monus n n = O.
Admitted.
  
Definition n_le_m__Sn_le_Sm : forall (n m : nat), (le n m) -> (le (S n) (S m))
  := fun n m H => (H.1; ap S H.2).

Lemma order_partitions : forall (n m : nat), (le n m) + (lt m n).
Proof.
  induction n.
    intro m. left. exists m. reflexivity.
  induction m.
    right. exists n. reflexivity.
    destruct IHm.
      left. destruct l as [x p]. exists (S x).
      simpl. apply (ap S). apply ((plus_n_Sm _ _)^ @ p).
      destruct (IHn m).
        left. apply n_le_m__Sn_le_Sm. apply l0.
        right. destruct l0 as [x p]. exists x. simpl. apply (ap S). apply p.
Defined.
  

Definition r : nat * nat -> nat * nat.
  intro z. destruct z as [a b].
  destruct (order_partitions b a).
  apply (monus a b, O).
  apply (O, monus b a).
Defined.
  
Definition int := {x : nat * nat & r x = x}.

Definition int_to_nat_1_nat : int -> (nat + Unit + nat).
  intro z. destruct z as [[a b] p]. destruct (decidable_paths_nat a b).
  left. right. apply tt.
  destruct (order_partitions b a).
  right. apply (pred (monus a b)).
  left. left. apply (pred (monus b a)).
Defined.

Definition nat_1_nat_to_int : (nat + Unit + nat) -> int :=
  fun z =>
    match z with
      | inl a => match a with
                   | inl n => ((O, S n); 1)
                   | inr _ => ((O, O); 1)
                 end
      | inr n => ((S n, O); 1)
    end.
        
Lemma lt_le : forall n m, (lt n m) -> (le n m).
Proof.
  intros n m p. destruct p as [k p]. exists (S k). 
  apply p.
Defined.


Theorem ex6_12 : int <~> (nat + Unit + nat).
Proof.
  refine (equiv_adjointify int_to_nat_1_nat nat_1_nat_to_int _ _).
  
  intro z. destruct z as [[n | n] | n].
  reflexivity. 
  unfold int_to_nat_1_nat. simpl. repeat f_ap. apply contr_unit. reflexivity.
  
  intro z. destruct z as [[a b] p].
  apply path_sigma_uncurried.
  assert (
    (nat_1_nat_to_int (int_to_nat_1_nat ((a, b); p))).1 = ((a, b); p).1
  ) as H.
  unfold nat_1_nat_to_int, int_to_nat_1_nat, r in *. simpl in *.
  destruct (decidable_paths_nat a b).
  destruct (order_partitions b a). refine (_ @ p).
    apply path_prod. 
    assert (b = O). apply (ap snd p)^. 
    assert (a = O). apply (p0 @ X).
    simpl. transitivity (monus a 0). simpl. apply X0^. f_ap. apply X^.
    reflexivity.
    assert (a = O). apply (ap fst p)^. assert (b = O). apply (p0^ @ X). simpl. 
    apply path_prod. apply X^. apply X0^.

  destruct (order_partitions b a); refine (_ @ p);
    apply path_prod.
    simpl. refine ((Spred _ _) @ _).
    intro H. apply monus_eq_O__n_le_m in H. 
    apply le_antisymmetric in H. symmetry in H. apply n in H. contradiction.
    apply l. reflexivity. reflexivity. reflexivity.
    simpl. refine ((Spred _ _) @ _).
    intro H. 
    assert (a = b). refine ((ap fst p)^ @ H^ @ (ap snd p)).  apply n in X.
    contradiction. reflexivity. simpl in *.
    
    exists H.
    assert (IsHSet (nat * nat)) as Hn. apply hset_prod; apply hset_nat.
    apply set_path2.
Defined.

Definition int' := nat + Unit + nat.

End Exercise6_12.
