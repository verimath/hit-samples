Require Export HoTT Ch03.
Require Import HIT.TwoSphere.

Theorem ex4_1 `{Univalence} (A B : Type) (f : A <~> B) :
  {g : B -> A & {h : g o f == idmap & {e : f o g == idmap &
    (forall x, ap f (h x) = e (f x)) * (forall y, ap g (e y) = h (g y))}}}
  <~>
  forall x : A, @idpath _ x = @idpath _ x.
Proof.
  set (p := path_universe f).
  assert (fisp : f = equiv_path _ _ p).
    apply path_equiv. apply path_forall; intro a. simpl.
    unfold p. symmetry. apply transport_path_universe.
  clearbody p. induction p. rewrite fisp. simpl. 

  equiv_via ({g : A -> A & {h : g == idmap & {e : g == idmap &
    (h == e) 
  * ((fun y => ap g (e y)) == (fun y => h (g y)))}}}).
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro g. simpl.
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro h. simpl.
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e. simpl.
  simple refine (equiv_functor_prod' _ _). 
  simple refine (equiv_functor_forall' _ _). apply equiv_idmap. intro b. simpl.
  simple refine (equiv_adjointify _ _ _ _). 
    intro eq. apply ((ap_idmap _)^ @ eq).
    intro eq. apply ((ap_idmap _) @ eq).
    intro eq. hott_simpl.
    intro eq. hott_simpl.
  apply equiv_idmap.
  
  equiv_via ({g : A -> A & {h : g == idmap & {e : g == idmap &
   (h = e) * ((fun y => ap g (e y)) = (fun y => h (g y)))}}}).
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro g. simpl.
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro h. simpl.
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e. simpl.
  simple refine (equiv_functor_prod' _ _). 
  apply equiv_path_forall.
  apply equiv_path_forall.

  equiv_via ({h : {g : A -> A & g == idmap} & {e : h.1 == idmap &
   (h.2 = e) * ((fun y => ap h.1 (e y)) = (fun y => h.2 (h.1 y)))}}).
  refine (equiv_sigma_assoc _ _).

  transparent assert (HC : (Contr {g : A -> A & g == idmap})).
  exists (idmap; (fun x => 1)).
  intro h. destruct h as [g h].
  apply path_sigma_uncurried. simpl.
  exists (path_forall (fun x : A => x) g (fun x : A => (h x)^)).
  unfold pointwise_paths.
  apply path_forall; intro a.
  refine ((transport_forall_constant _ _ _) @ _).
  refine ((@path_forall_1_beta _ A (fun _ => A) a (fun z => z = a)
                               idmap g _ 1) @ _).
  refine ((transport_paths_l _ _) @ _).
  refine ((concat_p1 _) @ _).
  apply inv_V.
  equiv_via ({e : (center {g : A -> A & g == idmap}).1 == idmap &
   ((center {g : A -> A & g == idmap}).2 = e) 
   * ((fun y => ap (center {g : A -> A & g == idmap}).1 (e y)) 
      = (fun y => (center {g : A -> A & g == idmap}).2 
                     ((center {g : A -> A & g == idmap}).1 y)))}).
  refine (equiv_sigma_contr_base _ _ _).
  simpl. clear HC.
  
  equiv_via ({e : (fun x : A => x) == idmap & 
             {p : (fun x => 1) = e 
             & ((fun y : A => ap idmap (e y)) = (fun y : A => 1))}}).
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e.
  simple refine (equiv_adjointify _ _ _ _); simpl.
  intro p. apply (fst p; snd p).
  intro p. split. apply p.1. apply p.2.
  intro p. simpl. apply eta_sigma.
  intro p. simpl. apply eta_prod.

  equiv_via ({h : {e : (fun x:A => x) == idmap & (fun x => 1) = e} 
                    & (fun y : A => ap idmap (h.1 y)) = (fun y : A => 1)}).
  refine (equiv_sigma_assoc _ _).

  equiv_via ({h : {e : (fun x:A => x) == idmap & (fun x : A => 1) = e} 
                    & (fun y : A => h.1 y) = (fun y : A => 1)}).
  simple refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e. simpl.
  simple refine (equiv_adjointify _ _ _ _); simpl.
  intro eq. apply path_forall; intro a. refine (_ @ (apD10 eq a)).
    apply (ap_idmap _)^.
  intro eq. apply path_forall; intro a. refine ((ap_idmap _) @ _).
    apply (apD10 eq a).
  intro eq. refine (_ @ (eta_path_forall _ _ _)).
    apply (ap (path_forall _ _)). apply path_forall; intro a.
    apply moveR_Vp. refine ((apD10_path_forall _ _ _ a) @ _).
    reflexivity.
  intro eq. refine (_ @ (eta_path_forall _ _ _)).
    apply (ap (path_forall _ _)). apply path_forall; intro a.
    apply moveR_Mp. refine ((apD10_path_forall _ _ _ a) @ _).
    reflexivity.

  equiv_via ((fun y : A => (center {e : (fun x:A => x) == idmap & (fun x : A => 1) = e}).1 y) = (fun y : A => 1)).
  simple refine (equiv_sigma_contr_base _ _ _).

  simple refine (equiv_adjointify _ _ _ _).
  - intro eq. intro x. refine (_ @ (apD10 eq x)).
    apply (apD10 (center {e: (fun x:A => x) == idmap & (fun x:A => 1) = e}).2 x).
  - intro eq. apply path_forall. intro y.
    refine (_ @ (eq y)).
    apply (apD10 (center {e: (fun x:A => x) == idmap & (fun x:A => 1) = e}).2^ y).
  - intro eq. apply path_forall. intro x.
    apply moveR_Mp. refine ((apD10_path_forall _ _ _ _) @ _).
    refine (whiskerR _ (eq x)). refine (apD10_V _ x).
  - intro eq. apply (ap apD10)^-1. apply path_forall. intro x.
    refine ((apD10_path_forall _ _ _ _) @ _). apply moveR_Mp.
    refine (whiskerR _ (apD10 eq x)).
    refine (_ @ (apD10_V _ _)). f_ap. 
Defined.

Lemma not_all_sets `{Univalence} : ~ forall A, IsHSet A.
Proof.
  intro oops.
  apply idmap_bool_ne_negb.
  refine ((equiv_path_path_universe _)^ @ _).
  refine (_ @ (equiv_path_path_universe _)). f_ap.
  apply oops.
Defined.

Lemma loop_ne_1 `{Univalence} : loop <> 1.
Proof.
  intro oops.
  apply not_all_sets. intros A x y. apply hprop_allpath.
  intros p q. induction q.
  refine ((S1_rec_beta_loop A x p)^ @ _).
  refine (ap (ap _) oops).
Defined.

Lemma Book_6_4_2 `{Univalence} : {h : forall (x : S1), x = x & h <> (fun x => 1)}.
Proof.
  simple refine (S1_ind _ loop _; _).
  - refine ((transport_paths_lr _ _) @ _).
    refine ((ap (fun w => w @ _) (concat_Vp _)) @ _).
    refine (concat_1p _).
  - intro oops. apply loop_ne_1.
    apply (apD10 oops Circle.base).
Defined.

Definition not_all_1type `{U : Univalence} : ~ (forall A, IsTrunc 1 A).
Proof.
  intro oops. apply Book_6_4_2.2.
  simple refine (equiv_hprop_allpath _ _ _ _).
  simple refine (trunc_equiv (@paths (S1 -> S1) idmap idmap) _).
  - apply apD10.
  - simple refine (trunc_equiv (@equiv_idmap S1 = @equiv_idmap S1) 
                        (@path_equiv _ _ _ 1%equiv 1%equiv)^-1).
    apply hprop_allpath. simple refine (@set_path2 (S1 <~> S1) _ _ _).
    simple refine (trunc_equiv (S1 = S1) _).
    + apply equiv_path.
    + apply isequiv_equiv_path.
  - apply isequiv_apD10.
Defined.

Definition surf_ne_1 `{Univalence} : surf <> 1.
Proof.
  intro oops. apply not_all_1type.
  intros A x y p q. apply hprop_allpath. intros r s.
  induction s, p.
  refine ((S2_rec_beta_surf A x r)^ @ _).
  refine (ap (ap02 _) oops).
Defined.

Definition ap_homotopic {A B : Type} (f g : A -> B) (h : f == g)
         {x y : A} (q : x = y)
: ap f q = h x @ ap g q @ (h y)^.
Proof.
  apply moveL_pV. apply concat_Ap.
Defined.

  
Definition Book_6_4_2' `{Univalence}
: {h : forall x : S2, (idpath x) = 1 & h <> (fun x => 1)}.
Admitted.
    

Definition ex4_1' `{Univalence} : ~ IsHProp (forall x : S2, (idpath x) = 1).
Proof.
  intro oops. apply Book_6_4_2'.2.
  apply (equiv_hprop_allpath _ _ _ _).
Defined.
  


Definition equiv_to_contr_rel_equiv (A B : Type) :
  (A <~> B)
  ->
  {R : A -> B -> Type & (forall a, Contr {b : B & R a b})
                      * (forall b, Contr {a : A & R a b})}.
Proof.
  intro e.
  exists (fun a b => (e a = b)). split. 
  intro a. apply contr_basedpaths.
  intro b. refine (@contr_equiv' {a : A & e^-1 b = a} _ _ _).
  simple refine (equiv_functor_sigma' _ _).
  apply equiv_idmap. intro a. simpl.
  simple refine (equiv_adjointify _ _ _ _).
  intro eq. simple refine (_ @ (eisretr e b)). apply (ap e). apply eq^.
  intro eq. simple refine (_ @ (eissect e a)). apply (ap e^-1). apply eq^.
  intro eq. induction eq. simpl. 
  apply moveR_pM. refine (_ @ (concat_1p _)^). refine ((ap_V _ _) @ _).
  apply inverse2. refine ((ap_pp _ _ _) @ _).
  apply moveR_pM. refine ((ap_1 _ _ ) @ _). apply moveL_pV.
  refine ((concat_1p _) @ _). apply (eisadj e a)^.

  intro eq. induction eq. simpl.
  apply moveR_pM. refine ((ap_V _ _) @ _). refine (_ @ (concat_1p _)^).
  apply inverse2. refine ((ap_pp _ _ _) @ _). apply moveR_pM.
  refine ((ap_1 _ _) @ _). apply moveL_pV. refine ((concat_1p _) @ _).
  apply (other_adj _ _)^.
Defined.

Theorem isequiv_equiv_to_contr_rel_equiv `{Univalence} (A B : Type) :
  IsEquiv (equiv_to_contr_rel_equiv A B).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  intro R. destruct R as [R [f g]].
  simple refine (equiv_adjointify _ _ _ _).
  intro a. apply (center {b : B & R a b}).1.
  intro b. apply (center {a : A & R a b}).1.
  
  intro b. simpl. 
  destruct (center {a : A & R a b}) as [a p]. simpl.
  destruct (center {b0 : B & R a b0}) as [b' q]. change b with (b; p).1.
  apply (ap pr1). apply path_ishprop.

  intro a. simpl.
  destruct (center {b : B & R a b}) as [b q]. simpl.
  destruct (center {a0 : A & R a0 b}) as [a' p]. 
  change a with (@pr1 _ (fun a' => R a' b) (a; q)).
  apply (ap pr1). apply path_ishprop.

  intro R. apply path_sigma_hprop. destruct R as [R [f g]]. simpl.
  apply path_forall; intro a. apply path_forall; intro b.
  destruct (center {b0 : B & R a b0}) as [b' p]. simpl. 
  apply path_universe_uncurried.
  simple refine (equiv_adjointify _ _ _ _).
  intro eq. apply (transport _ eq). apply p.
  intro q. change b with (b; q).1. change b' with (b'; p).1. apply (ap pr1).
  refine (path_contr _ _). apply (f a).
  intro q. refine ((pr2_path (path_contr (b'; p) (b; q))) @ _). reflexivity.
  intro eq. induction eq. simpl.
  path_via (@ap {b : B & R a b} _ pr1 (b'; p) _ 1). f_ap.
  apply concat_Vp.

  intro e. apply path_equiv. reflexivity.
Defined.

Definition qinv {A B : Type} (f : A -> B) :=
  {g : B -> A & (f o g == idmap) * (g o f == idmap)}.

Definition qinv_isequiv A B (f : A -> B) (p : qinv f) : IsEquiv f
  := isequiv_adjointify f p.1 (fst p.2) (snd p.2).

Definition isequiv_qinv : forall A B (f : A -> B), IsEquiv f -> qinv f.
Proof.
  intros A B f p. destruct p.
  exists equiv_inv. split. apply eisretr. apply eissect.
Defined.

Definition isequiv' {A B} (f : A -> B) :=
  (forall a, Contr {b : B & f a = b}) * (forall b, Contr {a : A & f a = b}).

Theorem ex4_2_i A B (f : A -> B) : qinv f -> isequiv' f.
Proof.
  intro p. apply qinv_isequiv in p. 
  set (Hf := BuildEquiv A B f p).
  set (HR := equiv_to_contr_rel_equiv A B Hf).
  set (R := pr1 HR). 
  set (Q := pr2 HR).
  split. apply (fst Q). apply (snd Q).
Defined.

Theorem ex4_2_ii A B (f : A -> B) : isequiv' f -> qinv f.
Proof.
  intro p. destruct p as [sect retr].
  transparent assert (g : (B -> A)).
  intro b. destruct (retr b). apply center.1.
  exists g. split.
  unfold g. intro b. destruct (retr b). apply center.2.
  unfold g. intro a. destruct (retr (f a)). 
  apply (ap pr1 (contr (a; 1))).
Defined.

Lemma hprop_prod : forall A, IsHProp A -> forall B, IsHProp B -> IsHProp (A * B).
Proof.
  intros A HA B HB z z'.
  apply (trunc_equiv' _ (equiv_path_prod z z')).
Defined.

Theorem ex4_2_iii `{Funext} A B (f : A -> B) : IsHProp (isequiv' f).
Proof.
  unfold isequiv'.
  typeclasses eauto.
Defined.
  



Theorem concat_Ap_w (A B : Type) (f g : A -> B) (p : forall x : A, f x = g x)
         (x y : A) (q : x = y)
  : ap f q  = p x @ ap g q @ (p y)^.
Proof.
  apply moveL_pV. apply concat_Ap.
Defined.


Theorem Book_4_1_1 `{Funext} (A B : Type) (f : A <~> B) :
  qinv f <~> forall x : A, x = x.
Proof.
  unfold qinv.
  equiv_via ({h : {g : B -> A & (f o g == idmap)} & (h.1 o f == idmap)}).
  simple refine (equiv_adjointify _ _ _ _).
  intro w. exists (w.1; fst w.2). apply (snd w.2).
  intro w. exists w.1.1. split. apply w.1.2. apply w.2.
  intro w. destruct w as [[g h] e]. reflexivity.
  intro w. destruct w as [g [h e]]. reflexivity.
  
  transparent assert (H' : (Contr {g : B -> A & f o g == idmap})).
  exists (f^-1; eisretr f). intro h. destruct h as [w h].
  apply path_sigma_uncurried. simpl.
  exists (path_forall f^-1 w (fun b : B => ap f^-1 (h b)^ @ eissect f (w b))).
  unfold pointwise_paths.
  apply path_forall; intro b.
  refine ((transport_forall_constant _ _ _) @ _).
  refine ((@path_forall_1_beta _ B (fun _ => A) b (fun z => f z = b) _ _ _ _) 
            @ _).
  refine ((transport_paths_Fl _ _) @ _).
  apply moveR_Vp. apply moveL_pM.
  refine (_ @ (ap_pp _ _ _)^).
  apply moveL_Mp. refine (_ @ (eisadj _ _)).
  apply moveR_Vp. apply moveL_pM.
  refine (_ @ (ap_compose _ _ _)).
  refine (_ @ (concat_Ap_w _ _ _ idmap (eisretr f) _ _ _)^).
  apply concat2. apply concat2. reflexivity. apply (ap_idmap _)^. reflexivity.

  equiv_via ((center {g : B -> A & f o g == idmap}).1 o f == idmap).
  refine (equiv_sigma_contr_base _ _ _).
  simpl. clear H'.

  simple refine (equiv_adjointify _ _ _ _).
  intro h. apply path_forall in h. intro x. refine ((eissect f _)^ @ _).
  apply (ap10 h x).
  intro h. intro x. refine ((eissect f _) @ _). apply (h x).
  intro h. apply path_forall; intro a.
  apply moveR_Vp. refine ((ap10_path_forall _ _ _ a) @ _). reflexivity.
  intro h. apply path_forall; intro a.
  apply moveR_Mp. apply concat2. reflexivity.
  refine ((ap10_path_forall _ _ _ a) @ _). reflexivity.
Defined.



Lemma equiv_prod_unit (A : Type) : A <~> A * Unit.
Proof.
  refine (equiv_adjointify (fun a => (a, tt)) (fun z => fst z) _ _).
  intro z. apply path_prod. reflexivity. apply eta_unit.
  intro a. reflexivity.
Defined.

Module Ex4.

Variables (A B C D : Type) (f : A -> B) (g : B -> C) (b : B).

Definition f_star (z : hfiber (g o f) (g b)) : hfiber g (g b) := 
  (f z.1; z.2).

Theorem ex4_4_i : hfiber (f_star) (b; 1) <~> hfiber f b.
Proof.
  equiv_via {a : A & {p : g (f a) = g b & (f_star (a; p) = (b; 1))}}.
  apply equiv_inverse. refine (equiv_sigma_assoc _ _). unfold f_star. simpl.

  equiv_via {a : A & {p : g (f a) = g b & {q : f a = b & 
               transport (fun x => g x = g b) q p = 1}}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_functor_sigma_id _). intro p.
  apply equiv_inverse. 
  refine (equiv_path_sigma (fun x => g x = g b) (f a; p) (b; 1)).
  
  equiv_via {a : A & {q : f a = b & {p : g (f a) = g b & 
               transport (fun x => g x = g b) q p = 1}}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_sigma_comm _ _ _).

  equiv_via {a : A & {q : f a = b & {p : g (f a) = g b & 
               p = transport (fun x => g x = g b) q^ 1}}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_functor_sigma_id _). intro p.
  refine (equiv_functor_sigma_id _). intro q.
  refine (BuildEquiv _ _ _ (isequiv_moveL_transport_V _ _ _ _)).
  
  equiv_via {a : A & {q : f a = b & Unit}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_functor_sigma_id _). intro p.
  refine equiv_contr_unit.

  refine (equiv_functor_sigma_id _). intro a.
  equiv_via ((f a = b) * Unit). refine (equiv_const_sigma_prod _ _).
  apply equiv_inverse. refine (equiv_prod_unit _).
Defined.

Theorem ex4_4_ii 
  : hfiber (g o f) (g b) <~> {w : hfiber g (g b) & hfiber f w.1}.
Proof.
  apply equiv_inverse. unfold hfiber.
  
  equiv_via {b' : B & {p : g b' = g b & {x : A & f x = b'}}}.
  apply equiv_inverse.
  refine (equiv_sigma_assoc _ _).

  equiv_via {b' : B & {x : A & {_ : g b' = g b & f x = b'}}}.
  refine (equiv_functor_sigma_id _). intro b'.
  refine (equiv_sigma_comm _ _ _).

  equiv_via {x : A & {b' : B & {_ : g b' = g b & f x = b'}}}.
  refine (equiv_sigma_comm _ _ _).
  
  refine (equiv_functor_sigma_id _). intro a.

  equiv_via {b' : B & {p : f a = b' & g b' = g b}}.
  refine (equiv_functor_sigma_id _). intro b'.
  equiv_via ((g b' = g b) * (f a = b')).
  refine (equiv_const_sigma_prod _ _).
  equiv_via ((f a = b') * (g b' = g b)).
  refine (equiv_prod_symm _ _).
  apply equiv_inverse.
  refine (equiv_const_sigma_prod _ _).
  
  
  equiv_via {w : {b' : B & f a = b'} & g w.1 = g b}.
  refine (equiv_sigma_assoc _ _).

  equiv_via (g (center {b' : B & f a = b'}).1 = g b).
  refine (equiv_sigma_contr_base _ _ _). simpl.

  simple refine (equiv_adjointify _ _ _ _).
  - intro eq. apply eq.
  - intro eq. apply eq.
  - intro eq. reflexivity.
  - intro eq. reflexivity.
Defined.
    
    

End Ex4.


Theorem two_out_of_six {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D) :
  IsEquiv (g o f) -> IsEquiv (h o g) ->
  (IsEquiv f /\ IsEquiv g /\ IsEquiv h /\ IsEquiv (h o g o f)).
Proof.
  intros Hgf Hhg. split.
  
  (* case f *)
  refine (isequiv_adjointify f ((g o f) ^-1 o g) _ _).
  intro b. 
  change (f (((g o f) ^-1 o g) b)) with ((f o (g o f) ^-1 o g) b).
  assert ((f o (g o f) ^-1 o g) b
          =
          ((h o g) ^-1 o (h o g) o f o (g o f) ^-1 o g) b).
  change (((h o g) ^-1 o (h o g) o f o (g o f) ^-1 o g) b)
         with ((((h o g) ^-1 ((h o g) ((f o (g o f) ^-1 o g) b))))).
  rewrite (eissect (h o g)). reflexivity.
  rewrite X.
  change (((h o g) ^-1 o (h o g) o f o (g o f) ^-1 o g) b)
         with ((((h o g) ^-1 o h) ((((g o f) ((g o f) ^-1 (g b))))))).
  rewrite (eisretr (g o f)).
  change (((h o g) ^-1 o h) (g b)) with (((h o g) ^-1 o (h o g)) b).
  apply (eissect (h o g)).

  intro a. apply (eissect (g o f)).

  split.
  (* case g *)
  refine (isequiv_adjointify g ((h o g) ^-1 o h) _ _).
  intro c.
  change (g (((h o g) ^-1 o h) c)) with ((g o (h o g) ^-1 o h) c).
  assert ((g o (h o g) ^-1 o h) c
          =
          (g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c).
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (((g o (h o g) ^-1 o h) ((g o f) ((g o f) ^-1 c)))).
  rewrite (eisretr (g o f)). reflexivity.
  rewrite X.
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (g (((h o g) ^-1 ((h o g) ((f o (g o f) ^-1) c))))).
  rewrite (eissect (h o g)).
  change (g ((f o (g o f) ^-1) c)) with (((g o f) o (g o f) ^-1) c).
  apply (eisretr (g o f)).

  intro b. apply (eissect (h o g)).

  split.
  (* case h *)
  refine (isequiv_adjointify h (g o (h o g) ^-1) _ _).
  intro d. apply (eisretr (h o g)).
  
  intro c.
  change ((g o (h o g) ^-1) (h c)) with ((g o (h o g) ^-1 o h) c).
  assert ((g o (h o g) ^-1 o h) c
          =
          (g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c).
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (((g o (h o g) ^-1 o h) ((g o f) ((g o f) ^-1 c)))).
  rewrite (eisretr (g o f)). reflexivity.
  rewrite X.
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (g ((h o g) ^-1 ((h o g) ((f o (g o f) ^-1) c)))).
  rewrite (eissect (h o g)).
  change (g ((f o (g o f) ^-1) c)) with (((g o f) o (g o f) ^-1) c).
  apply (eisretr (g o f)).
  
  (* case h o g o f *)
  refine (isequiv_adjointify (h o g o f) ((g o f) ^-1 o g o (h o g) ^-1) _ _).
  intro d.
  change ((h o g o f) (((g o f) ^-1 o g o (h o g) ^-1) d))
         with (h ((g o f) ((g o f) ^-1 ((g o (h o g) ^-1) d)))).
  rewrite (eisretr (g o f)).
  apply (eisretr (h o g)).

  intro a.
  change (((g o f) ^-1 o g o (h o g) ^-1) ((h o g o f) a))
         with ((((g o f) ^-1 o g) ((h o g) ^-1 ((h o g) (f a))))).
  rewrite (eissect (h o g)). apply (eissect (g o f)).
Qed.
  
Theorem isequiv_homotopic' : forall (A B : Type) (f g : A -> B),
  IsEquiv f -> f == g -> IsEquiv g.
Proof.
  intros A B f g p h.
  refine (isequiv_adjointify g f^-1 _ _).
  intros b. apply ((h (f^-1 b))^ @ (eisretr f b)).
  intros a. apply ((ap f^-1 (h a))^ @ (eissect f a)).
Defined.


Theorem Theorem2111' (A B : Type) (a a' : A) (f : A -> B) (H : IsEquiv f) :
  IsEquiv (fun p : a = a' => ap f p).
Proof.
  apply (two_out_of_six (fun p : a = a' => ap f p)
                        (fun p : (f a) = (f a') => ap f^-1 p)
                        (fun p : (f^-1 (f a)) = (f^-1 (f a')) => ap f p)).
  apply (isequiv_homotopic (fun p => (eissect f a) @ p @ (eissect f a')^)).
  intro p. induction p. hott_simpl.
  
  apply (isequiv_homotopic (fun p => (eisretr f (f a)) @ p @ (eisretr f (f a'))^)).
  intro p. induction p. hott_simpl.
Defined.



Module Ex6.

Hypothesis qinv_univalence : forall A B, qinv (equiv_path A B).

Theorem Book_4_9_2 (A B X : Type) (e : A <~> B) : (X -> A) <~> (X -> B).
Proof.
  destruct e as [f p].
  assert (qinv f) as q. exists f^-1. split. 
    apply (eisretr f). apply (eissect f).
  assert (A = B) as r. apply (qinv_univalence A B). 
  apply (BuildEquiv _ _ f p).
  path_induction. apply equiv_idmap.
Defined.


Lemma Book_4_1_2 `{Funext} (A : Type) (a : A) (q : a = a)
  : IsHSet (a = a) -> (forall x, Brck (a = x))
    -> (forall p : a = a, p @ q = q @ p)
    -> {f : forall (x : A), x = x & f a = q}.
Proof.
  intros eq g eta.
  transparent assert (Heq : (forall x y : A, IsHSet (x = y))).
  intros x y. 
  assert (Brck (a = x)) as p by auto. 
  assert (Brck (a = y)) as r by auto. 
  strip_truncations.
  simple refine (@trunc_equiv (a = a) _ _ _ _ _).
  intros s. apply (p^ @ s @ r).
  apply isequiv_concat_lr.
  set (B := fun x => {r : x = x & forall s : a = x, (r = s^ @ q @ s)}).
  transparent assert (HB : (forall x, (IsHProp (B x)))).
  intro x. assert (Brck (a = x)) as p by auto.
  strip_truncations.
  apply hprop_allpath. intros rh r'h'.
  destruct rh as [r h], r'h' as [r' h'].
  apply path_sigma_uncurried. exists ((h p) @ (h' p)^). simpl.
  apply path_forall. intro t. apply Heq.
  transparent assert (f' : (forall x, B x)).
  intro x. assert (Brck (a = x)) as p by auto. strip_truncations.
  exists (p^ @ q @ p). intro s. 
  apply moveL_pM. repeat (refine ((concat_pp_p _ _ _) @ _)).
  apply moveR_Vp. refine (_ @ (concat_pp_p _ _ _)).
  symmetry. apply eta.
  exists (fun x => (f' x).1).
  refine (((f' a).2 1) @ _).
  hott_simpl.
Defined.


  
End Ex6.
