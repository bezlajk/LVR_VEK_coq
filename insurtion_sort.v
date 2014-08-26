Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Sorting.

(** Aktiviramo notacijo za sezname. *)
Local Open Scope list_scope.
(** Definicija vstavlanja elementov v seznam. **)
Function vstavi (x:Z) (l: list Z) :=
     match l with
      | nil => x::nil
      | y::l' => if (x <=? y)%Z then x::y::l' else y::(vstavi x l')
end.

(** Urejanje seznama po principu insertion sort-a. **)
Fixpoint insert (l:list Z) :=
     match l with
      | nil => nil
      | x::l' => let l'' := (insert l') in vstavi x l''
end. 

Eval compute in (insert (2 :: 5 :: 1 :: 4 :: nil)%Z).

(** Dodajanje elementa ohranja urejen seznam. **)
Lemma urejen_t (a: Z) (l: list Z):
  urejen l -> urejen (vstavi a l).
Proof.
  intro.
  induction l.
  - auto.
  - simpl.
    case_eq (a <=? a0)%Z.
    + destruct l.
      * intro.
        apply Zle_bool_imp_le in H0.
        simpl.
        auto.
      * case_eq (a0 <=? z)%Z.
        apply urejen_tail in H. firstorder.
        apply Zle_bool_imp_le in H1; auto.
        apply Zle_bool_imp_le in H0; auto.
        firstorder.
        apply Zle_bool_imp_le in H1; auto.
   + firstorder; simpl.
     destruct l. 
     * firstorder.
       apply Z.leb_gt in H0.
       apply Z.lt_le_incl in H0.
       auto.
     * apply Z.leb_gt in H0. simpl.
       case_eq (a <=? z)%Z.
       apply Z.lt_le_incl in H0.
       split; auto.
       apply Zle_bool_imp_le in H1. firstorder.
       intro.
       SearchAbout  [(_ <=? _)%Z].
       apply Z.leb_gt in H1.
       destruct H.
       split. assumption.
       replace (z :: vstavi a l) with (vstavi a (z :: l)). 
       now apply IHl.
       simpl.
       case_eq (a<=?z)%Z.
       proof.
          intro.
          absurd ((a<=?z)%Z = true). 
          - rewrite -> not_true_iff_false.
               now apply Z.leb_gt.
          - assumption.
       end proof.
       intro.
       reflexivity.
Qed.

Lemma dodaj_glavo:
  forall (x:Z)(l:list Z), pojavi x (x :: l) = S (pojavi x l).

Proof.
  intros x l.
  simpl.
  case_eq (x=?x)%Z.
    - intro. auto.
    - intro. absurd ((x=?x)%Z = false).
      + SearchAbout (?A <> false).
        rewrite -> not_false_iff_true.
        apply Z.eqb_eq.
        reflexivity.
      + assumption.
Qed.

Lemma druga_glava:
   forall (x:Z)(a:Z)(l:list Z), 
          ((x =? a)%Z = false) -> pojavi x l = pojavi x (a :: l).

Proof.
  intros x a l H.
  simpl.
  case_eq (x=?a)%Z; intro.
  - absurd ((x =? a)%Z = false).
    + rewrite -> not_false_iff_true; assumption.
    + assumption.
  - reflexivity.
Qed.

Lemma ista_glava:
   forall (x:Z)(l:list Z)(l':list Z),(pojavi x l)=(pojavi x l') -> pojavi x (x :: l) = pojavi x (x :: l').

Proof.
  intros x l l' H.
  simpl.
  case_eq (x =? x)%Z.
  - intro.
    apply eq_S.
    assumption.
  - intro.
    assumption.
Qed.

Lemma vstavi_pojavitev:
  forall (x:Z)(l: list Z), S(pojavi x l)= pojavi x (vstavi x l).

Proof.
  induction l.
  - simpl. case_eq (x=?x)%Z.
    + intro. auto.
    + intro. absurd ((x=?x)%Z = false).
      * SearchAbout (?A <> false).
        rewrite -> not_false_iff_true.
        apply Z.eqb_eq.
        reflexivity.
      * assumption.
  - simpl.
    case_eq (x =? a)%Z.
    + intro.
      apply Z.eqb_eq in H.
      rewrite <- H. 
      case_eq (x <=? x)%Z.
      * intro.
        rewrite -> IHl.
        rewrite -> dodaj_glavo.
        apply eq_S.
        rewrite <- IHl. 
        rewrite <- dodaj_glavo.
        reflexivity.
      * intro.
        absurd ((x <=? x)%Z = false).
        apply not_false_iff_true.
        apply Z.leb_refl.
        assumption.
   + intro.
     case_eq (x <=? a)%Z. 
     * intro.
       rewrite <- dodaj_glavo.
       apply ista_glava.
       apply druga_glava.
       assumption.
     * intro.
       rewrite -> IHl.
       apply druga_glava.
       assumption.
Qed.

Lemma vstavi_nepojavitev:
  forall (x:Z)(a:Z)(l: list Z), (x<>a) -> pojavi x l= pojavi x (vstavi a l).
 
Proof.
  intros x a l H.
  induction l.
  - simpl.
    case_eq (x =? a)%Z.
    + intro.
      rewrite -> Z.eqb_eq in H0.
      absurd (x=a); auto. 
    + auto.
  - simpl.
    case_eq (x =? a)%Z.
    + intros.
      absurd (x=a)%Z.
      * auto.
      * apply Z.eqb_eq in H0; assumption.
    + intros.
      case_eq (x =? a0)%Z.
      * intros.
        case_eq (a <=? a0)%Z.
          intros.
          rewrite <- druga_glava ; [idtac|assumption].
          apply Z.eqb_eq in H1.
          replace  a0 with x. 
          rewrite <- dodaj_glavo; auto.
        
          intros.
          apply Z.eqb_eq in H1.
          replace  a0 with x.
          rewrite -> dodaj_glavo. 
          apply eq_S.
          assumption.
      * intros.
        case_eq (a <=? a0)%Z.
        intros. 
        rewrite <- druga_glava; [idtac | assumption].
        rewrite <- druga_glava; [auto | assumption].
    
        intros.
        rewrite <- druga_glava; [idtac | assumption].
        apply IHl.     
Qed.
    

Theorem permutacija:
  forall (l: list Z), (permutiran l (insert l)).
Proof.
  intro.
  induction l.
  - firstorder.
  - intro.
    simpl.
    case_eq (x =? a)%Z.
    + intro.
      apply Z.eqb_eq in H.
      replace a with x.
      replace (pojavi x l) with (pojavi x (insert l)). 
      apply vstavi_pojavitev.
      apply permutiran_sym.
      assumption.
    + intro.  
      apply Z.eqb_neq in H.
      replace (pojavi x l) with (pojavi x (insert l)). 
      apply vstavi_nepojavitev; assumption.
      apply permutiran_sym.
      assumption.
Qed.

Theorem urejenost:
  forall (l : list Z), urejen (insert l).
Proof.
  intro.
  induction l; firstorder.
  simpl.
  apply urejen_t.
  assumption.
Qed.

Theorem vse_dela_pravilno:
  forall (l : list Z), urejen (insert l) /\ permutiran l (insert l).

Proof.
  split; [apply urejenost | apply permutacija].
Qed.





































Theorem Mi_smo_najboljsa_skupina:
      true=true.
Admitted.
(**"Malo zabave za profesorja. :D" **).








