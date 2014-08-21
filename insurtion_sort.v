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
   (**+ intro. simpl.
     destruct l; simpl; firstorder.
     * apply Z.leb_gt in H0.
       apply Z.lt_le_incl in H0.
       auto.
     * apply Z.leb_gt in H0.
       case_eq**)

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
          - SearchAbout ((?a <? ?z)%Z = true).

           
            rewrite -> not_true_iff_false.
               now apply Z.leb_gt.


            (**rewrite <- not_false_iff_true.
            rewrite <- not_true_is_false.
            SearchAbout (?b <> true).
            apply eq_true_not_negb.
            firstorder.
            SearchPattern (?A = true -> negb ?A = false).
            rewrite ((a <=? z)%Z <> true) with (negb ((a <=? z)%Z) = true).
            SearchAbout (?A <> false).
            apply not_false_iff_true.
eq_true_not_negb.
            replace ((a <=? z)%Z <> true) with (negb ((a <=? z)%Z) = true).
            rewrite <- not_false_iff_true in H3.
            rewrite <- not_false_iff_true.**)

          - assumption.
       end proof.
       intro.
       reflexivity.
Qed.

Lemma vstavi_pojavitev:
  forall (x:Z)(l: list Z), S(pojavi x l)= pojavi x (vstavi x (insert l)).

Proof.
  induction l.
  - simpl. case_eq (x=?x)%Z.
    + intro. auto.
    + intro. absurd ((x=?x)%Z = false).
      * replace (x =? x)%Z with true.
        apply diff_true_false.
        replace (true = (x =? x)%Z) with ((x =? x)%Z=true). 
        apply Z.eqb_refl.
        admit.
      * assumption.
  - simpl.
    case_eq((x=?a)%Z); intros.
    + apply Z.eqb_eq in H.
      replace a with x. simpl.
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
    
    admit.
admit. 
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



