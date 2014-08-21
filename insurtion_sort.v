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
       (**
       SearchPattern ((?a <= ?z)%Z).
       simpl H.
       apply IH1.
       apply Z.leb_gt in H0.
       split. 
       apply Z.lt_le_incl in H0. auto.
       
       simpl.
       firstorder.
       **)
       admit.




       (*SearchAbout ((?a < ?b)%Z -> (?a <= ?b)%Z).

       simpl.


       destruct (z :: l).
       firstorder.
       apply Z.leb_gt in H0.
       apply Z.lt_le_incl in H0.
       auto.
       
    
     
       SearchAbout (?a <=? ?b)%Z.*)   
  admit.
Qed.


Theorem permutacija:
  forall (l: list Z), (permutiran l (insert l)).
Proof.
  intro.
  induction l.
  - firstorder.
  - intro.
    simpl.
    case (x =? a)%Z.
    
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



