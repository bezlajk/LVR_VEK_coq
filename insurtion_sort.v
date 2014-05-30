Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Sorting.

(** Aktiviramo notacijo za sezname. *)
Local Open Scope list_scope.
Function vstavi (x:Z) (l: list Z) :=
     match l with
      | nil => x::nil
      | y::l' => if (x <=? y)%Z then x::y::l' else y::(vstavi x l')
end.

Fixpoint insert (l:list Z) :=
     match l with
      | nil => nil
      | x::l' => let l'' := (insert l') in vstavi x l''
end. 

Eval compute in (insert (2 :: 5 :: 1 :: 4 :: nil)%Z).

Lemma urejen_t (a: Z) (l: list Z):
  urejen l -> urejen (vstavi a l).
Proof.
  intro.
  induction l.
  - auto.
  - (*urejen_tail želimo uporabiti na a0 in l v hipotezi H*)
    
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



