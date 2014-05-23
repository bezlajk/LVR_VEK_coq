Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort.

(** Aktiviramo notacijo za sezname. *)
Local Open Scope list_scope.
Function vstavi (x:Z) (l: list Z) :=
     match l with
      | nil => x::nil
      | y::l' => if (x >=? y)%Z then x::y::l' else y::(vstavi x l')
end.

Fixpoint insert (l:list Z) :=
     match l with
      | nil => nil
      | x::l' => let l'' := (insert l') in vstavi x l''
end. 