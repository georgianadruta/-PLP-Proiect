Include Nat.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

Inductive AExp :=
| anum : nat -> AExp
| astring : string -> AExp
| aplus : AExp -> AExp -> AExp
| aminus: AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion astring : string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (aminus A B) (at level 59, left associativity).
Notation "A *' B" := (amul A B) (at level 50, left associativity).
Notation "A /' B" := (adiv A B) (at level 50, left associativity).
Notation "A %' B" := (amod A B) (at level 50, left associativity).

Definition Env := string -> nat.
Definition env : Env :=
  fun s => 0.

Definition update (env : Env) (s : string) (x : nat) : Env :=
  fun y => if (eqb y s)
              then x
              else (env y).
