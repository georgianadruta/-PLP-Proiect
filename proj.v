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

Check env.

Reserved Notation "A =[ S ]=> N" (at level 70).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n 
| var : forall v sigma, astring v =[ sigma ]=> (sigma v) 
| add' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| sub' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    i1 > i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| times' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| div' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    i2 >0 -> 
    n = Nat.div i1 i2 ->
    a1 /' a2 =[sigma]=> n
| mod' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = Nat.modulo i1 i2 ->
    a1 %' a2 =[sigma]=> n

where "a =[ sigma ]=> n" := (aeval a sigma n).

Hint Constructors aeval.

(* Fixpoint aeval (a : AExp) (env : Env) : nat :=
  match a with
  | anum n' => n'
  | astring s' => s'
  | aplus a1 a2 => (aeval a1 env) + (aeval a2 env)
  | aminus a1 a2 => (aeval a1 env) + (aeval a2 env)
  | amul a1 a2 => (aeval a1 env) * (aeval a2 env)
  | adiv a1 a2 => Nat.div (aeval a1 env) (aeval a2 env)
  | amod a1 a2 => Nat.modulo (aeval a1 env) (aeval a2 env)
  end. *)
  
  
