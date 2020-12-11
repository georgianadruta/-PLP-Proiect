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

Check (2 +' 3 *' 5).
Check (12 %' 3 +' 5).

Definition Env := string -> nat.
Definition env : Env :=
  fun s => 0.

Definition update (env : Env) (s : string) (x : nat) : Env :=
  fun y => if (eqb y s)
              then x
              else (env y).

Check env.

Reserved Notation "A =[ S ]=> N" (at level 70).

Fixpoint aeval_fun (a : AExp) (env : Env) : nat :=
  match a with
  | anum n' => n'
  | astring s' => env s'
  | aplus a1 a2 => (aeval_fun a1 env) + (aeval_fun a2 env)
  | aminus a1 a2 => (aeval_fun a1 env) + (aeval_fun a2 env)
  | amul a1 a2 => (aeval_fun a1 env) * (aeval_fun a2 env)
  | adiv a1 a2 => Nat.div (aeval_fun a1 env) (aeval_fun a2 env)
  | amod a1 a2 => Nat.modulo (aeval_fun a1 env) (aeval_fun a2 env)
  end.

Compute aeval_fun (2 *' 3 %' 5) env.

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

Example ex0 : 10 =[ env ]=> 10.
Proof.
  apply const.
Qed.

Require Import Lia.

Example ex2 : 2 +' 2 =[ env ]=> 4.
Proof.
  eapply add'.
  - apply const.
  - apply const.
  - lia.
Qed.

Inductive BExp :=
  | btrue : BExp
  | bfalse : BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | blessthan : AExp -> AExp -> BExp
  | bequal : AExp -> AExp -> BExp.

Notation "! A" := (bnot A) (at level 75).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A =' B" := (bequal A B) (at level 70).

Check btrue.
Check bfalse.

Fixpoint beval_fun (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | bnot b' => negb (beval_fun b' env)
  | band b1 b2 => andb (beval_fun b1 env) (beval_fun b2 env)
  | bor b1 b2 => orb (beval_fun b1 env) (beval_fun b2 env)
  | blessthan a1 a2 => Nat.leb (aeval_fun a1 env) (aeval_fun a2 env)
  | bequal a1 a2 => Nat.eqb (aeval_fun a1 env) (aeval_fun a2 env)
  end.

Check ! (6 <' 10).
Check btrue or' btrue.
Check (1+1) =' 2.

Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env -> bool -> Prop :=
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_true : forall sigma, btrue ={ sigma }=> true
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_orfalse : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    bor b1 b2 ={ sigma }=> t
| e_ortrue : forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    bor b1 b2 ={ sigma }=> true
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <' a2 ={ sigma }=> b
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (Nat.eqb i1 i2) ->
    a1 =' a2 ={ sigma }=> b
where "B ={ S }=> B'" := (beval B S B').

Hint Constructors beval.
