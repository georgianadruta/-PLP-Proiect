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

Inductive BExp :=
  | btrue : BExp
  | bfalse : BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | blessthan : AExp -> AExp -> BExp
  | bequal : AExp -> AExp -> BExp.
(*ar mai trebui <=, >, >=*)

Notation "! A" := (bnot A) (at level 75).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A =' B" := (bequal A B) (at level 70).

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

Inductive Stmt :=
  | assignment : string -> AExp -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt 
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt.
(*ar mai trebui si instructiunea for*)

Notation "X ::= A" := (assignment X A) (at level 80).
Notation "S ;; S'" := (sequence S S') (at level 90, right associativity).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_iffalse: forall b s1 s2 sigma sigma2,
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma2 ->
    ifthenelse b s1 s2 -{ sigma }-> sigma2
| e_iftrue : forall b s1 s2 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    ifthenelse b s1 s2 -{ sigma }-> sigma1
| e_ifthenelsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
  ifthenelse b s1 s2 -{ sigma }-> sigma'
| e_ifthenelsetrue :  forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' -> 
    ifthenelse b s1 s2 -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Hint Constructors eval.
