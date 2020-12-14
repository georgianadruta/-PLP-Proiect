Include Nat.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Coq.ZArith.BinInt.
Require Import List.
Local Open Scope list_scope.
Scheme Equality for list.
Import ListNotations.

Inductive ErrorNat :=
| err_nat : ErrorNat
| unsigned : nat -> ErrorNat.

Inductive ErrorBool :=
| err_bool : ErrorBool
| boolean : bool -> ErrorBool.

Inductive ErrorString :=
| err_string : ErrorString
| char : string -> ErrorString.

(*Coercions pentru tipuri de variabile*)
Coercion unsigned : nat >-> ErrorNat.
Coercion boolean : bool >-> ErrorBool.
Notation "'char('S')'" := (ErrorString S) (at level 30). (*fara paranteze imi da eroare in Inductive newType
"Syntax error: [constr:operconstr] expected after 'char' (in [constr:operconstr])."*)

(*Inglobez toate tipurile de variabile intr un singur tip*)
Inductive Types :=
| err_undeclared : Types
| err_assignment : Types
| default : Types
| number : ErrorNat -> Types
| boolval : ErrorBool -> Types
| strval : ErrorString -> Types.

Scheme Equality for Types.

Inductive AExp :=
| aunsigned: ErrorNat -> AExp
| achar: ErrorString -> AExp
| aplus : AExp -> AExp -> AExp
| aminus: AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

(*Coercions pentru constante numerice si variabile*)
Coercion aunsigned : ErrorNat >-> AExp.
Coercion achar : ErrorString >-> AExp.

(*Notatii pentru operatiile aritmetice*)
Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (aminus A B) (at level 59, left associativity).
Notation "A *' B" := (amul A B) (at level 50, left associativity).
Notation "A /' B" := (adiv A B) (at level 50, left associativity).
Notation "A %' B" := (amod A B) (at level 50, left associativity).

Check (2 +' 3 *' 5).
Check (12 %' 3 +' 5).

(*Definire environment*)
Definition Env := string -> Types.
Definition env : Env :=
  fun s => err_undeclared.

Check env("12dec").

Definition CheckType (a : Types) (b : Types) : bool :=
match a with
| err_undeclared => match b with
                | err_undeclared => true
                | _ => false
                end
| err_assignment => match b with
                | err_assignment => true
                | _ => false
                end
| number x => match b with
                | number _y => true
                | _ => false
                end
| boolval x => match b with
                | boolval _y => true
                | _ => false
                end
| strval x => match b with
                | strval _y => true
                | _ => false
                end
| default => match b with
                | default => true
                | _ => false
                end
end.

Definition update (env : Env) (s : string) (x : Types) : Env :=
  fun y => if (eqb y s)
              then 
              if (andb (CheckType (err_undeclared) (env y)) (negb(CheckType (default) (x))))
              then err_undeclared
              else
                if (andb (CheckType (err_undeclared) (env y)) (CheckType (default) (x)))
                then default
                else
                  if (orb (CheckType (default) (env y)) (CheckType (x) (env y)))
                  then x
                  else err_assignment
            else env y.


Compute (update (update env "y" (default)) "y" (boolval true) "y").

Reserved Notation "A =[ S ]=> N" (at level 70).

(*Semantica Big-Step pentru operatiile aritmetice*)
Inductive aeval : AExp -> Env -> unsigned -> Prop :=
| const : forall n sigma, aunsigned n =[ sigma ]=> n 
| var : forall v sigma, achar v =[ sigma ]=> match (sigma v) with
                                              | stringVal s' => s'
                                              | _ => errString
                                              end
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
  | bvar : string -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | blessthan : AExp -> AExp -> BExp
  | bequal : AExp -> AExp -> BExp
  | bstrcmp : string -> string -> BExp. (*functia de comparare a 2 stringuri*)

Coercion bvar : string >-> BExp.

(*Notatii pentru operatiile boolene*)
Notation "! A" := (bnot A) (at level 75).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A =' B" := (bequal A B) (at level 70).
Notation "'strcmp(' A ',' B ')'" := (bstrcmp A B) (at level 90).

Check btrue.
Check bfalse.
Check strcmp("a", "b").

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with 
   | err_nat, _=> err_bool
   | _ , err_nat => err_bool
   | unsigned v1, unsigned v2 => boolean (Nat.leb v1 v2)
  end.

Definition not_ErrorBool (n : ErrorBool) : ErrorBool :=
  match n with 
   | err_bool => err_bool
   | boolean v => boolean (negb v)
  end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with 
   | err_bool, _=> err_bool
   | _ , err_bool => err_bool
   | boolean v1, boolean v2 => boolean (andb v1 v2)
  end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with 
   | err_bool, _=> err_bool
   | _ , err_bool => err_bool
   | boolean v1, boolean v2 => boolean (orb v1 v2)
  end.

Reserved Notation "B ={ S }=> B'" (at level 70).

(*Definire semantica Big-Step pentru operatii boolene*)
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_true : forall sigma, btrue ={ sigma }=> true
| e_var : forall v sigma, bvar v ={ sigma }=> match (sigma v) with 
                                              | boolean x => x
                                              | _ => err_bool
                                              end
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
    b = (lt_ErrorBool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (Nat.eqb i1 i2) ->
    a1 =' a2 ={ sigma }=> b
where "B ={ S }=> B'" := (beval B S B').

Hint Constructors beval.

Inductive Stmt :=
  | sequence : Stmt -> Stmt -> Stmt
  | declare_val : string -> AExp -> Stmt (*initializare variabila*)
  | assign_nat : string -> AExp -> Stmt (*pt a updata o variabila*)
  | declare_bool : string -> BExp -> Stmt
  | assign_bool : string -> AExp -> Stmt
  | ifthen : BExp -> Stmt -> Stmt 
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt 
  | fordo : Stmt -> BExp -> Stmt -> Stmt -> Stmt
  | strcat : string -> string -> Stmt
  | strcpy : string -> string -> Stmt.

(*Notatii*)
Notation "S ;; S'" := (sequence S S') (at level 90, right associativity).
Notation " 'unsigned' A ::= B " := (declare_val A ) (at level 50).
Notation "X :n= A" := (assign_nat X A) (at level 80).
Notation " 'bool' A ::= B " := (declare_val A ) (at level 50).
Notation "X :b= A" := (assign_bool X A) (at level 80).
Notation "'if' ( A ) 'then' { B }" := (ifthen A B) (at level 90).
Notation "'if' ( A ) 'then' { S1 } 'else' { S2 } " := (ifthenelse A S1 S2) (at level 97).
Notation "'for' ( A ; B ; C ) { D }" := (A ;; while B ( S ;; C )) (at level 90).
Notation "'while' ( A ) { B }" := (while A B) (at level 90).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

(*Evaluarea expresiilor*)
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_declare_val : forall a i x sigma sigma', 
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (unsigned i)) ->
    (x ::= a) -{ sigma }-> sigma'
| e_assign_val: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (unsigned i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_declare_bool : forall a i x sigma sigma', 
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (boolean i)) ->
    (x ::= a) -{ sigma }-> sigma'
| e_assign_bool: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
    sigma' = (update sigma x (boolean i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_ifthen : forall b s sigma,
    ifthen b s -{ sigma }-> sigma1
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
| e_forfalse : forall e1 e2 e3 s sigma,
    e2 ={ sigma }=> false ->
    fordo e1 e2 e3 s -{ sigma }-> sigma
| e_fortrue : forall e1 e2 e3 s sigma sigma',
    e2 ={ sigma }=> true ->
    (e1 ;; while e2 (s ;; e3)) -{ sigma }-> sigma' ->
    fordo e1 e2 e3 s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Hint Constructors eval.
 
Definition while_stmt :=
  unsigned "i" ::= 0 ;;
  unsigned "sum" ::= 0 ;;
  while ( "i" <' 6)
  {
    "sum" :n= "sum" +' "i";;
    "i" :n= "i" +' 1
  }
