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
| num : nat -> ErrorNat.

Inductive ErrorBool :=
| err_bool : ErrorBool
| boolean : bool -> ErrorBool.

Inductive ErrorString :=
| err_string : ErrorString
| char : string -> ErrorString.

Coercion num : nat >-> ErrorNat.
Coercion boolean : bool >-> ErrorBool.
Coercion char : string >-> ErrorString.

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
| avar: string -> AExp
| anum: ErrorNat -> AExp
| aplus : AExp -> AExp -> AExp
| aminus: AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

(*Coercions pentru constante numerice si variabile*)
Coercion anum : ErrorNat >-> AExp.
Coercion avar : string >-> AExp.

(*Notatii pentru operatiile aritmetice*)
Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (aminus A B) (at level 59, left associativity).
Notation "A *' B" := (amul A B) (at level 50, left associativity).
Notation "A /' B" := (adiv A B) (at level 50, left associativity).
Notation "A %' B" := (amod A B) (at level 50, left associativity).

Check (2 +' 3 *' 5).
Check (12 %' 3 +' 5).

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | err_nat, _ => err_nat
    | _, err_nat => err_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | err_nat, _ => err_nat
    | _, err_nat => err_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then err_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | err_nat, _ => err_nat
    | _, err_nat => err_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | err_nat, _ => err_nat
    | _, err_nat => err_nat
    | _, num 0 => err_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | err_nat, _ => err_nat
    | _, err_nat => err_nat
    | _, num 0 => err_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

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

(*Definire semantica clasica pentru operatiile aritmetice*)
Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | number n => n
                | _ => err_nat
              end
  | anum n => n
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | aminus a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat(aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.

Compute aeval_fun (2 *' 3 %' 5) env.
Compute aeval_fun (5 /' 0) env.

Reserved Notation "A =[ S ]=> N" (at level 70).

(*Semantica Big-Step pentru operatiile aritmetice*)
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n 
| var : forall v sigma, avar v =[ sigma ]=> match (sigma v) with
                                              | number s' => s'
                                              | _ => err_nat 
                                            end
| add' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| sub' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_ErrorNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| times' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| div' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| mod' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Hint Constructors aeval.

Example ex0 : 10 =[ env ]=> 10.
Proof.
  apply const.
Qed.

Example ex1 : 10 /' 0 =[ env ]=> err_nat.
Proof.
  eapply div'.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex2 : 3 -' 6=[ env ]=> err_nat.
Proof.
  eapply sub'.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Inductive BExp :=
  | berror : BExp
  | btrue : BExp
  | bfalse : BExp
  | bvar : string -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | blessthan : AExp -> AExp -> BExp.

Coercion bvar : string >-> BExp.

(*Notatii pentru operatiile boolene*)
Notation "!' A" := (bnot A) (at level 75).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).
Notation "A <' B" := (blessthan A B) (at level 70).

Check btrue.
Check bfalse.
Check (1 <' 4).

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
Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with 
   | err_nat, _=> err_bool
   | _ , err_nat => err_bool
   | num v1, num v2 => boolean (Nat.leb v1 v2)
  end.

Fixpoint beval_fun (a : BExp) (envnat : Env) : ErrorBool :=
  match a with
  | berror => err_bool
  | btrue => true
  | bfalse => false
  | bvar v => match (env v) with
                | boolval n => n
                | _ => err_bool
                end
  | bnot b1 => (not_ErrorBool (beval_fun b1 envnat))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | blessthan a1 a2 => (lt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  end.

Reserved Notation "B ={ S }=> B'" (at level 70).
(*Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> err_bool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | boolval x => x
                                                | _ => err_bool
                                                end
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_ErrorBool i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (a1 and' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (a1 or' a2) ={ sigma }=> b 
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_ErrorBool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
where "B ={ S }=> B'" := (beval B S B').*)

Inductive SExp :=
| sconst: ErrorString -> SExp
| svar : ErrorString -> SExp
| strlen : ErrorString -> SExp (*returneaza un char*)
| concat : ErrorString -> ErrorString -> SExp (*concatenarea a doua stringuri*)
| strcmp : ErrorString -> ErrorString -> SExp. (*comparatia a doua stringuri*)

Coercion sconst : ErrorString >-> SExp.
Coercion svar : ErrorString >-> SExp.
Notation "'strlen(' A ')'" := (strlen A) (at level 90).
Notation "'concat(' A ',' B ')'" := (concat A B) (at level 90).
Notation "'strcmp(' A ',' B ')'" := (strcmp A B) (at level 90).

(*Definition concat_ErrorString (s1 s2 : ErrorString) : ErrorString :=
  match s1, s2 with
    | err_string, _ => err_string
    | _, err_string => err_string
    | char v1, char v2 => concat(s1, s2)
    end.

Definition strcmp_ErrorString (s1 s2 : ErrorString) : ErrorString :=
  match s1, s2 with
    | err_string, _ => err_string
    | _, err_string => err_string
    | char v1, char v2 => strcmp(v1,v2)
    end.
Trebuie adaugat Fixpoint seval_fun si Inductive seval*)

Inductive vect :=
| error_vect: vect
| vector_nat : nat -> list ErrorNat -> vect
| vector_bool : bool -> list ErrorBool -> vect
| vector_str : string -> list ErrorString -> vect.

Inductive Stmt :=
  | sequence : Stmt -> Stmt -> Stmt
  | declare_val : string -> AExp -> Stmt (*initializare variabila*)
  | assign_val : string -> AExp -> Stmt (*pt a updata o variabila*)
  | declare_bool : string -> BExp -> Stmt
  | assign_bool : string -> AExp -> Stmt
  | declare_string : string -> SExp -> Stmt 
  | assign_string : string -> SExp -> Stmt
  | declare_vectorV : string -> vect -> Stmt
  | assign_vectorV : string -> vect -> Stmt
  | declare_vectorB: string -> vect -> Stmt
  | assign_vectorB : string -> vect -> Stmt
  | declare_vectorS : string -> vect -> Stmt
  | assign_vectorS : string -> vect -> Stmt
  | ifthen : BExp -> Stmt -> Stmt 
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt 
  (*inca nu stiu cum sa le implementez*)
  | switch : AExp -> list Cases -> Stmt 
  | call : string -> list string -> Stmt
with Cases :=
  caseDefault : Stmt -> Cases 
  | caseOther : AExp -> Stmt -> Cases.

(*Notatii*)
Notation "S ;; S'" := (sequence S S') (at level 90, right associativity).

Notation "'unsigned' V" := (declare_val V) (at level 90, right associativity).
Notation "'unsigned' V = E" := (assign_val V E) (at level 90, right associativity).

Notation "'bool0' V" := (declare_bool V) (at level 90, right associativity).
Notation "'bool' V = E" := (assign_bool V E) (at level 90, right associativity).

Notation "'char' V" := (declare_string V) (at level 90, right associativity).
Notation "'char' V = E" := (assign_string V E) (at level 90, right associativity).

Notation "'unsigned' A [ B ]n" := ( declare_vectorV A ( num B ) )(at level 50). (*unsigned A[100]*)
Notation "'bool' A [ B ]b" := ( declare_vectorB A ( num B ) )(at level 50).
Notation "'char' A [ B ]s" := ( declare_vectorS A ( num B ) )(at level 50).

Notation "A [ B ]n" := ( assign_vectorV A ( vector_nat B nil ) )(at level 50).
Notation "A [ B ]b" := ( assign_vectorB A ( vector_bool B nil ) )(at level 50).
Notation "A [ B ]s" := ( assign_vectorS A ( vector_str B nil ) )(at level 50).

Notation "A [ B ]n={ C1 ; C2 ; .. ; Cn }" := ( assign_vectorV A ( vector_nat B (cons num(C1) (cons num(C2) .. (cons num(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]b={ C1 ; C2 ; .. ; Cn }" := ( assign_vectorB A ( vector_bool B (cons boolean(C1) (cons boolean(C2) .. (cons boolean(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]s={ C1 ; C2 ; .. ; Cn }" := ( assign_vectorS A ( vector_str B (cons string(C1) (cons string(C2) .. (cons string(Cn) nil) ..) ) ) )(at level 50).

Notation "V :n= E" := (assign_val V E) (at level 90, right associativity).
Notation "V :b= E" := (assign_bool V E) (at level 90, right associativity).
Notation "V :s= E" := (assign_string V E) (at level 90, right associativity).

Notation "'if(' B ')' 'then{' S '}end'" := (ifthen B S) (at level 97).
Notation "'if(' B ')' 'then{' S1 '}else{' S2 '}end'" := (ifthenelse B S1 S2) (at level 97).

Notation "'while(' B ')' 'do{' S '}'" := (while B S) (at level 97).

Notation "'default:{' S '};'" := (caseDefault S) (at level 96).
Notation "'case(' E '):{' S '};'" := (caseOther E S) (at level 96).
Notation "'switch(' E '){' C1 .. Cn '}end'" := (switch E (cons C1 .. (cons Cn nil) .. )) (at level 97).

(*Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                  | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                  | nat_decl a aexp => update (update env a default) a (number (aeval_fun aexp env))
                  | bool_decl b bexp => update (update env b default) b (boolval (beval_fun bexp env))
                  | nat_assign a aexp => update env a (number (aeval_fun aexp env))
                  | bool_assign b bexp => update env b (boolval (beval_fun bexp env))
                  | ifthen cond s' => 
                      match (beval_fun cond env) with
                       | err_bool => env
                       | boolean v => match v with
                                      | true => eval_fun s' env gas'
                                      | false => env
                                      end
                      end
                  | ifthenelse cond S1 S2 => 
                      match (beval_fun cond env) with
                        | err_bool => env
                        | boolean v  => match v with
                                           | true => eval_fun S1 env gas'
                                           | false => eval_fun S2 env gas'
                                        end
                      end
                  | while cond s' => 
                      match (beval_fun cond env) with
                        | err_bool => env
                        | boolean v => match v with
                                          | true => eval_fun (s' ;; (while cond s')) env gas'
                                          | false => env
                                       end
                      end
                 end
     end.

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

(*Evaluarea expresiilor*)
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (number i)) ->
   (x :n= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (number i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (res_boolval i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (boolval i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Hint Constructors eval.*)



