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

Notation "unsigned( N )" := (num N).
Notation "char( S )" := (char S).
Notation "bool( B )" := (boolean B).

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
Check (12 %' 3 -' 5).

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
Compute aeval_fun (12 %' 0) env.
Compute aeval_fun (12 -' 21) env.

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
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
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
    (!' a1) ={ sigma }=> b
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
where "B ={ S }=> B'" := (beval B S B').

Compute beval_fun (1 <' 5) env.
Compute beval_fun (!' btrue) env.
Compute beval_fun (btrue and' bfalse) env.
Compute beval_fun (btrue or' btrue) env.

Inductive SExp :=
| sconst: ErrorString -> SExp
| svar : ErrorString -> SExp
| strlen : ErrorString -> SExp (*returneaza un char*)
| concat : ErrorString -> ErrorString -> SExp (*concatenarea a doua stringuri*)
| strcmp : ErrorString -> ErrorString -> SExp(*comparatia a doua stringuri*).

Coercion sconst : ErrorString >-> SExp.
Coercion svar : ErrorString >-> SExp.
Notation "'strlen(' A ')'" := (strlen A) (at level 90).
Notation "'concat(' A ',' B ')'" := (concat A B) (at level 90).
Notation "'strcmp(' A ',' B ')'" := (strcmp A B) (at level 90).

(*Definition concat_error (s1 s2 : SExp) : ErrorString :=
  match s1, s2 with
    | err_string, _ => err_string
    | _, err_string => err_string
    | sconst str1, sconst str2 => concat(str1,str2)
  end.

Definition strcmp_error (s1 s2 : SExp) : ErrorString :=
  match s1, s2 with
    | err_string, _ => err_string
    | _, err_string => err_string
    | sconst str1, sconst str2 => strcmp(str1,str2)
  end.

Fixpoint seval_fun (a : SExp) (env : Env) : ErrorString :=
  match a with
    | serror => err_string
    | svar v => match (env v) with
                  | strval s => s
                  | _ => strval
                end
    | sconst v => v
    | concat a1 a2 => (concat_error (seval_fun a1 env) (seval_fun a2 env))
    | strcmp a1 a2 => (strcmp_error (seval_fun a1 env) (seval_fun a2 env))
  end.

Inductive seval : SExp -> Env -> ErrorString -> Prop :=
  | s_error: forall sigma, err_string  ={ sigma }=> error_str
  | s_var: forall v sigma, svar v ={ sigma }=>  match (sigma v) with
                                                   | strval x => x
                                                   | _ => err_string
                                                 end
  | s_const: forall s sigma, sconst ={ sigma }=> s
  | s_concat: forall s1 s2 i1 i2 sigma s,
               s1 =[ sigma ]=> i1 ->
               s2 =[ sigma ]=> i2 ->
               s = (concat_error i1 i2) ->
               concat(s1,s2) ={ sigma }=> s
  | s_strcmp: forall s1 s2 i1 i2 sigma s,
               s1 =[ sigma ]=> i1 ->
               s2 =[ sigma ]=> i2 ->
               s = (strcmp_error i1 i2) ->
               strcmp(s1,s2) ={ sigma }=> s
  | s_strcpy: forall s1 s2 i1 i2 sigma s,
               s1 =[ sigma ]=> i1 ->
               s2 =[ sigma ]=> i2 ->
               s = (strcpy_error i1 i2) ->
               strcpy(s1,s2) ={ sigma }=> s
  where "B ={ S }=> B'" := (seval B S B').
*)

Check strlen("mama").
Check concat("ab","cd").
Check strcmp("plp","plp").

(*tipuri de vectori: unsigned, bool, char*)
Inductive vect :=
| error_vect: vect
| vector_nat : nat -> list ErrorNat -> vect
| vector_bool : bool -> list ErrorBool -> vect
| vector_str : string -> list ErrorString -> vect.

Inductive Stmt :=
  | sequence : Stmt -> Stmt -> Stmt
  | declare_val : string -> AExp -> Stmt (*declarare variabila cu sau fara initializare*)
  | assign_val : string -> AExp -> Stmt (*pt a updata o variabila*)
  | declare_bool : string -> BExp -> Stmt
  | assign_bool : string -> BExp -> Stmt
  | declare_string : string -> SExp -> Stmt 
  | assign_string : string -> SExp -> Stmt
  | declare_vector : string -> vect -> Stmt
  | ifthen : BExp -> Stmt -> Stmt 
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt 
  | For : Stmt -> BExp -> Stmt -> Stmt ->Stmt
  | break : Stmt
  | continue  : Stmt
  | switch : AExp -> list Cases -> Stmt 
  | call : string -> list string -> Stmt
with Cases :=
  caseDefault : Stmt -> Cases 
  | caseOther : AExp -> Stmt -> Cases.

(*Notatii*)
Notation "S ;; S'" := (sequence S S') (at level 90, right associativity).

Notation "'unsigned' V" := (declare_val V) (at level 90, right associativity).
Notation "'unsigned' V ::= E" := (assign_val V E) (at level 90, right associativity).
Notation "V :n= E" := (assign_val V E) (at level 90, right associativity).

Notation "'bool' V" := (declare_bool V) (at level 90, right associativity).
Notation "'bool' V ::= E" := (assign_bool V E) (at level 90, right associativity).
Notation "V :b= E" := (assign_bool V E) (at level 90, right associativity).

Notation "'char' V" := (declare_string V) (at level 90, right associativity).
Notation "'char' V ::= E" := (assign_string V E) (at level 90, right associativity).
Notation "V :s= E" := (assign_string V E) (at level 90, right associativity).

Notation "'unsigned' A [ B ]" := ( declare_vector A ( vector_nat B nil ) )(at level 50).
Notation "'unsigned' A [ B ]:n={ C1 ; C2 ; .. ; Cn }" := ( declare_vector A ( vector_nat B (cons nat(C1) (cons nat(C2) .. (cons nat(Cn) nil) ..) ) ) )(at level 50).

Notation "'bool' A [ B ]" := ( declare_vector A ( vector_bool B nil ) )(at level 50).
Notation "'bool' A [ B ]:b={ C1 ; C2 ; .. ; Cn }" := ( declare_vector A ( vector_bool B (cons bool(C1) (cons bool(C2) .. (cons bool(Cn) nil) ..) ) ) )(at level 50).

Notation "'char' A [ B ]" := ( declare_vector A ( vector_str B nil ) )(at level 50).
Notation "'char' A [ B ]:s={ C1 ; C2 ; .. ; Cn }" := ( declare_vector A ( vector_str B (cons string(C1) (cons string(C2) .. (cons string(Cn) nil) ..) ) ) )(at level 50).

Notation "'If' ( B ) 'Then' { S } 'End'" := (ifthen B S) (at level 97).
Notation "'If' ( B ) 'Then' { S1 } 'Else' { S2 } 'End'" := (ifthenelse B S1 S2) (at level 97).

Notation "'While'( B ) 'Do {' S '}'" := (while B S) (at level 97).

Notation "'for' ( A ; B ; C ) { D }" := (For A B C D) (at level 91).

Notation "'default:{' S '};'" := (caseDefault S) (at level 96).
Notation "'case(' E '):{' S '};'" := (caseOther E S) (at level 96).
Notation "'switch(' E '){' C1 .. Cn '}end'" := (switch E (cons C1 .. (cons Cn nil) .. )) (at level 97).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

(*Evaluarea expresiilor
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
   sigma' = (update sigma x (boolval i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (boolval i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_str_decl: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (strval i)) ->
    (x :s= a) -{ sigma }-> sigma'
| e_str_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (strval i)) ->
    (x :s= a) -{ sigma }-> sigma'
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
| e_forfalse : forall a b st s1 sigma sigma',
    a -{ sigma }-> sigma' ->
    b ={ sigma' }=> false ->
    For a b st s1 -{ sigma }-> sigma'
| e_fortrue : forall a b st s1 sigma sigma' sigma'',
    a -{ sigma }-> sigma' ->
    b ={ sigma' }=> true ->
    (sequence s1 (sequence st  (forcontent b st s1))) -{ sigma' }-> sigma'' ->
    For a b st s1 -{ sigma }-> sigma''
| e_switch: forall a i c b s sigma sigma',
              a ={ sigma }=> i ->
              b = (Nat.eqb i c) ->
              switch b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                  | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                  | declare_val a aexp => update (update env a default) a (number (aeval_fun aexp env))
                  | declare_bool b bexp => update (update env b default) b (boolval (beval_fun bexp env))
                  | declare_string b sexp => update (update env b default) b (strval (seval_fun sexp env))
                  | assign_val a aexp => update env a (number (aeval_fun aexp env))
                  | assign_bool b bexp => update env b (boolval (beval_fun bexp env))
                  | assign_string b sexp => update env b (strval (seval_fun sexp env))
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
                  (*trebuie adaugate for si switch*)
                 end
     end.
*)

Check unsigned "sum" ::= 0.
Check "sum" :n= 50.

Check bool "V" ::= bfalse.
Check "V" :b= btrue.

Check char "str" ::= "abcd".
Check "str" :s= "eeee".

Check break.
Check continue.

Check If (1 <' 2) Then {"a" :b= btrue} End.
Check If (9 <' 3) Then {"x" :b= btrue} Else {"x" :b= bfalse} End.

Check unsigned "A"[50].
Check unsigned "B"[50] :n= { 0 ; 10 ; 20 }.

Check For ("i" :n= 0; "i" <' 10; "i" :n= ("i" +' 1))
      {
        "sum" :n= ("sum" +' "i")
      }.

Check while (sum <' 51) Do 
      {
        "sum" :n= ("sum" -' 1)
      }.

Definition while_stmt :=
    unsigned "i" ::= 0 ;;
    unsigned "sum" ::= 0;;
    while ("i" <' 6) 
        {
           "sum" :n= "sum" +' "i" ;;
           "i" :n= "i" +' 1
        }.

Compute (eval_fun while_stmt env 30) "sum".

(*Implementare stack*)
Definition Var := string.

Inductive Instruction :=
| push_const : ErrorNat -> Instruction
| push_var : ErrorString -> Instruction
| adds : Instruction
| muls : Instruction.

Compute (push_const 10).
Compute adds.

Definition Stack := list ErrorNat.

(*Fixpoint run_instruction (i : Instruction)
         (env : ErrorString -> ErrorNat) (stack : Stack) : Stack :=
  match i with
  | push_const c => (c :: stack)
  | push_var x => ((env x) :: stack)
  | adds => match stack with
           | n1 :: n2 :: stack' => (aplus n1 n2) :: stack'
           | _ => stack
           end 
  | muls => match stack with
           | n1 :: n2 :: stack' => (n1 * n2) :: stack'
           | _ => stack
           end
  end.

Compute (run_instruction (push_const 1012) env0 []).
Compute (run_instruction (push_var "x") env0 []).
Compute (run_instruction add env0 [10;12;20]).
Compute (run_instruction mul env0 [10;12;20]).

Fixpoint run_instructions (is' : list Instruction)
         (env : Var -> nat) (stack : Stack) : Stack :=
  match is' with
  | [] => stack
  | i :: is'' => run_instructions is'' env (run_instruction i env stack)
  end.

Definition pgm1 := [
                    push_const 19 ;
                    push_var "x"
                  ].
Compute run_instructions pgm1 env0 [].

Definition pgm2 := [
                    push_const 19 ;
                    push_var "x" ;
                    add;
                    push_var "x";
                    mul
                  ].
Compute run_instructions pgm2 env0 [].

(* Compilation *)  
Fixpoint compile (e : Exp) : list Instruction :=
  match e with
  | const c => [push_const c]
  | id x => [push_var x]
  | plus e1 e2 => (compile e1) ++ (compile e2) ++ [add]
  | times e1 e2 => (compile e1) ++ (compile e2) ++ [mul]
  end.

Compute compile (2 +' (id "x")).
Compute compile (2 +' (id "x") *' 7).
Compute compile (2 *' (id "x") +' 7).

Compute interpret (2 *' (id "x") +' 7) env0.
Compute run_instructions
        (compile (2 *' (id "x") +' 7))
        env0
        [].*)
