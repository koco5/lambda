From Hammer Require Import Hammer.
Require Vector Strings.String.
Require Import List.

Inductive AST :=
  | Name : String.string -> AST
  | Abstraction : String.string -> AST -> AST
  (* parameter, then the term under abstraction *)
  | Application : AST -> AST -> AST
  (* function, then argument *)
. 

Definition NameList := list (String.string).

(* get the first index of a list satisfying a decidable property P *)
Definition first_index {A} (l : list A)
                           (P : A -> Prop)
                           (P_dec : forall e, {P e} + {~P e})
                           : {n : nat
                             | Forall (fun e => ~ P e) (firstn n l)
                               /\ (match (nth_error l n) with
                                   | Some e => P e /\ n < length l
                                   | None => n = length l end)}.
Proof.
 pose (fo := fold_left
               (fun (i : (prod bool nat)) next_elem =>
                 if (fst i)
                 then i
                 else (if P_dec next_elem
                       then (true, (snd i))
                       else (false, S (snd i))))).
 assert (true_drops : forall li i, snd (fo li (true, i)) = i).
 { intros li. induction li; auto. }
 assert (snd_S : forall li i,
            (snd (fo li (false, S i))) = S (snd (fo li (false, i)))).
 { intros li. induction li; auto. Reconstr.scrush. }
 exists (snd (fo l (false, 0))).
 induction l.
 - simpl; auto.
 - split.
   + destruct (Forall_forall
                (fun e => ~ P e)
                (firstn (snd (fo l (false, 0))) l))
              as [F_f _].
     destruct IHl as [IH_notP IH_last].
     pose (x_in_first := F_f IH_notP).
     destruct (Forall_forall
                (fun e : A => ~ P e)
                (firstn (snd (fo (a :: l) (false, 0))) (a :: l)))
              as [_ g].
     apply g. simpl.
     intros x x_in.
     destruct (P_dec a).
     * rewrite true_drops in x_in. destruct x_in.
     * pose (f_n_cons := firstn_cons (snd (fo l (false, 0))) a l).
       rewrite snd_S in x_in. rewrite f_n_cons in x_in.
       destruct x_in; Reconstr.scrush.
   + simpl.
     destruct (P_dec a).
     * rewrite true_drops.
       Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_0_succ) (@Coq.Lists.List.nth_error).
     * rewrite snd_S. simpl.
       Reconstr.rcrush (@Coq.Lists.List.nth_error_Some, @Coq.Arith.Lt.lt_n_S) (@Coq.Init.Datatypes.snd).
Defined.

Inductive NamelessAST (abs_level : nat) :=
  | Reference : {n : nat | n < abs_level} -> NamelessAST abs_level
  (* Bruijn index *)
  | NamelessAbstraction : NamelessAST (S abs_level) -> NamelessAST abs_level
  (* term under abstraction *)
  | NamelessApplication : NamelessAST abs_level -> NamelessAST abs_level -> NamelessAST abs_level
  (* function, then argument *)
.

Definition search_namelist (l : NameList) (name : String.string) : option {n | n < length l}.
Proof.
 pose (cmp_fun := fun e => name = e).
 pose (cmp_dec := String.string_dec name).
 destruct (first_index l cmp_fun cmp_dec) as [n n_prop].
 destruct (nth_error l n).
 - refine (Some _). exists n. Reconstr.scrush.
 - exact None.
Defined.

Local Fixpoint remove_ast_names_h (env : NameList) (ast : AST) : option (NamelessAST (length env)).
Proof.
  destruct ast as [name|parameter abstracted_term|function argument].
  { destruct (search_namelist env name) as [found|].
      - refine (Some _). constructor 1. destruct found as [n n_prop]. 
        exists (n). assumption.
      - constructor 2. }
  { pose (new_env := parameter :: env).
    destruct (remove_ast_names_h new_env abstracted_term) as [found|].
    - assert (new_env_len : (length new_env) = (S (length env))).
      {  auto. }
      rewrite new_env_len in found.
      exact (Some (NamelessAbstraction _ found)).
    - exact None. }
  { destruct (remove_ast_names_h env function) as [nameless_fun|].
    - destruct (remove_ast_names_h env argument) as [nameless_arg|].
      + exact (Some (NamelessApplication _ nameless_fun nameless_arg)).
      + exact None.
    - exact None. }
Defined.

Definition remove_ast_names (ast : AST) := Eval compute in remove_ast_names_h nil ast.

Inductive Closure := Lambda :
                       {abs_level
                        & ((NamelessAST (abs_level))
                           (* The term under abstraction *)
                           * (Vector.t Closure (abs_level)))%type}
                           (* The environment *)
                       -> Closure.
Definition Applicative := {abs_level
                           & ((NamelessAST (S abs_level))
                              * (Vector.t Closure (abs_level)))%type}.
  (* An abstraction requiring an argument before being applied *)

Definition ProgramState : Set :=
  Closure *
  (* term to evaluate *)
  {continuation_length
   & Vector.t
     (* Continuations *)
       (Closure
        (* we are evaluating the operator, the continuation holds the operand *)
        + Applicative)
        (* we are evaluating the operand, this is the evaluated operator*)
       continuation_length}.

Definition load_ast : NamelessAST O -> ProgramState.
Proof.
  intros ast. destruct ast as [reference|abstracted_term|function argument].
  - exfalso. Reconstr.scrush.
  - constructor.
    + constructor. exists O. split.
      * constructor 2. exact abstracted_term.
      * constructor 1.
    + exists O. constructor 1.
  - constructor.
    + constructor. exists O. split.
      * exact function.
      * constructor 1.
    + exists 1. constructor 2.
      * left. constructor. exists O. split.
        { exact argument. }
        { constructor 1. }
      * constructor 1.
Defined.

Definition step : ProgramState -> ProgramState.
Proof.
  intros initial_state.
  destruct initial_state as [evaluating_term continuation].
  destruct evaluating_term as [evaluating_closure].
  destruct evaluating_closure as [evaluating_abs_level evaluating_contents].
  destruct evaluating_contents as [evaluating_ast evaluating_environment].
  destruct evaluating_ast as [evaluating_reference
                             |evaluating_abstracted_term
                             |evaluating_function evaluating_argument].
  - (* replace the reference with the element at its index *)
    constructor.
    + exact (Vector.nth_order evaluating_environment (proj2_sig evaluating_reference)).
    + exact continuation. 
  - (* this is a lambda; see what's in the continuation *)
    destruct continuation as [continuation_length continuation_contents].
    destruct continuation_contents as [|continuation_head continuation_tail_length continuation_tail].
    + (* the continuation is empty, the program has halted *)
      constructor.
      * constructor. exists evaluating_abs_level. split.
        { constructor 2. exact evaluating_abstracted_term. }
        { exact evaluating_environment. }
      * exists O. constructor 1.
    + destruct continuation_head as [continuation_operand
                                    |continuation_applicative].
      * (* put the evaluated operator in the continuation and prepare to
           evaluate the operand *)
        constructor.
        { exact continuation_operand. }
        { exists (S continuation_tail_length). constructor 2.
          - right. unfold Applicative. exists evaluating_abs_level.
            split.
            + exact evaluating_abstracted_term.
            + exact evaluating_environment.
          - exact continuation_tail. }
      * (* apply the operator in the continuation to the argument;
           make sure to reconstruct the argument first *)
        constructor.
        { destruct continuation_applicative as [applicative_abs_level applicative_contents].
          destruct applicative_contents as [applicative_term applicative_env].
          constructor. exists (S applicative_abs_level). split.
          - exact applicative_term.
          - constructor 2.
            + constructor. exists evaluating_abs_level. split.
              * constructor 2. exact evaluating_abstracted_term.
              * exact evaluating_environment.
            + exact applicative_env. }
        exists continuation_tail_length. exact continuation_tail.
  - (* an application; put the argument on the stack and prepare to evaluate
       the operator *)
    constructor.
    + constructor. exists evaluating_abs_level. split.
      * exact evaluating_function.
      * exact evaluating_environment.
    + destruct continuation as [continuation_length continuation_contents].
      exists (S continuation_length). constructor 2.
      * left. constructor. exists evaluating_abs_level. split.
        { exact evaluating_argument. }
        { exact evaluating_environment. }
      * exact continuation_contents.
Defined.