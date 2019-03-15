Require Import List.
From Hammer Require Hammer.

Lemma hd_skip : forall {A} (l : list A) n, hd_error (skipn n l) = nth_error l n.
Proof.
  induction l; Reconstr.scrush.
Qed.

Lemma first_add : forall {A} (l : list A) (n : nat), firstn (S n) l = (firstn n l) ++ (match nth_error l n with | Some e => (e :: nil) | None => nil end).
Proof. induction l.
 - Reconstr.scrush.
 - Reconstr.ryelles4 (@Coq.Lists.List.firstn_O, @hd_skip) (@Coq.Lists.List.firstn, @Coq.Init.Datatypes.app, @Coq.Lists.List.nth_error, @Coq.Lists.List.skipn).
Qed.

Lemma Forall_last : forall {A} (l : list A) (P : A -> Prop) (x : A), Forall P l /\ P x <-> Forall P (l ++ (x :: nil)).
Proof.
 induction l; Reconstr.scrush.
Qed.

Lemma skip_one : forall {A} l tail (head : A) n, head :: tail = skipn n l -> tail = skipn (S n) l.
Proof.
 induction l.
 - induction tail.
   + auto.
   + Reconstr.scrush.
 - Reconstr.scrush.
Qed.

Definition first_index {A}
                       (l : list A)
                       (P : A -> Prop)
                       (P_dec : forall e, {P e} + {~P e})
                       : {n | Forall (fun e => ~P e) (firstn n l)
                              /\ match (nth_error l n) with
                                 | Some e => P e
                                 | None => False end }
                         + {Forall (fun e => ~P e) l}.
Proof.
  (* right index *)
  induction l as [|next tail_l IHl]; auto.
  destruct (P_dec next) as [?|not_P_next].
  - left. exists O. Reconstr.scrush.
  - destruct IHl as [found|not_found].
    + destruct found as [found_n found_n_prop].
      left. exists (S found_n). Reconstr.scrush.
    + right. Reconstr.scrush.
Restart.
  pose (ind_type := {rec : ((list A) * nat) | Forall (fun e => ~P e) (firstn (snd rec) l) /\ (fst rec) = skipn (snd rec) l }).
  pose (Wfr := Wf_nat.well_founded_ltof ind_type (fun e => length (fst (proj1_sig e)))).
  assert (start : ind_type). { exists (l, O). Reconstr.scrush. }
  refine (well_founded_induction_type Wfr (fun _ => _) _ start).
  clear start.
  intros initial.
  remember initial as initial_copy.
  destruct initial as [initial_existential initial_prop].
  destruct initial_existential as [initial_list initial_counter].
  destruct initial_list as [|initial_list_head initial_list_tail].
  - intros. right. admit. (* CVC4 says it's correct, but hammer can't reconstruct *)
  - destruct (P_dec initial_list_head).
    + intros. left. exists initial_counter.
      pose (hd_skip l initial_counter). admit. (* same *)
    + intros rec. refine (rec ?[next] _).
      [next]:{ unfold ind_type. exists (initial_list_tail, S initial_counter).
               pose (hd_skip l initial_counter). split.
               - simpl in initial_prop. simpl snd. pose (first_add l initial_counter).
                 rewrite e0. rewrite <- e. destruct initial_prop. rewrite <- e1. simpl.
                 destruct (Forall_last (firstn initial_counter l) (fun e => ~P e) initial_list_head).
                 apply H. auto.
               - simpl fst. simpl snd. destruct initial_prop. simpl in e0.
                 rewrite skip_one with l initial_list_tail initial_list_head initial_counter; auto. }
      Reconstr.scrush.
Admitted.