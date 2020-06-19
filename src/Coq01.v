Module coq_basics.

  Definition negb (b: bool): bool :=
    match b with
    | true => false
    | false => true
    end
  .

  Check negb.

  Definition andb (b0 b1: bool): bool :=
    match b0 with
    | false => false
    | true => b1
    end
  .

  Check andb.

  (* (* Fix this definition! *) *)
  (* Definition orb (b0 b1: bool): bool := true. *)

  (* Check orb. *)

  (* Example orbTest0: orb true true = true. *)
  (* Proof. reflexivity. Qed. *)
  (* Example orbTest1: orb true false = true. *)
  (* Proof. reflexivity. Qed. *)
  (* Example orbTest2: orb false true = true. *)
  (* Proof. reflexivity. Qed. *)
  (* Example orbTest3: orb false false = false. *)
  (* Proof. reflexivity. Qed. *)


  Fixpoint even (n: nat): bool :=
    match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
    end
  .

  Check even.

  (* (* Fix this defintion! *) *)
  (* Definition odd (n: nat): bool := true. *)

  (* Check odd. *)

  (* Example oddTest0: odd 0 = false. *)
  (* Proof. reflexivity. Qed. *)
  (* Example oddTest1: odd 2 = false. *)
  (* Proof. reflexivity. Qed. *)
  (* Example oddTest2: odd 7 = true. *)
  (* Proof. reflexivity. Qed. *)
  (* Example oddTest3: odd 23 = true. *)
  (* Proof. reflexivity. Qed. *)


  Definition applyOnce {X: Type} (f: X -> X) (x: X): X :=
    f x
  .

  Check applyOnce.

  Fixpoint applyNTimes {X: Type} (n: nat) (f: X -> X) (x: X): X :=
    match n with
    | 0 => x
    | S n' => applyNTimes n' f (f x)
    end
  .

  Check applyNTimes.

  Theorem silly0:
    1 + 1 = 2.
  Proof.
    reflexivity.
  Qed.

  Theorem silly1: forall (n: nat),
      n = n.
  Proof.
    reflexivity.
  Qed.

  Theorem plus_O_n: forall (n: nat),
      0 + n = n.
  Proof.
    intros n.
    reflexivity.
  Qed.

  Theorem plus_id_simple: forall (n m: nat),
      n = m ->
      n + n = m + m.
  Proof.
    intros n m H.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem plus_id_complex: forall (n m o: nat),
      n = m ->
      m = o ->
      n + m = m + o.
  Proof.
    intros n m o H0 H1.
    rewrite -> H0.
    rewrite -> H1.
    reflexivity.
  Qed.





  Theorem andb_b_false: forall b,
      andb b false = false.
  Proof.
    intro b.
    destruct b.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_orb_eq: forall b0 b1,
      andb b0 b1 = orb b0 b1 ->
      b0 = b1.
  Proof.
    intros b0 b1.
    destruct b0.
    - destruct b1.
      + reflexivity.
      + simpl.
        intro H. rewrite -> H. reflexivity.
    - destruct b1.
      + simpl.
        intro H. rewrite -> H. reflexivity.
      + reflexivity.
  Qed.

  Fixpoint beq_nat (n m: nat): bool :=
    match n with
    | 0 => match m with
           | 0 => true
           | S m' => false
           end
    | S n' => match m with
              | 0 => false
              | S m' => beq_nat n' m'
              end
    end
  .

  Theorem beq_nat_plus1_O: forall (n: nat),
      beq_nat (n + 1) 0 = false.
  Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.
  Qed.

End coq_basics.











Module coq_inductive_definition.

  Inductive nat :=
  | O: nat
  | S: nat -> nat
  .

  Inductive bool :=
  | true: bool
  | false: bool
  .

  Inductive list (X: Type) :=
  | nil: list X
  | cons: X -> list X -> list X
  .

  Check nil.
  Check cons bool false (cons bool true (nil bool)).

  Arguments nil {X}.
  Arguments cons {X} _ _.

  Check nil.
  Check cons false (cons true nil).

  Theorem zero_is_one_than: forall P,
      0 = 1 -> P.
  Proof. intros P contra. inversion contra. Qed.

  Theorem only_one_head: forall X (l: list X) h0 h1 t0 t1,
      l = cons h0 t0 ->
      l = cons h1 t1 ->
      h0 = h1.
  Proof.
    intros X l h0 h1 t0 t1 H0 H1.
    destruct l.
    - inversion H0.
    - inversion H0. inversion H1. rewrite <- H2, <-H4. reflexivity.
  Qed.

End coq_inductive_definition.


Theorem plus_n_O: forall n,
    n + 0 = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_Sn_m_n_Sm: forall n m,
    S n + m = n + S m.
Proof.
  intros n m.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_comm: forall n m,
    n + m = m + n.
Proof.
  intros n m.
  induction n.
  - rewrite plus_n_O. reflexivity.
  - rewrite <- plus_Sn_m_n_Sm. simpl.
    rewrite IHn. reflexivity.
Qed.


Inductive list (X: Type) :=
| nil: list X
| cons: X -> list X -> list X
.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint length {X: Type} (l: list X): nat :=
  match l with
  | nil => 0
  | cons h t => S (length t)
  end
.

Fixpoint app {X: Type} (l0 l1: list X): list X :=
  match l0 with
  | nil => l1
  | cons h0 t0 => cons h0 (app t0 l1)
  end
.

Theorem app_length: forall X (l0 l1: list X),
    length l0 + length l1 = length (app l0 l1).
Proof.
  intros X l0 l1.
  induction l0.
  - reflexivity.
  - simpl. rewrite IHl0. reflexivity.
Qed.

Fixpoint snoc {X: Type} (x: X) (l: list X): list X :=
  match l with
  | nil => cons x nil
  | cons h t => cons h (snoc x t)
  end
.

Fixpoint reverse {X: Type} (l: list X): list X :=
  match l with
  | nil => nil
  | cons h t => snoc h (reverse t)
  end
.

Lemma snoc_length: forall X (x: X) (l: list X),
    length (snoc x l) = S (length l).
Proof.
  intros X x l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem reverse_length: forall X (l: list X),
    length l = length (reverse l).
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite -> snoc_length.
    rewrite <- IHl. reflexivity.
Qed.








Module coq_logic_definition.

  Check 1 = 1.
  Check forall n m: nat, n + m = m + n.
  Check 1 = 2.
  Check forall n: nat, n = 2.

  Locate "=".
  Check eq.
  Check @eq.
  Print eq.

  Inductive and (A B: Prop): Prop :=
  | conj: A -> B -> A /\ B

  where "A /\ B" := (and A B): type_scope
  .

  Locate "/\".
  Print and.

  Inductive or (A B: Prop): Prop :=
  | or_introl: A -> A \/ B
  | or_intror: B -> A \/ B

  where "A \/ B" := (or A B): type_scope
  .

  Locate "\/".
  Print or.

  Definition not (P: Prop) :=
    P -> False
  .
  Notation "~ P" := (not P) : type_scope.

  Locate "~".
  Print not.

  Inductive False: Prop :=
  .

  Print False.

  Inductive True :=
  | I: True
  .

  Print True.

  Definition iff (P Q: Prop): Prop :=
    (P -> Q) /\ (Q -> P)
  .
  Notation "P <-> Q" := (iff P Q): type_scope.

  Locate "<->".
  Print iff.

  Inductive ex (A: Type) (P: A -> Prop): Prop :=
  | ex_intro: forall x: A, P x -> ex A P.
  Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
                                      (at level 200, x binder, right associativity,
                                       format "'[' 'exists' '/ ' x .. y , '/ ' p ']'")
                                    : type_scope.

  Locate "exists".
  Print ex.

End coq_logic_definition.



Theorem truth:
  True.
Proof.
  apply I.
Qed.

Theorem ex_falso_quodlibet: forall P,
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem and_comm: forall P Q,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - apply HQ.
  - apply HP.
Qed.

Theorem or_comm: forall P Q,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Theorem iff_refl: forall P,
    P <-> P.
Proof.
  intros P.
  split.
  - intro H. apply H.
  - intro H. apply H.
Qed.

Theorem iff_sym: forall P Q,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HPQ HQP]. split.
  - apply HQP.
  - apply HPQ.
Qed.

Theorem iff_trans: forall P Q R,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ]. split.
  - intros HP. apply HQR. apply HPQ. apply HP.
  - intros HR. apply HQP. apply HRQ. apply HR.
Qed.

Theorem or_distributes_over_and: forall P Q R,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | HQR].
    + split.
      * left. apply HP.
      * left. apply HP.
    + inversion HQR as [HQ HR].
      split.
      * right. apply HQ.
      * right. apply HR.
  - intros [H0 H1].
    inversion H0 as [HP | HQ].
    + left. apply HP.
    + inversion H1 as [HP | HR].
      * left. apply HP.
      * right. split.
        { apply HQ. }
        { apply HR. }
Qed.

Theorem forall_then_not_exists_not: forall X (P: X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P HA HEnot.
  inversion HEnot.
  apply H. apply HA.
Qed.

Theorem forall_not_then_not_exists: forall X (P: X -> Prop),
    (forall x, ~ P x) -> ~ (exists x, P x).
Proof.
  intros X P HAnot HE.
  inversion HE. apply HAnot in H. apply H.
Qed.

Theorem exists_then_not_forall_not: forall X (P: X -> Prop),
    (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
  intros X P HE HAnot.
  inversion HE. apply HAnot in H. apply H.
Qed.

Theorem exists_not_then_not_forall: forall X (P: X -> Prop),
    (exists x, ~ P x) -> ~ (forall x, P x).
Proof.
  intros X P HEnot HA.
  inversion HEnot. apply H. apply HA.
Qed.

Axiom functional_extensionality: forall {X Y: Type} {f g: X -> Y},
    (forall x, f x = g x) -> f = g.

Example plus_comm_lambda: plus = fun n m => m + n.
Proof. apply functional_extensionality. intros n.
       apply functional_extensionality. intros m.
       apply plus_comm. Qed.

Definition excluded_middle: Prop := forall P, P \/ ~P.

Theorem not_exists_not_then_forall: forall X (P: X -> Prop),
  excluded_middle ->
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros X P HExMid HnotEnot x.
  assert (P x \/ ~ P x).
  - apply HExMid.
  - destruct H as [HP | HnotP].
    + apply HP.
    + exfalso. apply HnotEnot.
      exists x. apply HnotP.
Qed.

Definition peirce := forall P Q: Prop,
    ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
    ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
    ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
    (P->Q) -> (~P\/Q).

(* Prove that these classical propositions are equivalent.
 * In the other world, show that
 * for any two of these propositions, biconditional(iff) is satisfied. *)

Theorem excluded_middle__de_morgan_not_and_not:
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not. unfold not.
  intros He P Q HPFQFF.
  remember (He P) as HP.
  inversion HP.
  - left. apply H.
  - remember (He Q) as HQ.
    inversion HQ.
    + right. apply H0.
    + apply ex_falso_quodlibet. apply HPFQFF. split. apply H. apply H0.
Qed.

Theorem implies_to_or__excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or. unfold excluded_middle. unfold not.
  intros Hi P.
  apply or_comm. apply Hi. intros HP. apply HP.
Qed.

Theorem double_negation_elimination__implies_to_or :
  double_negation_elimination -> implies_to_or.
Proof.
  unfold double_negation_elimination. unfold implies_to_or. unfold not.
  intros Hc P Q HPQ. apply Hc. intros HPFQF. apply HPFQF.
  left. intros HP. apply HPFQF. right. apply HPQ. apply HP.
Qed.

Theorem de_morgan_not_and_not__double_negation_elimination :
  de_morgan_not_and_not -> double_negation_elimination.
Proof.
  unfold de_morgan_not_and_not. unfold double_negation_elimination. unfold not.
  intros Hd P HPFF.
  remember (Hd P False) as HPFQFFPQ.
  assert (P \/ False -> P).
  - intros. inversion H. apply H0. inversion H0.
  - apply H. apply HPFQFFPQ. intros HPFFF.
    inversion HPFFF. apply HPFF. apply H0.
Qed.

(* Except peirce, every propositions are equivalent. *)

Theorem peirce__double_negation_elimination :
  peirce -> double_negation_elimination.
Proof.
  unfold peirce. unfold double_negation_elimination. unfold not.
  intros Hp P HPFF. apply Hp with False. intros HPF. apply HPFF in HPF. inversion HPF.
Qed.

Theorem double_negation_elimination__peirce :
  double_negation_elimination -> peirce.
Proof.
  unfold double_negation_elimination. unfold peirce. unfold not.
  intros Hc P Q HPQP. apply Hc. intros HPF. apply HPF. apply HPQP. intros HP.
  apply Hc. intros HQF. apply HPF. apply HP.
Qed.
