import Mathlib.Probability.Kernel.Basic

open ProbabilityTheory MeasureTheory

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {s : Set α} (hs : MeasurableSet s)
  [DecidablePred fun x => x ∈ s]
  (κ η : Kernel α β)
  [IsMarkovKernel κ] [IsMarkovKernel η] :
  IsMarkovKernel (Kernel.piecewise hs κ η) :=
inferInstance

section types
  def f (x : Nat) := x + 0

  example (n : Nat) : f n = n := rfl

  def double (x : Nat) : Nat := x + x
  def add (x : Nat) (y : Nat) := x + y

  def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

  #eval doTwice double 2

  #eval add (double 3) (7 + 9)

  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

  def square (x : Nat) : Nat := x * x

  #eval compose Nat Nat Nat double square 3
end types

section props
  def Implies (p q : Prop) : Prop := p → q
  #check And
  #check Implies

  variable (p q : Prop)
  #check p → q → p ∧ q

  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
  #check fun (hp : p) (hq : q) => And.intro hp hq

  variable (p q : Prop)
  example (h : p ∧ q) : p := And.left h /-- extract left part of h -/
  example (h : p ∧ q) : q := And.right h /-- extract right part of h -/
  example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

  /-- Proof that conjuction is commutative -/
  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
      (fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))

  #check and_swap p q

  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h

  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    fun h : ∀ x : α, p x ∧ q x =>
    fun y : α =>
    show p y from (h y).left

  -- Equality relation
  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd

  #check Eq.refl

  -- Same equality relation as above
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)

  example : a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

  example : a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

  variable (α β : Type)
  example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
  example (a : α) (b : β) : (a,b).1 = a := rfl
  example : 2 + 3 = 5 := rfl

  -- substitution:
  example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2

  variable (a b c : Nat)
  example : a + 0 = a := Nat.add_zero a

  -- existential quantifier
  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    Exists.intro 1 h
end props

section tactics
  theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
    apply And.intro
    exact hp
    apply And.intro
    exact hq
    exact hp

  example (α : Type) : ∀ x : α, x = x := by
    intro x
    exact Eq.refl x

  variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃

example (p q : Prop) : p → q → p := by
  intro hp hq
  exact hp

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

variable (k : Nat) (f : Nat → Nat)
example (h_1 : f 0 = 0) (h_2 : k = 0) : f k = 0 := by
  rw [h_2]
  rw [h_1]

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
end tactics

section Hidden
  inductive Prod1 (α : Type u) (β : Type v)
    | mk : α → β → Prod1 α β

  def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
    match p with
    | Prod.mk a b => a

  def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
    match p with
    | Prod.mk a b => b

  inductive BinaryTree where
    | leaf : BinaryTree
    | node : BinaryTree → BinaryTree → BinaryTree

  def t1 : BinaryTree := BinaryTree.leaf
  def t2 : BinaryTree := BinaryTree.node BinaryTree.leaf BinaryTree.leaf
  def t3 : BinaryTree := BinaryTree.node (BinaryTree.node BinaryTree.leaf BinaryTree.leaf) BinaryTree.leaf

  example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
    intro n
    cases n
    . exact hz
    . apply hs










end Hidden
