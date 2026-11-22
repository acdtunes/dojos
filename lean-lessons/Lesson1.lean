/-!
# Lesson 1: Lean basics

Run this file with `lean Lesson1.lean`, or open it in VS Code with the
Lean 4 extension to see results live as you type.
-/

/-! ## 1. Values and types

Every value in Lean has a type. `#eval` computes a value; `#check` shows a type. -/

#eval 2 + 3          -- 5
#eval "hi" ++ "!"    -- "hi!"
#check 2 + 3         -- 2 + 3 : Nat
#check "hi"          -- "hi" : String

/-! ## 2. Defining functions -/

def double (n : Nat) : Nat := n + n

#eval double 21      -- 42

/-- Functions can be defined by cases, using pattern matching. -/
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 10       -- 55

/-! ## 3. Statements are types, proofs are values

`2 + 2 = 4` is a type. A proof of it is a value of that type.
`theorem name : statement := proof` -/

-- `rfl` ("reflexivity"): both sides compute to the same thing.
theorem two_plus_two : 2 + 2 = 4 := rfl

theorem double_three : double 3 = 6 := rfl

-- `decide`: let Lean check a concrete, finite fact by computing.
theorem ten_lt_twenty : 10 < 20 := by decide

/-! ## 4. Tactics

`by` switches to tactic mode: you give commands that transform the goal
until nothing is left. In VS Code, put your cursor on a line to see the
current goal. -/

-- `intro` names an assumption; `exact` closes the goal with a term.
theorem self_imp (P : Prop) : P → P := by
  intro hp
  exact hp

-- `And`: build with `⟨_, _⟩`, take apart with `obtain`.
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

-- `rw` rewrites using an equation.
theorem rw_example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

-- `omega` solves linear arithmetic over Nat and Int automatically.
theorem omega_example (x y : Nat) (h : x < y) : x + 1 ≤ y := by
  omega

-- `induction`: prove for 0, then show n implies n + 1.
theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  unfold double
  omega

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sumTo
    rw [Nat.mul_add, ih]
    -- goal: 2 * (n + 1) + n * (n + 1) = (n + 1) * (n + 1 + 1)
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-! ## 5. Exercises

Replace each `sorry` with a proof. Lean warns about every `sorry`
left, so when the file runs with no warnings, you're done.
Hints are in the comments. -/

-- (a) Hint: `rfl`.
theorem ex_a : double 5 = 10 := sorry

-- (b) Hint: `intro`, then `obtain`, then `exact`.
theorem ex_b (P Q : Prop) : P ∧ Q → P := by
  sorry

-- (c) Hint: `intro` twice, then `exact` with something built from both.
theorem ex_c (P Q : Prop) : P → Q → P ∧ Q := by
  sorry

-- (d) Hint: `omega`.
theorem ex_d (n : Nat) : double n ≥ n := by
  unfold double
  sorry

-- (e) Challenge. Hint: `induction n`, and use `unfold sumTo` and `omega`.
theorem ex_e (n : Nat) : sumTo n ≥ n := by
  sorry
