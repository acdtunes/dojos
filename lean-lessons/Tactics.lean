/-!
# A guided tour of Lean tactics

Every example here is checked by Lean. Open the file in VS Code with the
Lean 4 extension and click on each line to watch the goal change.
-/

def double (n : Nat) : Nat := n + n

/-! ## Group 1: finishing a goal -/

-- `rfl`: both sides compute to the same value.
example : 3 * 4 = 12 := by rfl
example : double 4 = 8 := by rfl

-- `decide`: Lean evaluates a concrete true/false question.
example : 7 < 10 ∧ 10 ≠ 11 := by decide

-- `exact`: give exactly the proof the goal needs.
example (P : Prop) (hp : P) : P := by exact hp

-- `assumption`: look for a matching hypothesis yourself.
example (P Q : Prop) (_hp : P) (hq : Q) : Q := by assumption

-- `trivial`: tries simple things (`rfl`, `True.intro`, `assumption`, ...).
example : True := by trivial

/-! ## Group 2: implications and "for all" -/

-- `intro`: to prove `A → B`, assume `A` and prove `B`.
example (P Q : Prop) (hq : Q) : P → Q := by
  intro _hp        -- we don't need `P`, so the name starts with `_`
  exact hq

-- `intro` also handles `∀`: "take an arbitrary n".
example : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

-- `apply`: if `h : A → B` and the goal is `B`, `apply h` leaves goal `A`.
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h          -- goal is now `P`
  exact hp

-- `specialize`: plug a value into a hypothesis.
example (f : Nat → Nat) (h : ∀ n, f n = n) : f 5 = 5 := by
  specialize h 5   -- h : f 5 = 5
  exact h

/-! ## Group 3: "and", "or", "iff" -/

-- `constructor`: split `A ∧ B` (or `A ↔ B`) into two goals.
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp       -- first goal: P
  · exact hq       -- second goal: Q

-- Shortcut: the anonymous constructor ⟨_, _⟩.
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- `obtain`: take a hypothesis apart.
example (P Q : Prop) (h : P ∧ Q) : Q := by
  obtain ⟨_hp, hq⟩ := h
  exact hq

-- `left` / `right`: to prove `A ∨ B`, choose a side.
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

-- `cases`: to use `h : A ∨ B`, handle each case separately.
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

-- `rcases` does the same with pattern syntax: `|` separates cases.
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq

-- `↔` is two implications; `constructor` splits it.
example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hp, hq⟩; exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩; exact ⟨hp, hq⟩

/-! ## Group 4: "exists" -/

-- Prove `∃ x, ...` by giving a witness and then the proof.
example : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

-- `refine` gives part of the proof and leaves `?_` holes as new goals.
example : ∃ n : Nat, n + 3 = 10 := by
  refine ⟨7, ?_⟩   -- goal: 7 + 3 = 10
  rfl

-- `obtain` unpacks an existential: you get the witness and its property.
example (h : ∃ n : Nat, n > 5) : ∃ m : Nat, m > 4 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

/-! ## Group 5: "not" and contradictions

`¬ P` means `P → False`, so `intro` works on it. -/

example (P : Prop) (hp : P) : ¬¬P := by
  intro hnp        -- hnp : ¬P, goal: False
  exact hnp hp     -- ¬P applied to P gives False

-- `contradiction`: finishes when hypotheses clash (e.g. `h : P` and `h' : ¬P`).
example (P Q : Prop) (hp : P) (hnp : ¬P) : Q := by
  contradiction

-- `exfalso`: change any goal to `False` (handy before deriving a clash).
example (n : Nat) (h : n < 0) : n = 42 := by
  exfalso
  omega

-- `by_cases`: split on whether a statement is true or false.
example (n : Nat) : n = 0 ∨ n > 0 := by
  by_cases h : n = 0
  · left; exact h
  · right; omega

/-! ## Group 6: rewriting and simplifying -/

-- `rw [h]`: with `h : a = b`, replace `a` by `b` in the goal.
example (a b : Nat) (h : a = b) : a + a = b + b := by
  rw [h]

-- `rw [← h]` rewrites the other way (b to a).
example (a b : Nat) (h : a = b) : b * 2 = a * 2 := by
  rw [← h]

-- `rw [...] at h` rewrites inside a hypothesis instead.
example (a b c : Nat) (h1 : a = b) (h2 : a = c) : b = c := by
  rw [h1] at h2
  exact h2

-- `rw` with a library lemma: `Nat.add_comm : a + b = b + a`.
example (x y : Nat) : x + y = y + x := by
  rw [Nat.add_comm]

-- `unfold`: replace a definition by its body.
example (n : Nat) : double n = n + n := by
  unfold double
  rfl

-- `simp`: apply many simplification lemmas automatically.
example (xs : List Nat) : (xs ++ []).length = xs.length := by
  simp

-- `simp only [...]`: simplify with just the lemmas you list (more predictable).
example (a : Nat) : a + 0 + 0 = a := by
  simp only [Nat.add_zero]

-- `simp at h` simplifies a hypothesis.
example (a : Nat) (h : a + 0 = 5) : a = 5 := by
  simp at h
  exact h

/-! ## Group 7: arithmetic automation -/

-- `omega`: linear arithmetic (+, -, *, by constants, <, ≤, %, /) over Nat/Int.
example (x y : Nat) (h1 : x + y = 10) (h2 : x = 3) : y = 7 := by
  omega

example (n : Nat) (h : n % 2 = 1) : n ≠ 0 := by
  omega

-- `omega` can't multiply two variables, but it treats such products as
-- unknowns, so this still works:
example (x y : Nat) (h : x * y = 5) : x * y + 1 = 6 := by
  omega

/-! ## Group 8: building a proof in steps -/

-- `have`: prove a helper fact along the way.
example (a b : Nat) (h : a < b) : a + 1 < b + 2 := by
  have h2 : a + 1 ≤ b := by omega
  omega

-- `show`: state the current goal explicitly (documentation and a check).
example (n : Nat) : double n = 2 * n := by
  unfold double
  show n + n = 2 * n
  omega

-- `calc`: a chain of equalities or inequalities, each step justified.
example (a b c : Nat) (h1 : a = b) (h2 : b = c + 1) : a = c + 1 := by
  calc a = b     := h1
       _ = c + 1 := h2

/-! ## Group 9: induction -/

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

-- `induction n`: prove the `zero` case, then `succ` using `ih` for n.
example (n : Nat) : sumTo n ≥ n := by
  induction n with
  | zero => unfold sumTo; omega
  | succ n ih =>             -- ih : sumTo n ≥ n
    unfold sumTo             -- goal: n + 1 + sumTo n ≥ n + 1
    omega

-- Induction works on lists too: `[]` case, then `x :: xs`.
example (xs : List Nat) : (xs.map id).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, List.length]
    rw [ih]

/-! ## Group 10: combinators -/

-- `<;>`: run the next tactic on every goal the previous one produced.
example (P Q : Prop) (hp : P) (hq : Q) : (P ∨ False) ∧ (Q ∨ False) := by
  constructor <;> left <;> assumption

-- `first | t1 | t2`: try t1, and if it fails, t2.
example (n : Nat) : n + 0 = n := by
  first | decide | rfl

-- `repeat' t`: keep applying t to every goal until it fails everywhere.
-- `all_goals t`: run t on every remaining goal.
example (P : Prop) (hp : P) : P ∧ P ∧ P := by
  repeat' constructor
  all_goals exact hp
