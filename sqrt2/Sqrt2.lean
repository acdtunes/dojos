/-!
# √2 is irrational

A self-contained proof in core Lean 4 (no Mathlib).

"√2 is rational" would mean `√2 = p / q` for integers `p`, `q` with `q ≠ 0`,
i.e. `p * p = 2 * (q * q)`. We show this equation has no solution with
`q ≠ 0`, by infinite descent: any solution `(p, q)` yields a smaller solution
`(q / 2, p / 2)`.
-/

/-- If `n * n` is even, then `n` is even. -/
theorem even_of_sq_even (n : Nat) (h : (n * n) % 2 = 0) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact h0
  · rw [Nat.mul_mod, h1] at h
    contradiction

/-- `p * p = 2 * (q * q)` forces `q = 0` (infinite descent on `q`). -/
theorem sq_eq_two_mul_sq (q : Nat) : ∀ p : Nat, p * p = 2 * (q * q) → q = 0 := by
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro p h
    -- p is even: p = 2k
    have hp : p % 2 = 0 := even_of_sq_even p (by rw [h, Nat.mul_mod_right])
    obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k := ⟨p / 2, by omega⟩
    -- so q * q = 2 * (k * k)
    have hq2 : q * q = 2 * (k * k) := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
      rw [← h, Nat.mul_mul_mul_comm, Nat.mul_assoc]
    -- q is even: q = 2m
    have hq : q % 2 = 0 := even_of_sq_even q (by rw [hq2, Nat.mul_mod_right])
    obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m := ⟨q / 2, by omega⟩
    -- so k * k = 2 * (m * m), a smaller solution
    have hk : k * k = 2 * (m * m) := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
      rw [← hq2, Nat.mul_mul_mul_comm, Nat.mul_assoc]
    cases Nat.eq_zero_or_pos m with
    | inl hm => rw [hm]
    | inr hm =>
      have : m = 0 := ih m (by omega) k hk
      omega

/-- There are no natural numbers `p`, `q` with `q ≠ 0` and `(p / q)² = 2`. -/
theorem sqrt_two_irrational_nat :
    ¬ ∃ p q : Nat, q ≠ 0 ∧ p * p = 2 * (q * q) := by
  intro ⟨p, q, hq, h⟩
  exact hq (sq_eq_two_mul_sq q p h)

/-- The same over the integers: no `p q : Int` with `q ≠ 0` and `p² = 2 q²`. -/
theorem sqrt_two_irrational :
    ¬ ∃ p q : Int, q ≠ 0 ∧ p * p = 2 * (q * q) := by
  intro ⟨p, q, hq, h⟩
  apply sqrt_two_irrational_nat
  refine ⟨p.natAbs, q.natAbs, by omega, ?_⟩
  have := congrArg Int.natAbs h
  simpa only [Int.natAbs_mul] using this
