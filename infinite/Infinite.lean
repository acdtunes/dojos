/-!
# The natural numbers are infinite

A self-contained proof in core Lean 4 (no Mathlib).

"Finite" would mean that all natural numbers fit in some finite collection.
We show that no finite collection can contain them all, in two forms:

* no finite list contains every natural number, and
* for no `k` is there a function from `Fin k` (the numbers `0, …, k-1`)
  onto `Nat`.

In both cases the idea is the same: find a number at least as big as
every member, and add 1. The result is missing from the collection.
-/

/-- Every element of a list of naturals is at most the list's sum. -/
theorem le_sum_of_mem {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, .head _ => by simp only [List.sum_cons]; omega
  | y :: ys, .tail _ h => by
      have := le_sum_of_mem h
      simp only [List.sum_cons]; omega

/-- No finite list contains every natural number. -/
theorem nat_not_finite_list (l : List Nat) : ∃ n, n ∉ l :=
  ⟨l.sum + 1, fun h => by have := le_sum_of_mem h; omega⟩

/-- Any function `f : Fin k → Nat` has an upper bound `B`. -/
theorem bounded_fin : ∀ (k : Nat) (f : Fin k → Nat), ∃ B, ∀ i, f i ≤ B
  | 0, _ => ⟨0, fun i => i.elim0⟩
  | k + 1, f => by
    -- bound the first `k` values, then add the last one
    obtain ⟨B, hB⟩ := bounded_fin k (fun i => f ⟨i.val, by omega⟩)
    refine ⟨B + f ⟨k, by omega⟩, fun i => ?_⟩
    by_cases h : i.val < k
    · have : f i ≤ B := hB ⟨i.val, h⟩
      omega
    · have hi : i = ⟨k, by omega⟩ := Fin.ext (show i.val = k by omega)
      rw [hi]; omega

/-- For no `k` does a function from `Fin k` hit every natural number. -/
theorem nat_infinite (k : Nat) (f : Fin k → Nat) : ∃ n, ∀ i, f i ≠ n := by
  obtain ⟨B, hB⟩ := bounded_fin k f
  exact ⟨B + 1, fun i h => by have := hB i; omega⟩
