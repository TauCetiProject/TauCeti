/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Operations
public import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Products of finite exponentials in nilpotent submodules

If `M ^ n = ⊥`, the difference `IsNilpotent.exp x * IsNilpotent.exp y - 1` has vanishing
`n`-th power for `x, y ∈ M`. In particular, this supplies the nilpotency witness needed for
the finite logarithm of the product. The submodule need not be closed under rational scalars
or multiplication; the result also applies to left ideals.
-/

public section

namespace Submodule

variable {R A : Type*} [Ring A] [Module ℚ A] [Semiring R] [Module R A]
  [IsScalarTower R A A]

/-- The difference from one of a product of finite exponentials of elements of a submodule
has vanishing `n`-th power whenever the submodule does. No closure under rational scalars
or multiplication is required. -/
theorem exp_mul_exp_sub_one_pow_eq_zero (M : Submodule R A) {n : ℕ} (hM : M ^ n = ⊥)
    {x y : A} (hx : x ∈ M) (hy : y ∈ M) :
    (IsNilpotent.exp x * IsNilpotent.exp y - 1) ^ n = 0 := by
  let _ : Algebra ℚ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
  cases n with
  | zero =>
    simpa only [hM, mem_bot, pow_zero] using M.pow_mem_pow hx 0
  | succ n =>
    -- Rational spans of the positive powers retain their word-length bounds.
    let W (t : ℕ) : Set A := ⋃ k ≥ t + 1, ((M ^ k : Submodule R A) : Set A)
    let J := span ℚ (W 0)
    have hmul (t : ℕ) : ∀ b ∈ W t, ∀ c ∈ W 0, b * c ∈ W (t + 1) := by
      rintro b hb c hc
      obtain ⟨i, hi, hb⟩ := Set.mem_iUnion₂.mp hb
      obtain ⟨j, hj, hc⟩ := Set.mem_iUnion₂.mp hc
      refine Set.mem_iUnion₂.mpr ⟨i + j, by omega, ?_⟩
      rw [M.pow_add (by omega : j ≠ 0)]
      exact mul_mem_mul hb hc
    have hpow (t : ℕ) : J ^ (t + 1) ≤ span ℚ (W t) :=
      span_pow_succ_le_span_of_forall_mul_mem subset_span (fun t b hb c hc ↦
        subset_span (hmul t b hb c hc)) t
    -- All sufficiently long words vanish, and the positive-word span is closed under products.
    have hJ : J ^ (n + 1) = ⊥ := by
      apply le_bot_iff.mp
      refine (hpow n).trans (span_le.mpr ?_)
      intro a ha
      obtain ⟨k, hk, ha⟩ := Set.mem_iUnion₂.mp ha
      have hkM : M ^ k = ⊥ :=
        (pow_eq_pow_of_pow_succ_eq_pow (by rw [Submodule.pow_succ, hM, bot_mul]) hk).trans hM
      simpa only [hkM, SetLike.mem_coe, mem_bot] using ha
    have hJJ : J * J ≤ J := by
      rw [← pow_two]
      exact (hpow 1).trans (span_mono (by
        intro a ha
        obtain ⟨k, hk, ha⟩ := Set.mem_iUnion₂.mp ha
        exact Set.mem_iUnion₂.mpr ⟨k, by omega, ha⟩))
    -- The positive-degree exponential terms and their products belong to this nilpotent span.
    have hexp (z : A) (hz : z ∈ M) : IsNilpotent.exp z - 1 ∈ J := by
      have hz0 : z ^ (n + 1) = 0 := by
        simpa only [hM, mem_bot] using M.pow_mem_pow hz (n + 1)
      rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ _) hz0),
        Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
        add_sub_cancel_right]
      exact J.sum_mem fun i _ ↦ J.smul_mem _ (subset_span
        (Set.mem_iUnion₂.mpr ⟨i + 1, Nat.succ_le_succ (Nat.zero_le _), M.pow_mem_pow hz _⟩))
    have he : IsNilpotent.exp x * IsNilpotent.exp y - 1 ∈ J := by
      have heq : IsNilpotent.exp x * IsNilpotent.exp y - 1 =
          (IsNilpotent.exp x - 1) * (IsNilpotent.exp y - 1) +
            (IsNilpotent.exp x - 1) + (IsNilpotent.exp y - 1) := by
        simp only [sub_mul, mul_sub, mul_one, one_mul]
        abel
      rw [heq]
      exact J.add_mem (J.add_mem (hJJ (mul_mem_mul (hexp x hx) (hexp y hy)))
        (hexp x hx)) (hexp y hy)
    simpa only [hJ, mem_bot] using J.pow_mem_pow he (n + 1)

end Submodule
