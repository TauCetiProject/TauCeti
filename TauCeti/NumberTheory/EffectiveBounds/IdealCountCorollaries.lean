/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.IdealCount

/-!
# Consumer forms of the explicit ideal count

The EffectiveBounds roadmap's Layer 1 ideal-count target is the explicit estimate

`#{I ≠ ⊥ : absNorm I ≤ X} ≤ X² * 2^[F:ℚ]`.

The core theorem `TauCeti.NumberField.card_ideal_absNorm_le` states this with a real norm bound
`X`. Later effective estimates often carry natural-number bounds and external degree bounds, so
this file records the corresponding monotone forms without revisiting the Rankin-style proof.

## Main results

* `TauCeti.NumberField.ncard_ideal_absNorm_le_nat`: the ideal count with a natural-number norm
  bound.
* `TauCeti.NumberField.ncard_ideal_absNorm_le_of_nat_le_of_finrank_le`: the monotone form using
  separate bounds for the ideal norm and the field degree.
* `TauCeti.NumberField.ncard_ideal_absNorm_le_of_finrank_le`: the degree-monotone form with the
  original real norm bound.

No formal code is vendored. These are direct corollaries of the migrated Layer 1 bound
`TauCeti.NumberField.card_ideal_absNorm_le`, whose source attribution is in
`TauCeti/NumberTheory/EffectiveBounds/IdealCount.lean`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

open Module NumberField

/-- The set of nonzero integral ideals of `𝓞 F` with natural norm at most `N`. -/
private abbrev idealsWithAbsNormNatLe (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Set (Ideal (𝓞 F)) :=
  {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}

/-- The set of nonzero integral ideals of `𝓞 F` with real norm at most `X`. -/
private abbrev idealsWithAbsNormRealLe (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Set (Ideal (𝓞 F)) :=
  {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}

private theorem idealsWithAbsNormNatLe_finite (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    (idealsWithAbsNormNatLe F N).Finite :=
  (Ideal.finite_setOf_absNorm_le N).subset fun _ hI => hI.2

private theorem idealsWithAbsNormNatLe_eq_real (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    idealsWithAbsNormNatLe F N = idealsWithAbsNormRealLe F (N : ℝ) := by
  ext I
  exact and_congr_right fun _ => by exact_mod_cast (Iff.rfl : Ideal.absNorm I ≤ N ↔ _)

private theorem idealsWithAbsNormNatLe_zero (F : Type*) [Field F] [NumberField F] :
    idealsWithAbsNormNatLe F 0 = ∅ := by
  ext I
  simp only [idealsWithAbsNormNatLe, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hI0 hI
  exact hI0 (Ideal.absNorm_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hI))

private theorem ncard_idealsWithAbsNormNatLe_real_le (F : Type*) [Field F] [NumberField F]
    {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((idealsWithAbsNormNatLe F N).ncard : ℝ) ≤ (N : ℝ) ^ 2 * 2 ^ finrank ℚ F := by
  rw [idealsWithAbsNormNatLe_eq_real F N]
  simpa [idealsWithAbsNormRealLe] using (card_ideal_absNorm_le F (X := (N : ℝ)) hN).2

/-- **Natural-number ideal count.** The number of nonzero integral ideals of `𝓞 F` with norm at
most `N` is at most `N² * 2^[F:ℚ]`. -/
theorem ncard_ideal_absNorm_le_nat (F : Type*) [Field F] [NumberField F]
    (N : ℕ) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard ≤
      N ^ 2 * 2 ^ finrank ℚ F := by
  suffices (idealsWithAbsNormNatLe F N).ncard ≤ N ^ 2 * 2 ^ finrank ℚ F by
    simpa [idealsWithAbsNormNatLe] using this
  rcases N with _ | N
  · rw [idealsWithAbsNormNatLe_zero F]
    simp
  have hreal : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hcount' := ncard_idealsWithAbsNormNatLe_real_le F (N := N + 1) hreal
  exact_mod_cast hcount'

/-- If `1 ≤ X` and `[F : ℚ] ≤ n`, then the number of nonzero integral ideals of norm at most
`X` is at most `X² * 2^n`. This is the degree-monotone form of
`TauCeti.NumberField.card_ideal_absNorm_le`. -/
theorem ncard_ideal_absNorm_le_of_finrank_le (F : Type*) [Field F] [NumberField F]
    {X : ℝ} {n : ℕ} (hX : 1 ≤ X) (hn : finrank ℚ F ≤ n) :
    (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
      X ^ 2 * 2 ^ n := by
  calc
    (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ))
        ≤ X ^ 2 * 2 ^ finrank ℚ F := (card_ideal_absNorm_le F hX).2
    _ ≤ X ^ 2 * 2 ^ n := by
      have hpow : (2 : ℝ) ^ finrank ℚ F ≤ 2 ^ n := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg X)

/-- Monotone natural-number ideal count: if all ideals under consideration have norm at most
`N`, and `N ≤ B`, and `[F : ℚ] ≤ n`, then there are at most `B² * 2^n` of them. -/
theorem ncard_ideal_absNorm_le_of_nat_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {N B n : ℕ}
    (hN : N ≤ B) (hn : finrank ℚ F ≤ n) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard ≤ B ^ 2 * 2 ^ n := by
  calc
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard
        ≤ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ B}.ncard := by
          exact Set.ncard_le_ncard
            (by rintro I ⟨hI0, hI⟩; exact ⟨hI0, hI.trans hN⟩)
            (idealsWithAbsNormNatLe_finite F B)
    _ ≤ B ^ 2 * 2 ^ finrank ℚ F := ncard_ideal_absNorm_le_nat F B
    _ ≤ B ^ 2 * 2 ^ n := by
      exact Nat.mul_le_mul_left (B ^ 2) (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn)

/-- If `[F : ℚ] ≤ n`, then the number of nonzero integral ideals of norm at most `N` is at most
`N² * 2^n`. -/
theorem ncard_ideal_absNorm_le_nat_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {N n : ℕ}
    (hn : finrank ℚ F ≤ n) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard ≤ N ^ 2 * 2 ^ n :=
  ncard_ideal_absNorm_le_of_nat_le_of_finrank_le F le_rfl hn

end TauCeti.NumberField
