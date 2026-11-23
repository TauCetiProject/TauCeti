/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Maximal-ideal primary components over a discrete valuation ring

For a discrete valuation ring `(R, 𝔪)` with fraction ring `K`, `R` and `K` have no nonzero
`𝔪`-power torsion, while the quotient `K ⧸ R` is entirely `𝔪`-power torsion.

## Main results

* `TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_self`: `𝔪.primaryComponent R = ⊥`.
* `TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_fractionRing`:
  `𝔪.primaryComponent K = ⊥`.
* `TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_quotient_fractionRing`:
  `𝔪.primaryComponent (K ⧸ R) = ⊤`.
-/

public section

namespace TauCeti.IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- Over a discrete valuation ring `(R, 𝔪)`, `R` itself has no nonzero `𝔪`-power torsion. -/
lemma primaryComponent_maximalIdeal_self :
    (IsLocalRing.maximalIdeal R).primaryComponent R = ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.primaryComponent_span_singleton_eq_bot_iff]
  exact fun _ _ hxy ↦ mul_left_cancel₀ hϖ.ne_zero hxy

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction ring `K`, `K` has no nonzero `𝔪`-power
torsion because any uniformizer acts invertibly on `K`. -/
lemma primaryComponent_maximalIdeal_fractionRing :
    (IsLocalRing.maximalIdeal R).primaryComponent K = ⊥ := by
  let := IsFractionRing.toField R (K := K)
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.primaryComponent_span_singleton_eq_bot_iff]
  intro x y hxy
  have hϖK : algebraMap R K ϖ ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hϖ.ne_zero
  simpa only [Algebra.smul_def, mul_eq_mul_left_iff, hϖK, or_false] using hxy

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction ring `K`, the quotient `K ⧸ R` is
entirely `𝔪`-power torsion: every fraction has denominator a unit times a power of a
uniformizer. -/
lemma primaryComponent_maximalIdeal_quotient_fractionRing :
    (IsLocalRing.maximalIdeal R).primaryComponent
      (K ⧸ LinearMap.range (Algebra.linearMap R K)) = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Submodule.eq_top_iff']
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨⟨a, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  obtain ⟨k, u, rfl⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp hs) hϖ
  rw [Ideal.mem_primaryComponent_span_singleton_iff]
  refine ⟨k, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨↑u⁻¹ * a, ?_⟩
  have hspec := IsLocalization.mk'_spec' K a ⟨↑u * ϖ ^ k, hs⟩
  -- Multiply by `u⁻¹` in `R`: `(u * ϖ^k) • mk' K a _ = algebraMap R K a`.
  calc Algebra.linearMap R K (↑u⁻¹ * a)
    _ = (↑u⁻¹ : R) • algebraMap R K a := by
      rw [Algebra.linearMap_apply, map_mul, ← Algebra.smul_def]
    _ = (↑u⁻¹ : R) • ((↑u * ϖ ^ k) • IsLocalization.mk' K a ⟨↑u * ϖ ^ k, hs⟩) := by
      rw [← hspec, ← Algebra.smul_def]
    _ = ϖ ^ k • IsLocalization.mk' K a ⟨↑u * ϖ ^ k, hs⟩ := by
      rw [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul]

end TauCeti.IsDiscreteValuationRing
