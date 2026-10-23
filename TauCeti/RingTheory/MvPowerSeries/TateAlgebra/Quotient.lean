/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.OpenMapping
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Quotient maps of restricted power series

A bounded coefficient homomorphism with a uniform bound on coefficient lifts induces an open
quotient map of restricted-series rings for their Gauss norm topologies. The lift has the same
norm bound as the coefficient lifts, at every positive real polyradius.

Neither completeness nor a finite variable set is needed. The lifting hypothesis is stronger
than algebraic surjectivity; the quotient topology alone does not assert equality with a
prescribed quotient norm.

The coefficientwise lifting construction extends
`TauCeti.MvPowerSeries.restrictedMap_surjective`, using Mathlib's `isRestricted_map`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedRing S] [IsUltrametricDist S] {c : σ → ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)

variable [∀ i, Fact (0 < c i)]

/-- A nonnegative bound on coefficient lifts is also a bound on lifts for the Gauss norm. -/
theorem exists_restrictedMap_eq_and_norm_le {L : ℝ} (hL : 0 ≤ L)
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : IsRestricted.subring (R := S) c) :
    ∃ f, restrictedMap φ hφ f = g ∧ ‖f‖ ≤ L * ‖g‖ := by
  obtain ⟨f, hf, hcoeff⟩ := exists_restrictedMap_eq_and_norm_coeff_le φ hφ hlift g
  exact ⟨f, hf, norm_le_mul_of_norm_coeff_le hL hcoeff⟩

/-- Uniformly bounded coefficient lifts make the induced map of restricted series open. -/
theorem isOpenMap_restrictedMap {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    IsOpenMap (restrictedMap (c := c) φ hφ) := by
  apply isOpenMap_of_exists_norm_le (restrictedMap (c := c) φ hφ) (K := max L 0)
  apply exists_restrictedMap_eq_and_norm_le φ hφ (le_max_right L 0)
  intro b
  obtain ⟨a, ha, hnorm⟩ := hlift b
  exact ⟨a, ha, hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left L 0) (norm_nonneg b))⟩

/-- A bounded coefficient homomorphism with uniformly bounded lifts induces a quotient map
for the Gauss norm topologies at arbitrary positive polyradii. -/
theorem isQuotientMap_restrictedMap {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    Topology.IsQuotientMap (restrictedMap (c := c) φ hφ) :=
  (isOpenMap_restrictedMap φ hφ hlift).isQuotientMap
    (continuous_restrictedMap φ hφ) (restrictedMap_surjective φ hφ hlift)

end TauCeti.MvPowerSeries
