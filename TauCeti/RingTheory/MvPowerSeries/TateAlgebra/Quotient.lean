/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Quotient maps of restricted power series

A bounded coefficient homomorphism with a uniform bound on coefficient lifts induces an open
quotient map of restricted-series rings for their Gauss norm topologies. The lift has the same
norm bound as the coefficient lifts, at every positive real polyradius. Its kernel consists of
the series whose coefficients belong to the coefficient kernel.

These statements supply topological quotient interfaces for coefficient base change and finite
presentations. Neither completeness nor a finite variable set is needed. The lifting hypothesis
is stronger than algebraic surjectivity; the quotient topology alone does not assert equality
with a prescribed quotient norm.

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
  refine ⟨f, hf, (norm_le_iff (mul_nonneg hL (norm_nonneg g))).mpr fun t ↦ ?_⟩
  calc
    ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤
        L * ‖coeff t (g : MvPowerSeries σ S)‖ * t.prod (c · ^ ·) :=
      mul_le_mul_of_nonneg_right (hcoeff t) (prod_pow_pos t).le
    _ ≤ L * ‖g‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le g t) hL

/-- Uniformly bounded coefficient lifts make the induced map of restricted series open. -/
theorem isOpenMap_restrictedMap {L : ℝ} (hL : 0 < L)
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    IsOpenMap (restrictedMap (c := c) φ hφ) := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU f hf
  refine ⟨ε / L, div_pos hε hL, ?_⟩
  intro g hg
  obtain ⟨q, hq, hqn⟩ := exists_restrictedMap_eq_and_norm_le φ hφ hL.le hlift
    (g - restrictedMap φ hφ f)
  refine ⟨f + q, hεU ?_, ?_⟩
  · have hg' : ‖g - restrictedMap φ hφ f‖ < ε / L := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hg
    have hq' : ‖q‖ < ε := hqn.trans_lt <| by
      simpa only [mul_comm] using (lt_div_iff₀ hL).mp hg'
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hq'
  · simp only [map_add, hq, add_sub_cancel]

/-- A bounded coefficient homomorphism with uniformly bounded lifts induces a quotient map
for the Gauss norm topologies at arbitrary positive polyradii. -/
theorem isQuotientMap_restrictedMap {L : ℝ} (hL : 0 < L)
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    Topology.IsQuotientMap (restrictedMap (c := c) φ hφ) :=
  (isOpenMap_restrictedMap φ hφ hL hlift).isQuotientMap
    (continuous_restrictedMap φ hφ) (restrictedMap_surjective φ hφ hlift)

end TauCeti.MvPowerSeries
