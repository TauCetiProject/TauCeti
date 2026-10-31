/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Integral.Basic
public import TauCeti.RingTheory.Affinoid.SpectralRadius
public import TauCeti.RingTheory.Affinoid.ValueGroup
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand

/-!
# Strict affinoidness at positive polyradii

A finite-variable restricted-series algebra at positive polyradii is strictly affinoid over
`K` if and only if each radius has a positive integral power in the value group of `K`.
Thus the radii need not themselves be norms of scalars. In the strict case the supremum
norm is the weighted Gauss norm.

The finite monomial extension
`TauCeti.MvPowerSeries.exists_injective_finite_algHom_of_norm_mul_pow_eq_one` supplies a finite
map from the unit-radius Tate algebra. Closure of affinoid algebras under finite extensions
then gives a surjective unit-radius Tate presentation, as required by `IsAffinoidAlgebra`.
Conversely, the affinoid value-group theorem applied to the variables detects every radius:
their supremum norms are their Gauss norms, since the latter are multiplicative.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.5.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] {r : σ → ℝ} [∀ i, Fact (0 < r i)]

/-- Restricted series at positive polyradii in the divisible hull of the value group form a
strictly affinoid algebra. The positive exponent and scalar may depend on the variable. -/
theorem isAffinoidAlgebra_isRestricted_of_pow_eq_norm
    (hr : ∀ i, ∃ n : ℕ, 0 < n ∧ ∃ c : Kˣ, r i ^ n = ‖(c : K)‖) :
    IsAffinoidAlgebra K (IsRestricted.subring (R := K) r) := by
  obtain ⟨φ, -, hφ⟩ :=
    MvPowerSeries.exists_injective_finite_algHom_of_norm_mul_pow_eq_one (K := K) (r := r)
      (fun i ↦ by
        obtain ⟨n, hn, c, hc⟩ := hr i
        exact ⟨n, hn.ne', (c : K)⁻¹, by simp [norm_inv, hc, c.ne_zero]⟩)
  exact isAffinoidAlgebra_tate.of_algHom_finite φ hφ

omit [Finite σ] in
/-- Strict affinoidness forces every positive radius into the divisible hull of the value
group. A single positive exponent works simultaneously for all variables. -/
theorem exists_pow_eq_norm_of_isAffinoidAlgebra_isRestricted
    (hA : IsAffinoidAlgebra K (IsRestricted.subring (R := K) r)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, ∃ c : Kˣ, r i ^ n = ‖(c : K)‖ := by
  obtain ⟨n, hn, h⟩ := hA.exists_supSeminorm_pow_eq_norm
  refine ⟨n, by omega, fun i ↦ ?_⟩
  obtain ⟨c, hc⟩ := h (⟨X i, isRestricted_X r i⟩ : IsRestricted.subring (R := K) r)
  rw [hA.supSeminorm_eq_norm_of_normMulClass, MvPowerSeries.norm_X] at hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hc ▸ pow_pos (Fact.out : 0 < r i) n)
  exact ⟨Units.mk0 c hc0, hc⟩

/-- **Strict-polyradius criterion.** Restricted series at positive polyradii are strictly
`K`-affinoid exactly when every radius belongs to the divisible hull of `|Kˣ|`. -/
theorem isAffinoidAlgebra_isRestricted_iff_pow_eq_norm :
    IsAffinoidAlgebra K (IsRestricted.subring (R := K) r) ↔
      ∀ i, ∃ n : ℕ, 0 < n ∧ ∃ c : Kˣ, r i ^ n = ‖(c : K)‖ := by
  constructor
  · intro hA
    obtain ⟨n, hn, h⟩ := exists_pow_eq_norm_of_isAffinoidAlgebra_isRestricted hA
    exact fun i ↦ ⟨n, hn, h i⟩
  · exact isAffinoidAlgebra_isRestricted_of_pow_eq_norm

end TauCeti
