/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Integral
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand

/-!
# Strict affinoidness at positive polyradii

A finite-variable restricted-series algebra at positive polyradii is strictly affinoid over
`K` if each radius has a positive integral power in the value group of `K`. Thus the radii need
not themselves be norms of scalars.

The finite monomial extension
`TauCeti.MvPowerSeries.exists_injective_finite_algHom_of_norm_mul_pow_eq_one` supplies a finite
map from the unit-radius Tate algebra. Closure of affinoid algebras under finite extensions
then gives a surjective unit-radius Tate presentation, as required by `IsAffinoidAlgebra`.

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

end TauCeti
