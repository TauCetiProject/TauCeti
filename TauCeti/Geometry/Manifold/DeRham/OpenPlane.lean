/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Exactness

/-!
# Vanishing of top-degree de Rham cohomology on open subsets of `ℂ`

Every smooth real-valued `2`-form on an arbitrary open subset `U ⊆ ℂ` is exact
(`TauCeti.exists_mextDerivₗ_eq_of_opens_complex`), proved via global solvability of the
inhomogeneous Cauchy–Riemann equation `\bar∂ u = f` on `U`. Consequently, the second de Rham
cohomology group `H²_dR(U)` vanishes (`TauCeti.subsingleton_deRhamCohomology_two_opens_complex`),
and combining this with the dimensional vanishing in degrees `k > 2` shows that `H^k_dR(U) = 0`
for all `k ≥ 2` (`TauCeti.subsingleton_deRhamCohomology_opens_complex_of_two_le`).

No connectedness, boundedness, or topological hypothesis on `U` is required.

## Main declarations

* `TauCeti.exactForms_two_eq_top_opens_complex`: every smooth real `2`-form on an open subset
  `U ⊆ ℂ` is exact.
* `TauCeti.exactForms_two_eq_closedForms_opens_complex`: on an open subset `U ⊆ ℂ`, exact smooth
  real `2`-forms coincide with closed smooth real `2`-forms.
* `TauCeti.subsingleton_deRhamCohomology_two_opens_complex`: `H²_dR(U) = 0` for every open subset
  `U ⊆ ℂ`.
* `TauCeti.subsingleton_deRhamCohomology_opens_complex_of_two_le`: `H^k_dR(U) = 0` for every open
  subset `U ⊆ ℂ` and every `k ≥ 2`.

## References

* Lars Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Chapter 1.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold

namespace TauCeti

/-- Every smooth real-valued `2`-form on an open subset `U ⊆ ℂ` is exact. -/
theorem exactForms_two_eq_top_opens_complex (U : Opens ℂ) :
    exactForms 𝓘(ℝ, ℂ) U 2 = ⊤ := by
  refine eq_top_iff.2 fun η _ ↦ ?_
  rw [exactForms_succ]
  exact exists_mextDerivₗ_eq_of_opens_complex η

/-- On an open subset `U ⊆ ℂ`, exact smooth real `2`-forms coincide with closed smooth real
`2`-forms. -/
theorem exactForms_two_eq_closedForms_opens_complex (U : Opens ℂ) :
    exactForms 𝓘(ℝ, ℂ) U 2 = closedForms 𝓘(ℝ, ℂ) U 2 :=
  le_antisymm (exactForms_le_closedForms 𝓘(ℝ, ℂ) 2)
    (by rw [exactForms_two_eq_top_opens_complex]; exact le_top)

/-- **Top-degree de Rham cohomology vanishes on every open subset of `ℂ`.** -/
theorem subsingleton_deRhamCohomology_two_opens_complex (U : Opens ℂ) :
    Subsingleton (deRhamCohomology 𝓘(ℝ, ℂ) U 2) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective 𝓘(ℝ, ℂ) 2 c
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_two_eq_closedForms_opens_complex]
  exact φ.property

/-- **De Rham cohomology of an open subset of `ℂ` vanishes in all degrees `k ≥ 2`.** -/
theorem subsingleton_deRhamCohomology_opens_complex_of_two_le (U : Opens ℂ) {k : ℕ}
    (hk : 2 ≤ k) : Subsingleton (deRhamCohomology 𝓘(ℝ, ℂ) U k) := by
  rcases hk.eq_or_lt with rfl | hlt
  · exact subsingleton_deRhamCohomology_two_opens_complex U
  · exact subsingleton_deRhamCohomology_of_finrank_lt 𝓘(ℝ, ℂ) U
      (by rwa [Complex.finrank_real_complex])

end TauCeti
