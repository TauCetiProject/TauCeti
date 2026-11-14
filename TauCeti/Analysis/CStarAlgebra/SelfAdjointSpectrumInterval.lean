/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Spectral intervals of self-adjoint elements

Let `a` be a self-adjoint element of a real normed star algebra with an isometric continuous
functional calculus for self-adjoint elements, for instance a C⋆-algebra. Every point of the real
spectrum of `a` has absolute value at most `‖a‖`
(`IsometricContinuousFunctionalCalculus.norm_spectrum_le`). When the algebra is nontrivial, `‖a‖`
is attained as the largest such absolute value
(`IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum`); in a trivial algebra the
spectrum is empty and `‖a‖ = 0`. In either case, for `0 ≤ r`, `‖a‖ ≤ r` exactly when the real
spectrum of `a` lies in the interval `[-r, r]`; this turns spectral localisation into norm bounds
and back.

In a unital C⋆-algebra, equipping the algebra locally with its canonical spectral order turns
asymmetric real-spectrum inclusions `spectrum ℝ a ⊆ [m, M]` into operator inequalities
`algebraMap ℝ A m ≤ a ≤ algebraMap ℝ A M`, which add across binary and finite sums of self-adjoint
elements without requiring an ambient `PartialOrder` or `StarOrderedRing` instance on `A`.

If instead the spectrum has a gap around zero of radius `r > 0`, then `a` is invertible and its
canonical ring inverse has norm at most `r⁻¹`; this is
`IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le` in
`TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.GapInverse`, which applies to `a`
and its real spectrum directly.

## Main results

* `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: for `0 ≤ r`, `‖a‖ ≤ r` if and only if
  `spectrum ℝ a ⊆ Set.Icc (-r) r`.
* `IsSelfAdjoint.spectrum_add_subset_Icc`: real-spectrum interval bounds add for two self-adjoint
  elements of a unital C⋆-algebra.
* `TauCeti.spectrum_sum_subset_Icc`: real-spectrum interval bounds add across any finite sum of
  self-adjoint elements of a unital C⋆-algebra.
-/

public section

namespace IsSelfAdjoint

section IsometricCFC

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A} {r : ℝ}

/-- The norm of a self-adjoint element is at most `r ≥ 0` exactly when its real spectrum lies
in the interval `[-r, r]`. -/
theorem norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  simpa [Set.subset_def, abs_le, cfc_id' ℝ a] using norm_cfc_le_iff (id : ℝ → ℝ) a hr

end IsometricCFC

/-- If two self-adjoint elements of a unital C⋆-algebra have real spectra in `[m₁, M₁]` and
`[m₂, M₂]`, then the real spectrum of their sum lies in `[m₁ + m₂, M₁ + M₂]`. -/
theorem spectrum_add_subset_Icc {A : Type*} [CStarAlgebra A] {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) {m₁ M₁ m₂ M₂ : ℝ}
    (haI : spectrum ℝ a ⊆ Set.Icc m₁ M₁) (hbI : spectrum ℝ b ⊆ Set.Icc m₂ M₂) :
    spectrum ℝ (a + b) ⊆ Set.Icc (m₁ + m₂) (M₁ + M₂) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hle₁ : algebraMap ℝ A m₁ ≤ a :=
    (algebraMap_le_iff_le_spectrum ha).mpr fun x hx => (haI hx).1
  have hge₁ : a ≤ algebraMap ℝ A M₁ :=
    (le_algebraMap_iff_spectrum_le ha).mpr fun x hx => (haI hx).2
  have hle₂ : algebraMap ℝ A m₂ ≤ b :=
    (algebraMap_le_iff_le_spectrum hb).mpr fun x hx => (hbI hx).1
  have hge₂ : b ≤ algebraMap ℝ A M₂ :=
    (le_algebraMap_iff_spectrum_le hb).mpr fun x hx => (hbI hx).2
  have hlow : algebraMap ℝ A (m₁ + m₂) ≤ a + b := by
    rw [map_add]
    exact add_le_add hle₁ hle₂
  have hhigh : a + b ≤ algebraMap ℝ A (M₁ + M₂) := by
    rw [map_add]
    exact add_le_add hge₁ hge₂
  exact fun x hx => ⟨(algebraMap_le_iff_le_spectrum (ha.add hb)).mp hlow x hx,
    (le_algebraMap_iff_spectrum_le (ha.add hb)).mp hhigh x hx⟩

end IsSelfAdjoint

namespace TauCeti

open Finset

/-- If self-adjoint elements `a i` (`i ∈ s`) of a unital C⋆-algebra have real spectra in
`[m i, M i]`, then the real spectrum of `∑ i ∈ s, a i` lies in `[∑ i ∈ s, m i, ∑ i ∈ s, M i]`,
including when `s = ∅`. -/
theorem spectrum_sum_subset_Icc {A ι : Type*} [CStarAlgebra A] (s : Finset ι) {a : ι → A}
    {m M : ι → ℝ} (ha : ∀ i ∈ s, IsSelfAdjoint (a i))
    (hI : ∀ i ∈ s, spectrum ℝ (a i) ⊆ Set.Icc (m i) (M i)) :
    spectrum ℝ (∑ i ∈ s, a i) ⊆ Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sum_empty, Set.Icc_self]
      by_cases hA : Nontrivial A
      · simp
      · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
        simp
  | @insert i s hi ih =>
      have hsa_sum : IsSelfAdjoint (∑ j ∈ s, a j) :=
        isSelfAdjoint_sum s fun j hj => ha j (mem_insert_of_mem hj)
      rw [sum_insert hi, sum_insert hi, sum_insert hi]
      exact (ha i (mem_insert_self i s)).spectrum_add_subset_Icc hsa_sum
        (hI i (mem_insert_self i s))
        (ih (fun j hj => ha j (mem_insert_of_mem hj))
          (fun j hj => hI j (mem_insert_of_mem hj)))

end TauCeti
