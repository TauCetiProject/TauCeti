/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Checks: the Gaussian perimeter of half-spaces

With `φ = gaussianPDFReal 0 1`, `Φ = cdf (gaussianReal 0 1)` and the Gaussian isoperimetric
function `I = φ ∘ Φ⁻¹`, the half-space `{x | ⟪x, ν⟫ < c}` of a unit vector `ν` has Gaussian
measure `Φ(c)` and Gaussian perimeter `φ(c)` (`TauCeti.gaussianPerimeter_setOf_inner_lt`).

* A half-space of Gaussian measure `v` has Gaussian perimeter `I(v)`
  (`TauCeti.gaussianPerimeter_setOf_inner_lt_eq_gaussianIsoperimetricProfile`).
* The half-space through the origin has perimeter `φ(0) = I(1/2)`.
* In `ℝ²`, the half-plane `{x | 1 < x₀}` has perimeter `φ(1)`, and `{x | x₀ < 1}` too.
* Gaussian perimeter is not translation invariant: translating `{x | ⟪x, ν⟫ < 0}` by a unit
  vector `ν` changes the perimeter from `φ(0)` to `φ(1) < φ(0)`.
* The half-spaces `U_k = {x | ⟪x, ν⟫ < k}` have perimeters `φ(k) → 0` and Gaussian measures
  tending to `1`, so `U_k → E` in `L¹(γ)`, and `P_γ(E) = 0`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TauCeti TauCeti.Probability
open scoped ENNReal RealInnerProductSpace Topology

namespace TauCeti.Examples.GaussianHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A half-space of Gaussian measure `v` has Gaussian perimeter `I(v)`. -/
example (ν : E) (c : ℝ) :
    gaussianPerimeter {x : E | ⟪x, ν⟫ < c} =
      ENNReal.ofReal (gaussianIsoperimetricProfile ((stdGaussian E).real {x | ⟪x, ν⟫ < c})) :=
  gaussianPerimeter_setOf_inner_lt_eq_gaussianIsoperimetricProfile ν c

/-- The half-space through the origin has Gaussian perimeter `φ(0) = I(1/2)`. -/
theorem gaussianPerimeter_setOf_inner_lt_zero {ν : E} (hν : ν ≠ 0) :
    gaussianPerimeter {x : E | ⟪x, ν⟫ < 0} = ENNReal.ofReal (gaussianIsoperimetricProfile 2⁻¹) := by
  rw [gaussianPerimeter_setOf_inner_lt_of_ne_zero hν, zero_div, gaussianIsoperimetricProfile_half]

/-- The coordinate `x₀` of `ℝ²` is the inner product with the unit vector `e₀`. -/
private theorem inner_single (x : EuclideanSpace ℝ (Fin 2)) (a : ℝ) :
    ⟪x, EuclideanSpace.single 0 a⟫ = x 0 * a := by
  simp [EuclideanSpace.inner_single_right, mul_comm]

private theorem norm_single (a : ℝ) (ha : |a| = 1) :
    ‖EuclideanSpace.single (0 : Fin 2) a‖ = 1 := by
  simp [ha]

/-- In `ℝ²`, the half-plane `{x | x₀ < c}` has Gaussian perimeter `φ(c)`. -/
theorem gaussianPerimeter_setOf_lt (c : ℝ) :
    gaussianPerimeter {x : EuclideanSpace ℝ (Fin 2) | x 0 < c} =
      ENNReal.ofReal (gaussianPDFReal 0 1 c) := by
  rw [← gaussianPerimeter_setOf_inner_lt (norm_single 1 (by simp)) c]
  simp [inner_single]

/-- In `ℝ²`, the half-plane `{x | c < x₀}` has Gaussian perimeter `φ(c)`. -/
theorem gaussianPerimeter_setOf_gt (c : ℝ) :
    gaussianPerimeter {x : EuclideanSpace ℝ (Fin 2) | c < x 0} =
      ENNReal.ofReal (gaussianPDFReal 0 1 c) := by
  rw [← gaussianPDFReal_zero_neg, ← gaussianPerimeter_setOf_inner_lt (norm_single (-1) (by simp))]
  congr 1
  ext x
  simp [inner_single]

/-- The half-plane `{x | 1 < x₀}` has Gaussian perimeter `φ(1)`. -/
example : gaussianPerimeter {x : EuclideanSpace ℝ (Fin 2) | 1 < x 0} =
    ENNReal.ofReal (gaussianPDFReal 0 1 1) :=
  gaussianPerimeter_setOf_gt 1

/-- `φ(1) < φ(0)`. -/
theorem gaussianPDFReal_one_lt_gaussianPDFReal_zero :
    gaussianPDFReal 0 1 1 < gaussianPDFReal 0 1 0 := by
  rw [gaussianPDFReal_zero_one, gaussianPDFReal_zero_one]
  gcongr
  norm_num

/-- **Gaussian perimeter is not translation invariant.** For a unit vector `ν`, translating
`{x | ⟪x, ν⟫ < 0}` by `ν` gives `{x | ⟪x, ν⟫ < 1}`, whose Gaussian perimeter `φ(1)` is smaller
than `φ(0)`. -/
theorem gaussianPerimeter_setOf_inner_lt_one_lt_gaussianPerimeter_setOf_inner_lt_zero {ν : E}
    (hν : ‖ν‖ = 1) :
    gaussianPerimeter {x : E | ⟪x, ν⟫ < 1} < gaussianPerimeter {x : E | ⟪x, ν⟫ < 0} := by
  rw [gaussianPerimeter_setOf_inner_lt hν, gaussianPerimeter_setOf_inner_lt hν]
  exact (ENNReal.ofReal_lt_ofReal_iff (gaussianPDFReal_pos _ _ _ one_ne_zero)).2
    gaussianPDFReal_one_lt_gaussianPDFReal_zero

/-- For a unit vector `ν`, the half-spaces `U_k = {x | ⟪x, ν⟫ < k}` have Gaussian perimeters
`φ(k) → 0`. -/
theorem tendsto_gaussianPerimeter_setOf_inner_lt {ν : E} (hν : ‖ν‖ = 1) :
    Tendsto (fun k : ℕ => gaussianPerimeter {x : E | ⟪x, ν⟫ < k}) atTop (𝓝 0) := by
  have hφ := (tendsto_gaussianPDFReal_cocompact 0 1).mono_left atTop_le_cocompact
  simp_rw [gaussianPerimeter_setOf_inner_lt hν]
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal (hφ.comp tendsto_natCast_atTop_atTop)

/-- For a unit vector `ν`, the half-spaces `U_k = {x | ⟪x, ν⟫ < k}` converge to `E` in `L¹(γ)`:
the Gaussian measure of the complement `{x | k ≤ ⟪x, ν⟫}` is `1 - Φ(k) → 0`. -/
theorem tendsto_measureReal_stdGaussian_compl_setOf_inner_lt {ν : E} (hν : ‖ν‖ = 1) :
    Tendsto (fun k : ℕ => (stdGaussian E).real {x | ⟪x, ν⟫ < k}ᶜ) atTop (𝓝 0) := by
  have h (k : ℕ) : (stdGaussian E).real {x | ⟪x, ν⟫ < k}ᶜ = 1 - cdf (gaussianReal 0 1) k := by
    rw [measureReal_compl (measurableSet_lt (by fun_prop) measurable_const), probReal_univ,
      measureReal_stdGaussian_setOf_inner_lt hν]
  simp_rw [h]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_cdf_atTop (gaussianReal 0 1)).comp tendsto_natCast_atTop_atTop)

/-- The limit `E` of the half-spaces `U_k` has Gaussian perimeter `0`. -/
example : gaussianPerimeter (univ : Set E) = 0 :=
  gaussianPerimeter_univ

end TauCeti.Examples.GaussianHalfSpace
