/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
public import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Examples.Analysis.BoundedVariation.Gaussian.HalfSpace
import TauCeti.Examples.Probability.Distributions.Gaussian.Tails

/-!
# Checks: Gaussian cylinders

For a subspace `F` of `E` and `U ⊆ F`, the cylinder `U ⊕ Fᗮ` is the preimage of `U` under the
orthogonal projection onto `F`; its standard Gaussian measure is `γ_F(U)`
(`Submodule.stdGaussian_preimage_orthogonalProjectionOnto`). These are the Checks of the cylinder
statement `γ_E(U ⊕ Fᗮ) = γ_F(U)`, `P_{γ_E}(U ⊕ Fᗮ) = P_{γ_F}(U)`, with both sides computed.

* For a unit vector `ν` and `F = ℝ ν`, the cylinder over the half-line `{y ∈ F | ⟪y, ν⟫ < s}` is
  the half-space `{x | ⟪x, ν⟫ < s}`. Both sets have Gaussian measure `Φ(s)` and Gaussian
  perimeter `φ(s)`. In `ℝ²` with `ν = e₀` the cylinder is `{x | x₀ < s}`.
* For `F = {0}`, a subset `U` of `F` is `∅` or `F`, the cylinder is `∅` or `E`, and both
  perimeters vanish.
* Gaussian perimeter is not translation invariant: translating `{x | x₀ < 0}` in `ℝ²` by `e₀`
  gives `{x | x₀ < 1}`, and the perimeter changes from `φ(0) ≈ 0.398942` to `φ(1) ≈ 0.241971`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set TauCeti TauCeti.Probability
open scoped ENNReal RealInnerProductSpace Pointwise

namespace TauCeti.Examples.GaussianCylinder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector `ν`, as an element of the line `ℝ ν`. -/
def lineVec (ν : E) : (ℝ ∙ ν) :=
  ⟨ν, Submodule.mem_span_singleton_self ν⟩

/-- `lineVec ν` is `ν`. -/
@[simp]
theorem coe_lineVec (ν : E) : (lineVec ν : E) = ν :=
  (rfl)

/-- `lineVec ν` has the norm of `ν`. -/
theorem norm_lineVec (ν : E) : ‖lineVec ν‖ = ‖ν‖ := by
  rw [← Submodule.norm_coe, coe_lineVec]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The cylinder over a half-line and the half-line have the same Gaussian measure `Φ(s)`. -/
example {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) :
    (stdGaussian E).real {x : E | ⟪x, ν⟫ < s} = cdf (gaussianReal 0 1) s ∧
      (stdGaussian (ℝ ∙ ν)).real {y | ⟪y, lineVec ν⟫ < s} = cdf (gaussianReal 0 1) s := by
  refine ⟨measureReal_stdGaussian_setOf_inner_lt hν s, ?_⟩
  rw [measureReal_def, ← Submodule.stdGaussian_preimage_orthogonalProjectionOnto,
    Submodule.preimage_orthogonalProjectionOnto_setOf_inner _ _ (· < s), coe_lineVec,
    ← measureReal_def, measureReal_stdGaussian_setOf_inner_lt hν s]

/-- The cylinder over a half-line and the half-line have the same Gaussian perimeter `φ(s)`. -/
example {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) :
    gaussianPerimeter ((ℝ ∙ ν).orthogonalProjectionOnto ⁻¹' {y | ⟪y, lineVec ν⟫ < s}) =
        ENNReal.ofReal (gaussianPDFReal 0 1 s) ∧
      gaussianPerimeter {y : (ℝ ∙ ν) | ⟪y, lineVec ν⟫ < s} =
        ENNReal.ofReal (gaussianPDFReal 0 1 s) := by
  rw [Submodule.preimage_orthogonalProjectionOnto_setOf_inner _ _ (· < s), coe_lineVec]
  exact ⟨gaussianPerimeter_setOf_inner_lt hν s,
    gaussianPerimeter_setOf_inner_lt ((norm_lineVec ν).trans hν) s⟩

/-- In `ℝ²`, over the first coordinate axis `F = ℝ e₀`, the cylinder over `(-∞, s)` is
`{x | x₀ < s}`, of Gaussian perimeter `φ(s)`. -/
example (s : ℝ) :
    (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℝ)).orthogonalProjectionOnto ⁻¹'
        {y | ⟪y, lineVec (EuclideanSpace.single 0 1)⟫ < s} = {x | x 0 < s} ∧
      gaussianPerimeter {x : EuclideanSpace ℝ (Fin 2) | x 0 < s} =
        ENNReal.ofReal (gaussianPDFReal 0 1 s) := by
  have hset : {x : EuclideanSpace ℝ (Fin 2) | ⟪x, EuclideanSpace.single 0 1⟫ < s} =
      {x | x 0 < s} := by
    ext x
    simp [EuclideanSpace.inner_single_right]
  rw [Submodule.preimage_orthogonalProjectionOnto_setOf_inner _ _ (· < s), coe_lineVec, hset]
  exact ⟨rfl, GaussianHalfSpace.gaussianPerimeter_setOf_lt s⟩

/-- Over `F = {0}`, every subset of `F` is `∅` or `F`, its cylinder is `∅` or `E`, and the two
Gaussian perimeters vanish. -/
example (U : Set (⊥ : Submodule ℝ E)) :
    ((U = ∅ ∧ (⊥ : Submodule ℝ E).orthogonalProjectionOnto ⁻¹' U = ∅) ∨
      (U = univ ∧ (⊥ : Submodule ℝ E).orthogonalProjectionOnto ⁻¹' U = univ)) ∧
      gaussianPerimeter ((⊥ : Submodule ℝ E).orthogonalProjectionOnto ⁻¹' U) = 0 ∧
      gaussianPerimeter U = 0 := by
  rcases (subsingleton_of_subsingleton (s := U)).eq_empty_or_singleton with rfl | ⟨u, rfl⟩
  · rw [preimage_empty]
    exact ⟨Or.inl ⟨rfl, rfl⟩, gaussianPerimeter_empty, gaussianPerimeter_empty⟩
  · have hU : ({u} : Set (⊥ : Submodule ℝ E)) = univ := by
      ext v
      simp [Subsingleton.elim v u]
    rw [hU, preimage_univ]
    exact ⟨Or.inr ⟨rfl, rfl⟩, gaussianPerimeter_univ, gaussianPerimeter_univ⟩

/-- Translating `{x | x₀ < 0}` in `ℝ²` by `e₀` gives `{x | x₀ < 1}`. -/
theorem vadd_setOf_lt_zero :
    EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +ᵥ {x : EuclideanSpace ℝ (Fin 2) | x 0 < 0} =
      {x | x 0 < 1} := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  simp [add_comm]

/-- Gaussian perimeter is not translation invariant: `{x | x₀ < 0}` in `ℝ²` has perimeter
`φ(0) ≈ 0.398942`, and its translate by `e₀` has perimeter `φ(1) ≈ 0.241971`, both to within
`5 · 10⁻⁷`. -/
example :
    |(gaussianPerimeter {x : EuclideanSpace ℝ (Fin 2) | x 0 < 0}).toReal - 0.398942| < 5e-7 ∧
      |(gaussianPerimeter (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +ᵥ
          {x : EuclideanSpace ℝ (Fin 2) | x 0 < 0})).toReal - 0.241971| < 5e-7 := by
  rw [vadd_setOf_lt_zero, GaussianHalfSpace.gaussianPerimeter_setOf_lt,
    GaussianHalfSpace.gaussianPerimeter_setOf_lt,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  exact ⟨GaussianTails.abs_gaussianPDFReal_zero_sub_lt,
    GaussianTails.abs_gaussianPDFReal_one_sub_lt⟩

end TauCeti.Examples.GaussianCylinder
