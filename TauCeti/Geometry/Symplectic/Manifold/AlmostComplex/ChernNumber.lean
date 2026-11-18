/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
public import TauCeti.Topology.VectorBundle.Complex.Clutching
import TauCeti.Geometry.Symplectic.Cayley.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.FiniteDimensional

/-!
# The first Chern number of a symplectic manifold on spheres

Let `σ` be a fibrewise nondegenerate smooth two-form on a manifold `M`, for instance a symplectic
form. An almost complex structure `J` tamed by `σ` makes the tangent bundle a complex vector bundle
`(TM, J)` (`TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`), and the
clutching number of this bundle on spheres (`TauCeti.clutchingNumberHom`) is the clutching
description of its first Chern number `c₁(TM, J) : π₂(M, x) → ℤ`; no comparison with a
cohomological first Chern class is made here. This file shows that it depends only on `σ`.

For two structures `J₀` and `J₁` tamed by `σ`, the endomorphism `1 - J₁ J₀` of each tangent space
is invertible (`TauCeti.SmoothTwoForm.Tames.isUnit_one_sub_toEndomorphism_mul`, from the linear
statement `TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul`), and it intertwines `J₀` with `J₁`.
So it is an isomorphism of complex vector bundles `(TM, J₀) ≅ (TM, J₁)`
(`TauCeti.Bundle.ContinuousComplexStructure.oneSubMulEquiv`), and the two bundles have the same
clutching numbers (`TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`). No path between `J₀` and
`J₁` is needed.

On a Hausdorff σ-compact manifold every such `σ` has a compatible almost complex structure
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`), so the first Chern number of `σ`
on spheres, `TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom`, is the clutching number of
`(TM, J)` for a chosen compatible `J`. By the invariance above it is the clutching number of
`(TM, J)` for every tame `J`, with any complex model fibre
(`TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom_eq_clutchingNumberHom`). For a symplectic
manifold this is the first Chern number on spheres that, with the symplectic area, defines the
period group and the grading of capped Hamiltonian Floer theory.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom`: the first Chern number of `σ` on
  `π₂(M, x)`.

## Main results

* `TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`: the complex tangent bundles of two
  structures tamed by `σ` have the same clutching numbers.
* `TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom_eq_clutchingNumberHom`: the first Chern
  number of `σ` is the clutching number of `(TM, J)` for any `σ`-tame `J`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Chapter 4 (almost complex structures, and the first Chern class of a symplectic manifold, which
  does not depend on the tame almost complex structure).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {J₀ J₁ : SmoothAlmostComplexStructure I M}

/-- For two smooth almost complex structures tamed by `σ`, the endomorphism `1 - J₁ J₀` of every
tangent space is invertible. -/
theorem Tames.isUnit_one_sub_toEndomorphism_mul (h₀ : σ.Tames J₀) (h₁ : σ.Tames J₁) (x : M) :
    IsUnit (1 - J₁.toEndomorphism x * J₀.toEndomorphism x) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hσ := h₀.isNondegenerate
  have h := ((hσ.tames_iff.1 h₁) x).isUnit_one_sub_mul ((hσ.tames_iff.1 h₀) x)
  refine ContinuousLinearMap.isUnit_of_isUnit_toLinearMap_of_finiteDimensional ?_
  simpa using h

variable (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [Fact (finrank ℝ E = 2 * finrank ℂ G')]

/-- **The first Chern number does not depend on the tame almost complex structure.** For two smooth
almost complex structures `J₀` and `J₁` tamed by `σ`, the complex tangent bundles `(TM, J₀)` and
`(TM, J₁)`, with any complex model fibres `G` and `G'`, have the same clutching numbers on
`π₂(M, x)`. -/
theorem Tames.clutchingNumberHom_eq (h₀ : σ.Tames J₀) (h₁ : σ.Tames J₁) (n₀ n₁ : ℕ∞) (x : M) :
    clutchingNumberHom G' (J₁.toContMDiff n₁).toContinuousComplexStructure.Fiber x =
      clutchingNumberHom G (J₀.toContMDiff n₀).toContinuousComplexStructure.Fiber x := by
  -- The complex structure of `(TM, J)` on each tangent space is the endomorphism of `J`.
  have hJ (J : SmoothAlmostComplexStructure I M) (n : ℕ∞) (b : M) :
      (J.toContMDiff n).toContinuousComplexStructure b = J.toEndomorphism b :=
    ContinuousLinearMap.ext fun v ↦
      (ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply _ b v).trans
        (J.toContMDiff_apply n b v)
  refine Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_isUnit G G' (fun b ↦ ?_) x
  rw [hJ, hJ]
  exact h₀.isUnit_one_sub_toEndomorphism_mul h₁ b

variable [T2Space M] [SigmaCompactSpace M]

namespace IsNondegenerate

/-- The model fibre `ℂ^(dim M / 2)` of the complex tangent bundles of `M` has half the real
dimension of `M`, since the dimension of `M` is even. -/
private theorem fact_finrank (h : σ.IsNondegenerate) (x : M) :
    Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have heven : Even (finrank ℝ E) :=
    (h.exists_compatible.choose.almostComplexStructureAt x).even_finrank_real
  rw [finrank_euclideanSpace_fin]
  exact ⟨(Nat.two_mul_div_two_of_even heven).symm⟩

/-- The **first Chern number** `c₁ : π₂(M, x) → ℤ` of a fibrewise nondegenerate smooth two-form `σ`,
for instance a symplectic form: the clutching number of the complex tangent bundle `(TM, J)` for an
almost complex structure `J` tamed by `σ`. It does not depend on `J`
(`TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom_eq_clutchingNumberHom`); the definition
uses a chosen compatible `J` and the model fibre `ℂ^(dim M / 2)`. -/
def chernNumberHom (h : σ.IsNondegenerate) (x : M) : Additive (π_ 2 M x) →+ ℤ :=
  haveI := h.fact_finrank x
  clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))
    (h.exists_compatible.choose.toContMDiff 0).toContinuousComplexStructure.Fiber x

/-- The first Chern number of `σ` is the clutching number of the complex tangent bundle `(TM, J)`
for any almost complex structure `J` tamed by `σ`, with any complex model fibre `G`. -/
theorem chernNumberHom_eq_clutchingNumberHom (h : σ.IsNondegenerate)
    {J : SmoothAlmostComplexStructure I M} (hJ : σ.Tames J) (n : ℕ∞) (x : M) :
    h.chernNumberHom x =
      clutchingNumberHom G (J.toContMDiff n).toContinuousComplexStructure.Fiber x := by
  have := h.fact_finrank x
  rw [chernNumberHom]
  exact Tames.clutchingNumberHom_eq G (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) hJ
    h.exists_compatible.choose_spec.tames n 0 x

end IsNondegenerate

end TauCeti.SmoothTwoForm
