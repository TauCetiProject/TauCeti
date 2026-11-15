/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Countable rectifiability of finite-dimensional spaces, subspaces, and linear fibres

Every subset of a finite-dimensional real normed space `E` is countably `(dim E)`-rectifiable,
since any linear isomorphism with `EuclideanSpace ℝ (Fin (dim E))` is Lipschitz. Pushing this
forward along isometric inclusions and translations shows that finite-dimensional linear subspaces,
finite-dimensional affine subspaces of normed torsors, and fibres of linear maps with
finite-dimensional kernel are countably rectifiable of their intrinsic dimension.

For a linear map `L : E →ₗ[ℝ] F` between finite-dimensional real spaces, every fibre is countably
`(dim E - dim F)`-rectifiable when `L` is surjective, and almost every fibre is empty when `L` is
not surjective. Hence almost every fibre of any linear map is countably
`(dim E - dim F)`-rectifiable for any additive Haar measure on the codomain.

## Main statements

* `TauCeti.CountablyRectifiable.of_finiteDimensional`: every subset of a finite-dimensional real
  normed space `E` is countably `(dim E)`-rectifiable.
* `Submodule.countablyRectifiable`: a finite-dimensional real submodule is countably rectifiable of
  its dimension, without assuming the ambient normed space is finite-dimensional.
* `AffineSubspace.countablyRectifiable`: an affine subspace with finite-dimensional direction in a
  real normed torsor is countably rectifiable of its direction's dimension.
* `LinearMap.countablyRectifiable_preimage_singleton`: every fibre of a real linear map with
  finite-dimensional kernel is countably rectifiable of the kernel's dimension.
* `LinearMap.countablyRectifiable_preimage_singleton_of_surjective`: every fibre of a surjective
  linear map from a finite-dimensional real normed space is countably `(dim E - dim F)`-rectifiable.
* `LinearMap.ae_countablyRectifiable_preimage_singleton`: almost every fibre of any linear map
  between finite-dimensional real normed spaces is countably `(dim E - dim F)`-rectifiable.

## References

* H. Federer, *Geometric Measure Theory*, §3.2 (rectifiable sets and linear slicing).
* L. Simon, *Lectures on Geometric Measure Theory*, §11 (countably rectifiable sets).
-/

public section

open Filter Function MeasureTheory Module Set
open scoped NNReal

namespace TauCeti

namespace CountablyRectifiable

/-- Every subset of a finite-dimensional real normed space `E` is countably
`(dim E)`-rectifiable, via a continuous linear equivalence with Euclidean space. -/
theorem of_finiteDimensional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (s : Set E) :
    CountablyRectifiable (finrank ℝ E) s := by
  let e : EuclideanSpace ℝ (Fin (finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ))
  have hs : e '' (e.symm '' s) = s := ContinuousLinearEquiv.image_symm_image e s
  rw [← hs]
  exact (CountablyRectifiable.euclidean (e.symm '' s)).image
    e.toContinuousLinearMap.lipschitzWith.lipschitzOnWith

end CountablyRectifiable

end TauCeti

open TauCeti

/-- A finite-dimensional submodule of a real normed space is countably rectifiable of its
dimension. The ambient space need not be finite-dimensional. -/
theorem Submodule.countablyRectifiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (p : Submodule ℝ E) [FiniteDimensional ℝ p] :
    CountablyRectifiable (finrank ℝ p) (p : Set E) := by
  have h : (p : Set E) = Subtype.val '' (univ : Set p) := by simp
  rw [h, CountablyRectifiable.isometry_image_iff isometry_subtype_coe]
  exact .of_finiteDimensional univ

/-- An affine subspace with finite-dimensional direction in a normed torsor over a real normed
space is countably rectifiable of its direction's dimension. Neither nonemptiness of the affine
subspace nor finite dimensionality of the ambient space is needed. -/
theorem AffineSubspace.countablyRectifiable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]
    (s : AffineSubspace ℝ P) [FiniteDimensional ℝ s.direction] :
    CountablyRectifiable (finrank ℝ s.direction) (s : Set P) := by
  rcases (s : Set P).eq_empty_or_nonempty with hs | ⟨q, hq⟩
  · simpa only [hs] using CountablyRectifiable.empty
  let e : EuclideanSpace ℝ (Fin (finrank ℝ s.direction)) ≃L[ℝ] s.direction :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ))
  let φ : EuclideanSpace ℝ (Fin (finrank ℝ s.direction)) → P := fun u ↦ (e u : V) +ᵥ q
  have hlip : LipschitzWith ‖e.toContinuousLinearMap‖₊ φ := by
    have hvadd : LipschitzWith 1 (fun w : s.direction ↦ (w : V) +ᵥ q) :=
      ((IsometryEquiv.vaddConst q).isometry.comp isometry_subtype_coe).lipschitzWith
    simpa only [one_mul, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      IsometryEquiv.vaddConst_apply, φ] using hvadd.comp e.toContinuousLinearMap.lipschitzWith
  have hφ : φ '' univ = (s : Set P) := by
    ext p
    simp only [image_univ, mem_range, φ, SetLike.mem_coe]
    refine ⟨?_, fun hp ↦ ?_⟩
    · rintro ⟨u, rfl⟩
      exact AffineSubspace.vadd_mem_of_mem_direction (e u).2 hq
    · refine ⟨e.symm ⟨p -ᵥ q, AffineSubspace.vsub_mem_direction hp hq⟩, ?_⟩
      simp
  rw [← hφ]
  exact CountablyRectifiable.of_lipschitzOnWith hlip.lipschitzOnWith

namespace LinearMap

/-- Every fibre of a real linear map with finite-dimensional kernel is countably rectifiable of
the dimension of its kernel. Neither finite dimensionality of the domain nor any topological
structure on the codomain is needed. -/
theorem countablyRectifiable_preimage_singleton {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) [FiniteDimensional ℝ (ker L)] (y : F) :
    CountablyRectifiable (finrank ℝ (ker L)) (L ⁻¹' {y}) := by
  rcases (L ⁻¹' {y}).eq_empty_or_nonempty with hy | ⟨x₀, hx₀⟩
  · simpa only [hy] using CountablyRectifiable.empty
  have hfib : L ⁻¹' {y} = (x₀ + ·) '' (ker L : Set E) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_image, SetLike.mem_coe, mem_ker]
    refine ⟨fun hx ↦ ⟨x - x₀, ?_, add_sub_cancel x₀ x⟩, ?_⟩
    · rw [map_sub, hx, hx₀, sub_self]
    · rintro ⟨z, hz, rfl⟩
      rw [map_add, hz, add_zero]
      exact hx₀
  rw [hfib, CountablyRectifiable.isometry_image_iff (isometry_add_left x₀)]
  exact (ker L).countablyRectifiable

/-- Every fibre of a surjective linear map from a finite-dimensional real normed space is countably
`(dim E - dim F)`-rectifiable. -/
theorem countablyRectifiable_preimage_singleton_of_surjective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (hL : Surjective L) (y : F) :
    CountablyRectifiable (finrank ℝ E - finrank ℝ F) (L ⁻¹' {y}) := by
  have hdim : finrank ℝ E - finrank ℝ F = finrank ℝ (ker L) := by
    have hrk := L.finrank_range_add_finrank_ker
    rw [range_eq_top.2 hL, finrank_top] at hrk
    omega
  rw [hdim]
  exact L.countablyRectifiable_preimage_singleton y

/-- Almost every fibre of any linear map between finite-dimensional real normed spaces is
countably `(dim E - dim F)`-rectifiable, for any additive Haar measure on the codomain: when the
map is not surjective, almost every fibre is empty. -/
theorem ae_countablyRectifiable_preimage_singleton {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] F) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (L ⁻¹' {y}) := by
  by_cases hL : Surjective L
  · exact Eventually.of_forall (L.countablyRectifiable_preimage_singleton_of_surjective hL)
  · filter_upwards [L.ae_preimage_singleton_eq_empty μ hL] with y hy
    simpa only [hy] using CountablyRectifiable.empty

end LinearMap

end
