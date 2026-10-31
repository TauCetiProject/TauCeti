/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart

import TauCeti.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Regular points and regular values of maps between manifolds

A point `x` is a *regular point* of a map `f : M → N` between manifolds when the manifold
derivative `mfderiv I J f x` is surjective, and `y : N` is a *regular value* of `f` when every
point of the fibre `f ⁻¹' {y}` is a regular point. A value outside the range of `f` is regular.
These are the points and values at which a mapping degree is counted. Sard's theorem
(`TauCeti.dense_isRegularValue`) says that the regular values of a differentiable map from a
Lindelöf real manifold to a real manifold, both modelled on finite-dimensional spaces of the same
dimension and of class at least `C¹`, are dense.

Read in the extended charts at arbitrary points `x₀` and `y₀` whose sources contain `x` and
`f x`, the point `x` is regular exactly when the Fréchet derivative of the coordinate expression
of `f` within `range I` is surjective. This is how flat statements about critical points transfer
to manifolds, including manifolds with boundary or corners.

## Main definitions

* `TauCeti.IsRegularPoint I J f x`: the manifold derivative of `f` at `x` is surjective.
* `TauCeti.IsRegularValue I J f y`: every point of the fibre of `f` over `y` is regular.

## Main results

* `TauCeti.isRegularValue_iff_notMem_image`: the regular values are the complement of the image
  of the set of non-regular points.
* `TauCeti.isRegularPoint_iff_surjective_fderivWithin`: regularity read in arbitrary charts.
* `TauCeti.isRegularPoint_iff_surjective_fderiv`: for maps between normed spaces, regularity is
  surjectivity of the Fréchet derivative.
* `TauCeti.isRegularPoint_iff_injective_mfderiv`: between models of the same finite dimension,
  regularity is injectivity of the manifold derivative.
* `TauCeti.IsRegularPoint.mdifferentiableAt`: a map into a normed space is differentiable at its
  regular points.
* `TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq`: a map into a level set `f ⁻¹' {y}`
  near a point has tangent images there in the kernel of the derivative of `f`.
* `TauCeti.IsRegularPoint.finrank_ker_mfderiv_add_finrank` and
  `TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`: at a regular point the kernel of the
  derivative has codimension the dimension of the target, and it is the tangent image of every
  immersion into the level from a manifold of that dimension.
* `TauCeti.IsRegularPoint.surjective_fderiv_comp_extChartAt_symm` and
  `TauCeti.IsRegularPoint.finrank_ker_fderiv_comp_extChartAt_symm`: on a boundaryless manifold, at
  a regular point of a map into a normed space the derivative in the preferred extended chart is
  surjective, with kernel of codimension one for scalar functions.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4 (regular points and values) and Theorem 6.10 (Sard).
-/

public section

open Function Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {x : M} {y : N}

variable (I J) in
/-- A point `x` is a regular point of `f` when the manifold derivative of `f` at `x` is
surjective. Where `f` is not differentiable its manifold derivative is `0`, so such a point is
regular only when the model of the target is the zero space. -/
def IsRegularPoint (f : M → N) (x : M) : Prop :=
  Surjective (mfderiv I J f x)

variable (I J) in
/-- A value `y` is a regular value of `f` when every point of the fibre of `f` over `y` is a
regular point. In particular every value outside the range of `f` is regular. -/
def IsRegularValue (f : M → N) (y : N) : Prop :=
  ∀ x, f x = y → IsRegularPoint I J f x

theorem isRegularPoint_iff : IsRegularPoint I J f x ↔ Surjective (mfderiv I J f x) :=
  Iff.rfl

theorem isRegularValue_iff : IsRegularValue I J f y ↔ ∀ x, f x = y → IsRegularPoint I J f x :=
  Iff.rfl

/-- A point of the fibre over a regular value is a regular point. -/
theorem IsRegularValue.isRegularPoint (hy : IsRegularValue I J f y) (hx : f x = y) :
    IsRegularPoint I J f x :=
  hy x hx

/-- A value is regular exactly when it is not the image of a non-regular point. -/
theorem isRegularValue_iff_notMem_image :
    IsRegularValue I J f y ↔ y ∉ f '' {x | ¬ IsRegularPoint I J f x} := by
  simp only [IsRegularValue, mem_image, mem_ofPred_eq, not_exists, not_and]
  exact forall_congr' fun x ↦ by tauto

/-- The set of regular values is the complement of the image of the non-regular points. -/
theorem setOf_isRegularValue_eq_compl_image :
    {y | IsRegularValue I J f y} = (f '' {x | ¬ IsRegularPoint I J f x})ᶜ :=
  ext fun _ ↦ isRegularValue_iff_notMem_image

/-- A value outside the range of `f` is a regular value. -/
theorem isRegularValue_of_notMem_range (hy : y ∉ range f) : IsRegularValue I J f y :=
  fun x hx ↦ (hy ⟨x, hx⟩).elim

/-- Read in the extended charts at `x₀` and `y₀`, whose sources contain `x` and `f x`, a point
`x` at which `f` is differentiable is regular exactly when the Fréchet derivative within
`range I` of the coordinate expression of `f` is surjective at the chart image of `x`. The charts
need not be centred at `x` and `f x`. -/
theorem isRegularPoint_iff_surjective_fderivWithin [IsManifold I 1 M] [IsManifold J 1 N]
    {x₀ : M} {y₀ : N} (hf : MDifferentiableAt I J f x) (hx : x ∈ (chartAt H x₀).source)
    (hfx : f x ∈ (chartAt H' y₀).source) :
    IsRegularPoint I J f x ↔ Surjective (fderivWithin 𝕜
      (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ x)) := by
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hfx' : f x ∈ (extChartAt J y₀).source := by rwa [extChartAt_source]
  have hmem : extChartAt I x₀ x ∈ range I :=
    extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hx')
  rw [(hf.hasMFDerivAt.hasFDerivWithinAt_of_mem_source hx hfx).fderivWithin
    (I.uniqueDiffOn _ hmem)]
  -- Both chart derivatives are invertible, so they do not affect surjectivity. The coercion of a
  -- composite of continuous linear maps is the composite of their coercions.
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_extChartAt (I := J) hfx'
  obtain ⟨B, hB⟩ := isInvertible_mfderivWithin_extChartAt_symm (I := I)
    ((extChartAt I x₀).map_source hx')
  rw [← hA, ← hB, isRegularPoint_iff]
  exact ((EquivLike.comp_surjective _ A).trans (EquivLike.surjective_comp B _)).symm

/-- For a scalar function, regularity is equivalent to a nonzero differential, read in the
scalar field using `mvfderiv`. No differentiability hypothesis is needed. -/
theorem isRegularPoint_iff_mvfderiv_ne_zero {g : M → 𝕜} :
    IsRegularPoint I 𝓘(𝕜) g x ↔ mvfderiv I g x ≠ 0 := by
  rw [isRegularPoint_iff]
  have h : Surjective (mvfderiv I g x) ↔ Surjective (mfderiv I 𝓘(𝕜) g x) := by
    simpa only [mvfderiv, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe] using
      EquivLike.comp_surjective (mfderiv I 𝓘(𝕜) g x) (NormedSpace.fromTangentSpace (g x))
  rw [← h]
  refine (LinearMap.surjective_iff_ne_zero (f := (mvfderiv I g x).toLinearMap)).trans ?_
  exact not_congr (ContinuousLinearMap.coe_inj (f := mvfderiv I g x) (g := 0))

/-- For a map between normed spaces, a regular point is a point at which the Fréchet derivative
is surjective. -/
theorem isRegularPoint_iff_surjective_fderiv {f : E → E'} {x : E} :
    IsRegularPoint 𝓘(𝕜, E) 𝓘(𝕜, E') f x ↔ Surjective (fderiv 𝕜 f x) := by
  -- `mfderiv_eq_fderiv` conjugates by the identifications of tangent spaces with `E` and `E'`.
  rw [isRegularPoint_iff, mfderiv_eq_fderiv]
  exact (EquivLike.comp_surjective _ (NormedSpace.fromTangentSpace (f x)).symm).trans
    (EquivLike.surjective_comp (NormedSpace.fromTangentSpace x) _)

/-- Between manifolds modelled on finite-dimensional spaces of the same dimension, a point is
regular exactly when the manifold derivative there is injective. -/
theorem isRegularPoint_iff_injective_mfderiv [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E') :
    IsRegularPoint I J f x ↔ Injective (mfderiv I J f x) :=
  -- `TangentSpace I x` is `E` and `TangentSpace J (f x)` is `E'` by definition, so `hdim` and
  -- the `FiniteDimensional` instances apply to the tangent spaces.
  isRegularPoint_iff.trans (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv I J f x : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x))) hdim).symm

/-- A regular point of a map into a normed space is a point of differentiability. Without
differentiability the derivative is `0`, so the target is the zero space and the map is constant. -/
theorem IsRegularPoint.mdifferentiableAt {g : M → E'} (h : IsRegularPoint I 𝓘(𝕜, E') g x) :
    MDifferentiableAt I 𝓘(𝕜, E') g x := by
  by_contra hg
  rw [isRegularPoint_iff, mfderiv_zero_of_not_mdifferentiableAt hg] at h
  have : Subsingleton E' := ⟨fun a b ↦ by
    obtain ⟨_, ha⟩ := h a
    obtain ⟨_, hb⟩ := h b
    exact ha.symm.trans hb⟩
  exact hg ((mdifferentiableAt_const (c := g x)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _))

section Level

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] {g : P → M}

/-- The tangent images at `p` of a map into a level set `f ⁻¹' {y}` near `p` lie in the kernel of
the derivative of `f`. No differentiability is needed: where `g` or `f` is not differentiable, the
tangent image is `0` or the kernel is everything. -/
theorem range_mfderiv_le_ker_mfderiv_of_eventually_eq {p : P} (hg : ∀ᶠ q in 𝓝 p, f (g q) = y) :
    (mfderiv K I g p).range ≤ (mfderiv I J f (g p)).ker := by
  by_cases hgp : MDifferentiableAt K I g p
  · by_cases hfp : MDifferentiableAt I J f (g p)
    · rintro _ ⟨v, rfl⟩
      have hfg : f ∘ g =ᶠ[𝓝 p] fun _ ↦ y := hg
      have := mfderiv_comp_apply p hfp hgp v
      rw [hfg.mfderiv_eq, mfderiv_const] at this
      exact this.symm
    · simp [mfderiv_zero_of_not_mdifferentiableAt hfp]
  · simp [mfderiv_zero_of_not_mdifferentiableAt hgp]

variable [FiniteDimensional 𝕜 E]

/-- **Dimension of the tangent space of a regular level.** At a regular point the kernel of the
derivative has codimension `dim N`. -/
theorem IsRegularPoint.finrank_ker_mfderiv_add_finrank (h : IsRegularPoint I J f x) :
    Module.finrank 𝕜 ((mfderiv I J f x).ker) + Module.finrank 𝕜 E' =
      Module.finrank 𝕜 E := by
  have := LinearMap.finrank_range_add_finrank_ker (mfderiv I J f x).toLinearMap
  rw [LinearMap.range_eq_top.2 h, finrank_top, finrank_tangentSpace, finrank_tangentSpace] at this
  rw [← this, add_comm]

/-- **The tangent space of a regular level.** Let `g : P → M` map into the level `f ⁻¹' {y}` near
`p`, with injective derivative at `p`, from a manifold of the dimension of the level. If `g p` is a
regular point of `f`, the tangent image of `g` at `p` is the kernel of the derivative of `f`. -/
theorem IsRegularPoint.range_mfderiv_eq_ker_mfderiv {p : P} (hg : ∀ᶠ q in 𝓝 p, f (g q) = y)
    (h : IsRegularPoint I J f (g p)) (hinj : Injective (mfderiv K I g p))
    (hdim : Module.finrank 𝕜 E'' + Module.finrank 𝕜 E' = Module.finrank 𝕜 E) :
    (mfderiv K I g p).range = (mfderiv I J f (g p)).ker := by
  refine Submodule.eq_of_le_of_finrank_eq (range_mfderiv_le_ker_mfderiv_of_eventually_eq hg) ?_
  rw [LinearMap.finrank_range_of_inj hinj, finrank_tangentSpace]
  have := h.finrank_ker_mfderiv_add_finrank
  omega

end Level

section Boundaryless

variable [I.Boundaryless]

/-- At a regular point of a map into a normed space on a boundaryless manifold, the coordinate
expression in the preferred extended chart has surjective derivative. -/
theorem IsRegularPoint.surjective_fderiv_comp_extChartAt_symm {g : M → E'}
    (h : IsRegularPoint I 𝓘(𝕜, E') g x) :
    Surjective (fderiv 𝕜 (g ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
  by_cases hg : MDifferentiableAt I 𝓘(𝕜, E') g x
  · have h' : Surjective (mvfderiv I g x) := (NormedSpace.fromTangentSpace (g x)).surjective.comp
      (isRegularPoint_iff.1 h)
    rwa [hg.mvfderiv_eq_fderiv_comp_extChartAt_symm] at h'
  · -- Without differentiability the manifold derivative is `0`, so `E'` is the zero space.
    rw [isRegularPoint_iff, mfderiv_zero_of_not_mdifferentiableAt hg] at h
    intro v
    obtain ⟨u, hu⟩ := h v
    exact ⟨0, by rw [map_zero]; exact hu⟩

/-- At a regular point of a scalar function on a boundaryless manifold, the kernel of the
preferred-chart derivative has codimension one. -/
theorem IsRegularPoint.finrank_ker_fderiv_comp_extChartAt_symm [FiniteDimensional 𝕜 E]
    {g : M → 𝕜} (h : IsRegularPoint I 𝓘(𝕜) g x) :
    Module.finrank 𝕜 (fderiv 𝕜 (g ∘ (extChartAt I x).symm) (extChartAt I x x)).ker =
      Module.finrank 𝕜 E - 1 := by
  have hne : (fderiv 𝕜 (g ∘ (extChartAt I x).symm) (extChartAt I x x) : E →ₗ[𝕜] 𝕜) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := h.surjective_fderiv_comp_extChartAt_symm 1
    have hv' := LinearMap.congr_fun h0 v
    rw [ContinuousLinearMap.coe_coe, hv, LinearMap.zero_apply] at hv'
    exact one_ne_zero hv'
  have := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  omega

end Boundaryless

end TauCeti
