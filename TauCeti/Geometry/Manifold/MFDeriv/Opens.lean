/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Tangent images on open submanifolds

Restriction to an open source preserves the tangent image at each point. Inclusion of an open
target maps the tangent image by the canonical tangent-space equivalence. These identities let
pointwise conditions on tangent images be checked in open submanifolds. Since the differential of
the inclusion of an open subset is the identity of the model space, restricting a map to an open
source, or following a map into an open target by the inclusion, does not change its differential
applied to a tangent vector. Differentiability itself is local, so a map and its restriction to
an open source have vanishing differentials at the same points, with no differentiability
assumption. The same holds for the differential `mvfderiv` of a vector-valued function
(`TauCeti.Manifold.mvfderiv_comp_subtype_val`), and the differential of a `C¹` map on an open
subset of a normed space depends continuously on the point
(`TauCeti.Manifold.continuous_mfderiv_of_contMDiff_opens`). Likewise the restriction
`f⁻¹(U) → U` of a map to the preimage of an open subset has the differential of the map
(`TauCeti.Manifold.mfderiv_restrictPreimage_apply`), and so the same tangent image
(`TauCeti.Manifold.mem_range_mfderiv_restrictPreimage_iff`).

A map read in the coordinate of a chart of the maximal atlas, `x ↦ g (e x)`, is differentiable on
every open subset of the chart's source where `g` is differentiable at the chart image
(`TauCeti.Manifold.mdifferentiable_restrict_comp_chart`).
-/

public section

open TopologicalSpace
open scoped Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Restricting a map to an open source preserves its tangent image. No differentiability is
assumed: where the map is not differentiable, neither is its restriction. -/
theorem range_mfderiv_comp_subtype_val {U : Opens N} {f : N → M} (x : U) :
    LinearMap.range (mfderiv J I (f ∘ (Subtype.val : U → N)) x).toLinearMap =
      LinearMap.range (mfderiv J I f (x : N)).toLinearMap := by
  ext w
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  exact exists_congr fun v ↦ by rw [mfderiv_comp_subtype_val_apply]

/-- Inclusion of an open target transports the tangent image by the canonical tangent-space
equivalence. No differentiability is assumed: where the map is not differentiable, neither is
its composition with the inclusion. -/
theorem range_mfderiv_subtype_val_comp {U : Opens M} {f : N → U} (x : N) :
    LinearMap.range (mfderiv J I ((Subtype.val : U → M) ∘ f) x).toLinearMap =
      (LinearMap.range (mfderiv J I f x).toLinearMap).map
        (tangentSpaceOpenEquiv (I := I) (f x)).toLinearEquiv.toLinearMap := by
  ext w
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨mfderiv J I f x v, ⟨v, rfl⟩, by
      rw [mfderiv_subtype_val_comp_apply]; exact tangentSpaceOpenEquiv_apply _ _⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, by rw [mfderiv_subtype_val_comp_apply]; exact (tangentSpaceOpenEquiv_apply _ _).symm⟩

/-- The differential of a map vanishes at a point of an open subset exactly when the differential
of its restriction to that subset does. No differentiability is assumed: where the map is not
differentiable, neither is its restriction, and both differentials are zero by convention. -/
@[simp]
theorem mfderiv_comp_subtype_val_eq_zero_iff {U : Opens N} {f : N → M} {x : U} :
    mfderiv J I (f ∘ (Subtype.val : U → N)) x = 0 ↔ mfderiv J I f (x : N) = 0 := by
  simp only [ContinuousLinearMap.ext_iff, zero_apply, mfderiv_comp_subtype_val_apply]
  -- The tangent spaces at `x` in `U` and at `(x : N)` in `N` are both the model space `E'`.
  exact Iff.rfl

/-- Restricting a vector-valued function to an open source does not change its differential. No
differentiability is assumed: where the function is not differentiable, neither is its
restriction. -/
theorem mvfderiv_comp_subtype_val {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {U : Opens N} (f : N → F) (x : U) :
    mvfderiv J (f ∘ (Subtype.val : U → N)) x = mvfderiv J f (x : N) := by
  ext v
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp_subtype_val_apply]
  -- The tangent spaces at `x` in `U` and at `(x : N)` in `N` are both the model space `E'`, and
  -- `fromTangentSpace` is the identity of it at either base point.
  rfl

/-- The differential of a `C¹` map `a` on an open subset `U` of a normed space depends
continuously on the point of `U`, as a continuous linear map `E →L[𝕜] F`. -/
theorem continuous_mfderiv_of_contMDiff_opens {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {U : Opens E} {a : U → F} {n : WithTop ℕ∞}
    (ha : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n a) (hn : n ≠ 0) :
    Continuous (Y := E →L[𝕜] F) fun x : U ↦ mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) a x := by
  -- Extend `a` from `U` to `E`, where its differential is a Fréchet derivative.
  let ã : E → F := Function.extend Subtype.val a 0
  have hãa : (fun x : U ↦ ã x) = a := funext (Subtype.val_injective.extend_apply a 0)
  have hda (x : U) : (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) a x : E →L[𝕜] F) = fderiv 𝕜 ã x := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [← hãa]
    exact (mfderiv_comp_subtype_val_apply (f := ã) w).trans
      (DFunLike.congr_fun mfderiv_eq_fderiv w)
  simp only [hda]
  exact continuous_iff_continuousAt.2 fun x ↦ ContinuousAt.comp (g := fderiv 𝕜 ã)
    ((contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1 (hãa ▸ ha x))).continuousAt_fderiv
      hn) continuous_subtypeVal.continuousAt

/-- Restricting a map `f : N → M` to the preimage `f⁻¹(U) → U` of an open subset `U` does not
change its differential. No differentiability is assumed. -/
theorem mfderiv_restrictPreimage_apply {f : N → M} (hf : Continuous f) (U : Opens M)
    {x : (⟨f ⁻¹' U, U.isOpen.preimage hf⟩ : Opens N)} (v : TangentSpace J x) :
    mfderiv (M := (⟨f ⁻¹' U, U.isOpen.preimage hf⟩ : Opens N)) (M' := U) J I
      ((U : Set M).restrictPreimage f) x v = mfderiv J I f x v :=
  mfderiv_apply_of_subtype_val_comp_eq (A := f) rfl v

/-- The restriction `f⁻¹(U) → U` of a map `f` to the preimage of an open subset `U` has injective
differential at a point exactly when `f` does. -/
theorem injective_mfderiv_restrictPreimage_iff {f : N → M} (hf : Continuous f) (U : Opens M)
    {x : (⟨f ⁻¹' U, U.isOpen.preimage hf⟩ : Opens N)} :
    Function.Injective (mfderiv (M := (⟨f ⁻¹' U, U.isOpen.preimage hf⟩ : Opens N)) (M' := U) J I
      ((U : Set M).restrictPreimage f) x) ↔ Function.Injective (mfderiv J I f x) := by
  simp only [Function.Injective, mfderiv_restrictPreimage_apply hf U]
  -- The tangent spaces at `x` in `f⁻¹(U)` and at `(x : N)` in `N` are both the model space `E'`.
  exact Iff.rfl

/-- The restriction `f⁻¹(U) → U` of a map `f` to the preimage of an open subset `U` has the same
tangent image at a point as `f`. -/
theorem mem_range_mfderiv_restrictPreimage_iff {f : N → M} (hf : Continuous f) (U : Opens M)
    {x : (⟨f ⁻¹' U, U.isOpen.preimage hf⟩ : Opens N)} {v : TangentSpace I (f x)} :
    v ∈ (mfderiv (M := (⟨f ⁻¹' U, U.isOpen.preimage hf⟩ : Opens N)) (M' := U) J I
      ((U : Set M).restrictPreimage f) x).range ↔ v ∈ (mfderiv J I f x).range := by
  -- Membership in a range unfolds to an existential, and the tangent spaces at the images in `U`
  -- and in `M` are both the model space `E`.
  exact exists_congr fun w ↦ iff_of_eq (congrArg (· = v) (mfderiv_restrictPreimage_apply hf U w))

/-- A map read in the coordinate of a chart `e` of the maximal atlas, `x ↦ g (e x)`, is
differentiable on every open subset `W` of the chart's source on which `g` is differentiable at the
chart image of each point. -/
theorem mdifferentiable_restrict_comp_chart {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J 1 N) {W : Opens N} (hW : (W : Set N) ⊆ e.source)
    {g : H' → M} (hg : ∀ x ∈ W, MDifferentiableAt J I g (e x)) :
    MDifferentiable J I fun x : W ↦ g (e x) := fun x ↦
  mdifferentiableAt_comp_subtype_val_iff.2
    ((hg x x.property).comp (x : N) (mdifferentiableAt_of_mem_maximalAtlas he (hW x.property)))

end TauCeti.Manifold
