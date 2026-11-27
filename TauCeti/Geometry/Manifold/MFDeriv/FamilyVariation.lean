/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic

/-!
# The variation field of a family of maps

For a family of maps `Φ t : M → N`, `t ∈ ℝ`, the variation field `X = ∂_t Φ(t₀, ·)`
(`TauCeti.familyVariationField`) at `t₀` is the vector field along `Φ t₀` whose value at `y` is
the velocity at `t₀` of the curve `t ↦ Φ t y`. It is the family analogue of the variation field
`TauCeti.Manifold.variationField` of a two-parameter family of curves, and is the infinitesimal
deformation in the first variation of volume of an immersion
(`TauCeti.Geometry.Manifold.Riemannian.Immersion.FirstVariation`).

## Main definitions

* `TauCeti.familyVariationField`: the variation field `X = ∂_t Φ(t₀, ·)` of a family of maps.

## Main results

* `TauCeti.familyVariationField_eq_zero`: the variation field vanishes where the family is
  locally constant in `t`.
* `TauCeti.familyVariationField_eq_mfderiv`: the variation field is the differential of the
  uncurried family in the direction of the parameter.
* `TauCeti.contMDiffAt_familyVariationField`,
  `TauCeti.mdifferentiableAt_sectionCoord_familyVariationField`: the variation field of a family
  which is `C²` at `(t₀, x)` is a `C¹` section along `Φ t₀` near `x`, with a differentiable
  coordinate reading.
-/

public section

open Bundle Manifold Filter Function
open TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {Φ : ℝ → M → N} {t₀ : ℝ} {x : M}

variable (J Φ t₀) in
/-- The **variation field** `X = ∂_t Φ(t₀, ·)` of a family of maps `Φ t : M → N` at `t₀`: at `y`,
the velocity at `t₀` of the curve `t ↦ Φ t y`. It is a vector field along `Φ t₀`. -/
def familyVariationField (y : M) : TangentSpace J (Φ t₀ y) :=
  curveVelocity J (fun t ↦ Φ t y) t₀

omit [TopologicalSpace M] in
/-- The defining formula for the variation field. -/
theorem familyVariationField_apply (y : M) :
    familyVariationField J Φ t₀ y = curveVelocity J (fun t ↦ Φ t y) t₀ :=
  (rfl)

omit [TopologicalSpace M] in
/-- The variation field as a function of the point: the unapplied form of
`familyVariationField_apply`. -/
theorem familyVariationField_def :
    familyVariationField J Φ t₀ = fun y ↦ curveVelocity J (fun t ↦ Φ t y) t₀ :=
  (rfl)

omit [TopologicalSpace M] in
/-- At a point which the maps of the family near `t₀` all send to the same image, the variation
field vanishes. -/
@[simp]
theorem familyVariationField_eq_zero {y : M} (h : ∀ᶠ t in 𝓝 t₀, Φ t y = Φ t₀ y) :
    familyVariationField J Φ t₀ y = 0 := by
  rw [familyVariationField_apply, curveVelocity_apply,
    Filter.EventuallyEq.mfderiv_eq (f := fun _ ↦ Φ t₀ y) h, mfderiv_const]
  exact zero_apply _

/-- The variation field is the differential of the uncurried family in the direction of the
parameter. -/
theorem familyVariationField_eq_mfderiv {y : M}
    (hΦ : MDifferentiableAt (𝓘(ℝ).prod I) J (uncurry Φ) (t₀, y)) :
    familyVariationField J Φ t₀ y = mfderiv (𝓘(ℝ).prod I) J (uncurry Φ) (t₀, y) (1, 0) :=
  hΦ.curveVelocity_eq_mfderiv_uncurry_apply_mk_zero (g := id) (hasDerivAt_id t₀)

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- The variation field of a family which is `C²` at `(t₀, x)` is `C¹` at `x`, as a section of
the tangent bundle of `N` along `Φ t₀`. -/
theorem contMDiffAt_familyVariationField
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) :
    ContMDiffAt I J.tangent 1
      (fun y ↦ (⟨Φ t₀ y, familyVariationField J Φ t₀ y⟩ : TangentBundle J N)) x := by
  have hf : ContMDiffAt (I.prod 𝓘(ℝ)) J 2 (uncurry fun (y : M) (t : ℝ) ↦ Φ t y) (x, t₀) :=
    hΦ.comp (x, t₀) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hϕ := hf.mfderiv (fun (y : M) (t : ℝ) ↦ Φ t y) (fun _ ↦ t₀) (m := 1) contMDiffAt_const
    (by norm_num)
  have hv : ContMDiffAt I 𝓘(ℝ).tangent 1
      (fun _ : M ↦ (⟨t₀, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ)) x := contMDiffAt_const
  have hb : ContMDiffAt I J 1 (fun y ↦ Φ t₀ y) x :=
    (hΦ.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).of_le (by norm_num)
  have := ContMDiffAt.clm_apply_of_inCoordinates hϕ hv hb
  simpa only [familyVariationField, curveVelocity_apply] using this

/-- The variation field of a family which is `C²` at `(t₀, x)` has a differentiable coordinate
reading at `x`. -/
theorem mdifferentiableAt_sectionCoord_familyVariationField
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) :
    MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) (Φ t₀) (familyVariationField J Φ t₀) (Φ t₀ x)) x :=
  mdifferentiableAt_sectionCoord (Φ t₀) _
    ((contMDiffAt_familyVariationField hΦ).mdifferentiableAt (by norm_num))
    (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (Φ t₀ x))

end TauCeti
