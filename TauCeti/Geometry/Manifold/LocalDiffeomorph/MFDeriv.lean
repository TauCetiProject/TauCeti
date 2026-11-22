/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Differentials of a partial diffeomorphism

The differentials of a partial diffeomorphism and of its inverse are mutually inverse at
corresponding points, as for a global diffeomorphism
(`Diffeomorph.mfderiv_symm_apply_mfderiv_apply`). The differential at a point of the source is a
linear equivalence, as for a global diffeomorphism (`Diffeomorph.isInvertible_mfderiv`), so for a
partial diffeomorphism into a normed space the differential read in that space is bijective. On the
open source of a partial diffeomorphism the differential within the source is the differential.
More generally, this holds at any point of an open partial homeomorphism where it and its inverse
are differentiable.

For partial diffeomorphisms `ψ`, `χ`, `φ` into normed spaces, such as charts, the transitions
`ψ ∘ φ⁻¹` are differentiable, and their derivatives compose by the chain rule.

## Main results

* `IsLocalDiffeomorphAt.finrank_eq`: a local diffeomorphism of nonzero regularity has source
  and target model spaces of equal dimension.
* `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_symm_mfderiv_apply`,
  `IsLocalDiffeomorphAt.mfderiv_mfderivToContinuousLinearEquiv_symm_apply`: the inverse of the
  differential of a local diffeomorphism, `(df_x)⁻¹`, undoes `df_x` on either side.

* `OpenPartialHomeomorph.mfderiv_symm_apply_mfderiv_apply`,
  `OpenPartialHomeomorph.mfderiv_apply_mfderiv_symm_apply`: where an open partial homeomorphism
  and its inverse are differentiable, their differentials are mutually inverse.
* `OpenPartialHomeomorph.mvfderiv_eq_fderiv_symm_trans_comp`: for open partial homeomorphisms
  `ψ₁`, `ψ₂` into a normed space, the differential of `ψ₂` is that of `ψ₁` followed by the
  derivative of the transition `ψ₂ ∘ ψ₁⁻¹`.
* `OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans`: dually, the
  differential of `ψ₁⁻¹` is the derivative of the transition `ψ₂ ∘ ψ₁⁻¹` followed by the
  differential of `ψ₂⁻¹`.
* `PartialDiffeomorph.mfderivWithin_source`: the differential within the source is the differential.
* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply`: the differential of the inverse undoes the
  differential.
* `PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`: the differential undoes the differential of
  the inverse.
* `PartialDiffeomorph.isInvertible_mfderiv`: the differential at a point of the source is a
  linear equivalence.
* `PartialDiffeomorph.mfderiv_symm_trans_apply_mfderiv_apply`: for partial diffeomorphisms `Φ₁`,
  `Φ₂` out of the same manifold, the differential of `Φ₂ ∘ Φ₁⁻¹` carries that of `Φ₁` to that of
  `Φ₂`.
* `PartialDiffeomorph.bijective_mvfderiv`: for a partial diffeomorphism into a normed space, the
  differential read in that space is bijective at a point of the source.
* `PartialDiffeomorph.hasDerivAt_comp_symm_of_mfderiv_eq_zero`: at a critical point of a map into a
  normed space, read through a partial diffeomorphism into a normed space, the derivative along a
  curve `t ↦ φ⁻¹ (L t)` vanishes.
* `OpenPartialHomeomorph.hasFDerivAt_comp_symm_trans`: the chain rule for transitions
  `ψ₀ ∘ ψ₂⁻¹ = (ψ₀ ∘ ψ₁⁻¹) ∘ (ψ₁ ∘ ψ₂⁻¹)` of open partial homeomorphisms into normed spaces.
* `PartialDiffeomorph.differentiableAt_comp_symm`: for partial diffeomorphisms into normed spaces,
  the transition `ψ ∘ φ⁻¹` is differentiable.
* `PartialDiffeomorph.fderiv_comp_symm_eq_comp`: the derivatives of transitions compose, the
  chain rule `D(ψ ∘ φ⁻¹) = D(ψ ∘ χ⁻¹) ∘ D(χ ∘ φ⁻¹)`.
-/

public section

open Filter
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

/-- A local diffeomorphism of nonzero regularity has source and target model spaces of equal
dimension. -/
theorem IsLocalDiffeomorphAt.finrank_eq {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    Module.finrank 𝕜 E = Module.finrank 𝕜 F := by
  simpa only [TauCeti.finrank_tangentSpace] using
    (hf.mfderivToContinuousLinearEquiv hn).toLinearEquiv.finrank_eq

/-- The inverse of the differential of a local diffeomorphism undoes the differential:
`(df_x)⁻¹ (df_x v) = v`. -/
@[simp]
theorem IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_symm_mfderiv_apply {f : M → N}
    {x : M} (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) (v : TangentSpace I x) :
    (hf.mfderivToContinuousLinearEquiv hn).symm (mfderiv I J f x v) = v := by
  rw [← hf.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The differential of a local diffeomorphism undoes the inverse of the differential:
`df_x ((df_x)⁻¹ w) = w`. -/
@[simp]
theorem IsLocalDiffeomorphAt.mfderiv_mfderivToContinuousLinearEquiv_symm_apply {f : M → N}
    {x : M} (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) (w : TangentSpace J (f x)) :
    mfderiv I J f x ((hf.mfderivToContinuousLinearEquiv hn).symm w) = w := by
  rw [← hf.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

namespace OpenPartialHomeomorph

/-- The differential of the inverse of an open partial homeomorphism undoes its differential at a
point of the source where both are differentiable. -/
theorem mfderiv_symm_apply_mfderiv_apply (Φ : OpenPartialHomeomorph M N) {x : M}
    (hx : x ∈ Φ.source) (hΦ : MDifferentiableAt I J Φ x)
    (hΦs : MDifferentiableAt J I Φ.symm (Φ x)) (v : TangentSpace I x) :
    mfderiv J I Φ.symm (Φ x) (mfderiv I J Φ x v) = v := by
  have hcomp := mfderiv_comp x hΦs hΦ
  have heq : (Φ.symm ∘ Φ : M → M) =ᶠ[𝓝 x] id :=
    eventually_of_mem (Φ.open_source.mem_nhds hx) fun z hz ↦ Φ.left_inv hz
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (DFunLike.congr_fun hcomp v).symm

/-- The differential of an open partial homeomorphism undoes the differential of its inverse at a
point of the target where both are differentiable. -/
theorem mfderiv_apply_mfderiv_symm_apply (Φ : OpenPartialHomeomorph M N) {y : N}
    (hy : y ∈ Φ.target) (hΦ : MDifferentiableAt I J Φ (Φ.symm y))
    (hΦs : MDifferentiableAt J I Φ.symm y) (v : TangentSpace J y) :
    mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y v) = v :=
  Φ.symm.mfderiv_symm_apply_mfderiv_apply hy hΦs hΦ v

section Transition

variable {V₀ V₁ V₂ : Type*} [NormedAddCommGroup V₀] [NormedSpace 𝕜 V₀]
  [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [NormedAddCommGroup V₂] [NormedSpace 𝕜 V₂]

/-- **The chain rule for transitions of charts.** For a point `x` in the sources of `ψ₁` and `ψ₂`,
the transition `ψ₀ ∘ ψ₂⁻¹` agrees near `ψ₂ x` with `(ψ₀ ∘ ψ₁⁻¹) ∘ (ψ₁ ∘ ψ₂⁻¹)`, so its derivative
there is the composite of the derivatives of the two transitions. -/
theorem hasFDerivAt_comp_symm_trans (ψ₀ : OpenPartialHomeomorph M V₀)
    (ψ₁ : OpenPartialHomeomorph M V₁) (ψ₂ : OpenPartialHomeomorph M V₂) {x : M}
    (hx₁ : x ∈ ψ₁.source) (hx₂ : x ∈ ψ₂.source) {D₀₁ : V₁ →L[𝕜] V₀} {D₁₂ : V₂ →L[𝕜] V₁}
    (hT₀₁ : HasFDerivAt (fun z ↦ ψ₀ (ψ₁.symm z)) D₀₁ (ψ₁ x))
    (hT₁₂ : HasFDerivAt (fun z ↦ ψ₁ (ψ₂.symm z)) D₁₂ (ψ₂ x)) :
    HasFDerivAt (fun z ↦ ψ₀ (ψ₂.symm z)) (D₀₁ ∘L D₁₂) (ψ₂ x) := by
  have hT₀₁' : HasFDerivAt (fun z ↦ ψ₀ (ψ₁.symm z)) D₀₁ (ψ₁ (ψ₂.symm (ψ₂ x))) := by
    rwa [ψ₂.left_inv hx₂]
  refine (hT₀₁'.comp (ψ₂ x) hT₁₂).congr_of_eventuallyEq ?_
  -- Near `ψ₂ x` the map `ψ₂⁻¹` lands in the source of `ψ₁`, where `ψ₁⁻¹ ∘ ψ₁` is the identity.
  have hsource : ∀ᶠ z in 𝓝 (ψ₂ x), ψ₂.symm z ∈ ψ₁.source :=
    ψ₂.continuousAt_symm (ψ₂.map_source hx₂) |>.preimage_mem_nhds
      (ψ₁.open_source.mem_nhds (by rwa [ψ₂.left_inv hx₂]))
  filter_upwards [hsource] with z hz
  simp [ψ₁.left_inv hz]

end Transition

/-- **The chain rule for a change of chart into a normed space.** Let `ψ₁` and `ψ₂` be open
partial homeomorphisms from `M` into a normed space `F`, and let `w` lie in the source of the
transition `ψ₂ ∘ ψ₁⁻¹`. If `ψ₁` is differentiable at `ψ₁⁻¹ w` and the transition at `w`, then the
differential of `ψ₂` at `ψ₁⁻¹ w`, read in `F`, is that of `ψ₁` followed by the derivative of the
transition at `w`. -/
theorem mvfderiv_eq_fderiv_symm_trans_comp {ψ₁ ψ₂ : OpenPartialHomeomorph M F} {w : F}
    (hw : w ∈ (ψ₁.symm.trans ψ₂).source) (hψ₁ : MDifferentiableAt I 𝓘(𝕜, F) ψ₁ (ψ₁.symm w))
    (hΘ : DifferentiableAt 𝕜 (ψ₁.symm.trans ψ₂) w) :
    mvfderiv I ψ₂ (ψ₁.symm w) =
      (fderiv 𝕜 (ψ₁.symm.trans ψ₂) w).comp (mvfderiv I ψ₁ (ψ₁.symm w)) := by
  have hw' : w ∈ ψ₁.target ∧ ψ₁.symm w ∈ ψ₂.source := by simpa using hw
  -- Near `ψ₁⁻¹ w`, the chart `ψ₂` is the transition after `ψ₁`.
  have hev : (ψ₂ : M → F) =ᶠ[𝓝 (ψ₁.symm w)] (ψ₁.symm.trans ψ₂) ∘ ψ₁ := by
    filter_upwards [ψ₁.open_source.mem_nhds (ψ₁.map_target hw'.1)] with y hy
    simp [ψ₁.left_inv hy]
  have hΘ' : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, F) (ψ₁.symm.trans ψ₂) (ψ₁ (ψ₁.symm w)) := by
    rw [ψ₁.right_inv hw'.1]
    exact hΘ.mdifferentiableAt
  ext v
  rw [ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply, hev.mfderiv_eq, mfderiv_comp _ hΘ' hψ₁, ψ₁.right_inv hw'.1,
    mfderiv_eq_fderiv]
  -- The casts `tangentSpaceCast` and `NormedSpace.fromTangentSpace` inserted by the chain rule
  -- and by `mfderiv_eq_fderiv` act as the identity by definition.
  rfl

/-- **The chain rule for the inverse of a change of chart.** Let `ψ₁` and `ψ₂` be open partial
homeomorphisms from `M` into a normed space `F`, and let `w` lie in the source of the transition
`ψ₂ ∘ ψ₁⁻¹`. If `ψ₂⁻¹` is differentiable at the image of `w` under the transition and the
transition at `w`, then the differential of `ψ₁⁻¹` at `w` is the derivative of the transition at
`w` followed by the differential of `ψ₂⁻¹`. -/
theorem mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans {ψ₁ ψ₂ : OpenPartialHomeomorph M F}
    {w : F} (hw : w ∈ (ψ₁.symm.trans ψ₂).source)
    (hψ₂s : MDifferentiableAt 𝓘(𝕜, F) I ψ₂.symm (ψ₁.symm.trans ψ₂ w))
    (hΘ : DifferentiableAt 𝕜 (ψ₁.symm.trans ψ₂) w) :
    mfderiv 𝓘(𝕜, F) I ψ₁.symm w =
      (mfderiv 𝓘(𝕜, F) I ψ₂.symm (ψ₁.symm.trans ψ₂ w)).comp (fderiv 𝕜 (ψ₁.symm.trans ψ₂) w) := by
  -- Near `w`, the inverse of `ψ₁` is the inverse of `ψ₂` after the transition.
  have hev : (ψ₁.symm : F → M) =ᶠ[𝓝 w] ψ₂.symm ∘ (ψ₁.symm.trans ψ₂) := by
    filter_upwards [(ψ₁.symm.trans ψ₂).open_source.mem_nhds hw] with q hq
    have hq' : q ∈ ψ₁.target ∧ ψ₁.symm q ∈ ψ₂.source := by simpa using hq
    simp [ψ₂.left_inv hq'.2]
  rw [hev.mfderiv_eq, mfderiv_comp _ hψ₂s hΘ.mdifferentiableAt, mfderiv_eq_fderiv]
  -- The casts `tangentSpaceCast` and `NormedSpace.fromTangentSpace` inserted by the chain rule
  -- and by `mfderiv_eq_fderiv` act as the identity by definition.
  rfl

end OpenPartialHomeomorph

namespace PartialDiffeomorph

/-- On the open source of a partial diffeomorphism the differential within the source is the
differential. -/
theorem mfderivWithin_source (Φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x ∈ Φ.source) : mfderivWithin I J Φ Φ.source x = mfderiv I J Φ x :=
  mfderivWithin_of_isOpen Φ.open_source hx

/-- The differential of the inverse of a partial diffeomorphism undoes its differential. -/
theorem mfderiv_symm_apply_mfderiv_apply (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M}
    (hx : x ∈ Φ.source) (v : TangentSpace I x) :
    mfderiv J I Φ.symm (Φ x) (mfderiv I J Φ x v) = v :=
  Φ.toOpenPartialHomeomorph.mfderiv_symm_apply_mfderiv_apply hx (Φ.mdifferentiableAt hn hx)
    (Φ.symm.mdifferentiableAt hn (Φ.map_source hx)) v

/-- The differential of a partial diffeomorphism undoes the differential of its inverse. -/
theorem mfderiv_apply_mfderiv_symm_apply (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) (v : TangentSpace J y) :
    mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y v) = v :=
  Φ.symm.mfderiv_symm_apply_mfderiv_apply hn hy v

/-- The differential of a partial diffeomorphism at a point of its source is a linear
equivalence. -/
theorem isInvertible_mfderiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M}
    (hx : x ∈ Φ.source) : (mfderiv I J Φ x).IsInvertible :=
  (Φ.isLocalDiffeomorphAt I J n hx).isInvertible_mfderiv hn

/-- For partial diffeomorphisms `Φ₁` and `Φ₂` out of the same manifold whose sources contain `x`,
the differential of the transition `Φ₂ ∘ Φ₁⁻¹` at `Φ₁ x` carries the differential of `Φ₁` at `x`
to that of `Φ₂`. -/
theorem mfderiv_symm_trans_apply_mfderiv_apply {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    (Φ₁ : PartialDiffeomorph I J M N n) (Φ₂ : PartialDiffeomorph I K M P n) (hn : n ≠ 0) {x : M}
    (h₁ : x ∈ Φ₁.source) (h₂ : x ∈ Φ₂.source) (v : TangentSpace I x) :
    mfderiv J K (Φ₁.symm.trans Φ₂) (Φ₁ x) (mfderiv I J Φ₁ x v) = mfderiv I K Φ₂ x v := by
  rw [coe_trans, mfderiv_comp_apply_of_eq (Φ₁ x) (Φ₂.mdifferentiableAt hn h₂)
    (Φ₁.symm.mdifferentiableAt hn (Φ₁.map_source h₁)) (Φ₁.left_inv h₁),
    Φ₁.mfderiv_symm_apply_mfderiv_apply hn h₁]

/-- The differential of a partial diffeomorphism into a normed space, read in that space, is
bijective at a point of the source. -/
theorem bijective_mvfderiv (Φ : PartialDiffeomorph I 𝓘(𝕜, F) M F n) (hn : n ≠ 0) {x : M}
    (hx : x ∈ Φ.source) : Function.Bijective (mvfderiv I Φ x) := by
  have h := Φ.isInvertible_mfderiv hn hx
  refine ⟨TauCeti.injective_mvfderiv_iff.2 h.injective, fun w ↦ ?_⟩
  obtain ⟨v, hv⟩ := h.surjective w
  exact ⟨v, (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans hv⟩

/-- At a critical point `φ⁻¹ (L t₀)` of a map `g` into a normed space, read through a partial
diffeomorphism `φ` into a normed space, the derivative of `g` along the curve `t ↦ φ⁻¹ (L t)`
vanishes at `t₀`. -/
theorem hasDerivAt_comp_symm_of_mfderiv_eq_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (φ : PartialDiffeomorph I 𝓘(𝕜, F) M F n) (hn : n ≠ 0) {g : M → G}
    {L : 𝕜 → F} {t₀ : 𝕜} (hL : DifferentiableAt 𝕜 L t₀) (ht₀ : L t₀ ∈ φ.target)
    (hg : MDifferentiableAt I 𝓘(𝕜, G) g (φ.symm (L t₀)))
    (h0 : mfderiv I 𝓘(𝕜, G) g (φ.symm (L t₀)) = 0) :
    HasDerivAt (fun t ↦ g (φ.symm (L t))) 0 t₀ := by
  have hγ : MDifferentiableAt 𝓘(𝕜) I (fun t ↦ φ.symm (L t)) t₀ :=
    (φ.symm.mdifferentiableAt hn ht₀).comp t₀ (mdifferentiableAt_iff_differentiableAt.2 hL)
  have hd : HasFDerivAt (fun t ↦ g (φ.symm (L t))) (0 : 𝕜 →L[𝕜] G) t₀ := by
    have h := hg.hasMFDerivAt.comp t₀ hγ.hasMFDerivAt
    rwa [h0, ContinuousLinearMap.zero_comp, hasMFDerivAt_iff_hasFDerivAt] at h
  simpa using hd.hasDerivAt

section Transition

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
  {G'' : Type*} [NormedAddCommGroup G''] [NormedSpace 𝕜 G'']

/-- The transition `ψ ∘ φ⁻¹` between two partial diffeomorphisms into normed spaces is
differentiable at the image under `φ` of every point of both sources. -/
theorem differentiableAt_comp_symm (ψ : PartialDiffeomorph I 𝓘(𝕜, G') M G' n)
    (φ : PartialDiffeomorph I 𝓘(𝕜, G) M G n) (hn : n ≠ 0)
    {x : M} (hψ : x ∈ ψ.source) (hφ : x ∈ φ.source) :
    DifferentiableAt 𝕜 (fun z ↦ ψ (φ.symm z)) (φ x) :=
  mdifferentiableAt_iff_differentiableAt.1 <| (ψ.mdifferentiableAt hn hψ).comp_of_eq (φ x)
    (φ.symm.mdifferentiableAt hn (φ.map_source hφ)) (φ.left_inv hφ)

/-- **The chain rule for transitions.** For partial diffeomorphisms `ψ`, `χ`, `φ` into normed
spaces whose sources contain `x`, the derivative of the transition `ψ ∘ φ⁻¹` at `φ x` is the
derivative of `χ ∘ φ⁻¹` at `φ x` followed by that of `ψ ∘ χ⁻¹` at `χ x`. -/
theorem fderiv_comp_symm_eq_comp (ψ : PartialDiffeomorph I 𝓘(𝕜, G'') M G'' n)
    (χ : PartialDiffeomorph I 𝓘(𝕜, G') M G' n) (φ : PartialDiffeomorph I 𝓘(𝕜, G) M G n)
    (hn : n ≠ 0)
    {x : M} (hψ : x ∈ ψ.source) (hχ : x ∈ χ.source) (hφ : x ∈ φ.source) :
    fderiv 𝕜 (fun z ↦ ψ (φ.symm z)) (φ x) =
      (fderiv 𝕜 (fun z ↦ ψ (χ.symm z)) (χ x)).comp (fderiv 𝕜 (fun z ↦ χ (φ.symm z)) (φ x)) :=
  (ψ.toOpenPartialHomeomorph.hasFDerivAt_comp_symm_trans χ.toOpenPartialHomeomorph
    φ.toOpenPartialHomeomorph hχ hφ (ψ.differentiableAt_comp_symm χ hn hψ hχ).hasFDerivAt
    (χ.differentiableAt_comp_symm φ hn hχ hφ).hasFDerivAt).fderiv

end Transition

end PartialDiffeomorph

/-- On the source of a partial diffeomorphism `Φ` agreeing with a local diffeomorphism `f`, the
inverse of the differential of `f` is the differential of `Φ⁻¹`: `(df_x)⁻¹ = dΦ⁻¹_(f x)`. -/
theorem IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_symm_apply {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) {Φ : PartialDiffeomorph I J M N n}
    (hfΦ : Set.EqOn f Φ Φ.source) (hx : x ∈ Φ.source) (w : TangentSpace J (f x)) :
    (hf.mfderivToContinuousLinearEquiv hn).symm w = mfderiv J I Φ.symm (f x) w := by
  set u := (hf.mfderivToContinuousLinearEquiv hn).symm w
  have hw : mfderiv I J f x u = w := hf.mfderiv_mfderivToContinuousLinearEquiv_symm_apply hn w
  -- Near `x` the map `f` is `Φ`, so `df_x = dΦ_x`, and `dΦ⁻¹_(Φ x) ∘ dΦ_x` is the identity.
  have hd : mfderiv I J f x = mfderiv I J Φ x :=
    (eventuallyEq_of_mem (Φ.open_source.mem_nhds hx) hfΦ).mfderiv_eq
  rw [← hw, hd]
  exact (Φ.mfderiv_symm_apply_mfderiv_apply hn hx u).symm.trans
    (congrArg (fun y : N ↦ (mfderiv J I Φ.symm y (mfderiv I J Φ x u) : E)) (hfΦ hx).symm)
