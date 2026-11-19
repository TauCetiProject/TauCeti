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

* `OpenPartialHomeomorph.mfderiv_symm_apply_mfderiv_apply`,
  `OpenPartialHomeomorph.mfderiv_apply_mfderiv_symm_apply`: where an open partial homeomorphism
  and its inverse are differentiable, their differentials are mutually inverse.
* `PartialDiffeomorph.mfderivWithin_source`: the differential within the source is the differential.
* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply`: the differential of the inverse undoes the
  differential.
* `PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`: the differential undoes the differential of
  the inverse.
* `PartialDiffeomorph.isInvertible_mfderiv`: the differential at a point of the source is a
  linear equivalence.
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
