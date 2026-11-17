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
* `PartialDiffeomorph.differentiableAt_comp_symm`: for partial diffeomorphisms into normed spaces,
  the transition `ψ ∘ φ⁻¹` is differentiable.
* `PartialDiffeomorph.fderiv_comp_symm_eq_comp`: the derivatives of transitions compose, the
  chain rule `D(ψ ∘ φ⁻¹) = D(ψ ∘ χ⁻¹) ∘ D(χ ∘ φ⁻¹)`.
* `PartialDiffeomorph.apply_mem_symm_trans_source`, `PartialDiffeomorph.symm_trans_apply_apply`,
  `PartialDiffeomorph.mfderiv_symm_trans_apply`, and
  `PartialDiffeomorph.mfderiv_symm_trans_eq_of_comp`: source membership, evaluation, and
  differential of a manifold transition `Φ₀.symm.trans Φ₁` at `Φ₀ z`.
-/

public section

open Filter Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

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

section SymmTrans

variable {G H'' Z : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- For partial diffeomorphisms `Φ₀` and `Φ₁` defined at `z`, the image `Φ₀ z` lies in the source
of `Φ₀.symm.trans Φ₁`. -/
theorem apply_mem_symm_trans_source (Φ₀ : PartialDiffeomorph K I Z M n)
    (Φ₁ : PartialDiffeomorph K J Z N n) {z : Z} (hz₀ : z ∈ Φ₀.source) (hz₁ : z ∈ Φ₁.source) :
    Φ₀ z ∈ (Φ₀.symm.trans Φ₁).source := by
  have hz : Φ₀.symm (Φ₀ z) = z := Φ₀.left_inv hz₀
  rw [PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage, hz]
  exact ⟨Φ₀.map_source hz₀, hz₁⟩

/-- At any `z ∈ Φ₀.source`, the transition `Φ₀.symm.trans Φ₁` sends `Φ₀ z` to `Φ₁ z`. -/
theorem symm_trans_apply_apply (Φ₀ : PartialDiffeomorph K I Z M n)
    (Φ₁ : PartialDiffeomorph K J Z N n) {z : Z} (hz₀ : z ∈ Φ₀.source) :
    (Φ₀.symm.trans Φ₁) (Φ₀ z) = Φ₁ z := by
  have hz : Φ₀.symm (Φ₀ z) = z := Φ₀.left_inv hz₀
  rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hz]

/-- The differential of `Φ₀.symm.trans Φ₁` at `Φ₀ z` is the composition of `dΦ₀⁻¹_(Φ₀ z)` followed
by `dΦ₁_z`. -/
theorem mfderiv_symm_trans_apply (Φ₀ : PartialDiffeomorph K I Z M n)
    (Φ₁ : PartialDiffeomorph K J Z N n) (hn : n ≠ 0)
    {z : Z} (hz₀ : z ∈ Φ₀.source) (hz₁ : z ∈ Φ₁.source) (v : TangentSpace I (Φ₀ z)) :
    mfderiv I J (Φ₀.symm.trans Φ₁) (Φ₀ z) v =
      mfderiv K J Φ₁ z (mfderiv I K Φ₀.symm (Φ₀ z) v) := by
  rw [PartialDiffeomorph.coe_trans]
  exact mfderiv_comp_apply_of_eq (Φ₀ z) (Φ₁.mdifferentiableAt hn hz₁)
    (Φ₀.symm.mdifferentiableAt hn (Φ₀.map_source hz₀)) (Φ₀.left_inv hz₀) v

/-- If at `z ∈ Φ₀.source ∩ Φ₁.source` with `Φ₀ z = x` and `Φ₁ z = y` the differential of `Φ₁`
factors as `A ∘ dΦ₀_z`, then the differential of `Φ₀.symm.trans Φ₁` at `x` equals `A`. -/
theorem mfderiv_symm_trans_eq_of_comp (Φ₀ : PartialDiffeomorph K I Z M n)
    (Φ₁ : PartialDiffeomorph K J Z N n) (hn : n ≠ 0)
    {z : Z} {x : M} {y : N} (hz₀ : z ∈ Φ₀.source) (hz₁ : z ∈ Φ₁.source)
    (hx : Φ₀ z = x) (hy : Φ₁ z = y)
    {A : TangentSpace I x →L[𝕜] TangentSpace J y}
    (hA : mfderiv K J Φ₁ z = A.comp (mfderiv K I Φ₀ z)) :
    mfderiv I J (Φ₀.symm.trans Φ₁) x = A := by
  subst hx; subst hy
  ext v
  have hz : Φ₀.symm (Φ₀ z) = z := Φ₀.left_inv hz₀
  have hinv := Φ₀.mfderiv_apply_mfderiv_symm_apply hn (Φ₀.map_source hz₀) v
  rw [hz] at hinv
  exact (Φ₀.mfderiv_symm_trans_apply Φ₁ hn hz₀ hz₁ v).trans <|
    (DFunLike.congr_fun hA _).trans (congrArg A hinv)

end SymmTrans

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
      (fderiv 𝕜 (fun z ↦ ψ (χ.symm z)) (χ x)).comp (fderiv 𝕜 (fun z ↦ χ (φ.symm z)) (φ x)) := by
  have hφx : φ.symm (φ x) = x := φ.left_inv hφ
  -- Near `φ x`, the point `φ⁻¹ z` lies in the source of `χ`, so `χ⁻¹ ∘ χ` cancels there.
  have hsource : ∀ᶠ z in 𝓝 (φ x), φ.symm z ∈ χ.source :=
    (φ.symm.mdifferentiableAt hn (φ.map_source hφ)).continuousAt.preimage_mem_nhds
      (by rw [hφx]; exact χ.open_source.mem_nhds hχ)
  have heq : (fun z ↦ ψ (χ.symm z)) ∘ (fun z ↦ χ (φ.symm z)) =ᶠ[𝓝 (φ x)]
      fun z ↦ ψ (φ.symm z) :=
    hsource.mono fun z hz ↦ congrArg ψ (χ.left_inv hz)
  have hχx : χ (φ.symm (φ x)) = χ x := by rw [hφx]
  have h₁ := ψ.differentiableAt_comp_symm χ hn hψ hχ
  rw [← hχx] at h₁
  rw [← heq.fderiv_eq, fderiv_comp (φ x) h₁ (χ.differentiableAt_comp_symm φ hn hχ hφ), hχx]

end Transition

end PartialDiffeomorph
