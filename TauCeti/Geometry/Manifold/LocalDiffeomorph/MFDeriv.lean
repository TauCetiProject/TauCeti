/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Differentials of a partial diffeomorphism

The differentials of a partial diffeomorphism and of its inverse are mutually inverse at
corresponding points, as for a global diffeomorphism
(`Diffeomorph.mfderiv_symm_apply_mfderiv_apply`), and on the open source of a partial
diffeomorphism the differential within the source is the differential.

For partial diffeomorphisms `ψ`, `χ`, `φ` into normed spaces, such as charts, the transitions
`ψ ∘ φ⁻¹` are differentiable, and their derivatives compose by the chain rule.

## Main results

* `PartialDiffeomorph.mfderivWithin_source`: the differential within the source is the differential.
* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply`: the differential of the inverse undoes the
  differential.
* `PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`: the differential undoes the differential of
  the inverse.
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

namespace PartialDiffeomorph

/-- On the open source of a partial diffeomorphism the differential within the source is the
differential. -/
theorem mfderivWithin_source (Φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x ∈ Φ.source) : mfderivWithin I J Φ Φ.source x = mfderiv I J Φ x :=
  mfderivWithin_of_isOpen Φ.open_source hx

/-- The differential of the inverse of a partial diffeomorphism undoes its differential. -/
theorem mfderiv_symm_apply_mfderiv_apply (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M}
    (hx : x ∈ Φ.source) (v : TangentSpace I x) :
    mfderiv J I Φ.symm (Φ x) (mfderiv I J Φ x v) = v := by
  have hcomp := mfderiv_comp x (Φ.symm.mdifferentiableAt hn (Φ.map_source hx))
    (Φ.mdifferentiableAt hn hx)
  have heq : (Φ.symm ∘ Φ : M → M) =ᶠ[𝓝 x] id :=
    eventually_of_mem (Φ.open_source.mem_nhds hx) fun z hz ↦ Φ.left_inv hz
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (DFunLike.congr_fun hcomp v).symm

/-- The differential of a partial diffeomorphism undoes the differential of its inverse. -/
theorem mfderiv_apply_mfderiv_symm_apply (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) (v : TangentSpace J y) :
    mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y v) = v :=
  Φ.symm.mfderiv_symm_apply_mfderiv_apply hn hy v

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
