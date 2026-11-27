/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.TensorProduct.Basic
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Tensoring with a line bundle that has a nowhere-zero section

Let `L` be a line bundle, with model fibre of dimension one, and let `s` be a section of `L` that
vanishes nowhere. Then `v ↦ v ⊗ s b` is a fibrewise linear isomorphism `E b ≃ E b ⊗ L b`
(`TauCeti.bundleTensorEquivOfNeZero`): its inverse divides by `s b`, through the coordinate
`TauCeti.VectorBundle.lineCoord` of the line `L b` along `s b`. When `s` is continuous, so is this
isomorphism on total spaces (`TauCeti.continuous_bundleTensorEquivOfNeZero`). So tensoring with a
trivializable line changes nothing.

## Main declarations

* `TauCeti.bundleTensorEquivOfNeZero`: `E b ≃ E b ⊗ L b`, `v ↦ v ⊗ s b`, with inverse
  `v ⊗ w ↦ c • v` for `w = c • s b` (`TauCeti.bundleTensorEquivOfNeZero_symm_apply_tmul`).
* `TauCeti.continuous_bundleTensorEquivOfNeZero`: it is continuous on total spaces.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 5, §6 (tensor products of vector bundles).
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped TensorProduct

namespace TauCeti

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle 𝕜 F E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {L : B → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module 𝕜 (L x)]
  [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace G L)] [FiberBundle G L]
  [VectorBundle 𝕜 G L]
  [∀ x, TopologicalSpace (E x ⊗[𝕜] L x)] [∀ x, IsModuleTopology 𝕜 (E x ⊗[𝕜] L x)]
  (hG : Module.finrank 𝕜 G = 1) {s : ∀ x, L x} (hs : ∀ x, s x ≠ 0)

variable (F) in
/-- **Tensoring with a line with a nowhere-zero section.** For a line bundle `L` with a
nowhere-zero section `s`, the fibrewise isomorphism `E b ≃ E b ⊗ L b`, `v ↦ v ⊗ s b`
(`TauCeti.bundleTensorEquivOfNeZero_apply`). -/
def bundleTensorEquivOfNeZero (x : B) : E x ≃L[𝕜] E x ⊗[𝕜] L x :=
  letI := VectorBundle.isTopologicalAddGroup 𝕜 F E x
  letI := VectorBundle.continuousSMul 𝕜 F E x
  letI := FiberBundle.t2Space F E x
  letI := VectorBundle.finiteDimensional 𝕜 F E x
  haveI : IsModuleTopology 𝕜 (E x) := isModuleTopologyOfFiniteDimensional
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    ((_root_.TensorProduct.rid 𝕜 (E x)).symm.trans
      (_root_.TensorProduct.congr (LinearEquiv.refl 𝕜 _)
        (VectorBundle.lineCoord hG (hs x)).symm.toLinearEquiv))

/-- The isomorphism `E b ≃ E b ⊗ L b` of a nowhere-zero section `s` of a line bundle `L` is
`v ↦ v ⊗ s b`. -/
@[simp]
theorem bundleTensorEquivOfNeZero_apply (x : B) (v : E x) :
    bundleTensorEquivOfNeZero F hG hs x v = v ⊗ₜ[𝕜] s x := by
  simp [bundleTensorEquivOfNeZero]

/-- The inverse of `E b ≃ E b ⊗ L b` divides by `s b`: it sends `v ⊗ w` to `c • v`, where
`w = c • s b`. -/
@[simp]
theorem bundleTensorEquivOfNeZero_symm_apply_tmul (x : B) (v : E x) (w : L x) :
    (bundleTensorEquivOfNeZero F hG hs x).symm (v ⊗ₜ[𝕜] w) =
      VectorBundle.lineCoord hG (hs x) w • v := by
  rw [ContinuousLinearEquiv.symm_apply_eq, bundleTensorEquivOfNeZero_apply, TensorProduct.smul_tmul,
    VectorBundle.lineCoord_smul_self]

variable [FiniteDimensional 𝕜 G] in
/-- For a continuous nowhere-zero section `s` of a line bundle `L`, the isomorphism
`E ≃ E ⊗ L`, `v ↦ v ⊗ s b`, is continuous on total spaces. -/
theorem continuous_bundleTensorEquivOfNeZero
    (hsc : Continuous fun x ↦ TotalSpace.mk' G x (s x)) :
    Continuous fun p : TotalSpace F E ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F G)
      (E := fun x ↦ E x ⊗[𝕜] L x) p.proj (bundleTensorEquivOfNeZero F hG hs p.proj p.snd) := by
  have := VectorBundle.isTopologicalAddGroup 𝕜 F E
  have := VectorBundle.continuousSMul 𝕜 F E
  have := VectorBundle.isTopologicalAddGroup 𝕜 G L
  have := VectorBundle.continuousSMul 𝕜 G L
  simp only [bundleTensorEquivOfNeZero_apply]
  exact Continuous.tmul_section (b := TotalSpace.proj) (v := TotalSpace.snd) continuous_id
    (hsc.comp (continuous_proj F E))

end TauCeti
