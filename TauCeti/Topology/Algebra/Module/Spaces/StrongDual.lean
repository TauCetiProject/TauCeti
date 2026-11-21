/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Strong-bidual reflexivity from dual identifications

Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` upgrades to topological linear isomorphisms from
both `E` and `F` onto their strong biduals (`ContinuousLinearEquiv.bidualEquivOfDualEquiv`,
`ContinuousLinearEquiv.dualBidualEquivOfDualEquiv`).

## Main declarations

* `ContinuousLinearEquiv.bidualEquivOfDualEquiv`: strong-bidual evaluation equivalence on `E` from
  a compatible dual identification `(StrongDual 𝕜 E ≃L[𝕜] F, E ≃L[𝕜] StrongDual 𝕜 F)`.
* `ContinuousLinearEquiv.dualBidualEquivOfDualEquiv`: strong-bidual evaluation equivalence on `F`
  from the same dual identification.
-/

public section

namespace ContinuousLinearEquiv

section DualReflexivity

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` is a topological linear isomorphism
`E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`, equal to
`b.trans (a.symm.arrowCongr (.refl 𝕜 𝕜))`. -/
def bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  let e := b.trans (a.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))
  have he : ∀ x, e x = ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) x := fun x ↦
    ContinuousLinearMap.ext fun ℓ ↦ by
      simpa [e, trans_apply, arrowCongr_apply, refl_apply] using h x ℓ
  { __ := (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    invFun := e.symm
    left_inv x := by rw [LinearMap.toFun_eq_coe, ← he x, e.symm_apply_apply]
    right_inv Ξ := by rw [LinearMap.toFun_eq_coe, ← he (e.symm Ξ), e.apply_symm_apply]
    continuous_toFun := e.continuous.congr he
    continuous_invFun := e.symm.continuous }

@[simp]
theorem coe_bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    ⇑(bidualEquivOfDualEquiv a b h) =
      (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  (rfl)

@[simp]
theorem toLinearMap_bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    (bidualEquivOfDualEquiv a b h).toLinearMap = ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

theorem bidualEquivOfDualEquiv_apply_apply (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x)
    (x : E) (ℓ : StrongDual 𝕜 E) :
    bidualEquivOfDualEquiv a b h x ℓ = ℓ x :=
  (rfl)

omit [ContinuousSMul 𝕜 E] in
/-- Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` is also a topological linear isomorphism
`F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)`. -/
def dualBidualEquivOfDualEquiv [ContinuousSMul 𝕜 F]
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) :=
  bidualEquivOfDualEquiv b.symm a.symm fun f φ ↦ by
    rw [← h (b.symm φ) (a.symm f), b.apply_symm_apply, a.apply_symm_apply]

omit [ContinuousSMul 𝕜 E] in
@[simp]
theorem coe_dualBidualEquivOfDualEquiv [ContinuousSMul 𝕜 F]
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    ⇑(dualBidualEquivOfDualEquiv a b h) =
      (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : F →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) :=
  (rfl)

omit [ContinuousSMul 𝕜 E] in
@[simp]
theorem toLinearMap_dualBidualEquivOfDualEquiv [ContinuousSMul 𝕜 F]
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    (dualBidualEquivOfDualEquiv a b h).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

omit [ContinuousSMul 𝕜 E] in
theorem dualBidualEquivOfDualEquiv_apply_apply [ContinuousSMul 𝕜 F]
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x)
    (f : F) (φ : StrongDual 𝕜 F) :
    dualBidualEquivOfDualEquiv a b h f φ = φ f :=
  (rfl)

end DualReflexivity

end ContinuousLinearEquiv
