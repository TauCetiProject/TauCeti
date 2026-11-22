/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Strong-bidual reflexivity from dual identifications

Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` upgrades to topological linear isomorphisms from
both `E` and `F` onto their strong biduals (`ContinuousLinearEquiv.bidualEquivOfDualEquiv`,
`ContinuousLinearEquiv.dualBidualEquivOfDualEquiv`).

## Main declarations

* `ContinuousLinearEquiv.bidualEquivOfDualEquiv`,
  `ContinuousLinearEquiv.bidualEquivOfDualEquiv_eq_trans`: strong-bidual evaluation equivalence
  on `E` from a compatible dual identification
  `(StrongDual 𝕜 E ≃L[𝕜] F, E ≃L[𝕜] StrongDual 𝕜 F)`, and its factorization.
* `ContinuousLinearEquiv.dualBidualEquivOfDualEquiv`: strong-bidual evaluation equivalence on
  `F` from the same dual identification.
* `ContinuousLinearEquiv.trans_dualBidualEquivOfDualEquiv`: compatibility of `a` composed with
  `dualBidualEquivOfDualEquiv a b h` against `b.arrowCongr (.refl 𝕜 𝕜)`.
-/

public section

namespace ContinuousLinearEquiv

section DualReflexivity

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` is a topological linear isomorphism
`E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`, equal to
`b.trans (a.symm.arrowCongr (.refl 𝕜 𝕜))`. -/
def bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (_h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  b.trans (a.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

@[simp]
theorem bidualEquivOfDualEquiv_apply_apply (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x)
    (x : E) (ℓ : StrongDual 𝕜 E) :
    bidualEquivOfDualEquiv a b h x ℓ = ℓ x := by
  simpa [bidualEquivOfDualEquiv] using h x ℓ

@[simp]
theorem toLinearMap_bidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    letI : ContinuousSMul 𝕜 E := b.continuousSMul
    (bidualEquivOfDualEquiv a b h).toLinearMap = ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) := by
  let : ContinuousSMul 𝕜 E := b.continuousSMul
  ext x ℓ
  exact bidualEquivOfDualEquiv_apply_apply a b h x ℓ

/-- `bidualEquivOfDualEquiv a b h` factors as `b` followed by `a.symm.arrowCongr (.refl 𝕜 𝕜)`. -/
theorem bidualEquivOfDualEquiv_eq_trans (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    bidualEquivOfDualEquiv a b h =
      b.trans (a.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)) := by
  rw [bidualEquivOfDualEquiv]

/-- Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` is also a topological linear isomorphism
`F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)`. -/
def dualBidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) :=
  bidualEquivOfDualEquiv b.symm a.symm fun f φ ↦ by
    rw [← h (b.symm φ) (a.symm f), b.apply_symm_apply, a.apply_symm_apply]

@[simp]
theorem dualBidualEquivOfDualEquiv_apply_apply
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x)
    (f : F) (φ : StrongDual 𝕜 F) :
    dualBidualEquivOfDualEquiv a b h f φ = φ f :=
  bidualEquivOfDualEquiv_apply_apply _ _ _ f φ

@[simp]
theorem toLinearMap_dualBidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    letI : ContinuousSMul 𝕜 F := a.symm.continuousSMul
    (dualBidualEquivOfDualEquiv a b h).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) := by
  let : ContinuousSMul 𝕜 F := a.symm.continuousSMul
  ext f φ
  exact dualBidualEquivOfDualEquiv_apply_apply a b h f φ

/-- Composing `a : StrongDual 𝕜 E ≃L[𝕜] F` with the dual-bidual equivalence
`dualBidualEquivOfDualEquiv a b h` agrees with `b.arrowCongr (.refl 𝕜 𝕜)`. -/
theorem trans_dualBidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    a.trans (dualBidualEquivOfDualEquiv a b h) = b.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) := by
  ext ℓ Ξ
  obtain ⟨x, rfl⟩ := b.surjective Ξ
  simp [h]

end DualReflexivity

end ContinuousLinearEquiv
