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
`b : E ≃L[𝕜] StrongDual 𝕜 F`, `ContinuousLinearEquiv.bidualEquivOfDualEquiv` constructs the
topological linear isomorphism `b.trans (a.symm.arrowCongr (.refl 𝕜 𝕜))` from `E` onto its
strong bidual. When `a` and `b` are compatible with evaluation (`b x (a ℓ) = ℓ x`), this map
agrees with canonical evaluation `ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)`; swapping `a`
and `b` via `bidualEquivOfDualEquiv b.symm a.symm` yields the corresponding strong-bidual
equivalence on `F` (`ContinuousLinearEquiv.trans_bidualEquivOfDualEquiv`).

## Main declarations

* `ContinuousLinearEquiv.bidualEquivOfDualEquiv`,
  `ContinuousLinearEquiv.bidualEquivOfDualEquiv_eq_trans`: strong-bidual isomorphism on `E` from
  a dual identification `(StrongDual 𝕜 E ≃L[𝕜] F, E ≃L[𝕜] StrongDual 𝕜 F)`, and its
  factorization.
* `ContinuousLinearEquiv.bidualEquivOfDualEquiv_apply_apply`,
  `ContinuousLinearEquiv.toLinearMap_bidualEquivOfDualEquiv`: identification with canonical
  evaluation `ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` when `b x (a ℓ) = ℓ x`.
* `ContinuousLinearEquiv.trans_bidualEquivOfDualEquiv`: compatibility of `a` composed with
  `bidualEquivOfDualEquiv b.symm a.symm` against `b.arrowCongr (.refl 𝕜 𝕜)`.
-/

public section

namespace ContinuousLinearEquiv

section DualReflexivity

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F`, constructs the topological linear isomorphism
`b.trans (a.symm.arrowCongr (.refl 𝕜 𝕜)) : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`. When
`b x (a ℓ) = ℓ x`, this agrees with canonical evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)`. -/
def bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  b.trans (a.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

@[simp]
theorem bidualEquivOfDualEquiv_apply_apply (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x)
    (x : E) (ℓ : StrongDual 𝕜 E) :
    bidualEquivOfDualEquiv a b x ℓ = ℓ x := by
  simpa [bidualEquivOfDualEquiv] using h x ℓ

@[simp]
theorem toLinearMap_bidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    letI : ContinuousSMul 𝕜 E := b.continuousSMul
    (bidualEquivOfDualEquiv a b).toLinearMap = ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) := by
  let : ContinuousSMul 𝕜 E := b.continuousSMul
  ext x ℓ
  exact bidualEquivOfDualEquiv_apply_apply a b h x ℓ

/-- `bidualEquivOfDualEquiv a b` factors as `b` followed by `a.symm.arrowCongr (.refl 𝕜 𝕜)`. -/
theorem bidualEquivOfDualEquiv_eq_trans (a : StrongDual 𝕜 E ≃L[𝕜] F)
    (b : E ≃L[𝕜] StrongDual 𝕜 F) :
    bidualEquivOfDualEquiv a b =
      b.trans (a.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)) := by
  rw [bidualEquivOfDualEquiv]

/-- Composing `a : StrongDual 𝕜 E ≃L[𝕜] F` with `bidualEquivOfDualEquiv b.symm a.symm` agrees
with `b.arrowCongr (.refl 𝕜 𝕜)`. -/
theorem trans_bidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F) :
    a.trans (bidualEquivOfDualEquiv b.symm a.symm) =
      b.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) := by
  ext ℓ Ξ
  simp [bidualEquivOfDualEquiv_eq_trans]

end DualReflexivity

end ContinuousLinearEquiv
