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
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)` upgrades to a topological linear isomorphism from `E`
onto its strong bidual (`ContinuousLinearEquiv.bidualEquivOfDualEquiv`); swapping `a` and `b` via
`bidualEquivOfDualEquiv b.symm a.symm` yields the corresponding strong-bidual equivalence on `F`
(`ContinuousLinearEquiv.trans_bidualEquivOfDualEquiv`).

## Main declarations

* `ContinuousLinearEquiv.bidualEquivOfDualEquiv`,
  `ContinuousLinearEquiv.bidualEquivOfDualEquiv_eq_trans`: strong-bidual evaluation equivalence
  on `E` from a compatible dual identification
  `(StrongDual 𝕜 E ≃L[𝕜] F, E ≃L[𝕜] StrongDual 𝕜 F)`, and its factorization.
* `ContinuousLinearEquiv.trans_bidualEquivOfDualEquiv`: compatibility of `a` composed with
  `bidualEquivOfDualEquiv b.symm a.symm h` against `b.arrowCongr (.refl 𝕜 𝕜)`.
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

/-- Composing `a : StrongDual 𝕜 E ≃L[𝕜] F` with `bidualEquivOfDualEquiv b.symm a.symm h` agrees
with `b.arrowCongr (.refl 𝕜 𝕜)`. -/
theorem trans_bidualEquivOfDualEquiv
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (f : F) (φ : StrongDual 𝕜 F), a.symm f (b.symm φ) = φ f) :
    a.trans (bidualEquivOfDualEquiv b.symm a.symm h) =
      b.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) := by
  ext ℓ Ξ
  simpa using (h (a ℓ) Ξ).symm

end DualReflexivity

end ContinuousLinearEquiv
