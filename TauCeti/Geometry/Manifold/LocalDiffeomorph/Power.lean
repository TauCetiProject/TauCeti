/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The power map is a local diffeomorphism away from `0`

On an `RCLike` field `𝕂`, the derivative of `w ↦ w ^ k` at `z` is multiplication by
`k z ^ (k - 1)`, a unit when `k ≠ 0` and `z ≠ 0`. By the inverse function theorem
(`TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq`), the power map is then a `C^n` local
diffeomorphism at `z`. At `0` it is not one for `k ≥ 2`, since its derivative vanishes there.

## Main declarations

* `TauCeti.isLocalDiffeomorphAt_pow`: `w ↦ w ^ k` is a local diffeomorphism at every `w ≠ 0`,
  for `k ≠ 0`.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

/-- **The power map is a local diffeomorphism away from `0`.** For `k ≠ 0` and `1 ≤ n`, the map
`w ↦ w ^ k` of an `RCLike` field is a `C^n` local diffeomorphism at every `z ≠ 0`, since its
derivative there is multiplication by the unit `k z ^ (k - 1)`. -/
theorem isLocalDiffeomorphAt_pow {𝕂 : Type*} [RCLike 𝕂] {n : ℕ∞ω} (hn : 1 ≤ n) {k : ℕ}
    (hk : k ≠ 0) {z : 𝕂} (hz : z ≠ 0) : IsLocalDiffeomorphAt 𝓘(𝕂) 𝓘(𝕂) n (· ^ k) z := by
  have hc : (k * z ^ (k - 1) : 𝕂) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hk) (pow_ne_zero _ hz)
  refine isLocalDiffeomorphAt_of_mfderiv_eq (s := univ)
    (e := ContinuousLinearEquiv.unitsEquivAut 𝕂 (Units.mk0 _ hc))
    (contDiff_id.pow k).contMDiff.contMDiffOn isOpen_univ (mem_univ z)
    BoundarylessManifold.isInteriorPoint hn ?_
  -- The derivative of `w ↦ w ^ k` at `z` is multiplication by the unit `k z ^ (k - 1)`.
  have h : ((ContinuousLinearEquiv.unitsEquivAut 𝕂 (Units.mk0 _ hc) : 𝕂 ≃L[𝕂] 𝕂) : 𝕂 →L[𝕂] 𝕂) =
      ContinuousLinearMap.toSpanSingleton 𝕂 (k * z ^ (k - 1)) := by
    ext
    simp
  exact h.trans (hasDerivAt_pow k z).hasFDerivAt.hasMFDerivAt.mfderiv.symm

end TauCeti
