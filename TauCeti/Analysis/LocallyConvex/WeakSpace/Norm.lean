/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic

/-!
# Weak lower semicontinuity of norm energies

Let `E` and `F` be normed spaces over `𝕜 = ℝ` or `ℂ`, let `D : E →L[𝕜] F` be bounded and let
`g : ℝ → β` be lower semicontinuous and monotone on `[0, ∞)`. The energy `u ↦ g ‖D u‖` is lower
semicontinuous for the weak topology of `E`
(`ContinuousLinearMap.lowerSemicontinuous_comp_norm_comp_toWeakSpace_symm`). Its sublevel sets are
convex, since `‖D (a u + b v)‖ ≤ max ‖D u‖ ‖D v‖` for a convex combination and `g` is monotone,
so it is quasiconvex and `QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm` applies.

The instances are the norm `‖u‖`, the norm powers `‖u‖ ^ p` for `0 ≤ p`, and the quadratic energy
`‖D u‖ ^ 2` of a bounded linear map `D`. For a complex space, convexity is real convexity: the
real scalar structure enters only through the convex combinations.

## Main results

* `ContinuousLinearMap.lowerSemicontinuous_comp_norm_comp_toWeakSpace_symm`: `u ↦ g ‖D u‖` is
  weakly lower semicontinuous.
* `TauCeti.lowerSemicontinuous_norm_comp_toWeakSpace_symm`: the norm is weakly lower
  semicontinuous.
* `TauCeti.lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm`: so is `‖u‖ ^ p` for `0 ≤ p`.
* `ContinuousLinearMap.lowerSemicontinuous_norm_sq_comp_toWeakSpace_symm`: so is `‖D u‖ ^ 2`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Corollary 3.9.
-/

public section

open Set

namespace ContinuousLinearMap

variable {𝕜 E F β : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Weak lower semicontinuity of norm energies.** For a bounded linear map `D` and a lower
semicontinuous `g` that is monotone on `[0, ∞)`, the energy `u ↦ g ‖D u‖` is lower
semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_comp_norm_comp_toWeakSpace_symm [LinearOrder β]
    (D : E →L[𝕜] F) {g : ℝ → β} (hg : MonotoneOn g (Ici 0)) (hlsc : LowerSemicontinuous g) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ g ‖D ((toWeakSpace 𝕜 E).symm u)‖ := by
  -- The real scalar structure only serves to form convex combinations.
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  let _ : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  have _ : IsScalarTower ℝ 𝕜 F := RestrictScalars.isScalarTower ℝ 𝕜 F
  refine QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm (f := fun u ↦ g ‖D u‖) ?_
    (hlsc.comp (continuous_norm.comp D.continuous))
  refine quasiconvexOn_iff_le_max.2 ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  -- `u ↦ ‖D u‖` is convex, so it is at most the max of its endpoint values on a segment.
  have hle : ‖D (a • x + b • y)‖ ≤ max ‖D x‖ ‖D y‖ :=
    (convexOn_univ_norm.comp_linearMap (D.restrictScalars ℝ : E →ₗ[ℝ] F)).le_on_segment'
      trivial trivial ha hb hab
  calc g ‖D (a • x + b • y)‖ ≤ g (max ‖D x‖ ‖D y‖) :=
        hg (norm_nonneg _) (le_max_of_le_left (norm_nonneg _)) hle
    _ = max (g ‖D x‖) (g ‖D y‖) := hg.map_max (norm_nonneg _) (norm_nonneg _)

/-- **Weak lower semicontinuity of quadratic energies.** For a bounded linear map `D`,
`u ↦ ‖D u‖ ^ 2` is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_norm_sq_comp_toWeakSpace_symm (D : E →L[𝕜] F) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ ‖D ((toWeakSpace 𝕜 E).symm u)‖ ^ 2 :=
  D.lowerSemicontinuous_comp_norm_comp_toWeakSpace_symm (g := fun r : ℝ ↦ r ^ 2)
    (fun _ hr _ _ hrs ↦ pow_le_pow_left₀ hr hrs 2) (continuous_pow 2).lowerSemicontinuous

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Weak lower semicontinuity of the norm.** -/
theorem lowerSemicontinuous_norm_comp_toWeakSpace_symm :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ ‖(toWeakSpace 𝕜 E).symm u‖ :=
  (ContinuousLinearMap.id 𝕜 E).lowerSemicontinuous_comp_norm_comp_toWeakSpace_symm
    monotoneOn_id continuous_id.lowerSemicontinuous

/-- **Weak lower semicontinuity of norm powers.** For `0 ≤ p`, `u ↦ ‖u‖ ^ p` is lower
semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm {p : ℝ} (hp : 0 ≤ p) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ ‖(toWeakSpace 𝕜 E).symm u‖ ^ p :=
  (ContinuousLinearMap.id 𝕜 E).lowerSemicontinuous_comp_norm_comp_toWeakSpace_symm
    (g := fun r : ℝ ↦ r ^ p) (fun _ hr _ _ hrs ↦ Real.rpow_le_rpow hr hrs hp)
    (Real.continuous_rpow_const hp).lowerSemicontinuous

end TauCeti
