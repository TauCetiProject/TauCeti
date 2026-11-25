/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic

/-!
# Weak lower semicontinuity of norm energies

Let `E` and `F` be normed spaces over `𝕜 = ℝ` or `ℂ`, let `D : E →L[𝕜] F` be bounded and let
`g : ℝ → β` be lower semicontinuous and monotone on `[0, ∞)`. The energy `u ↦ g ‖D u‖` is lower
semicontinuous for the weak topology of `E`
(`TauCeti.lowerSemicontinuous_comp_norm_clm_comp_toWeakSpace_symm`). Its sublevel sets are
convex, since `‖D (a u + b v)‖ ≤ max ‖D u‖ ‖D v‖` for a convex combination and `g` is monotone,
so it is quasiconvex and `QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm` applies.

The instances are the norm `‖u‖`, the norm powers `‖u‖ ^ p` for `0 ≤ p`, and the quadratic energy
`‖D u‖ ^ 2` of a bounded linear map `D`. For a complex space, convexity is real convexity: the
real scalar structure enters only through the convex combinations.

## Main results

* `TauCeti.lowerSemicontinuous_comp_norm_clm_comp_toWeakSpace_symm`: `u ↦ g ‖D u‖` is weakly lower
  semicontinuous.
* `TauCeti.lowerSemicontinuous_norm_comp_toWeakSpace_symm`: the norm is weakly lower
  semicontinuous.
* `TauCeti.lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm`: so is `‖u‖ ^ p` for `0 ≤ p`.
* `TauCeti.lowerSemicontinuous_norm_clm_sq_comp_toWeakSpace_symm`: so is `‖D u‖ ^ 2`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Corollary 3.9.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E F β : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Weak lower semicontinuity of norm energies.** For a bounded linear map `D` and a lower
semicontinuous `g` that is monotone on `[0, ∞)`, the energy `u ↦ g ‖D u‖` is lower
semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_comp_norm_clm_comp_toWeakSpace_symm [LinearOrder β]
    (D : E →L[𝕜] F) {g : ℝ → β} (hg : MonotoneOn g (Ici 0)) (hlsc : LowerSemicontinuous g) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ g ‖D ((toWeakSpace 𝕜 E).symm u)‖ := by
  -- The real scalar structure only serves to form convex combinations.
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  refine QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm (f := fun u ↦ g ‖D u‖) ?_
    (hlsc.comp (continuous_norm.comp D.continuous))
  refine quasiconvexOn_iff_le_max.2 ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have hle : ‖D (a • x + b • y)‖ ≤ max ‖D x‖ ‖D y‖ := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) a x, RCLike.real_smul_eq_coe_smul (K := 𝕜) b y,
      map_add, map_smul, map_smul]
    calc ‖(a : 𝕜) • D x + (b : 𝕜) • D y‖ ≤ a * ‖D x‖ + b * ‖D y‖ := by
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * max ‖D x‖ ‖D y‖ + b * max ‖D x‖ ‖D y‖ := by gcongr <;> simp
      _ = max ‖D x‖ ‖D y‖ := by rw [← add_mul, hab, one_mul]
  calc g ‖D (a • x + b • y)‖ ≤ g (max ‖D x‖ ‖D y‖) :=
        hg (norm_nonneg _) (le_max_of_le_left (norm_nonneg _)) hle
    _ = max (g ‖D x‖) (g ‖D y‖) := hg.map_max (norm_nonneg _) (norm_nonneg _)

/-- **Weak lower semicontinuity of the norm.** -/
theorem lowerSemicontinuous_norm_comp_toWeakSpace_symm :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ ‖(toWeakSpace 𝕜 E).symm u‖ :=
  lowerSemicontinuous_comp_norm_clm_comp_toWeakSpace_symm (ContinuousLinearMap.id 𝕜 E)
    monotoneOn_id continuous_id.lowerSemicontinuous

/-- **Weak lower semicontinuity of norm powers.** For `0 ≤ p`, `u ↦ ‖u‖ ^ p` is lower
semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm {p : ℝ} (hp : 0 ≤ p) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ ‖(toWeakSpace 𝕜 E).symm u‖ ^ p :=
  lowerSemicontinuous_comp_norm_clm_comp_toWeakSpace_symm (g := fun r : ℝ ↦ r ^ p)
    (ContinuousLinearMap.id 𝕜 E) (fun _ hr _ _ hrs ↦ Real.rpow_le_rpow hr hrs hp)
    (Real.continuous_rpow_const hp).lowerSemicontinuous

/-- **Weak lower semicontinuity of quadratic energies.** For a bounded linear map `D`,
`u ↦ ‖D u‖ ^ 2` is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_norm_clm_sq_comp_toWeakSpace_symm (D : E →L[𝕜] F) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ ‖D ((toWeakSpace 𝕜 E).symm u)‖ ^ 2 :=
  lowerSemicontinuous_comp_norm_clm_comp_toWeakSpace_symm (g := fun r : ℝ ↦ r ^ 2) D
    (fun _ hr _ _ hrs ↦ pow_le_pow_left₀ hr hrs 2) (continuous_pow 2).lowerSemicontinuous

end TauCeti
