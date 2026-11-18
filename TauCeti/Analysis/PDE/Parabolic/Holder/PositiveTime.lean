/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
public import TauCeti.Analysis.PDE.Parabolic.Holder.TemporalCutoff

/-!
# Positive-time estimates for the parabolic Cauchy problem

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in `C_b^{α,α/2}`, `0 < α < 1`, with `a` uniformly elliptic. The global Schauder
estimate (`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`) bounds the
order-two norm of `u ∈ C_b^{2+α,1+α/2}` by `P u` and by the `C_b^{2,α}` norm of the initial value
`u(·, 0)`. Away from the initial time the supremum of `u(·, 0)` suffices: this file proves the
**positive-time estimate**

`δ^(1 + α/2) ‖u‖_{2+α,par; [δ, T]} ≤ C (sup |u(·, 0)| + ‖P u‖_{α,par})` for `0 < δ < T`

(`TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le`), where
`‖u‖_{2+α,par; [δ, T]}` is the order-two norm of the restriction of `u` to `ℝⁿ × [δ, T]`, and `C`
depends only on the dimension, `α`, the ellipticity constants, a bound on the Hölder norms of the
coefficients and a bound on the horizon. The weight `δ^(1 + α/2)` is the parabolic order of the
top-order seminorms `[D_x² u]_{α,par}` and `[∂ₜ u]_{α,par}`. Since the right-hand side sees only
the supremum of the initial value, the estimate is uniform along approximations of a bounded
uniformly continuous initial value by smooth ones.

## The argument

* **Time cutoff.** A cutoff `χ` (`TauCeti.ParabolicC2HolderSpace.exists_temporal_cutoff`)
  vanishing up to time `δ / 2` and equal to one from time `δ` on does not depend on the spatial
  variable, so `P (χ u) = χ P u + (∂ₜ χ) u`
  (`TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_mul_eq_of_spatialFDerivL_eq_zero`).
  As `χ u` vanishes at the initial time and equals `u` on `[δ, T]`, the Schauder estimate bounds
  the norm of `u` on `[δ, T]` by `‖χ‖ ‖P u‖` and the Hölder norm of `(∂ₜ χ) u`.
* **The cutoff error.** Since `∂ₜ χ` vanishes before `δ / 2`, the Hölder norm of `(∂ₜ χ) u` sees
  the Hölder norm of `u` on `[δ / 2, T]` only
  (`ContinuousLinearMap.norm_compHolder₂_valueHolderL_le_of_eq_zero`). Interpolation at the spatial
  scale `ρ = √(κ δ)` (`TauCeti.ParabolicC2HolderSpace.norm_valueHolderL_le_add_sq_mul`) bounds
  that norm by a multiple of `(κ δ)^(-α/2) sup |u|` plus `2 κ δ` times the order-two norm of `u`
  on `[δ / 2, T]`.
* **Absorption.** With `‖∂ₜ χ‖_∞ ≲ δ⁻¹` and `[∂ₜ χ]_{α,par} ≲ δ^(-1 - α/2)`, the weighted norm
  `Φ(δ) = δ^(1 + α/2) ‖u‖_{2+α,par; [δ, T]}` satisfies
  `Φ(δ) ≤ C (sup |u| + ‖P u‖) + Φ(δ / 2) / 2` for `κ` small. The function `Φ` is bounded by
  `T^(1 + α/2) ‖u‖`, so its supremum absorbs the last term. Finally the comparison principle
  (`norm_valueL_le_exp_mul_mul_add_norm_euclideanParabolicOperatorL`) bounds `sup |u|` by
  `sup |u(·, 0)|` and `‖P u‖_∞`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le`: **the positive-time
  estimate**.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4
  (time localization of parabolic estimates).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

section Euclidean

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ} {hT : 0 < T}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}

/-- **Schauder estimate after a temporal cutoff.** Let `C_S` be a constant of the Schauder estimate
on `ℝⁿ × [0, T]`, and let `χ` be a spatially constant cutoff vanishing up to time `s > 0`, equal to
one from time `δ < T` on. Then the restriction of `u` to `[δ, T]` is bounded by the Hölder norms of
`χ` and `∂ₜ χ`, by `P u`, by the supremum of `u`, and by the parabolic Hölder norm of `u` on
`[s, T]` only. -/
private theorem norm_restrictL_le_of_temporal_cutoff (hα : α ≤ 1) {C_S : ℝ} (hC_S : 0 ≤ C_S)
    (hS : ∀ v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ‖v‖ ≤ C_S * (‖euclideanParabolicOperatorL hα a b c v‖ +
        ‖v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖))
    {χ : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT} {s δ : ℝ} (hs : 0 < s) (hsδ : s ≤ δ)
    (hδT : δ < T)
    (hχ0 : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time ≤ s → χ p = 0)
    (hχ1 : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      δ ≤ (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time → χ p = 1)
    (hχt : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time < s → timeDerivL χ p = 0)
    (hχx : spatialFDerivL χ = 0) (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    ‖restrictL (hs.le.trans hsδ) le_rfl hδT u‖ ≤ C_S * (‖valueHolderL hα χ‖ *
        ‖euclideanParabolicOperatorL hα a b c u‖ +
      (‖(timeDerivL χ).toBoundedContinuousFunction‖ *
          ‖valueHolderL hα (restrictL hs.le le_rfl (hsδ.trans_lt hδT) u)‖ +
        nnHolderNorm α (timeDerivL χ : slab (E := EuclideanSpace ℝ ι) 0 T → ℝ) * ‖valueL u‖)) := by
  set v := (ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u
  -- On `[δ, T]` the product `χ u` is `u`, and it vanishes at the initial time.
  have hres : restrictL (hs.le.trans hsδ) le_rfl hδT u =
      restrictL (hs.le.trans hsδ) le_rfl hδT v := by
    ext p
    have h := hχ1 (inclusion (slab_subset_slab (hs.le.trans hsδ) le_rfl) p) (mem_slab.1 p.2).1
    simp [v, h]
  have htr : v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 :=
    CkHolderSpace.ext fun x ↦ by
      have h := hχ0 (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) (by rw [time_slabMk]; exact hs.le)
      simp [v, spatialTrace_apply, h]
  have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have h₁ := (ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_apply_le (valueHolderL hα χ)
    (euclideanParabolicOperatorL hα a b c u)
  have h₂ := (ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_valueHolderL_le_of_eq_zero hα hs.le
    (hsδ.trans_lt hδT) hχt u
  rw [hres]
  refine (norm_restrictL_le _ _ _ v).trans ((hS v).trans ?_)
  rw [htr, norm_zero, add_zero, euclideanParabolicOperatorL_def,
    parabolicOperatorL_mul_eq_of_spatialFDerivL_eq_zero hα _ _ _ χ u hχx,
    ← euclideanParabolicOperatorL_def]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hC_S
  · exact h₁.trans (by gcongr; exact mul_le_of_le_one_left (norm_nonneg _) hmul)
  · exact h₂.trans (mul_le_of_le_one_left (by positivity) hmul)

omit [DecidableEq ι] in
/-- Interpolation for `u` on `[d, T]` at the time scale `2 κ d`: the parabolic Hölder norm of the
value of `u` there is bounded by the supremum of `u` and by `4 κ d` times the order-two norm of `u`
on `[d, T]`. -/
private theorem norm_valueHolderL_restrictL_le (hα : α ≤ 1) {κ d : ℝ} (hκ : 0 < κ)
    (hκ₄ : κ ≤ 1 / 4) (hd : 0 < d) (hdT : 2 * d < T)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    ‖valueHolderL hα (restrictL hd.le le_rfl (by linarith : d < T) u)‖ ≤
      (1 + 40 * ((2 * κ) ^ (-((α : ℝ) / 2)) / d ^ ((α : ℝ) / 2))) * ‖valueL u‖ +
        4 * κ * d * ‖restrictL hd.le le_rfl (by linarith : d < T) u‖ := by
  set w := restrictL (α := α) (F := ℝ) (hab := hT) hd.le le_rfl (by linarith : d < T) u
  set ρ := √(2 * κ * d) with hρ_def
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hρ2 : ρ ^ 2 = 2 * κ * d := Real.sq_sqrt (by positivity)
  have hρα : ρ ^ (-(α : ℝ)) = (2 * κ) ^ (-((α : ℝ) / 2)) / d ^ ((α : ℝ) / 2) := by
    rw [hρ_def, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by positivity) hd.le, show 1 / 2 * -(α : ℝ) = -((α : ℝ) / 2) by ring,
      Real.rpow_neg hd.le]
    exact (div_eq_mul_inv _ _).symm
  have hW := norm_valueHolderL_le_add_sq_mul hα w hρ (by rw [hρ2]; nlinarith)
  have hwV : ‖valueL w‖ ≤ ‖valueL u‖ := norm_valueL_restrictL_le u
  have hwY : (nnHolderNorm α ((spatialSecondFDerivL w).toBoundedContinuousFunction : _ → _) : ℝ) +
      nnHolderNorm α ((timeDerivL w).toBoundedContinuousFunction : _ → _) ≤ ‖w‖ := by
    have := norm_def w
    linarith [norm_nonneg (valueL w), norm_nonneg (spatialFDerivL w),
      norm_nonneg (spatialSecondFDerivL w).toBoundedContinuousFunction,
      norm_nonneg (timeDerivL w).toBoundedContinuousFunction]
  rw [hρα, hρ2] at hW
  refine hW.trans ?_
  have : 0 ≤ 1 + 40 * ((2 * κ) ^ (-((α : ℝ) / 2)) / d ^ ((α : ℝ) / 2)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hwV this, mul_le_mul_of_nonneg_left hwY
    (by positivity : (0 : ℝ) ≤ 2 * (2 * κ * d))]

/-- The weighted arithmetic of one step of the positive-time estimate: the bound for the norm
`X` on `[2 d, T]` from `norm_restrictL_le_of_temporal_cutoff`, multiplied by the weight
`(2 d)^(1 + α/2)`, in terms of the weighted norm `d^(1 + α/2) Y` on `[d, T]`. -/
private theorem rpow_mul_le_of_le {α C_S Mχ κ T₀ d X Y P V : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 1)
    (hC_S : 0 ≤ C_S) (hMχ : 0 ≤ Mχ) (hκ : 0 < κ) (hd : 0 < d) (hdT₀ : d ≤ T₀) (hY : 0 ≤ Y)
    (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hX : X ≤ C_S * (24 * (1 + Mχ / d + Mχ * d ^ (-1 - α / 2)) * P +
      (Mχ / d * ((1 + 40 * ((2 * κ) ^ (-(α / 2)) / d ^ (α / 2))) * V + 4 * κ * d * Y) +
        Mχ * d ^ (-1 - α / 2) * V))) :
    (2 * d) ^ (1 + α / 2) * X ≤
      C_S * (96 * (T₀ ^ (1 + α / 2) + Mχ * T₀ ^ (α / 2) + Mχ) * P +
        4 * Mχ * (1 + T₀ ^ (α / 2) + 40 * (2 * κ) ^ (-(α / 2))) * V) +
      16 * C_S * Mχ * κ * (d ^ (1 + α / 2) * Y) := by
  set k := (2 * κ) ^ (-(α / 2))
  set e := d ^ (α / 2)
  have he : 0 < e := by positivity
  have hk : 0 ≤ k := by positivity
  have hde : d ^ (1 + α / 2) = d * e := by rw [Real.rpow_add hd, Real.rpow_one]
  have hde' : d ^ (-1 - α / 2) = (d * e)⁻¹ := by
    rw [show -1 - α / 2 = -(1 + α / 2) by ring, Real.rpow_neg hd.le, hde]
  have hc₂ : (2 : ℝ) ^ (1 + α / 2) ≤ 4 :=
    (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith : 1 + α / 2 ≤ 2)).trans_eq
      (by norm_num)
  have hT₁ : d * e ≤ T₀ ^ (1 + α / 2) := by
    rw [← hde]
    exact Real.rpow_le_rpow hd.le hdT₀ (by positivity)
  have hT₂ : e ≤ T₀ ^ (α / 2) := Real.rpow_le_rpow hd.le hdT₀ (by positivity)
  have e₁ : d * e * (24 * (1 + Mχ / d + Mχ * (d * e)⁻¹)) = 24 * (d * e + Mχ * e + Mχ) := by
    field_simp
  have e₂ : d * e * (Mχ / d * ((1 + 40 * (k / e)) * V + 4 * κ * d * Y)) =
      Mχ * (e + 40 * k) * V + 4 * Mχ * κ * (d * e) * Y := by
    field_simp
  have e₃ : d * e * (Mχ * (d * e)⁻¹ * V) = Mχ * V := by field_simp
  rw [hde'] at hX
  rw [Real.mul_rpow zero_le_two hd.le, hde]
  calc 2 ^ (1 + α / 2) * (d * e) * X
      ≤ 2 ^ (1 + α / 2) * (d * e) * (C_S * (24 * (1 + Mχ / d + Mχ * (d * e)⁻¹) * P +
          (Mχ / d * ((1 + 40 * (k / e)) * V + 4 * κ * d * Y) + Mχ * (d * e)⁻¹ * V))) := by
        gcongr
    _ = 2 ^ (1 + α / 2) * C_S * (24 * (d * e + Mχ * e + Mχ) * P +
          (Mχ * (e + 40 * k) * V + 4 * Mχ * κ * (d * e) * Y + Mχ * V)) := by
        rw [← e₁, ← e₂, ← e₃]
        ring
    _ ≤ 4 * C_S * (24 * (T₀ ^ (1 + α / 2) + Mχ * T₀ ^ (α / 2) + Mχ) * P +
          (Mχ * (T₀ ^ (α / 2) + 40 * k) * V + 4 * Mχ * κ * (d * e) * Y + Mχ * V)) := by
        gcongr
    _ = _ := by ring

/-- **One step of the weighted estimate.** With the Schauder constant `C_S`, a cutoff `χ` rising
from `0` to `1` on `[δ / 2, δ]` with constant `Mχ`, and `0 < κ ≤ 1/4`, the weighted norm of `u` on
`[δ, T]` is bounded by `P u`, the supremum of `u` and `16 C_S Mχ κ` times the weighted norm on
`[δ / 2, T]`. -/
private theorem rpow_mul_norm_restrictL_le_of_cutoff (hα : α ≤ 1) {C_S Mχ κ T₀ : ℝ}
    (hC_S : 0 ≤ C_S) (hMχ : 0 ≤ Mχ) (hκ : 0 < κ) (hκ₄ : κ ≤ 1 / 4) (hTT₀ : T ≤ T₀)
    (hS : ∀ v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ‖v‖ ≤ C_S * (‖euclideanParabolicOperatorL hα a b c v‖ +
        ‖v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖))
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T) {χ : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT}
    (hχ0 : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time ≤ δ / 2 → χ p = 0)
    (hχ1 : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      δ / 2 + δ / 2 ≤ (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time → χ p = 1)
    (hχt : ∀ p, timeDerivL χ p = (δ / 2)⁻¹ * deriv Real.smoothTransition
      (((p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time - δ / 2) / (δ / 2)))
    (hχx : spatialFDerivL χ = 0)
    (hχs : ‖(timeDerivL χ).toBoundedContinuousFunction‖ ≤ Mχ / (δ / 2))
    (hχh : (nnHolderNorm α (timeDerivL χ : slab (E := EuclideanSpace ℝ ι) 0 T → ℝ) : ℝ) ≤
      Mχ * (δ / 2) ^ (-1 - (α : ℝ) / 2))
    (hχn : ‖χ‖ ≤ 1 + Mχ / (δ / 2) + Mχ * (δ / 2) ^ (-1 - (α : ℝ) / 2))
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤
      C_S * (96 * (T₀ ^ (1 + (α : ℝ) / 2) + Mχ * T₀ ^ ((α : ℝ) / 2) + Mχ) *
          ‖euclideanParabolicOperatorL hα a b c u‖ +
        4 * Mχ * (1 + T₀ ^ ((α : ℝ) / 2) + 40 * (2 * κ) ^ (-((α : ℝ) / 2))) * ‖valueL u‖) +
      16 * C_S * Mχ * κ * ((δ / 2) ^ (1 + (α : ℝ) / 2) *
        ‖restrictL (half_pos hδ).le le_rfl ((half_lt_self hδ).trans hδT) u‖) := by
  have hd : 0 < δ / 2 := half_pos hδ
  -- The cutoff is constant before `δ / 2`.
  have hχt0 : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time < δ / 2 → timeDerivL χ p = 0 :=
    fun p hp ↦ by
      rw [hχt, Real.smoothTransition.deriv_of_neg (div_neg_of_neg_of_pos (sub_neg.2 hp) hd),
        mul_zero]
  have hK1 := norm_restrictL_le_of_temporal_cutoff hα hC_S hS hd (half_le_self hδ.le) hδT hχ0
    (fun p hp ↦ hχ1 p (by linarith)) hχt0 hχx u
  have hW := norm_valueHolderL_restrictL_le hα hκ hκ₄ hd (by linarith) u
  have hχv := (norm_valueHolderL_le_mul hα χ).trans (mul_le_mul_of_nonneg_left hχn (by norm_num))
  have h := rpow_mul_le_of_le (α := α) (T₀ := T₀) α.coe_nonneg hα hC_S hMχ hκ hd (by linarith)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hK1.trans (by gcongr))
  refine (le_of_eq ?_).trans (h.trans (le_of_eq ?_))
  · rw [show 2 * (δ / 2) = δ by ring]
  -- `h` and the goal pass different proofs of `0 ≤ δ / 2` and `δ / 2 < T` to `restrictL`.
  -- Unifying them directly unfolds the norm of the irreducible space and fails, so `congr`
  -- identifies them.
  · congr 2

end Euclidean

section Weighted

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {lam Lam : ℝ}

/-- The interpolation scale `κ` of the positive-time estimate: small enough that the weighted
norm on the larger slab is absorbed with factor `1 / 2`. -/
private theorem exists_absorbing_scale {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ 16 * C * M * κ ≤ 1 / 2 := by
  have := mul_nonneg hC hM
  refine ⟨(4 + 32 * (C * M))⁻¹, by positivity, ?_, ?_⟩
  · rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  · rw [mul_assoc 16, ← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith

/-- **The positive-time Schauder estimate.** Let `0 < α < 1`, `0 < λ`, and let `K` and `T₀` bound
the Hölder norms of the coefficients and the horizon. There is a constant `C`, depending only on
these, on `Λ` and on the dimension, with the following property. Let
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` on `ℝⁿ × [0, T]`, `T ≤ T₀`, have coefficients in
`C_b^{α,α/2}` with `λ ‖ξ‖² ≤ ξᵀ a ξ ≤ Λ ‖ξ‖²` and Hölder norms at most `K`, and let
`u ∈ C_b^{2+α,1+α/2}` satisfy `|u(·, 0)| ≤ M`. Then for every `0 < δ < T`,

`δ^(1 + α/2) ‖u‖_{2+α,par; [δ, T]} ≤ C (M + ‖P u‖_{α,par})`,

where `‖u‖_{2+α,par; [δ, T]}` is the order-two norm of the restriction of `u` to `ℝⁿ × [δ, T]`.
Only the supremum of the initial value enters, not its `C_b^{2,α}` norm. -/
theorem exists_rpow_mul_norm_restrictL_le (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
          (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
          ∀ {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T),
            δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤
              C * (M + ‖euclideanParabolicOperatorL hα₁.le a b c u‖) := by
  obtain ⟨C_S, hC_S, hS⟩ :=
    exists_norm_le_euclideanParabolicOperatorL (ι := ι) (Lam := Lam) hα₀ hα₁ hlam K T₀
  obtain ⟨Mχ, hMχ, hcut⟩ :=
    exists_temporal_cutoff (α := α) (E := EuclideanSpace ℝ ι) (hα₁.le.trans (by norm_num))
  -- The time scale `κ δ` of the interpolation, small enough to absorb the weighted norm.
  obtain ⟨κ, hκ, hκ₄, hκ₂⟩ := exists_absorbing_scale hC_S hMχ
  set A := 96 * ((T₀ : ℝ) ^ (1 + (α : ℝ) / 2) + Mχ * (T₀ : ℝ) ^ ((α : ℝ) / 2) + Mχ)
  set B := 4 * Mχ * (1 + (T₀ : ℝ) ^ ((α : ℝ) / 2) + 40 * (2 * κ) ^ (-((α : ℝ) / 2)))
  set E₀ := Real.exp (K * T₀) * (1 + T₀)
  refine ⟨2 * C_S * (A + B * E₀), by positivity,
    fun T hT hTT₀ a b c ha ha' hak hbk hck u M hM δ hδ hδT ↦ ?_⟩
  set P := ‖euclideanParabolicOperatorL hα₁.le a b c u‖
  set V := ‖valueL u‖
  have hV : V ≤ E₀ * (M + P) := norm_valueL_le_exp_mul_mul_add_norm_euclideanParabolicOperatorL
    hα₁.le hTT₀ (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha q ξ)) hck u hM
  -- The weighted norms on the slabs `[d, T]`, bounded by `T₀^(1 + α/2) ‖u‖`.
  set Φ : Ioo (0 : ℝ) T → ℝ := fun d ↦
    (d : ℝ) ^ (1 + (α : ℝ) / 2) * ‖restrictL d.2.1.le le_rfl d.2.2 u‖
  have hΦ : BddAbove (range Φ) := ⟨(T₀ : ℝ) ^ (1 + (α : ℝ) / 2) * ‖u‖, by
    rintro _ ⟨d, rfl⟩
    exact mul_le_mul (Real.rpow_le_rpow d.2.1.le (d.2.2.le.trans (by exact_mod_cast hTT₀))
      (by positivity)) (norm_restrictL_le _ _ _ u) (norm_nonneg _) (by positivity)⟩
  have hstep (d : Ioo (0 : ℝ) T) : Φ d ≤ C_S * (A * P + B * V) +
      16 * C_S * Mχ * κ * Φ ⟨d / 2, half_pos d.2.1, (half_lt_self d.2.1).trans d.2.2⟩ := by
    -- The cutoff rises from `0` to `1` on `[d / 2, d]`.
    obtain ⟨χ, -, hχt, -, hχ0, hχ1, hχx, -, hχs, hχh, hχn⟩ := hcut (half_pos d.2.1) (d / 2) 0 T hT
    -- `Φ` and this bound pass different proofs of `0 ≤ d / 2` and `d / 2 < T` to `restrictL`.
    -- Unifying them directly unfolds the norm of the irreducible space and fails, so `convert`
    -- identifies them.
    convert rpow_mul_norm_restrictL_le_of_cutoff hα₁.le hC_S hMχ hκ hκ₄
      (show (T : ℝ) ≤ T₀ by exact_mod_cast hTT₀) (hS T hT hTT₀ a b c ha ha' hak hbk hck)
      d.2.1 d.2.2 hχ0 hχ1 hχt hχx hχs hχh hχn u using 3
  have : Nonempty (Ioo (0 : ℝ) T) := ⟨⟨T / 2, half_pos hT, half_lt_self hT⟩⟩
  -- As in `hstep`, `convert` identifies the proofs passed to `restrictL`.
  calc δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤ ⨆ d, Φ d := by
        convert le_ciSup hΦ ⟨δ, hδ, hδT⟩ using 1
    _ ≤ 2 * (C_S * (A * (M + P) + B * (E₀ * (M + P)))) :=
        (TauCeti.ciSup_le_two_mul_of_le_add_mul hΦ
          (fun d ↦ mul_nonneg (Real.rpow_nonneg d.2.1.le _) (norm_nonneg _)) hκ₂ _ hstep).trans
          (by gcongr; linarith [(abs_nonneg _).trans (hM 0)])
    _ = 2 * C_S * (A + B * E₀) * (M + P) := by ring

end Weighted

end TauCeti.ParabolicC2HolderSpace
