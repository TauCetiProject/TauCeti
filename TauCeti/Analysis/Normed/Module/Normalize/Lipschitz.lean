/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Lipschitz radial maps

A radial map `y ↦ (ρ ‖y‖ / ‖y‖) • y` keeps the direction of `y` and replaces its length by
`|ρ ‖y‖|`. This file proves that it is Lipschitz on any normed space over `ℝ` or `ℂ` when its
profile `ρ` is Lipschitz on `[0, ∞)` and grows at most linearly from `ρ 0 = 0`
(`TauCeti.lipschitzWith_ofReal_div_norm_smul`).

The main example is the truncated power `TauCeti.truncPow`, the radial map with profile
`t ↦ min t N ^ s`, which is Lipschitz for `s ≥ 1` (`TauCeti.lipschitzWith_truncPow`). For `s = 1`
the map truncates the length of `y` at `N`; for `s = q - 1` it is a truncation of the map
`y ↦ ‖y‖ ^ (q - 2) • y`, whose pairing with `y` is `‖y‖ ^ q` (`TauCeti.inner_truncPow`).
Composing a function in `Lᵖ` with these Lipschitz maps vanishing at `0` gives continuous maps of
`Lᵖ` into itself (`LipschitzWith.compLp`), which is how truncated extremal functions for `L^q`
norms are produced continuously from the function they norm.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

section NormedSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A radial map `y ↦ (ρ ‖y‖ / ‖y‖) • y`, which keeps the direction of `y` and replaces its length
by `|ρ ‖y‖|`, is Lipschitz with constant `2 c + L` when the profile `ρ` is `L`-Lipschitz on
`[0, ∞)` and `|ρ t| ≤ c t` there. -/
theorem lipschitzWith_ofReal_div_norm_smul {ρ : ℝ → ℝ} {L c : ℝ≥0}
    (hρ : LipschitzOnWith L ρ (Ici 0)) (hc : ∀ t, 0 ≤ t → |ρ t| ≤ c * t) :
    LipschitzWith (2 * c + L) fun y : E ↦ ((ρ ‖y‖ / ‖y‖ : ℝ) : 𝕜) • y := by
  -- By symmetry it suffices to compare `x` and `y` with `‖y‖ ≤ ‖x‖`.
  have key (x y : E) (hyx : ‖y‖ ≤ ‖x‖) :
      ‖((ρ ‖x‖ / ‖x‖ : ℝ) : 𝕜) • x - ((ρ ‖y‖ / ‖y‖ : ℝ) : 𝕜) • y‖ ≤ (2 * c + L) * ‖x - y‖ := by
    have hab : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
    rcases (norm_nonneg x).eq_or_lt with hx | hx
    · have hx0 : x = 0 := norm_eq_zero.1 hx.symm
      have hy0 : y = 0 := norm_le_zero_iff.1 (hyx.trans hx.symm.le)
      simp [hx0, hy0]
    -- Write the difference as a multiple of `x - y` plus a multiple of `y`.
    have hsplit : ((ρ ‖x‖ / ‖x‖ : ℝ) : 𝕜) • x - ((ρ ‖y‖ / ‖y‖ : ℝ) : 𝕜) • y =
        ((ρ ‖x‖ / ‖x‖ : ℝ) : 𝕜) • (x - y) + ((ρ ‖x‖ / ‖x‖ - ρ ‖y‖ / ‖y‖ : ℝ) : 𝕜) • y := by
      rw [smul_sub, RCLike.ofReal_sub, sub_smul]
      abel
    have hρx : |ρ ‖x‖| / ‖x‖ ≤ c := (div_le_iff₀ hx).2 (hc _ hx.le)
    have h1 : ‖((ρ ‖x‖ / ‖x‖ : ℝ) : 𝕜) • (x - y)‖ ≤ c * ‖x - y‖ := by
      rw [norm_smul, RCLike.norm_ofReal, abs_div, abs_norm]
      gcongr
    have hLip : |ρ ‖x‖ - ρ ‖y‖| ≤ L * (‖x‖ - ‖y‖) := by
      have := hρ.dist_le_mul _ (mem_Ici.2 (norm_nonneg x)) _ (mem_Ici.2 (norm_nonneg y))
      rwa [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hyx)] at this
    have h2 : ‖((ρ ‖x‖ / ‖x‖ - ρ ‖y‖ / ‖y‖ : ℝ) : 𝕜) • y‖ ≤ (c + L) * ‖x - y‖ := by
      rcases (norm_nonneg y).eq_or_lt with hy | hy
      · rw [norm_smul, ← hy, mul_zero]
        positivity
      have heq : ‖((ρ ‖x‖ / ‖x‖ - ρ ‖y‖ / ‖y‖ : ℝ) : 𝕜) • y‖ =
          |(ρ ‖x‖ - ρ ‖y‖) - ρ ‖x‖ / ‖x‖ * (‖x‖ - ‖y‖)| := by
        rw [norm_smul, RCLike.norm_ofReal, ← abs_norm y, ← abs_mul, abs_norm]
        congr 1
        field_simp
        ring
      rw [heq]
      calc _ ≤ |ρ ‖x‖ - ρ ‖y‖| + |ρ ‖x‖ / ‖x‖ * (‖x‖ - ‖y‖)| := abs_sub _ _
        _ ≤ L * (‖x‖ - ‖y‖) + c * (‖x‖ - ‖y‖) := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hyx), abs_div, abs_norm]
          gcongr
        _ = (c + L) * (‖x‖ - ‖y‖) := by ring
        _ ≤ (c + L) * ‖x - y‖ := by gcongr
    rw [hsplit]
    calc _ ≤ c * ‖x - y‖ + (c + L) * ‖x - y‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = (2 * c + L) * ‖x - y‖ := by ring
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact key x y h
  · rw [norm_sub_rev, norm_sub_rev x]
    exact key y x h

variable (𝕜) in
/-- The truncated power `y ↦ (min ‖y‖ N ^ s / ‖y‖) • y`, which keeps the direction of `y` and
replaces its length by `min ‖y‖ N ^ s` (`TauCeti.norm_truncPow`). -/
noncomputable def truncPow (N : ℝ≥0) (s : ℝ) (y : E) : E :=
  ((min ‖y‖ N ^ s / ‖y‖ : ℝ) : 𝕜) • y

variable (𝕜) in
/-- The defining formula of the truncated power. -/
theorem truncPow_def (N : ℝ≥0) (s : ℝ) (y : E) :
    truncPow 𝕜 N s y = ((min ‖y‖ N ^ s / ‖y‖ : ℝ) : 𝕜) • y :=
  (rfl)

/-- The truncated power vanishes at `0`. -/
@[simp]
theorem truncPow_zero (N : ℝ≥0) (s : ℝ) : truncPow 𝕜 N s (0 : E) = 0 := by
  simp [truncPow_def]

/-- For `s > 0` the truncated power has length `min ‖y‖ N ^ s`. -/
theorem norm_truncPow (N : ℝ≥0) {s : ℝ} (hs : 0 < s) (y : E) :
    ‖truncPow 𝕜 N s y‖ = min ‖y‖ N ^ s := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Real.zero_rpow hs.ne']
  · have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have := le_min hy'.le N.property
    rw [truncPow_def, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hy'.ne']

/-- The truncated power `TauCeti.truncPow`, which replaces the length of `y` by `min ‖y‖ N ^ s`,
is Lipschitz for `s ≥ 1`, with constant `(2 + s) N ^ (s - 1)`. -/
theorem lipschitzWith_truncPow (N : ℝ≥0) {s : ℝ} (hs : 1 ≤ s) :
    LipschitzWith (2 * N ^ (s - 1) + s.toNNReal * N ^ (s - 1)) (truncPow 𝕜 N s : E → E) := by
  rw [show (truncPow 𝕜 N s : E → E) = fun y ↦ ((min ‖y‖ N ^ s / ‖y‖ : ℝ) : 𝕜) • y from
    funext (truncPow_def 𝕜 N s)]
  refine lipschitzWith_ofReal_div_norm_smul (ρ := fun t ↦ min t N ^ s) ?_ fun t ht ↦ ?_
  · -- `t ↦ t ^ s` is `s N ^ (s - 1)`-Lipschitz on `[0, N]`, into which `min · N` maps `[0, ∞)`.
    have hpow : LipschitzOnWith (s.toNNReal * N ^ (s - 1)) (fun t : ℝ ↦ t ^ s) (Icc 0 N) := by
      refine (convex_Icc (0 : ℝ) N).lipschitzOnWith_of_nnNorm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
        (f' := fun t ↦ s * t ^ (s - 1))
        (fun t _ ↦ (Real.hasDerivAt_rpow_const (Or.inr hs)).hasDerivWithinAt) fun t ht ↦ ?_
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_mul,
        Real.coe_toNNReal _ (by linarith), NNReal.coe_rpow]
      have := ht.1
      have := ht.2
      rw [abs_of_nonneg (by positivity)]
      gcongr
    have hmin : LipschitzOnWith 1 (fun t : ℝ ↦ min t N) (Ici 0) :=
      (LipschitzWith.id.min_const _).lipschitzOnWith
    simpa [Function.comp_def] using hpow.comp hmin fun t ht ↦ ⟨le_min ht N.property,
        min_le_right _ _⟩
  · have hm : 0 ≤ min t N := le_min ht N.property
    rw [abs_of_nonneg (by positivity), NNReal.coe_rpow]
    calc min t N ^ s = min t N ^ (s - 1) * min t N := by
          rw [← Real.rpow_add_one' hm (by linarith)]
          ring_nf
      _ ≤ (N : ℝ) ^ (s - 1) * t := by
          have := min_le_left t N
          have := min_le_right t N
          gcongr

end NormedSpace

section InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

/-- The pairing of `y` with its truncated power is `‖y‖ min ‖y‖ N ^ s`. -/
theorem inner_truncPow (N : ℝ≥0) (s : ℝ) (y : E) :
    ⟪y, truncPow 𝕜 N s y⟫_𝕜 = ((‖y‖ * min ‖y‖ N ^ s : ℝ) : 𝕜) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [truncPow_def, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul]
    congr 1
    field_simp

end InnerProductSpace

end TauCeti
