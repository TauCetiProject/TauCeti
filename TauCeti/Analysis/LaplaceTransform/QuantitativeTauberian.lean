/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Complex.Taylor.RapidDecay
import TauCeti.Analysis.LaplaceTransform.PostWidder

/-!
# A quantitative Tauberian theorem for Laplace transforms

`TauCeti.eventually_norm_le_inv_pow_of_hasLaplace_dslope` gives inverse-power decay of every
order for a Lipschitz function whose Laplace transform continues as a divided difference in
a logarithmic region. It combines the Cauchy estimate
`eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow` with the Post–Widder approximation
`norm_smul_iteratedDeriv_sub_le_of_hasLaplace`.

The estimate is `New.eventually_abs_le_inv_pow_of_transform` in
`grh/src/Lib/Analytic/PrimeNumberTheorem/Tauberian.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`
(Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Filter Set
open scoped Nat NNReal Topology

namespace TauCeti

/-- If the Laplace transform of a function Lipschitz on `[0, ∞)` agrees on a right half-plane
with the translated divided difference `z ↦ dslope F 1 (1 + z)`, and `F` is holomorphic with
polylogarithmic growth on the expanding regions `Re z ≥ 1 - 1 / l ^ A`, `‖z‖ ≤ exp l`, then
the function decays faster than every inverse power at infinity. -/
theorem eventually_norm_le_inv_pow_of_hasLaplace_dslope {f : ℝ → ℂ} {F : ℂ → ℂ}
    {K : ℝ≥0} {a : ℝ} {A : ℕ} (hf : LipschitzOnWith K f (Ici 0))
    (hLaplace : ∀ z : ℂ, a < z.re → HasLaplace f z (dslope F 1 (1 + z)))
    (hF : ∀ᶠ l : ℝ in atTop, ∀ z : ℂ, 1 - 1 / l ^ A ≤ z.re → ‖z‖ ≤ Real.exp l →
      DifferentiableAt ℂ F z ∧ ‖F z‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ (u ^ B)⁻¹ := by
  filter_upwards [eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow hF
    (2 * B + 3) (B + 1), eventually_gt_atTop (max 1 a), eventually_ge_atTop (1 + (K : ℝ))]
    with u hC hu huK
  dsimp only at hC
  set k := ⌊u ^ (2 * B + 3 + 1)⌋₊
  set H : ℝ := (k + 1 : ℝ) / u with hH
  have hu₁ := lt_of_le_of_lt (le_max_left 1 a) hu
  have hu₀ := zero_lt_one.trans hu₁
  have hfloor : u ^ (2 * B + 3 + 1) < (k + 1 : ℝ) := Nat.lt_floor_add_one _
  have hk₂ : u ^ 2 ≤ u ^ (2 * B + 3 + 1) := pow_le_pow_right₀ hu₁.le (by lia)
  have huH : u < H := (lt_div_iff₀ hu₀).mpr (by simpa only [pow_two] using hk₂.trans_lt hfloor)
  have hcenter : ((k + 1 : ℕ) : ℝ) / H = u := by
    rw [Nat.cast_add, Nat.cast_one, hH, div_div_cancel₀ (by positivity)]
  have hloc : ∀ᶠ z in 𝓝 (H : ℂ), HasLaplace f z (dslope F 1 (1 + z)) :=
    (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      (by simpa only [mem_ofPred_eq, Complex.ofReal_re] using
        (lt_of_le_of_lt (le_max_right 1 a) hu).trans huH) |>.mono fun z hz ↦ hLaplace z hz
  let c : ℂ := ((-(H : ℂ)) ^ k * H / k.factorial) • iteratedDeriv k (dslope F 1) (1 + ↑H)
  have happrox := norm_smul_iteratedDeriv_sub_le_of_hasLaplace (hu₀.trans huH) hloc hf k
  have hcoeff : (H : ℂ) ^ (k + 1) * (-1) ^ k / k.factorial =
      (-(H : ℂ)) ^ k * H / k.factorial := by rw [neg_pow, pow_succ]; ring
  rw [iteratedDeriv_comp_const_add, hcoeff, hcenter] at happrox
  have hroot : u ^ (B + 2) ≤ √(k + 1 : ℕ) := by
    have hexponent : 2 * B + 3 + 1 = (B + 2) * 2 := by lia
    rw [← Real.sqrt_sq (x := u ^ (B + 2)) (by positivity), ← pow_mul, ← hexponent]
    exact Real.sqrt_le_sqrt (by simpa only [Nat.cast_add, Nat.cast_one] using hfloor.le)
  have herror : ‖c - f u‖ ≤ (K : ℝ) * (u ^ (B + 1))⁻¹ := calc
    _ ≤ (K : ℝ) * √(k + 1 : ℕ) / H := happrox
    _ = (K : ℝ) * u / √(k + 1 : ℕ) := by
      rw [hH, Nat.cast_add, Nat.cast_one, div_div_eq_mul_div]
      calc
        _ = ((K : ℝ) * u * √(k + 1 : ℝ)) / (√(k + 1 : ℝ) * √(k + 1 : ℝ)) := by
          rw [Real.mul_self_sqrt (by positivity)]
          ring
        _ = _ := mul_div_mul_right _ _ (by positivity)
    _ ≤ (K : ℝ) * u / u ^ (B + 2) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hu₀ _) hroot
    _ = _ := by
      rw [pow_succ, div_mul_eq_div_div_swap, mul_div_cancel_right₀ _ hu₀.ne', div_eq_mul_inv]
  calc
    ‖f u‖ ≤ ‖c‖ + ‖c - f u‖ := by
      rw [norm_sub_rev c (f u), add_comm]
      exact norm_le_norm_sub_add (f u) c
    _ ≤ (1 + (K : ℝ)) * (u ^ (B + 1))⁻¹ := by
      rw [add_mul, one_mul]
      exact add_le_add hC herror
    _ ≤ (u ^ B)⁻¹ := calc
      _ ≤ u * (u ^ (B + 1))⁻¹ := by gcongr
      _ = _ := by rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hu₀.ne', one_mul]

end TauCeti
