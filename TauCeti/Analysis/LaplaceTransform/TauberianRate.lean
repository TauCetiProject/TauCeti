/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.Lipschitz
import TauCeti.Analysis.LaplaceTransform.PostWidder
import TauCeti.Analysis.Complex.Taylor.RapidDecay

/-!
# A quantitative Tauberian theorem for Laplace transforms

Suppose the Laplace transform of a function on the positive ray is given by a shifted divided
difference of a holomorphic function with polylogarithmic growth in a logarithmically shrinking
region. Lipschitz control on the positive ray then gives decay faster than every inverse power.
This form applies to remainders in logarithmic coordinates when the holomorphic function is
built from logarithmic derivatives of L-functions.

The proof combines the Post–Widder approximation (D. V. Widder, *The Laplace Transform*,
Chapter VII) with a Cauchy estimate for the coefficient at a growing degree, as in
`New.eventually_abs_le_inv_pow_of_transform` in lsernau/grh-lean (revision `72fead1`),
`grh/src/Lib/Analytic/PrimeNumberTheorem/Tauberian.lean`.
-/

public section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti

private theorem postWidder_error_le {f : ℝ → ℂ} {F : ℂ → ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Ici 0))
    (hL : ∀ z : ℂ, 1 < z.re → HasLaplace f z (dslope F 1 (1 + z)))
    (B : ℕ) {u : ℝ} (hu : 0 < u) :
    let k := ⌊u ^ (2 * B + 3 + 1)⌋₊
    let H : ℝ := (k + 1 : ℝ) / u
    ‖((-(H : ℂ)) ^ k * H / k.factorial) • iteratedDeriv k (dslope F 1) (1 + (H : ℂ)) - f u‖ ≤
      (K : ℝ) / u ^ (B + 1) := by
  dsimp only
  set k := ⌊u ^ (2 * B + 3 + 1)⌋₊
  set H : ℝ := (k + 1 : ℝ) / u with hHeq
  have hk : u ^ (2 * (B + 2)) ≤ (k : ℝ) + 1 := by
    have he : 2 * (B + 2) = 2 * B + 3 + 1 := by omega
    rw [he]
    exact (Nat.lt_floor_add_one _).le
  have hH : 1 < H := (lt_div_iff₀ hu).2 (by
    rw [one_mul]
    rcases le_or_gt 1 u with hu₁ | hu₁
    · exact (le_self_pow₀ hu₁ (by omega : 2 * B + 3 + 1 ≠ 0)).trans_lt (Nat.lt_floor_add_one _)
    · exact hu₁.trans_le (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (H : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hH
  have hnear : ∀ᶠ z in 𝓝 (H : ℂ), HasLaplace f z (dslope F 1 (1 + z)) := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact hL z hz
  have h := norm_smul_iteratedDeriv_sub_le_of_hasLaplace (zero_lt_one.trans hH) hnear hf k
  have hcenter : ((k + 1 : ℕ) : ℝ) / H = u := by
    rw [Nat.cast_add, Nat.cast_one, div_div_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0)]
  have hscalar : (H : ℂ) ^ (k + 1) * (-1) ^ k = (-(H : ℂ)) ^ k * H := by
    rw [← neg_one_mul (H : ℂ), mul_pow, pow_succ]
    ring
  simp only [iteratedDeriv_comp_const_add, hcenter, hscalar] at h
  refine h.trans ?_
  push_cast
  have hsqrt : u ^ (B + 2) ≤ √((k : ℝ) + 1) := by
    simpa only [mul_comm 2 (B + 2), pow_mul, Real.sqrt_sq (by positivity : 0 ≤ u ^ (B + 2))]
      using Real.sqrt_le_sqrt hk
  have hsqrt₀ : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  calc
    (K : ℝ) * √((k : ℝ) + 1) / H = (K : ℝ) * u / √((k : ℝ) + 1) := by
      rw [hHeq, div_div_eq_mul_div]
      field_simp [hsqrt₀.ne', hu.ne']
      rw [Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)]
    _ ≤ (K : ℝ) * u / u ^ (B + 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
    _ = (K : ℝ) / u ^ (B + 1) := by
      rw [pow_succ u (B + 1)]
      field_simp

/-- A Lipschitz function on the nonnegative ray decays faster than every inverse power if its
Laplace transform at rate `s - 1` agrees with `(F(s) - F(1)) / (s - 1)` for `Re s > 2`, and
`F` is holomorphic with `‖F‖ ≤ l^A` on `Re s ≥ 1 - l⁻ᴬ`, `‖s‖ ≤ exp l` for all large `l`. -/
theorem eventually_norm_le_inv_pow_of_laplace_dslope {f : ℝ → ℂ} {F : ℂ → ℂ} {K : ℝ≥0} {A : ℕ}
    (hf : LipschitzOnWith K f (Ici 0))
    (hL : ∀ s : ℂ, 2 < s.re → (F s - F 1) / (s - 1) =
      ∫ v in Ioi (0 : ℝ), Complex.exp (-(s - 1) * v) • f v)
    (hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ A ≤ s.re → ‖s‖ ≤ Real.exp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ (u ^ B)⁻¹ := by
  have hshift (z : ℂ) (hz : 1 < z.re) : HasLaplace f z (dslope F 1 (1 + z)) := by
    have hz' : 2 < (1 + z).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have hne : 1 + z ≠ 1 := by
      intro he
      simp [he] at hz'
    refine HasLaplace.intro (hf.integrableOn_cexp_smul (zero_lt_one.trans hz)) ?_
    rw [dslope_of_ne F hne, slope_def_field]
    simpa only [add_sub_cancel_left] using (hL (1 + z) hz').symm
  filter_upwards [eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow hF (2 * B + 3) (B + 1),
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop ((K : ℝ) + 1)] with u hc hu hK
  let k := ⌊u ^ (2 * B + 3 + 1)⌋₊
  let H : ℝ := (k + 1 : ℝ) / u
  let c := ((-(H : ℂ)) ^ k * H / k.factorial) • iteratedDeriv k (dslope F 1) (1 + (H : ℂ))
  have hu₀ : 0 < u := zero_lt_one.trans hu
  have happrox : ‖c - f u‖ ≤ (K : ℝ) / u ^ (B + 1) := postWidder_error_le hf hshift B hu₀
  calc
    ‖f u‖ ≤ ‖c‖ + ‖c - f u‖ := norm_le_norm_add_norm_sub ..
    _ ≤ (u ^ (B + 1))⁻¹ + (K : ℝ) / u ^ (B + 1) := add_le_add hc happrox
    _ = ((K : ℝ) + 1) / u ^ (B + 1) := by rw [add_div, one_div, add_comm]
    _ ≤ (u ^ B)⁻¹ := by
      rw [pow_succ, ← div_div, ← one_div, div_right_comm]
      exact div_le_div_of_nonneg_right ((div_le_one hu₀).2 hK) (by positivity)

end TauCeti
