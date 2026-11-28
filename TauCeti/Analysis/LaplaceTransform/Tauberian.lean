/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.PostWidder
import TauCeti.Analysis.Complex.Taylor.RapidDecay

/-!
# A quantitative Laplace Tauberian theorem

A Lipschitz function on the positive ray decays faster than every inverse power if its
Laplace transform comes from a holomorphic divided difference with polylogarithmic
bounds in a logarithmic region. The rate in the conclusion is useful for smoothed prime
sums, where mere convergence does not suffice at a second cutoff.

This is the Post–Widder argument used in `New.eventually_abs_le_inv_pow_of_transform`
in `grh/src/Lib/Analytic/PrimeNumberTheorem/Tauberian.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

open Filter Set
open scoped NNReal Topology

namespace TauCeti

private theorem postWidder_error_le {u : ℝ} (hu : 0 ≤ u) (B : ℕ) :
    let k := ⌊u ^ ((2 * B + 3) + 1)⌋₊
    let H := ((k : ℝ) + 1) / u
    u ≤ H ∧ √((k : ℝ) + 1) / H ≤ (u ^ (B + 1))⁻¹ := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  dsimp only
  set k := ⌊u ^ ((2 * B + 3) + 1)⌋₊
  have hexp : (B + 2) * 2 = (2 * B + 3) + 1 := by omega
  have hk : (u ^ (B + 2)) ^ 2 ≤ (k : ℝ) + 1 := by
    rw [← pow_mul, hexp]
    exact (Nat.lt_floor_add_one _).le
  have hsqrt : u ^ (B + 2) ≤ √((k : ℝ) + 1) := by
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ u ^ (B + 2))] using Real.sqrt_le_sqrt hk
  have hu₂ : u ^ 2 ≤ (k : ℝ) + 1 := by
    rcases le_total u 1 with h | h
    · calc
        u ^ 2 ≤ 1 ^ 2 := by gcongr
        _ ≤ (k : ℝ) + 1 := by simp
    · refine le_trans ?_ hk
      gcongr
      exact le_self_pow₀ h (by omega)
  refine ⟨(le_div_iff₀ (by positivity)).2 (by simpa only [pow_two] using hu₂), ?_⟩
  have hs : 0 < √((k : ℝ) + 1) := by positivity
  calc
    √((k : ℝ) + 1) / (((k : ℝ) + 1) / u) = u / √((k : ℝ) + 1) := by
      rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) hs.ne']
      calc
        √((k : ℝ) + 1) * u * √((k : ℝ) + 1) = u * (√((k : ℝ) + 1)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (by positivity)]
    _ ≤ u / u ^ (B + 2) := by gcongr
    _ = (u ^ (B + 1))⁻¹ := by
      rw [pow_succ, div_mul_cancel_right₀ (by positivity : u ≠ 0)]

/-- Let `f` be Lipschitz on `[0, ∞)`, with Laplace transform given on a right half-plane by
`z ↦ dslope F 1 (1 + z)`. If `F` is holomorphic and bounded by `l ^ A` in the regions
`Re s ≥ 1 - 1 / l ^ A`, `‖s‖ ≤ exp l` for all sufficiently large `l`, then `‖f u‖ ≤ u⁻ᴮ`
for every `B : ℕ` and all sufficiently large `u`. -/
public theorem eventually_norm_le_inv_pow_of_hasLaplace {f : ℝ → ℂ} {F : ℂ → ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Ici 0)) {σ : ℝ}
    (hLaplace : ∀ z : ℂ, σ < z.re → HasLaplace f z (dslope F 1 (1 + z))) {A : ℕ}
    (hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ A ≤ s.re → ‖s‖ ≤ Real.exp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ (u ^ B)⁻¹ := by
  filter_upwards [eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow hF (2 * B + 3) (B + 1),
    eventually_gt_atTop σ, eventually_ge_atTop (1 + (K : ℝ))] with u hc hσ huK
  set k := ⌊u ^ ((2 * B + 3) + 1)⌋₊
  set H : ℝ := ((k : ℝ) + 1) / u
  have hu : 1 ≤ u := (le_add_of_nonneg_right K.coe_nonneg).trans huK
  obtain ⟨hH, herr⟩ := postWidder_error_le (zero_le_one.trans hu) B
  have hH₀ : 0 < H := zero_lt_one.trans_le (hu.trans hH)
  have hOpen : IsOpen {z : ℂ | σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL : ∀ᶠ z in 𝓝 (H : ℂ), HasLaplace f z (dslope F 1 (1 + z)) := by
    have hmem : (H : ℂ) ∈ {z : ℂ | σ < z.re} := by simpa using hσ.trans_le hH
    filter_upwards [hOpen.mem_nhds hmem] with z hz
    exact hLaplace z hz
  have hgamma := norm_smul_iteratedDeriv_sub_le_of_hasLaplace hH₀ hL hf k
  have hmean : ((k + 1 : ℕ) : ℝ) / H = u := by
    rw [Nat.cast_succ, div_div_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0)]
  have hneg : -(H : ℂ) = (-1 : ℂ) * H := (neg_one_mul _).symm
  have hscalar : (H : ℂ) ^ (k + 1) * (-1) ^ k = (-(H : ℂ)) ^ k * H := by
    rw [hneg, mul_pow, pow_succ]
    ac_rfl
  rw [hmean, iteratedDeriv_comp_const_add, hscalar] at hgamma
  let c := (((-(H : ℂ)) ^ k * H / k.factorial) •
    iteratedDeriv k (dslope F 1) (1 + (H : ℂ)))
  calc
    ‖f u‖ ≤ ‖c‖ + ‖c - f u‖ := by rw [norm_sub_rev]; exact norm_le_insert' _ _
    _ ≤ (u ^ (B + 1))⁻¹ + (K : ℝ) * (u ^ (B + 1))⁻¹ := by
      refine add_le_add hc (hgamma.trans ?_)
      rw [Nat.cast_succ, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left herr K.coe_nonneg
    _ = (1 + (K : ℝ)) * (u ^ (B + 1))⁻¹ := by ring
    _ ≤ u * (u ^ (B + 1))⁻¹ := mul_le_mul_of_nonneg_right huK (by positivity)
    _ = (u ^ B)⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

end TauCeti
