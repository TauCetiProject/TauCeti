/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Examples of the order symbols (DLMF 2.1.4–2.1.9)

The order symbols `∼`, `o` and `O` of DLMF §2.1(i) are Mathlib's `Asymptotics.IsEquivalent`,
`Asymptotics.IsLittleO` and `Asymptotics.IsBigO`. This file proves the examples that DLMF gives
for them, including the remark after 2.1.7 that `e^{-z} = o(1)` holds uniformly in a closed
sector `|ph z| ≤ π/2 - δ` but not in the open half-plane `|ph z| < π/2`.

## Main results

* `Complex.tanh_isEquivalent_id`: `tanh z ∼ z` as `z → 0` (DLMF 2.1.4).
* `Real.exp_neg_isLittleO_one`: `e^{-x} = o(1)` as `x → +∞` (DLMF 2.1.5).
* `Complex.exp_neg_isLittleO_one_sector`, `Complex.not_exp_neg_isLittleO_one_halfPlane`:
  `e^{-z} = o(1)` as `z → ∞` in `|ph z| ≤ π/2 - δ`, and not in `|ph z| < π/2`.
* `Real.sin_pi_mul_add_inv_isBigO`: `sin(πn + n⁻¹) = O(n⁻¹)` as `n → ±∞` in `ℤ` (DLMF 2.1.6).
* `Complex.exp_ofReal_mul_I_isBigO_one`: `e^{ix} = O(1)` on all of `ℝ` (DLMF 2.1.7).
* `Complex.tsum_tail_isBigO_pow`: the tail from index `n` of a power series that converges near
  `0` is `O(zⁿ)` (DLMF 2.1.8).
* `Complex.exp_sub_one_sub_isBigO_sq`: `e^z = 1 + z + O(z²)` as `z → 0` (DLMF 2.1.9).

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology Real

namespace Complex

/-- DLMF 2.1.4: `tanh z ∼ z` as `z → 0` in `ℂ`, along the full neighbourhood filter (both sides
vanish at `0`). -/
theorem tanh_isEquivalent_id : (fun z : ℂ => tanh z) ~[𝓝 0] fun z => z := by
  have hd : HasDerivAt tanh 1 0 := by
    have h := (hasDerivAt_sinh 0).div (hasDerivAt_cosh 0) (by simp)
    simp only [cosh_zero, sinh_zero, mul_zero, sub_zero, one_pow, div_one, mul_one] at h
    have he : sinh / cosh = tanh := funext fun z => (tanh_eq_sinh_div_cosh z).symm
    rwa [he] at h
  have h := hd.isLittleO
  simp only [tanh_zero, sub_zero, smul_eq_mul, mul_one] at h
  exact h

end Complex

/-- DLMF 2.1.5: `e^{-x} = o(1)` as `x → +∞` in `ℝ`. -/
theorem Real.exp_neg_isLittleO_one :
    (fun x : ℝ => Real.exp (-x)) =o[atTop] fun _ => (1 : ℝ) :=
  (isLittleO_one_iff ℝ).mpr Real.tendsto_exp_neg_atTop_nhds_zero

namespace Complex

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` as `z → ∞` in the closed sector
`|ph z| ≤ π/2 - δ`, for every `δ > 0`. -/
theorem exp_neg_isLittleO_one_sector {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ}]
      fun _ => (1 : ℂ) := by
  rcases lt_or_ge (π / 2 - δ) 0 with hneg | hnn
  · have hempty : {z : ℂ | |arg z| ≤ π / 2 - δ} = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz => (abs_nonneg _).not_gt (hz.trans_lt hneg)
    simp [hempty]
  set c := Real.sin δ
  have hc : 0 < c := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hre : ∀ z : ℂ, |arg z| ≤ π / 2 - δ → c * ‖z‖ ≤ z.re := fun z hz => by
    have h := (TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re (z := z)
      ⟨hnn, by linarith [Real.pi_pos]⟩).mp (abs_le.mp hz)
    rwa [Real.cos_pi_div_two_sub, mul_comm] at h
  refine (isLittleO_one_iff ℂ).mpr ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun z : ℂ => Real.exp (-(c * ‖z‖)))
      (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ}) (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_norm_cobounded_atTop.mono_left inf_le_left).const_mul_atTop hc)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
  rw [norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (by linarith [hre z hz])

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` fails as `z → ∞` in the open half-plane
`|ph z| < π/2`. Along `z = 1 + it`, `|e^{-z}| = e^{-1}`. -/
theorem not_exp_neg_isLittleO_one_halfPlane :
    ¬ (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}]
      fun _ => (1 : ℂ) := by
  intro h
  have ht := ((isLittleO_one_iff ℂ).mp h).norm
  set γ : ℝ → ℂ := fun t => 1 + t * I with hγ
  have hγt : Tendsto γ atTop (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr
      (Eventually.of_forall fun t => abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [hγ])))⟩
    refine tendsto_atTop_mono (fun t => ?_) tendsto_id
    calc t ≤ |t| := le_abs_self t
      _ = |(γ t).im| := by simp [hγ]
      _ ≤ ‖γ t‖ := abs_im_le_norm _
  have h2 := ht.comp hγt
  have h3 : (fun t => ‖exp (-γ t)‖) = fun _ => Real.exp (-1) := by
    funext t; simp [hγ, norm_exp]
  simp only [Function.comp_def, h3, norm_zero] at h2
  exact (Real.exp_pos (-1)).ne' (tendsto_nhds_unique tendsto_const_nhds h2)

end Complex

/-- DLMF 2.1.6: `sin(πn + n⁻¹) = O(n⁻¹)` as `n → ±∞` in `ℤ`. The bound holds for every integer,
with constant `1`. -/
theorem Real.sin_pi_mul_add_inv_isBigO :
    (fun n : ℤ => Real.sin (π * n + (n : ℝ)⁻¹)) =O[atTop ⊔ atBot] fun n => (n : ℝ)⁻¹ := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have h1 : |((-1 : ℝ) ^ n)| = 1 := by simp
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    show π * n + (n : ℝ)⁻¹ = (n : ℝ)⁻¹ + n * π by ring, Real.sin_add_int_mul_pi, abs_mul, h1,
    one_mul]
  exact Real.abs_sin_le_abs

namespace Complex

/-- DLMF 2.1.7: `e^{ix} = O(1)` for `x ∈ ℝ`, on the whole real line (the filter `⊤`). -/
theorem exp_ofReal_mul_I_isBigO_one :
    (fun x : ℝ => exp (x * I)) =O[⊤] fun _ => (1 : ℝ) :=
  isBigO_top.mpr ⟨1, fun x => by simp [norm_exp_ofReal_mul_I]⟩

/-- DLMF 2.1.8: if `∑ aₛ zˢ` converges for all sufficiently small `|z|`, then for each `n`,
`∑_{s ≥ n} aₛ zˢ = O(zⁿ)` as `z → 0`. For a function with a power series in Mathlib's sense this
is `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`; here the hypothesis is the convergence of the
scalar series. -/
theorem tsum_tail_isBigO_pow {a : ℕ → ℂ}
    (ha : ∃ r > 0, ∀ z : ℂ, ‖z‖ < r → Summable fun s => a s * z ^ s) (n : ℕ) :
    (fun z : ℂ => ∑' s, a (s + n) * z ^ (s + n)) =O[𝓝 0] fun z => z ^ n := by
  obtain ⟨r, hr, hs⟩ := ha
  set ρ : ℝ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsρ : Summable fun s => a s * (ρ : ℂ) ^ s :=
    hs ρ (by rw [norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; linarith)
  clear_value ρ
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, ‖a s‖ * ρ ^ s ≤ C := by
    have ht := hsρ.tendsto_atTop_zero.norm
    rw [← Nat.cofinite_eq_atTop] at ht
    obtain ⟨C, hC⟩ := ht.bddAbove_range_of_cofinite
    refine ⟨C, fun s => ?_⟩
    have := hC ⟨s, rfl⟩
    simpa [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hρ0] using this
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ ‖a 0‖ * ρ ^ 0).trans (hC 0)
  refine IsBigO.of_bound (2 * C / ρ ^ n) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hρ0)] with z hz
  rw [mem_ball_zero_iff] at hz
  have hq : ‖z‖ / ρ < 1 / 2 := by rw [div_lt_iff₀ hρ0]; linarith
  have hq0 : 0 ≤ ‖z‖ / ρ := by positivity
  have hgeom : HasSum (fun s : ℕ => C / ρ ^ n * ‖z‖ ^ n * (‖z‖ / ρ) ^ s)
      (C / ρ ^ n * ‖z‖ ^ n * (1 - ‖z‖ / ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hb : ∀ s, ‖a (s + n) * z ^ (s + n)‖ ≤ C / ρ ^ n * ‖z‖ ^ n * (‖z‖ / ρ) ^ s := by
    intro s
    have h1 : ‖a (s + n)‖ ≤ C / ρ ^ (s + n) := by
      rw [le_div_iff₀ (by positivity)]; exact hC _
    rw [norm_mul, norm_pow]
    calc ‖a (s + n)‖ * ‖z‖ ^ (s + n) ≤ C / ρ ^ (s + n) * ‖z‖ ^ (s + n) := by gcongr
      _ = C / ρ ^ n * ‖z‖ ^ n * (‖z‖ / ρ) ^ s := by
        rw [div_pow, pow_add, pow_add]; ring
  refine (tsum_of_norm_bounded hgeom hb).trans ?_
  rw [norm_pow]
  have h2 : (1 - ‖z‖ / ρ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc C / ρ ^ n * ‖z‖ ^ n * (1 - ‖z‖ / ρ)⁻¹ ≤ C / ρ ^ n * ‖z‖ ^ n * 2 := by gcongr
    _ = 2 * C / ρ ^ n * ‖z‖ ^ n := by ring

/-- DLMF 2.1.9: `e^z = 1 + z + O(z²)` as `z → 0` in `ℂ`. -/
theorem exp_sub_one_sub_isBigO_sq :
    (fun z : ℂ => exp z - 1 - z) =O[𝓝 0] fun z => z ^ 2 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
  rw [mem_closedBall_zero_iff] at hz
  simpa [norm_pow] using norm_exp_sub_one_sub_id_le hz

end Complex
