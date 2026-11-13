/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Divisor
public import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Calculus.FDeriv.ConstantDirection
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Hadamard factorization at order at most one

An entire function `f` of order at most one with `f 0 ≠ 0` is
`f s = exp (a + b s) ∏_ρ E₁(s / ρ) ^ m_ρ`, where `E₁ z = (1 - z) exp z` is the genus-one
elementary factor, the product runs over the support of Mathlib's whole-plane divisor of `f`
with its values `m_ρ` as multiplicities (`TauCeti.divisorProductOne`), `exp a = f 0` and
`b = logDeriv f 0`. Consequently, off the zeros,
`logDeriv f s = b + ∑_ρ m_ρ (1 / (s - ρ) + 1 / ρ)`, absolutely at each point and locally
uniformly on the complement of the zeros.

## Main results

* `TauCeti.OrderLE.exists_eq_cexp_mul_divisorProductOne` and `TauCeti.hadamard_of_orderLE_one`:
  Hadamard's factorization, with the product as `divisorProductOne f` and as a multipliable
  product over `ℂ`.
* `TauCeti.OrderLE.logDeriv_eq_add_tsum`,
  `TauCeti.OrderLE.summable_norm_divisor_mul_one_div_sub_add_one_div` and
  `TauCeti.OrderLE.hasSumLocallyUniformlyOn_logDeriv_sub`: the partial-fraction expansion of
  the logarithmic derivative; absolute convergence holds for every order below two.

The examples `exp (c s)` and `1 - s` use `TauCeti.divisorProductOne_cexp_mul` and
`TauCeti.divisorProductOne_one_sub`.

## Implementation notes

The quotient of `f` by its divisor product is entire and zero-free, hence `exp L` for an entire
`L` (`TauCeti.exists_differentiableOn_eqOn_mul_exp_of_divisor_eq`); the product converges by
`TauCeti.OrderLE.summable_divisor_toNat_mul_norm_inv_sq`. Its growth is controlled
through `L'` rather than through a minimum-modulus estimate for the product. Off the zeros,
`L' = logDeriv f - logDeriv (divisorProductOne f)`. At a point `z` with `‖z‖ ≥ 1`, Landau's
local lemma on `closedBall 0 (4 ‖z‖)`
(`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_half_le`), with the order bound
`‖f‖ = O(exp (‖s‖ ^ (3/2)))`, replaces `logDeriv f z` by the zeros in `closedBall 0 (2 ‖z‖)` up to
`O(√‖z‖)`. The paired series differs from that finite sum by
`O(√‖z‖ ∑ m_ρ ‖ρ‖ ^ (-3/2))`, which converges by
`TauCeti.OrderLE.summable_divisor_mul_norm_rpow`. By continuity the bound `‖L' z‖ = O(√‖z‖)`
holds at the zeros too. So `L'` is constant by the polynomial Liouville theorem
(`Differentiable.exists_eq_polynomial_eval_of_isLittleO_pow`), and `L` is affine.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 11 and 12.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §3.9.
-/

public section

open Complex Filter Metric Topology Bornology Asymptotics
open scoped BigOperators

namespace TauCeti

variable {f : ℂ → ℂ}

/-- A paired term, less its near part when `ρ` is close to the origin, is bounded by
`2 √‖z‖ m ‖ρ‖ ^ (-3/2)`. -/
private theorem norm_pair_sub_near_le {z ρ : ℂ} (hρ : ρ ≠ 0) (hzρ : z ≠ ρ) (m : ℕ) :
    ‖(m : ℂ) * (1 / (z - ρ) + 1 / ρ) -
        (if ‖ρ‖ ≤ 2 * ‖z‖ then (m : ℂ) / (z - ρ) else 0)‖ ≤
      2 * √‖z‖ * (m * (‖ρ‖ * √‖ρ‖)⁻¹) := by
  have ht := Real.sq_sqrt (norm_nonneg z)
  have hu := Real.sq_sqrt (norm_nonneg ρ)
  have ht0 := Real.sqrt_nonneg ‖z‖
  have hu0 : 0 < √‖ρ‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hρ)
  have htu' : (√‖z‖ ≤ √‖ρ‖) ↔ ‖z‖ ≤ ‖ρ‖ := Real.sqrt_le_sqrt_iff (norm_nonneg ρ)
  set t := √‖z‖
  set u := √‖ρ‖
  split_ifs with hle
  · have he : (m : ℂ) * (1 / (z - ρ) + 1 / ρ) - (m : ℂ) / (z - ρ) = (m : ℂ) / ρ := by ring
    rw [he, norm_div, RCLike.norm_natCast]
    have hut : √‖ρ‖ ≤ 2 * √‖z‖ := by nlinarith
    rw [← hu]
    calc (m : ℝ) / u ^ 2 = m / (u ^ 2 * u) * u := by field_simp
      _ ≤ m / (u ^ 2 * u) * (2 * t) := by gcongr
      _ = _ := by ring
  · push Not at hle
    have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    have he : (m : ℂ) * (1 / (z - ρ) + 1 / ρ) - 0 = m * z / ((z - ρ) * ρ) := by
      field_simp
      ring
    rw [he, norm_div, norm_mul, norm_mul, RCLike.norm_natCast]
    have hzρn : ‖ρ‖ / 2 ≤ ‖z - ρ‖ := by
      have := norm_sub_norm_le ρ z
      rw [norm_sub_rev] at this
      linarith
    have htu : t ≤ u := htu'.mpr (by linarith [norm_nonneg z])
    calc (m : ℝ) * ‖z‖ / (‖z - ρ‖ * ‖ρ‖) ≤ m * ‖z‖ / (‖ρ‖ / 2 * ‖ρ‖) := by
          gcongr
      _ = 2 * t * (m * (‖ρ‖ * u)⁻¹) * (t / u) := by
          rw [← ht, ← hu]
          field_simp
      _ ≤ 2 * t * (m * (‖ρ‖ * u)⁻¹) * 1 := by
          gcongr
          exact div_le_one_of_le₀ htu hu0.le
      _ = _ := mul_one _

/-- The local zero sum of Landau's lemma on `closedBall 0 (2 ‖z‖)` differs from the paired
divisor series at `z` by at most `2 √‖z‖ ∑ m_ρ ‖ρ‖ ^ (-3/2)`. -/
private theorem norm_finsum_sub_tsum_le (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))
    (hS : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      (MeromorphicOn.divisor f Set.univ ρ : ℝ) * ‖(ρ : ℂ)‖ ^ (-(3 / 2 : ℝ))))
    {z : ℂ} (hz : f z ≠ 0) :
    ‖(∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall 0 (2 * ‖z‖)) ρ : ℂ) / (z - ρ)) -
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)‖ ≤
      2 * √‖z‖ * ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        (MeromorphicOn.divisor f Set.univ ρ : ℝ) * ‖(ρ : ℂ)‖ ^ (-(3 / 2 : ℝ)) := by
  classical
  set d := MeromorphicOn.divisor f Set.univ with hd_def
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have hdn (ρ : ℂ) : 0 ≤ d ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa ρ
  have h0 : (0 : ℂ) ∉ d.support :=
    (hf.analyticAt _).notMem_divisor_support_of_ne_zero hf0
  have hzS : z ∉ d.support :=
    (hf.analyticAt _).notMem_divisor_support_of_ne_zero hz
  let ψ : ℂ → ℂ := fun ρ ↦ if ‖ρ‖ ≤ 2 * ‖z‖ then ((d ρ).toNat : ℂ) / (z - ρ) else 0
  let g : d.support → ℂ := fun ρ ↦ ((d ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)
  have hψsupp : Function.support ψ ⊆ d.support := by
    intro ρ hρ
    by_contra hns
    rw [Function.notMem_support] at hns
    exact hρ (by simp [ψ, hns])
  have hψfin : (Function.support ψ).Finite := by
    refine ((MeromorphicOn.divisor_norm_sublevel_finite f (2 * ‖z‖)).image
      Subtype.val).subset fun ρ hρ ↦ ⟨⟨ρ, hψsupp hρ⟩, ?_, rfl⟩
    by_contra hle
    exact hρ (ite_eq_right hle)
  have hfinsum : (∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall 0 (2 * ‖z‖)) ρ : ℂ) / (z - ρ)) =
      ∑' ρ : d.support, ψ ρ := by
    rw [tsum_subtype_eq_of_support_subset hψsupp, tsum_eq_finsum hψfin]
    refine finsum_congr fun ρ ↦ ?_
    by_cases hρ : ‖ρ‖ ≤ 2 * ‖z‖
    · have hmem : ρ ∈ closedBall (0 : ℂ) (2 * ‖z‖) := mem_closedBall_zero_iff.mpr hρ
      have heq : MeromorphicOn.divisor f (closedBall 0 (2 * ‖z‖)) ρ = d ρ := by
        rw [MeromorphicOn.divisor_apply (hfa.mono (Set.subset_univ _)).meromorphicOn hmem,
          hd_def, MeromorphicOn.divisor_apply hfa.meromorphicOn (Set.mem_univ ρ)]
      simp only [ψ, ite_eq_left hρ, heq]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg (hdn ρ)).symm
    · have hmem : ρ ∉ closedBall (0 : ℂ) (2 * ‖z‖) := by
        rwa [mem_closedBall_zero_iff]
      simp only [ψ, ite_eq_right hρ,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hmem, Int.cast_zero, zero_div]
  have hg : Summable g :=
    (summable_norm_natCast_divisor_mul_one_div_sub_add_one_div h0 hsum hzS).of_norm
  have hψ : Summable fun ρ : d.support ↦ ψ ρ :=
    summable_of_hasFiniteSupport (hψfin.preimage Subtype.val_injective.injOn)
  rw [hfinsum, ← hψ.tsum_sub hg, ← tsum_mul_left]
  refine tsum_of_norm_bounded (hS.mul_left _).hasSum fun ρ ↦ ?_
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h ↦ h0 (h ▸ ρ.property)
  have hzρ : z ≠ ρ := fun h ↦ hzS (h ▸ ρ.property)
  rw [norm_sub_rev, Real.rpow_neg (norm_nonneg _), Real.rpow_three_div_two_eq_mul_sqrt]
  have hc : (d ρ : ℝ) = ((d ρ).toNat : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg (hdn ρ)).symm
  rw [hc]
  exact norm_pair_sub_near_le hρ0 hzρ _

/-- The bound of Landau's local lemma on `closedBall 0 (4 r)`, for an entire function bounded by
`K exp ((4 r) ^ (3/2)) |f 0|` there, is `O(√r)` once `r ≥ 1`. -/
private theorem landau_bound_le_mul_sqrt {K r : ℝ} (hK : 0 ≤ Real.log K) (hr : 1 ≤ r) :
    48 / (4 * r) * (Real.log K + 8 * r * √r) ≤ (12 * Real.log K + 96) * √r := by
  have hr0 : 0 < r := by linarith
  have h1 : 48 / (4 * r) * (Real.log K + 8 * r * √r) = 12 * Real.log K / r + 96 * √r := by
    field_simp
    ring
  have h2 : 12 * Real.log K / r ≤ 12 * Real.log K * √r := by
    rw [div_le_iff₀ hr0]
    have h3 : 1 ≤ √r * r := one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hr) hr
    nlinarith [mul_le_mul_of_nonneg_left h3 hK]
  rw [h1]
  linarith

/-- Off the zeros and away from the origin, the logarithmic derivatives of an entire function of
order at most one and of its genus-one divisor product differ by `O(√‖z‖)`. This is the
quotient-growth estimate, proved from Landau's local lemma on `closedBall 0 (4 ‖z‖)`. -/
private theorem OrderLE.exists_norm_logDeriv_sub_logDeriv_divisorProductOne_le
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2)) :
    ∃ C R₀ : ℝ, ∀ z, R₀ ≤ ‖z‖ → f z ≠ 0 →
      ‖logDeriv f z - logDeriv (divisorProductOne f) z‖ ≤ C * √‖z‖ := by
  have h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support :=
    (hf.analyticAt _).notMem_divisor_support_of_ne_zero hf0
  -- Constants: the zero sum `S = ∑ m_ρ ‖ρ‖ ^ (-3/2)` and the order bound
  -- `‖f w‖ ≤ c exp (‖w‖ ^ (3/2))` for `‖w‖ ≥ L`.
  have hS := h.summable_divisor_mul_norm_rpow hf hf0 (p := 3 / 2) (by norm_num)
  set S := ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
    (MeromorphicOn.divisor f Set.univ ρ : ℝ) * ‖(ρ : ℂ)‖ ^ (-(3 / 2 : ℝ)) with hSdef
  obtain ⟨c, _, hb⟩ := (h.isBigO (A' := 3 / 2) (by norm_num)).exists_pos
  obtain ⟨L, _, hL⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hb.bound
  set K := max 1 (c / ‖f 0‖)
  have hK : 1 ≤ K := le_max_left _ _
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  refine ⟨12 * Real.log K + 96 + 2 * S, max (L / 4) 1, fun z hz hfz ↦ ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hzL : L ≤ 4 * ‖z‖ := by linarith [(le_max_left (L / 4) 1).trans hz]
  have hR : 0 < 4 * ‖z‖ := by linarith
  -- The order bound on the sphere of radius `4 ‖z‖`, in the form of Landau's lemma.
  have hM : ∀ w ∈ sphere (0 : ℂ) (4 * ‖z‖),
      ‖f w‖ ≤ K * Real.exp ((4 * ‖z‖) ^ (3 / 2 : ℝ)) * ‖f 0‖ := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    have hbw : ‖f w‖ ≤ c * ‖Real.exp (‖w‖ ^ (3 / 2 : ℝ))‖ := hL (show L ≤ ‖w‖ by rw [hw]; exact hzL)
    rw [Real.norm_eq_abs, Real.abs_exp, hw] at hbw
    have hcK : c ≤ K * ‖f 0‖ := by
      calc c = c / ‖f 0‖ * ‖f 0‖ := by field_simp
        _ ≤ K * ‖f 0‖ := by gcongr; exact le_max_right _ _
    calc ‖f w‖ ≤ c * Real.exp ((4 * ‖z‖) ^ (3 / 2 : ℝ)) := hbw
      _ ≤ K * ‖f 0‖ * Real.exp ((4 * ‖z‖) ^ (3 / 2 : ℝ)) := by gcongr
      _ = _ := by ring
  -- Landau's lemma: `logDeriv f z` is the zero sum over `closedBall 0 (2 ‖z‖)` up to `O(√‖z‖)`.
  have hland := AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_half_le
    (fun w _ ↦ hf.analyticAt w) hR hf0 hM (z := z) (by simp) hfz
  rw [show 4 * ‖z‖ / 2 = 2 * ‖z‖ by ring] at hland
  -- The tail: that finite sum is the paired series up to `2 √‖z‖ S`.
  have htail := norm_finsum_sub_tsum_le hf hf0 hsum hS hfz
  rw [← hSdef] at htail
  have hzS : z ∉ (MeromorphicOn.divisor f Set.univ).support :=
    (hf.analyticAt _).notMem_divisor_support_of_ne_zero hfz
  rw [logDeriv_divisorProductOne h0 hsum hzS]
  -- Combine the two estimates.
  have hlogM : Real.log (K * Real.exp ((4 * ‖z‖) ^ (3 / 2 : ℝ))) =
      Real.log K + 8 * ‖z‖ * √‖z‖ := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
      Real.rpow_three_div_two_eq_mul_sqrt, Real.sqrt_mul (by norm_num),
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  rw [hlogM] at hland
  refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hland htail).trans ?_)
  calc _ ≤ (12 * Real.log K + 96) * √‖z‖ + 2 * √‖z‖ * S :=
        add_le_add_left (landau_bound_le_mul_sqrt hlogK hz1) _
    _ = _ := by ring

/-- **Hadamard factorization at order at most one.** An entire function `f` of order at most one
with `f 0 ≠ 0` is `exp (a + b z)` times the genus-one product over its zeros, with
`exp a = f 0` and `b = logDeriv f 0`. -/
theorem OrderLE.exists_eq_cexp_mul_divisorProductOne (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) :
    ∃ a : ℂ, exp a = f 0 ∧ ∀ z, f z = exp (a + logDeriv f 0 * z) * divisorProductOne f z := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf hf0 (by norm_num)
  have hP : Differentiable ℂ (divisorProductOne f) := differentiable_divisorProductOne hsum
  obtain ⟨L, hL, heq⟩ := exists_differentiableOn_eqOn_mul_exp_of_divisor_eq
    (convex_univ.isSimplyConnected Set.univ_nonempty) isOpen_univ
    (fun z _ ↦ hf.analyticAt z) (fun z _ ↦ hP.analyticAt z) ⟨0, trivial, hf0⟩
    ⟨0, trivial, by simp⟩ (divisor_divisorProductOne hf hf0 hsum).symm
  have hL' : Differentiable ℂ L := differentiableOn_univ.mp hL
  have hdL : Differentiable ℂ (deriv L) := differentiableOn_univ.mp (hL.deriv isOpen_univ)
  set P := divisorProductOne f with hPdef
  have hfe : f = fun z ↦ P z * exp (L z) := funext fun z ↦ heq (Set.mem_univ z)
  have hPz {z : ℂ} (hfz : f z ≠ 0) : P z ≠ 0 := by
    intro hPz
    exact hfz (by rw [heq (Set.mem_univ z)]; simp [hPz])
  -- Off the zeros, `L'` is the difference of the two logarithmic derivatives.
  have hlog {z : ℂ} (hfz : f z ≠ 0) : logDeriv f z = logDeriv P z + deriv L z := by
    rw [hfe, logDeriv_mul_cexp (hPz hfz) (hP z) (hL' z)]
  obtain ⟨C, R₀, hC⟩ :=
    h.exists_norm_logDeriv_sub_logDeriv_divisorProductOne_le hf hf0 hsum
  -- The bound extends across the zeros by continuity.
  have hbound (z : ℂ) (hz : R₀ + 1 ≤ ‖z‖) : ‖deriv L z‖ ≤ C * √‖z‖ := by
    have hev : ∀ᶠ w in 𝓝[≠] z, ‖deriv L w‖ ≤ C * √‖w‖ := by
      have hfar : ∀ᶠ w in 𝓝[≠] z, R₀ < ‖w‖ :=
        nhdsWithin_le_nhds ((continuous_norm.tendsto z).eventually
          (eventually_gt_nhds (by linarith)))
      filter_upwards [AnalyticOnNhd.eventually_ne_zero_nhdsNE_of_preconnected
        (fun u _ ↦ hf.analyticAt u) isPreconnected_univ (Set.mem_univ 0) hf0 (Set.mem_univ z),
        hfar] with w hw hwR
      rw [← sub_eq_of_eq_add' (hlog hw)]
      exact hC w hwR.le hw
    exact le_of_tendsto_of_tendsto
      ((hdL.continuous.tendsto z).mono_left nhdsWithin_le_nhds).norm
      (((by fun_prop : Continuous fun w : ℂ ↦ C * √‖w‖).tendsto z).mono_left nhdsWithin_le_nhds)
      hev
  have hbigO : deriv L =O[cobounded ℂ] (fun z : ℂ ↦ √‖z‖) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (R₀ + 1)] with z hz
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact hbound z hz
  obtain ⟨p, hp, hpL⟩ := hdL.exists_eq_polynomial_eval_of_isLittleO_pow (n := 0)
    (hbigO.trans_isLittleO (isLittleO_sqrt_norm.congr_right fun z ↦ (pow_one z).symm))
  have hconst (z : ℂ) : deriv L z = deriv L 0 := by
    rw [congrFun hpL z, congrFun hpL 0, Polynomial.eq_C_of_natDegree_le_zero hp]
    simp
  have hb : deriv L 0 = logDeriv f 0 := by
    rw [hlog hf0, logDeriv_apply, hPdef, deriv_divisorProductOne_zero hsum,
      divisorProductOne_zero, zero_div, zero_add]
  refine ⟨L 0, ?_, fun z ↦ ?_⟩
  · rw [heq (Set.mem_univ 0)]
    beta_reduce
    rw [hPdef, divisorProductOne_zero, one_mul]
  · rw [heq (Set.mem_univ z)]
    beta_reduce
    have hLz : L z = L 0 + z * deriv L 0 := by
      simpa using apply_add_smul_eq_of_fderiv_apply_eq hL' (v := 1) hconst 0 z
    rw [hLz, hb, mul_comm, mul_comm z]

/-- **Hadamard's theorem at order at most one**, with the product taken over all of `ℂ`: for
every `s` the family `ρ ↦ E₁(ρ⁻¹ s) ^ m_ρ` over `ℂ` is multipliable and
`f s = exp (a + b s) ∏' ρ, E₁(ρ⁻¹ s) ^ m_ρ`, where `m_ρ` is the divisor of `f`,
`exp a = f 0` and `b = logDeriv f 0`. -/
theorem hadamard_of_orderLE_one (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    ∃ a b : ℂ, exp a = f 0 ∧ b = logDeriv f 0 ∧ ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactorOne (ρ⁻¹ * s) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat) ∧
      f s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactorOne (ρ⁻¹ * s) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf hf0 (by norm_num)
  obtain ⟨a, ha, hfa⟩ := h.exists_eq_cexp_mul_divisorProductOne hf hf0
  refine ⟨a, logDeriv f 0, ha, rfl, fun s ↦ ⟨(hasProd_divisorProductOne hsum s).multipliable, ?_⟩⟩
  rw [hfa s, divisorProductOne_eq_tprod]

/-- Off its zeros, the logarithmic derivative of an entire function of order at most one with
`f 0 ≠ 0` is its value at the origin plus the logarithmic derivative of the genus-one product. -/
theorem OrderLE.logDeriv_eq_add_logDeriv_divisorProductOne (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {z : ℂ} (hz : f z ≠ 0) :
    logDeriv f z = logDeriv f 0 + logDeriv (divisorProductOne f) z := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf hf0 (by norm_num)
  obtain ⟨a, _, hfa⟩ := h.exists_eq_cexp_mul_divisorProductOne hf hf0
  have hPz : divisorProductOne f z ≠ 0 := fun h0 ↦ hz (by rw [hfa z, h0, mul_zero])
  conv_lhs => rw [funext hfa]
  rw [logDeriv_cexp_mul hPz ((differentiable_divisorProductOne hsum) z) (by fun_prop)]
  simp

/-- **Partial fractions for the logarithmic derivative.** Off its zeros, an entire function of
order at most one with `f 0 ≠ 0` satisfies
`logDeriv f z = logDeriv f 0 + ∑' ρ, m_ρ (1 / (z - ρ) + 1 / ρ)`. -/
theorem OrderLE.logDeriv_eq_add_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {z : ℂ} (hz : f z ≠ 0) :
    logDeriv f z = logDeriv f 0 + ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  rw [h.logDeriv_eq_add_logDeriv_divisorProductOne hf hf0 hz,
    logDeriv_divisorProductOne
      ((hf.analyticAt _).notMem_divisor_support_of_ne_zero hf0)
      (h.summable_divisor_toNat_mul_norm_inv_sq hf hf0 (by norm_num))
      ((hf.analyticAt _).notMem_divisor_support_of_ne_zero hz)]

/-- The partial-fraction series of an entire function of order less than two, nonzero at the
origin, converges absolutely off its zeros. -/
theorem OrderLE.summable_norm_divisor_mul_one_div_sub_add_one_div {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (hA : A < 2) {z : ℂ} (hz : f z ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ‖((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)‖) :=
  summable_norm_natCast_divisor_mul_one_div_sub_add_one_div
    ((hf.analyticAt _).notMem_divisor_support_of_ne_zero hf0)
    (h.summable_divisor_toNat_mul_norm_inv_sq hf hf0 hA)
    ((hf.analyticAt _).notMem_divisor_support_of_ne_zero hz)

/-- The partial-fraction series of an entire function of order at most one converges locally
uniformly off its zeros to `logDeriv f - logDeriv f 0`. -/
theorem OrderLE.hasSumLocallyUniformlyOn_logDeriv_sub (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor f Set.univ).support) z ↦
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ))
      (fun z ↦ logDeriv f z - logDeriv f 0)
      ((MeromorphicOn.divisor f Set.univ).support)ᶜ := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf hf0 (by norm_num)
  have h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support :=
    (hf.analyticAt _).notMem_divisor_support_of_ne_zero hf0
  refine TendstoLocallyUniformlyOn.congr_right
    (hasSumLocallyUniformlyOn_logDeriv_divisorProductOne h0 hsum) fun z hz ↦ ?_
  have hfz : f z ≠ 0 := fun hfz ↦ divisorProductOne_ne_zero hsum h0 hz
    ((divisorProductOne_eq_zero_iff hf hf0 hsum z).mpr hfz)
  rw [h.logDeriv_eq_add_logDeriv_divisorProductOne hf hf0 hfz, add_sub_cancel_left]

/-! ### Examples -/

/-- The Hadamard data of `exp (c s)`: `a = 0`, `b = c`, and the product is empty. -/
example (c : ℂ) (s : ℂ) :
    exp (c * s) = exp (0 + c * s) * divisorProductOne (fun s ↦ exp (c * s)) s ∧
      logDeriv (fun s ↦ exp (c * s)) 0 = c := by
  refine ⟨by simp [divisorProductOne_cexp_mul], ?_⟩
  have hd : HasDerivAt (fun s ↦ exp (c * s)) (exp (c * 0) * (c * 1)) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul c).cexp
  rw [logDeriv_apply, hd.deriv]
  simp

/-- The Hadamard data of `1 - s`: `a = 0`, `b = -1`, and `1 - s = exp (-s) E₁(s)`. -/
example (s : ℂ) :
    1 - s = exp (0 + (-1) * s) * divisorProductOne (fun s ↦ 1 - s) s ∧
      logDeriv (fun s : ℂ ↦ 1 - s) 0 = -1 := by
  refine ⟨?_, by simp [logDeriv_apply]⟩
  rw [divisorProductOne_one_sub, weierstrassFactorOne_def, mul_left_comm, ← exp_add]
  simp

end TauCeti
