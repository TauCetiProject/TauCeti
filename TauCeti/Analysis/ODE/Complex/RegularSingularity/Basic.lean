/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Gronwall.Discrete
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Convergent series solutions at a regular singularity

For `f, g` around `z₀` with `(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and
`(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`, let
`Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α = (α - α₁)(α - α₂)` (`Re α₂ ≤ Re α₁`). On
`{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}` (via
`TauCeti.Analysis.Complex.PowerSeries.BranchCut`):
* Any sequence solving the indicial recursion at a root `ρ` of `Q` converges on `‖z - z₀‖ < r` and
  yields a solution of `w'' + f w' + g w = 0` (`TauCeti.regularSingular_solution`, specialized to
  `TauCeti.regularSingularCoeff_solution`). For a root `ρ` with no positive integer shift `ρ + s`
  (`s ≥ 1`) that is also a root of `Q`, normalized series solutions (`a₀ = 1`) are unique
  (`TauCeti.eq_regularSingularCoeff_of_solution`).
* Pointwise logarithmic-product operator identity for `L(w * log(· - z₀)) - log(· - z₀) * L(w)`
  (`TauCeti.deriv_deriv_add_mul_deriv_add_mul_mul_log_sub`).
* When `α₁ - α₂ = N ∈ ℕ`, there is a second holomorphic solution
  `w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c w₁(z) log(z - z₀)` (`b_N = 0`, `c = 1` for `N = 0`,
  `b₀ = 1` for `N ≥ 1`) with `∑ b_s (z - z₀)^s` convergent on `‖z - z₀‖ < r`
  (`TauCeti.regularSingular_second_solution`, uniqueness
  `TauCeti.eq_regularSingularSecondCoeff_of_solution`).
* Worked Euler–Cauchy example: `w'' - 2 z⁻² w = 0` at `z₀ = 0` (`α₁ = 2`, `α₂ = -1`, `c = 0`).

Abel–Liouville Wronskian formulas and fundamental pairs are in
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Wronskian`.

## References
* NIST DLMF §2.7(ii), 2.7.1–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Filter Finset Metric Set
open scoped Topology ENNReal

namespace TauCeti

/-! ### Internal analytic and majorant helpers -/

private theorem iteratedDeriv_two_eq (φ : ℂ → ℂ) : iteratedDeriv 2 φ = deriv (deriv φ) := by
  simp [iteratedDeriv_succ]

private theorem secondOrder_operator_add_const_mul {f g ψ Φ : ℂ → ℂ} {c' z : ℂ}
    (hψ₁ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hΦ₁ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ Φ w)
    (hψ₂ : DifferentiableAt ℂ (deriv ψ) z)
    (hΦ₂ : DifferentiableAt ℂ (deriv Φ) z) :
    (deriv (deriv fun w => ψ w + c' * Φ w) z + f z * deriv (fun w => ψ w + c' * Φ w) z +
        g z * (ψ z + c' * Φ z)) =
      (deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z) +
        c' * (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) := by
  have hd1_ev : deriv (fun w => ψ w + c' * Φ w) =ᶠ[𝓝 z] fun w => deriv ψ w + c' * deriv Φ w := by
    filter_upwards [hψ₁, hΦ₁] with w hwψ hwΦ
    exact ((hwψ.hasDerivAt).add ((hwΦ.hasDerivAt).const_mul c')).deriv
  have hd2 : deriv (deriv fun w => ψ w + c' * Φ w) z =
      deriv (deriv ψ) z + c' * deriv (deriv Φ) z :=
    (((hψ₂.hasDerivAt).add ((hΦ₂.hasDerivAt).const_mul c')).congr_of_eventuallyEq hd1_ev).deriv
  rw [hd1_ev.self_of_nhds, hd2]
  ring

/-- Lower bound `s² / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖` for sufficiently large `s : ℕ`. -/
private theorem exists_sq_div_two_le_norm_indicialPoly (f₀ g₀ σ : ℂ) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ := by
  set B : ℝ := ‖2 * σ + f₀ - 1‖ + ‖indicialPoly f₀ g₀ σ‖
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B + 1)
  refine ⟨max N 1, le_max_right _ _, fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (le_max_right N 1).trans hs
  have hNs : (N : ℝ) ≤ s := by exact_mod_cast (le_max_left N 1).trans hs
  have htri : (s : ℝ) ^ 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ +
      ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖ := by
    have h := norm_sub_le (indicialPoly f₀ g₀ (σ + s))
      ((2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ)
    have hdiff_id : indicialPoly f₀ g₀ (σ + s) -
        ((2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ) = (s : ℂ) ^ 2 := by
      rw [indicialPoly_add]; ring
    rwa [hdiff_id, norm_pow, Complex.norm_natCast] at h
  have hrem : ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖ ≤ B * s := by
    have h := norm_add_le ((2 * σ + f₀ - 1) * (s : ℂ)) (indicialPoly f₀ g₀ σ)
    rw [norm_mul, Complex.norm_natCast] at h
    nlinarith [norm_nonneg (indicialPoly f₀ g₀ σ)]
  nlinarith [hs1, hNs, hN, htri, hrem]

/-- One-step majorant inequality for a perturbed indicial convolution recursion at radius
`ρ > 0`. -/
private theorem indicial_rec_step_bound {σ : ℂ} {ρ Mf Mg CE : ℝ} {fs gs d E : ℕ → ℂ} {s K : ℕ}
    (hρ_pos : 0 < ρ) (hMf_pos : 0 < Mf) (hMg_pos : 0 < Mg) (hCE0 : 0 ≤ CE) (hs1 : 1 ≤ s)
    (hMf : ∀ k, ‖fs k‖ * ρ ^ k ≤ Mf) (hMg : ∀ k, ‖gs k‖ * ρ ^ k ≤ Mg)
    (hCE : ‖E s‖ * ρ ^ s ≤ CE * (s + 1))
    (hK : 2 * ((Mf + Mg) * (‖σ‖ + 1) + 2 * CE) < K)
    (hQs : (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly (fs 0) (gs 0) (σ + s)‖)
    (hds : indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ‖d s‖ * ρ ^ s ≤ (K : ℝ) / s * (1 + ∑ k ∈ range s, ‖d k‖ * ρ ^ k) := by
  set C₁ : ℝ := (Mf + Mg) * (‖σ‖ + 1); set μ : ℕ → ℝ := fun k => ‖d k‖ * ρ ^ k
  set S : ℝ := 1 + ∑ k ∈ range s, μ k
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hμ_nn : ∀ k, 0 ≤ μ k := fun _ => by positivity
  have hconv : (∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s) ≤
      (C₁ * s) * ∑ k ∈ range s, μ k := by
    rw [mul_sum]; refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt := mem_range.mp hk
    have hks : (k : ℝ) ≤ s := by exact_mod_cast hk_lt.le
    have htri : ‖(σ + k) * fs (s - k) + gs (s - k)‖ ≤ (‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
      have h1 := norm_add_le ((σ + k) * fs (s - k)) (gs (s - k))
      have h2 := norm_add_le σ (k : ℂ)
      rw [norm_mul] at h1; rw [Complex.norm_natCast] at h2; nlinarith [norm_nonneg (fs (s - k))]
    have hfgk : ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k) ≤ C₁ * s := by
      have hm := mul_le_mul_of_nonneg_right htri (pow_nonneg hρ_pos.le (s - k))
      have hMf' := hMf (s - k); have hMg' := hMg (s - k)
      dsimp only [C₁]; nlinarith [norm_nonneg σ, le_mul_of_one_le_right (norm_nonneg σ) hs_ge1]
    have hρs : ρ ^ s = ρ ^ (s - k) * ρ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_lt.le]
    calc ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s
        = (‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k)) * μ k := by
            rw [norm_mul, hρs]; dsimp only [μ]; ring
      _ ≤ (C₁ * s) * μ k := mul_le_mul_of_nonneg_right hfgk (hμ_nn k)
  have hrec : ‖indicialPoly (fs 0) (gs 0) (σ + s)‖ * μ s =
      ‖-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s‖ * ρ ^ s := by
    simpa [μ, norm_mul, mul_assoc] using congrArg (fun w => ‖w‖ * ρ ^ s) hds
  have htri_tot := mul_le_mul_of_nonneg_right
    (norm_add_le (-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k)) (E s))
    (pow_nonneg hρ_pos.le s)
  rw [norm_neg, add_mul] at htri_tot
  have hnorm_sum : ‖∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s ≤
      ∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s := by
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
  have hsum_nn : 0 ≤ ∑ k ∈ range s, μ k := sum_nonneg fun k _ => hμ_nn k
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hsum_le : C₁ * s * (∑ k ∈ range s, μ k) + CE * (s + 1) ≤ (C₁ + 2 * CE) * s * S := by
    dsimp only [S]
    nlinarith [hC₁0, mul_nonneg hCE0 (mul_nonneg hs_pos.le hsum_nn),
      mul_le_mul_of_nonneg_left hs_ge1 hCE0]
  have hprod_le : ((s : ℝ) ^ 2 / 2) * μ s ≤ ((K : ℝ) / 2 * s) * S := by
    have h1 := (mul_le_mul_of_nonneg_right hQs (hμ_nn s)).trans_eq hrec
    have hK' : (C₁ + 2 * CE) * s * S ≤ ((K : ℝ) / 2 * s) * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs_pos.le)
        (by dsimp [S]; linarith)
    linarith [h1, htri_tot, hnorm_sum, hconv, hCE, hsum_le, hK']
  rw [div_mul_eq_mul_div, le_div_iff₀ hs_pos]; nlinarith [hprod_le, hs_pos]

/-- Perturbed indicial majorant convergence: if `Q(σ + s) d_s = -∑_{k < s} ((σ + k) f_{s - k} +
g_{s - k}) d_k + E_s` for `s ≥ s₁`, where `‖E_s‖ ρ^s` grows at most linearly in `s` on every
sub-radius `0 < ρ < r`, then `∑ d_s (z - z₀)^s` converges on the entire open disc `‖z - z₀‖ < r`. -/
private theorem summable_of_perturbed_indicial_rec {z₀ σ : ℂ} {r : ℝ}
    {fs gs d E : ℕ → ℂ} {s₁ : ℕ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => gs s * (z - z₀) ^ s)
    (hE : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, ‖E s‖ * ρ ^ s ≤ C * (s + 1))
    (hd : ∀ s : ℕ, s₁ ≤ s → indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ∀ z, ‖z - z₀‖ < r → Summable fun s => d s * (z - z₀) ^ s := by
  intro z hz
  set ρ : ℝ := (‖z - z₀‖ + r) / 2
  have hρ_gt : ‖z - z₀‖ < ρ := by dsimp [ρ]; linarith
  have hρ_pos : 0 < ρ := (norm_nonneg _).trans_lt hρ_gt
  have hρ_lt : ρ < r := by dsimp [ρ]; linarith
  obtain ⟨Mf, hMf_pos, hMf⟩ :=
    FormalMultilinearSeries.exists_norm_mul_pow_le_of_norm_sub_lt fs z₀ hρ_pos.le hρ_lt hf
  obtain ⟨Mg, hMg_pos, hMg⟩ :=
    FormalMultilinearSeries.exists_norm_mul_pow_le_of_norm_sub_lt gs z₀ hρ_pos.le hρ_lt hg
  obtain ⟨CE, hCE0, hCE⟩ := hE ρ hρ_pos hρ_lt
  obtain ⟨s₂, hs₂1, hQ⟩ := exists_sq_div_two_le_norm_indicialPoly (fs 0) (gs 0) σ
  set s₀ : ℕ := max s₁ s₂; have hs₀1 : 1 ≤ s₀ := hs₂1.trans (le_max_right _ _)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ((Mf + Mg) * (‖σ‖ + 1) + 2 * CE))
  set μ : ℕ → ℝ := fun s => ‖d s‖ * ρ ^ s; set S₀ : ℝ := 1 + ∑ k ∈ range s₀, μ k
  have hμ0 : ∀ s, 0 ≤ μ s := fun _ => by positivity
  have hS₀_pos : 1 ≤ S₀ := by dsimp [S₀]; linarith [sum_nonneg fun k (_ : k ∈ range s₀) => hμ0 k]
  have hpoly := add_sum_range_le_mul_pow_of_le_div hs₀1 zero_le_one hμ0 fun s hs =>
    indicial_rec_step_bound hρ_pos hMf_pos hMg_pos hCE0 (hs₀1.trans hs) hMf hMg (hCE s) hK
      (hQ s ((le_max_right _ _).trans hs)) (hd s ((le_max_left _ _).trans hs))
  set q : ℝ := ‖z - z₀‖ / ρ; have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hρ_pos.le
  have hq1 : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0, div_lt_one hρ_pos]; exact hρ_gt
  refine Summable.of_norm_bounded_eventually_nat (f := fun s => d s * (z - z₀) ^ s)
    ((summable_pow_mul_geometric_of_norm_lt_one K hq1).mul_left (S₀ * 2 ^ K)) ?_
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (hs₀1.trans hs)
  have h2s : ((s + 1 : ℕ) : ℝ) ^ K ≤ 2 ^ K * (s : ℝ) ^ K := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) K
  have hμ_le_sum : μ s ≤ 1 + ∑ k ∈ range (s + 1), μ k := by
    rw [sum_range_succ]; linarith [sum_nonneg fun k (_ : k ∈ range s) => hμ0 k]
  have hμ_le : μ s ≤ S₀ * (2 ^ K * (s : ℝ) ^ K) :=
    (hμ_le_sum.trans (hpoly (s + 1) (hs.trans (Nat.le_succ s)))).trans
      (mul_le_mul_of_nonneg_left h2s (by linarith))
  have hpow_q : ‖z - z₀‖ ^ s = ρ ^ s * q ^ s := by
    rw [← mul_pow, mul_div_cancel₀ _ hρ_pos.ne']
  rw [norm_mul, norm_pow, hpow_q, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hμ_le (pow_nonneg hq0 s)).trans_eq (by ring)

/-! ### Differential operator on `(z - z₀)^σ ∑ c_s (z - z₀)^s` and `w₁(z) log(z - z₀)` -/

/-- Power-series identity for the indicial operator applied to `A(u) = ∑' s, c s * u ^ s` on
`‖u‖ < r`. -/
private theorem hasSum_operator_cpow_series {z₀ σ : ℂ} {r : ℝ} {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => gs s * (z - z₀) ^ s)
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A : ℂ → ℂ := fun w => ∑' s, c s * w ^ s
    HasSum (fun s : ℕ => (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
        ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s)
      ((u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) +
        (u * deriv A u + σ * A u) * (∑' s, fs s * u ^ s) +
        A u * (∑' s, gs s * u ^ s)) := by
  intro A
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt c z₀ hr
    fun z _ hzr => hc z hzr
  have hc_norm : Summable fun s : ℕ => ‖c s * u ^ s‖ := hpA.summable_norm_mul_pow_ofScalars hue
  have hsc_norm : Summable fun s : ℕ => ‖(s : ℂ) * c s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      c (hue.trans_le hpA.r_le) 1
  have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt fs z₀ hr hf)
      |>.summable_norm_mul_pow_ofScalars hue
  have hg_norm : Summable fun s : ℕ => ‖gs s * u ^ s‖ :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt gs z₀ hr hg)
      |>.summable_norm_mul_pow_ofScalars hue
  have hA0 : HasSum (fun s : ℕ => c s * u ^ s) (A u) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
      hpA.hasSum (mem_eball_zero_iff.mpr hue)
  have hA1 : HasSum (fun s : ℕ => (s : ℂ) * c s * u ^ s) (u * deriv A u) :=
    hpA.hasSum_mul_deriv_ofScalars hue
  have hA2 : HasSum (fun s : ℕ => (s : ℂ) * ((s : ℂ) - 1) * c s * u ^ s)
      (u ^ 2 * deriv (deriv A) u) := by
    have hraw := hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hue 2
    rw [iteratedDeriv_two_eq, zero_add] at hraw
    refine hraw.congr_fun fun s => ?_
    rcases s with _ | s <;>
      [simp; (simp only [Nat.descFactorial_succ, Nat.add_sub_cancel, Nat.descFactorial_zero,
        mul_one]; push_cast; ring)]
  have hσc_norm : Summable fun s : ℕ => ‖((σ + s) * c s) * u ^ s‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => by
      have hsplit : ((σ + s) * c s) * u ^ s = σ * (c s * u ^ s) + (s : ℂ) * c s * u ^ s := by
        ring
      rw [hsplit]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])) ((hc_norm.mul_left ‖σ‖).add hsc_norm)
  have hlead : HasSum (fun s : ℕ => (σ + s) * (σ + s - 1) * c s * u ^ s)
      (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) :=
    (((hA2.add (hA1.mul_left (2 * σ))).add (hA0.mul_left (σ * (σ - 1)))).congr_fun fun _ => by ring)
  have hP_prod := hasSum_sum_range_mul_of_summable_norm hσc_norm hf_norm
  rw [((hA1.add (hA0.mul_left σ)).congr_fun fun _ => by ring).tsum_eq] at hP_prod
  refine ((hlead.add hP_prod).add (hasSum_sum_range_mul_of_summable_norm hc_norm hg_norm)).congr_fun
    fun s => ?_
  rw [sum_range_succ_mul_pow (fun k => (σ + k) * c k) fs u s, sum_range_succ_mul_pow c gs u s,
    indicialPoly_def]
  have hsum : ((∑ k ∈ range s, (σ + k) * c k * fs (s - k)) + ∑ k ∈ range s, c k * gs (s - k)) *
      u ^ s = (∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s := by
    rw [← sum_add_distrib]; exact congrArg (· * u ^ s) (sum_congr rfl fun _ _ => by ring)
  linear_combination -hsum

/-- Operator evaluation for `ψ(z) = (z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit punctured
disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
private theorem operator_cpow_mul_tsum_eq {z₀ σ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    let ψ : ℂ → ℂ := fun w => (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s
    deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z =
      (z - z₀) ^ (σ - 2) * ∑' s : ℕ,
        (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
          ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * (z - z₀) ^ s := by
  intro ψ
  set A : ℂ → ℂ := fun u => ∑' s, c s * u ^ s; set u : ℂ := z - z₀
  have hr : 0 < r := (norm_nonneg u).trans_lt hzb
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  have han := FormalMultilinearSeries.analyticOnNhd_tsum_ofScalars_of_norm_sub_lt c z₀ hr
    fun w _ => hc w
  have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hinner := (((han u (mem_ball_zero_iff.mpr hzb)).differentiableAt.hasDerivAt.comp_sub_const
    z z₀).const_mul σ).add (hsub.mul
      ((han.deriv u (mem_ball_zero_iff.mpr hzb)).differentiableAt.hasDerivAt.comp_sub_const z z₀))
  have hev : deriv ψ =ᶠ[𝓝 z] ((fun w : ℂ => (w - z₀) ^ (σ - 1)) *
      ((fun w : ℂ => σ * A (w - z₀)) + (fun w : ℂ => w - z₀) * fun w : ℂ => deriv A (w - z₀))) := by
    filter_upwards [(isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r).mem_nhds ⟨hzs, hzb⟩]
      with w hw
    exact (hasDerivAt_cpow_mul_tsum hc hw.1 hw.2).deriv
  have hσ_sub : σ - 1 - 1 = σ - 2 := by ring
  have hcpow1 : u ^ (σ - 1) = u ^ (σ - 2) * u := by
    simpa [hσ_sub, Nat.cast_one, pow_one] using cpow_eq_cpow_sub_natCast_mul_pow hu0 (σ - 1) 1
  have hcpow2 : u ^ σ = u ^ (σ - 2) * u ^ 2 := by
    simpa using cpow_eq_cpow_sub_natCast_mul_pow hu0 σ 2
  have hderiv2 : deriv (deriv ψ) z =
      u ^ (σ - 2) * (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) := by
    rw [(((hsub.cpow_const (c := σ - 1) hzs).mul hinner).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.add_apply, Pi.mul_apply]; dsimp only [u] at hcpow1 ⊢
    rw [hσ_sub, hcpow1]; ring
  rw [(hasSum_operator_cpow_series (σ := σ) (fun w hw0 hwr => (hf w hw0 hwr).summable)
      (fun w hw0 hwr => (hg w hw0 hwr).summable) hc hzb).tsum_eq,
    (hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq, (hg z (norm_pos_iff.mpr hu0) hzb).tsum_eq, hderiv2,
    (hasDerivAt_cpow_mul_tsum hc hzs hzb).deriv]
  dsimp only [ψ, A, u]; rw [hcpow1, hcpow2]; ring

/-- Pointwise logarithmic-product identity for the second-order linear operator
`L(w) = w'' + f w' + g w` on the logarithm branch `z - z₀ ∈ slitPlane`: if `w` is
differentiable near `z` and `deriv w` is differentiable at `z`, then
`L(w * log(· - z₀)) z - log(z - z₀) * L(w) z` equals
`((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z)`. -/
theorem deriv_deriv_add_mul_deriv_add_mul_mul_log_sub
    {z₀ z : ℂ} (hzs : z - z₀ ∈ slitPlane) {f g w : ℂ → ℂ}
    (hw : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w u) (hdw : DifferentiableAt ℂ (deriv w) z) :
    let Φ : ℂ → ℂ := fun u => w u * Complex.log (u - z₀)
    (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) -
        Complex.log (z - z₀) * (deriv (deriv w) z + f z * deriv w z + g z * w z) =
      ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z) := by
  intro Φ
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hsub : HasDerivAt (fun u : ℂ => u - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hU_log : ∀ᶠ u in 𝓝 z, u - z₀ ∈ slitPlane :=
    (isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).mem_nhds hzs
  have hderiv1 : ∀ᶠ u in 𝓝 z,
      HasDerivAt Φ (deriv w u * Complex.log (u - z₀) + (u - z₀)⁻¹ * w u) u := by
    filter_upwards [hw, hU_log] with u hu hsu
    exact ((hu.hasDerivAt.mul (((hasDerivAt_id u).sub_const z₀).clog hsu)).congr_deriv
      (by dsimp only [id]; rw [one_div]; ring))
  have hd1 : deriv Φ z = deriv w z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w z :=
    hderiv1.self_of_nhds.deriv
  have hev : deriv Φ =ᶠ[𝓝 z]
      (deriv w * (fun u : ℂ => Complex.log (u - z₀)) + (fun u : ℂ => (u - z₀)⁻¹) * w) :=
    hderiv1.mono fun _ hu => hu.deriv
  have hd2 : deriv (deriv Φ) z = deriv (deriv w) z * Complex.log (z - z₀) +
      2 * (z - z₀)⁻¹ * deriv w z - ((z - z₀) ^ 2)⁻¹ * w z := by
    rw [(((hdw.hasDerivAt.mul (hsub.clog hzs)).add
      ((hsub.inv hzu0).mul hw.self_of_nhds.hasDerivAt)).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.inv_apply]; field_simp [hzu0]; ring
  rw [hd1, hd2]
  dsimp only [Φ]
  field_simp [hzu0]
  ring

/-- Operator identity for `Φ(z) = w₁(z) log(z - z₀)` when `w₁` solves `w₁'' + f w₁' + g w₁ = 0` on
the slit punctured disc. -/
private theorem hasDerivAt_and_operator_mul_log {z₀ : ℂ} {r : ℝ} {f g w₁ : ℂ → ℂ}
    (hw₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0) :
    let Φ : ℂ → ℂ := fun z => w₁ z * Complex.log (z - z₀)
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ Φ U ∧
      (∀ z ∈ U, HasDerivAt Φ (deriv w₁ z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w₁ z) z) ∧
      ∀ z ∈ U, deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z =
        ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w₁ z + ((z - z₀) * f z - 1) * w₁ z) := by
  intro Φ U
  have hopen : IsOpen U := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  have hw₁_at (z) (hz : z ∈ U) : DifferentiableAt ℂ w₁ z := hw₁.differentiableAt (hopen.mem_nhds hz)
  have hderiv1 : ∀ z ∈ U,
      HasDerivAt Φ (deriv w₁ z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w₁ z) z := fun z hz =>
    ((hw₁_at z hz).hasDerivAt.mul (((hasDerivAt_id z).sub_const z₀).clog hz.1)).congr_deriv
      (by dsimp only [id]; rw [one_div]; ring)
  refine ⟨fun z hz => (hderiv1 z hz).differentiableAt.differentiableWithinAt, hderiv1, ?_⟩
  rintro z ⟨hzs, hzb⟩
  have hw₁_ev : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w₁ u :=
    Eventually.mono (hopen.mem_nhds ⟨hzs, hzb⟩) hw₁_at
  have hdw₁ : DifferentiableAt ℂ (deriv w₁) z :=
    (hw₁.deriv hopen).differentiableAt (hopen.mem_nhds ⟨hzs, hzb⟩)
  have hpt := deriv_deriv_add_mul_deriv_add_mul_mul_log_sub (f := f) (g := g) hzs hw₁_ev hdw₁
  linear_combination hpt + Complex.log (z - z₀) * hsol₁ z hzs hzb

/-! ### Primary series solution at a regular singularity -/

/-- **Series solution at a regular singularity** (DLMF 2.7.2–2.7.5). Let `(z - z₀) f(z)` and
`(z - z₀)² g(z)` have power series `∑ fs s * (z - z₀)^s` and `∑ gs s * (z - z₀)^s` on the
punctured disc `0 < ‖z - z₀‖ < r`. If `ρ` is a root of `indicialPoly (fs 0) (gs 0)` and `a : ℕ → ℂ`
satisfies the indicial recursion, then `∑ a_s (z - z₀)^s` converges on the full disc `‖z - z₀‖ < r`,
and `w(z) = (z - z₀)^ρ ∑' s, a s * (z - z₀)^s` is a holomorphic solution of `w'' + f w' + g w = 0`
on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem regularSingular_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
    let w : ℂ → ℂ := fun z => (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s
    (∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  have hsum := summable_of_perturbed_indicial_rec (σ := ρ) (d := a) (E := 0) (s₁ := 1)
    (fun z hz0 hzr => (hf z hz0 hzr).summable) (fun z hz0 hzr => (hg z hz0 hzr).summable)
    (fun _ _ _ => ⟨0, le_rfl, fun _ => by simp⟩) (fun s hs => by simp [ha s hs])
  refine ⟨hsum, fun z hz =>
      (hasDerivAt_cpow_mul_tsum hsum hz.1 hz.2).differentiableAt.differentiableWithinAt,
    fun z hzs hzb => ?_⟩
  rw [operator_cpow_mul_tsum_eq hf hg hsum hzs hzb]
  have hcoeff : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (ρ + s) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k = 0 := fun s => by
    rcases eq_or_ne s 0 with rfl | hs
    · simp [hρ]
    · rw [ha s (Nat.pos_of_ne_zero hs), neg_add_cancel]
  simp [hcoeff]

/-- Specialization of `regularSingular_solution` to the canonical normalized sequence
`regularSingularCoeff fs gs ρ` (`a₀ = 1`) attached to a non-resonant indicial root `ρ`. -/
theorem regularSingularCoeff_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0) :
    let a := regularSingularCoeff fs gs ρ
    let w : ℂ → ℂ := fun z => (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s
    (∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 :=
  regularSingular_solution hf hg hρ fun _ hs =>
    indicialPoly_mul_regularSingularCoeff hs (hres _ hs)

/-- **Analytic uniqueness of the normalized series coefficients**: for `0 < r` and a non-resonant
indicial root `ρ`, any convergent power series `∑ a_s (z - z₀)^s` with `a 0 = 1` such that
`(z - z₀)^ρ ∑ a_s (z - z₀)^s` solves `w'' + f w' + g w = 0` on the slit punctured disc has
`a = regularSingularCoeff fs gs ρ`. -/
theorem eq_regularSingularCoeff_of_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hr : 0 < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0)
    (ha0 : a 0 = 1)
    (hsum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    (hsol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv (fun w => (w - z₀) ^ ρ * ∑' s, a s * (w - z₀) ^ s)) z +
        f z * deriv (fun w => (w - z₀) ^ ρ * ∑' s, a s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) = 0) :
    a = regularSingularCoeff fs gs ρ := by
  have hall := eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := ρ - 2) hr
    (fun u _ hu => (hasSum_operator_cpow_series (σ := ρ)
      (fun w hw0 hwr => (hf w hw0 hwr).summable)
      (fun w hw0 hwr => (hg w hw0 hwr).summable) hsum hu).summable)
    fun z hzs hzb => (operator_cpow_mul_tsum_eq hf hg hsum hzs hzb).symm.trans (hsol z hzs hzb)
  exact eq_regularSingularCoeff_of_rec hres ha0 fun s _ => by linear_combination hall s

/-! ### Second solution when the indicial roots differ by a natural number -/

/-- Power-series expansion for the shifted logarithmic forcing terms
`u ^ N * (2 u A₁'(u) + (2(α₂ + N) + P(u) - 1) A₁(u))` on `‖u‖ < r`. -/
private theorem hasSum_regularSingularLogForcing_mul_pow {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ}
    {fs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (ha : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A₁ : ℂ → ℂ := fun w => ∑' s, a s * w ^ s
    HasSum (fun s => regularSingularLogForcing fs a α₂ N s * u ^ s)
      (u ^ N * (2 * u * deriv A₁ u +
        (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u)) := by
  intro A₁
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt a z₀ hr
    fun z _ => ha z
  have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt fs z₀ hr hf)
      |>.summable_norm_mul_pow_ofScalars hue
  have hA0 : HasSum (fun s : ℕ => a s * u ^ s) (A₁ u) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
      hpA.hasSum (mem_eball_zero_iff.mpr hue)
  have hA1 : HasSum (fun s : ℕ => (s : ℂ) * a s * u ^ s) (u * deriv A₁ u) :=
    hpA.hasSum_mul_deriv_ofScalars hue
  have hprod :=
    hasSum_sum_range_mul_of_summable_norm (hpA.summable_norm_mul_pow_ofScalars hue) hf_norm
  have hunshifted : HasSum (fun m : ℕ =>
      ((2 * (α₂ + N + m) + fs 0 - 1) * a m + ∑ k ∈ range m, fs (m - k) * a k) * u ^ m)
      (2 * u * deriv A₁ u + (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u) := by
    have htot := ((hA1.mul_left 2).add (hA0.mul_left (2 * (α₂ + N) - 1))).add hprod
    have htot_eq :
        2 * (u * deriv A₁ u) + (2 * (α₂ + N) - 1) * A₁ u + A₁ u * ∑' s, fs s * u ^ s =
          2 * u * deriv A₁ u + (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u := by
      ring
    rw [htot_eq] at htot
    refine htot.congr_fun fun m => ?_
    have hsum_comm :
        (∑ k ∈ range m, a k * fs (m - k)) = ∑ k ∈ range m, fs (m - k) * a k :=
      sum_congr rfl fun _ _ => mul_comm _ _
    rw [sum_range_succ_mul_pow a fs u m, hsum_comm]; ring
  refine ((add_left_injective N).hasSum_iff fun s hs => ?_).mp
    ((hunshifted.mul_left (u ^ N)).congr_fun fun m => ?_)
  · rw [regularSingularLogForcing_of_lt _ _ _
      (by by_contra h; exact hs ⟨s - N, Nat.sub_add_cancel (not_lt.mp h)⟩), zero_mul]
  · simp only [Function.comp_apply]
    rw [regularSingularLogForcing_of_le _ _ _ (by omega), Nat.add_sub_cancel, pow_add]
    push_cast; ring

/-- Shared operator formula for any second-solution candidate
`w₂'(z) = (z - z₀)^{α₂} ∑ b' s * (z - z₀)^s + c' * w₁(z) * log(z - z₀)` when `α₁ = α₂ + N`. -/
private theorem operator_second_ansatz_eq {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs b' : ℕ → ℂ} {c' : ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂))
    (hb'_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b' s * (z - z₀) ^ s) :
    let a := regularSingularCoeff fs gs (α₂ + N)
    let w₁ : ℂ → ℂ := fun w => (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s
    let w₂' : ℂ → ℂ := fun w =>
      (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) + c' * w₁ w * Complex.log (w - z₀)
    let D : ℕ → ℂ := fun s =>
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) +
      c' * regularSingularLogForcing fs a α₂ N s
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ w₂' U ∧
      (∀ u : ℂ, ‖u‖ < r → Summable fun s => D s * u ^ s) ∧
      ∀ z ∈ U, deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z =
        (z - z₀) ^ (α₂ - 2) * ∑' s, D s * (z - z₀) ^ s := by
  intro a w₁ w₂' D U
  obtain ⟨ha_sum, hw₁_diff, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  obtain ⟨hΦ_diff, _, hΦ_op⟩ := hasDerivAt_and_operator_mul_log hw₁_diff hw₁_sol
  set ψ : ℂ → ℂ := fun w => (w - z₀) ^ α₂ * ∑' s, b' s * (w - z₀) ^ s
  set Φ : ℂ → ℂ := fun w => w₁ w * Complex.log (w - z₀)
  have hψ_diff : DifferentiableOn ℂ ψ U := fun w hw =>
    (hasDerivAt_cpow_mul_tsum hb'_sum hw.1 hw.2).differentiableAt.differentiableWithinAt
  have hw₂'_eq : w₂' = fun w => ψ w + c' * Φ w := by ext w; dsimp [w₂', ψ, Φ]; ring
  have hD_hasSum : ∀ u : ℂ, ‖u‖ < r → HasSum (fun s => D s * u ^ s)
      ((∑' s : ℕ, (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) * u ^ s) +
        c' * (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s))) := fun u hu =>
    (((hasSum_operator_cpow_series (σ := α₂) (fun w hw0 hwr => (hf w hw0 hwr).summable)
        (fun w hw0 hwr => (hg w hw0 hwr).summable) hb'_sum hu).summable.hasSum).add
      ((hasSum_regularSingularLogForcing_mul_pow (α₂ := α₂) (N := N)
        (fun w hw0 hwr => (hf w hw0 hwr).summable) ha_sum hu).mul_left c')).congr_fun
      fun _ => by dsimp [D]; ring
  refine ⟨by rw [hw₂'_eq]; exact hψ_diff.add (hΦ_diff.const_mul c'),
    fun u hu => (hD_hasSum u hu).summable, fun z ⟨hzs, hzb⟩ => ?_⟩
  have hopen := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  have hzU : z ∈ U := ⟨hzs, hzb⟩
  have hlin := secondOrder_operator_add_const_mul (f := f) (g := g) (c' := c') (z := z)
    (Eventually.mono (hopen.mem_nhds hzU) fun _ hw => hψ_diff.differentiableAt (hopen.mem_nhds hw))
    (Eventually.mono (hopen.mem_nhds hzU) fun _ hw => hΦ_diff.differentiableAt (hopen.mem_nhds hw))
    ((hψ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
    ((hΦ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
  rw [hw₂'_eq, hlin, operator_cpow_mul_tsum_eq (σ := α₂) hf hg hb'_sum hzs hzb,
    hΦ_op z hzU, (hD_hasSum (z - z₀) hzb).tsum_eq]
  set u : ℂ := z - z₀; have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  set A₁ : ℂ → ℂ := fun w => ∑' s, a s * w ^ s
  have hdw₁ : deriv w₁ z = u ^ (α₂ + (N : ℂ) - 1) * ((α₂ + N) * A₁ u + u * deriv A₁ u) :=
    (hasDerivAt_cpow_mul_tsum ha_sum hzs hzb).deriv
  have hcpow1 : u ^ (α₂ + (N : ℂ)) = u ^ (α₂ + (N : ℂ) - 1) * u := by
    simpa [Nat.cast_one, pow_one] using cpow_eq_cpow_sub_natCast_mul_pow hu0 (α₂ + (N : ℂ)) 1
  have hcpow2 : u ^ α₂ = u ^ (α₂ - 2) * u ^ 2 := by
    simpa using cpow_eq_cpow_sub_natCast_mul_pow hu0 α₂ 2
  have hcpow_N : (u ^ 2)⁻¹ * u ^ (α₂ + (N : ℂ)) = u ^ (α₂ - 2) * u ^ N := by
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_natCast, hcpow2]
    field_simp [hu0]
  rw [(hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq]; dsimp only [w₁, A₁, u] at hdw₁ ⊢; rw [hdw₁]
  linear_combination
    c' * (2 * (u ^ 2)⁻¹ * ((α₂ + ↑N) * A₁ u + u * deriv A₁ u)) * hcpow1.symm +
    c' * (2 * u * deriv A₁ u + (2 * (α₂ + ↑N) + u * f z - 1) * A₁ u) * hcpow_N

/-- **Logarithmic second solution at a regular singularity** (DLMF 2.7.6). When the indicial
polynomial factors as `(α - α₁)(α - α₂)` with `α₁ - α₂ = N ∈ ℕ`, the series
`∑ regularSingularSecondCoeff fs gs α₂ N s * (z - z₀)^s` converges on `‖z - z₀‖ < r`, and
`w₂(z) = (z - z₀)^{α₂} ∑' s, b s * (z - z₀)^s + c * w₁(z) * Complex.log (z - z₀)` is a
holomorphic solution of `w'' + f w' + g w = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem regularSingular_second_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let a := regularSingularCoeff fs gs α₁
    let b := regularSingularSecondCoeff fs gs α₂ N
    let c := regularSingularLogMultiplier fs gs α₂ N
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) + c * w₁ z * Complex.log (z - z₀)
    (∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0 := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨ha_sum, _, _⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  set a := regularSingularCoeff fs gs (α₂ + N)
  set b := regularSingularSecondCoeff fs gs α₂ N
  set c := regularSingularLogMultiplier fs gs α₂ N
  have hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s := by
    refine summable_of_perturbed_indicial_rec (σ := α₂)
      (E := fun s => -c * regularSingularLogForcing fs a α₂ N s) (s₁ := 0)
      (fun z hz0 hzr => (hf z hz0 hzr).summable) (fun z hz0 hzr => (hg z hz0 hzr).summable)
      (fun ρ hρ0 hρr => ?_) (fun s _ => by
        linear_combination regularSingularSecondCoeff_rec hfact s)
    obtain ⟨CF, hCF0, hCF⟩ := FormalMultilinearSeries.exists_norm_mul_pow_le_of_norm_sub_lt
      (regularSingularLogForcing fs a α₂ N) z₀ hρ0.le hρr fun z _ hzr =>
      (hasSum_regularSingularLogForcing_mul_pow (α₂ := α₂) (N := N)
        (fun w hw0 hwr => (hf w hw0 hwr).summable) ha_sum hzr).summable
    refine ⟨‖c‖ * CF, by positivity, fun s => ?_⟩
    rw [norm_mul, norm_neg, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      ((hCF s).trans (le_mul_of_one_le_right hCF0.le (le_add_of_nonneg_left (Nat.cast_nonneg s))))
      (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm
  obtain ⟨hw₂_diff, _, hw₂_op⟩ := operator_second_ansatz_eq (c' := c) hf hg hfact hb_sum
  refine ⟨hb_sum, hw₂_diff, fun z hzs hzb => ?_⟩
  rw [hw₂_op z ⟨hzs, hzb⟩]
  simp only [b, c, regularSingularSecondCoeff_rec hfact, zero_mul, tsum_zero, mul_zero]

/-- **Analytic uniqueness of the second solution's coefficients**: for `0 < r` and
`α₁ - α₂ = N ∈ ℕ`, if `b' : ℕ → ℂ` and `c' : ℂ` satisfy `b' N = 0`, the normalization
`(N = 0 → c' = 1) ∧ (1 ≤ N → b' 0 = 1)`, convergence of `∑ b'_s (z - z₀)^s` on `‖z - z₀‖ < r`,
and `(z - z₀)^{α₂} ∑ b'_s (z - z₀)^s + c' w₁(z) log(z - z₀)` solves `w'' + f w' + g w = 0` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, then `b' = regularSingularSecondCoeff fs gs α₂ N` and
`c' = regularSingularLogMultiplier fs gs α₂ N`. -/
theorem eq_regularSingularSecondCoeff_of_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ}
    {f g : ℂ → ℂ} {fs gs b' : ℕ → ℂ} {c' : ℂ} (hr : 0 < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N)
    (hb'N : b' N = 0)
    (hc'0 : N = 0 → c' = 1)
    (hb'0 : 1 ≤ N → b' 0 = 1)
    (hb'_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b' s * (z - z₀) ^ s)
    (hsol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      let w₁ := fun w => (w - z₀) ^ α₁ * ∑' s, regularSingularCoeff fs gs α₁ s * (w - z₀) ^ s
      let w₂' := fun w =>
        (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) + c' * w₁ w * Complex.log (w - z₀)
      deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z = 0) :
    b' = regularSingularSecondCoeff fs gs α₂ N ∧
      c' = regularSingularLogMultiplier fs gs α₂ N := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨_, hD_sum, hD_op⟩ := operator_second_ansatz_eq (c' := c') hf hg hfact hb'_sum
  exact eq_regularSingularSecondCoeff_of_rec hfact hb'N hc'0 hb'0 <|
    eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := α₂ - 2) hr (fun u _ hu => hD_sum u hu)
      fun z hzs hzb => (hD_op z ⟨hzs, hzb⟩).symm.trans (hsol z hzs hzb)

/-! ### Worked example: Euler–Cauchy equation `w'' - 2 z⁻² w = 0` at `z₀ = 0` -/

-- For `f = 0` and `g(z) = -2 z⁻²` at `z₀ = 0` (`f₀ = 0`, `g₀ = -2`), the indicial polynomial
-- factors as `(α - 2)(α + 1)` with roots `2` and `-1` differing by `N = 3`, all higher series
-- coefficients vanish, `c = 0`, and the canonical solutions on `slitPlane` are `z²` and `z⁻¹`.
example :
    let fs : ℕ → ℂ := 0
    let gs : ℕ → ℂ := Pi.single 0 (-2)
    (∀ α, indicialPoly (fs 0) (gs 0) α = (α - 2) * (α - (-1))) ∧
      (∀ s : ℕ, 1 ≤ s → regularSingularCoeff fs gs 2 s = 0) ∧
      regularSingularLogMultiplier fs gs (-1) 3 = 0 ∧
      (∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff fs gs (-1) 3 s = 0) ∧
      (∀ z ∈ slitPlane,
        (z ^ (2 : ℂ) * ∑' s, regularSingularCoeff fs gs 2 s * z ^ s) = z ^ 2) ∧
      ∀ z ∈ slitPlane,
        (z ^ (-1 : ℂ) * (∑' s, regularSingularSecondCoeff fs gs (-1) 3 s * z ^ s) +
          regularSingularLogMultiplier fs gs (-1) 3 *
            (z ^ (2 : ℂ) * ∑' s, regularSingularCoeff fs gs 2 s * z ^ s) * Complex.log z) =
          z⁻¹ := by
  intro fs gs
  have hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - 2) * (α - (-1)) := fun α => by
    simp only [indicialPoly_def, fs, gs, Pi.zero_apply, Pi.single_eq_same]; ring
  have hconv0 (σ : ℂ) (d : ℕ → ℂ) (m : ℕ) :
      (∑ k ∈ range m, ((σ + (k : ℂ)) * fs (m - k) + gs (m - k)) * d k) = 0 :=
    sum_eq_zero fun k hk => by
      have hmk : m - k ≠ 0 := by have := mem_range.mp hk; omega
      simp [fs, gs, Pi.single_eq_of_ne hmk]
  have ha_zero : ∀ s : ℕ, 1 ≤ s → regularSingularCoeff fs gs 2 s = 0 := fun s hs => by
    rw [regularSingularCoeff_of_ne_zero fs gs 2 (by omega), hconv0, mul_zero]
  have hc_zero : regularSingularLogMultiplier fs gs (-1) 3 = 0 := by
    rw [regularSingularLogMultiplier_of_ne_zero fs gs (-1) (by decide), hconv0, mul_zero]
  have hb_zero : ∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff fs gs (-1) 3 s = 0 := fun s hs => by
    rcases lt_trichotomy s 3 with hs3 | rfl | hs3
    · rw [regularSingularSecondCoeff_eq_regularSingularCoeff_of_lt fs gs (-1) hs3,
        regularSingularCoeff_of_ne_zero fs gs (-1) (by omega), hconv0, mul_zero]
    · exact regularSingularSecondCoeff_self fs gs (-1) 3
    · have htwo : (-1 : ℂ) + (3 : ℂ) = 2 := by norm_num
      have hQ := indicialPoly_add_nat_ne_zero_of_ne (f₀ := fs 0) (g₀ := gs 0) (α₂ := -1) (N := 3)
        (fun α => by simpa [htwo] using hfact α)
        (by omega) hs3.ne'
      exact mul_left_cancel₀ hQ (by
        simp [indicialPoly_mul_regularSingularSecondCoeff_of_gt hs3 hQ, hc_zero, hconv0])
  refine ⟨hfact, ha_zero, hc_zero, hb_zero, fun z _ => ?_, fun z _ => ?_⟩
  · rw [tsum_eq_single 0 fun s hs => by simp [ha_zero s (Nat.pos_of_ne_zero hs)]]; simp
  · rw [tsum_eq_single 0 fun s hs => by simp [hb_zero s (Nat.pos_of_ne_zero hs)]]
    simp [hc_zero, Complex.cpow_neg_one]

end TauCeti
