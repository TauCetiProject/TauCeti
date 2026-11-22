/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Factorial.Cast
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Gronwall.Discrete
import TauCeti.Analysis.ODE.Wronskian
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Convergent series solutions at a regular singularity

For `f, g` around `z₀` with `(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and
`(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`, let
`Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α = (α - α₁)(α - α₂)` (`Re α₂ ≤ Re α₁`). On the slit
punctured disc `TauCeti.regularSingularSlitDisc z₀ r`
(`{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`, via
`TauCeti.Analysis.Complex.PowerSeries.BranchCut`):
* Slit-plane logarithmic-product forcing identities for the second-order operator
  (`TauCeti.deriv_deriv_add_mul_deriv_add_mul_mul_log_sub`, `TauCeti.operator_mul_log`).
* Any sequence solving the indicial recursion at a root `ρ` of `Q` converges on `‖z - z₀‖ < r` and
  yields a solution of `w'' + f w' + g w = 0` (`TauCeti.regularSingular_solution`). For a
  non-resonant root `ρ` (`Q(ρ + s) ≠ 0` for `s ≥ 1`), the canonical series
  `TauCeti.regularSingularSolution` (`TauCeti.regularSingularSolution_eq`) satisfies
  `TauCeti.regularSingularCoeff_solution` (returning series convergence and `IsSolution` for
  `TauCeti.regularSingularEquation`), with normalized uniqueness
  `TauCeti.eq_regularSingularCoeff_of_solution`.
* The shifted logarithmic forcing coefficients `TauCeti.regularSingularLogForcing` sum to the
  Euler–Frobenius forcing series (`TauCeti.hasSum_regularSingularLogForcing_mul_pow`).
* When `α₁ - α₂ = N ∈ ℕ`, `TauCeti.regularSingularSecondSolution`
  (`TauCeti.regularSingularSecondSolution_eq`) defines the holomorphic second solution
  `w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c w₁(z) log(z - z₀)` (`b_N = 0`, `c = 1` for
  `N = 0`, `b₀ = 1` for `N ≥ 1`) with `∑ b_s (z - z₀)^s` convergent on `‖z - z₀‖ < r` and solving
  `TauCeti.regularSingularEquation` (`TauCeti.regularSingular_second_solution`, uniqueness
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

/-! ### Logarithmic product identities for the second-order operator -/

/-- Pointwise logarithmic-product identity for the second-order linear operator
`L(w) = w'' + f w' + g w` on the logarithm branch `z - z₀ ∈ Complex.slitPlane`: if `w` is
differentiable near `z` and `deriv w` is differentiable at `z`, then
`L(w * log(· - z₀)) z - log(z - z₀) * L(w) z` equals
`((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z)`. -/
theorem deriv_deriv_add_mul_deriv_add_mul_mul_log_sub
    {z₀ z : ℂ} (hzs : z - z₀ ∈ Complex.slitPlane) {f g w : ℂ → ℂ}
    (hw : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w u) (hdw : DifferentiableAt ℂ (deriv w) z) :
    let Φ : ℂ → ℂ := fun u ↦ w u * Complex.log (u - z₀)
    (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) -
        Complex.log (z - z₀) * (deriv (deriv w) z + f z * deriv w z + g z * w z) =
      ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z) := by
  intro Φ
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hsub : HasDerivAt (fun u : ℂ ↦ u - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hU_log : ∀ᶠ u in 𝓝 z, u - z₀ ∈ Complex.slitPlane :=
    (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).mem_nhds hzs
  have hderiv1 : ∀ᶠ u in 𝓝 z,
      HasDerivAt Φ (deriv w u * Complex.log (u - z₀) + (u - z₀)⁻¹ * w u) u := by
    filter_upwards [hw, hU_log] with u hu hsu
    exact hu.hasDerivAt.mul_log_sub hsu
  have hd1 : deriv Φ z = deriv w z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w z :=
    hderiv1.self_of_nhds.deriv
  have hev : deriv Φ =ᶠ[𝓝 z]
      (deriv w * (fun u : ℂ ↦ Complex.log (u - z₀)) + (fun u : ℂ ↦ (u - z₀)⁻¹) * w) :=
    hderiv1.mono fun _ hu ↦ hu.deriv
  have hd2 : deriv (deriv Φ) z = deriv (deriv w) z * Complex.log (z - z₀) +
      2 * (z - z₀)⁻¹ * deriv w z - ((z - z₀) ^ 2)⁻¹ * w z := by
    rw [(((hdw.hasDerivAt.mul (hsub.clog hzs)).add
      ((hsub.inv hzu0).mul hw.self_of_nhds.hasDerivAt)).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.inv_apply]; field_simp [hzu0]; ring
  rw [hd1, hd2]
  dsimp only [Φ]
  field_simp [hzu0]
  ring

/-- Domain-level logarithmic-product forcing identity: on any open set `U` contained in the
translated slit plane `{z | z - z₀ ∈ Complex.slitPlane}`, if `w₁` is complex differentiable on `U`
and solves `w₁'' + f w₁' + g w₁ = 0` on `U`, then `Φ(z) = w₁(z) * Complex.log (z - z₀)` is complex
differentiable on `U` and satisfies
`L(Φ) z = ((z - z₀) ^ 2)⁻¹ * (2 (z - z₀) w₁'(z) + ((z - z₀) f(z) - 1) w₁(z))` on `U`. -/
theorem operator_mul_log {z₀ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hU_slit : ∀ z ∈ U, z - z₀ ∈ slitPlane) {f g w₁ : ℂ → ℂ}
    (hw₁ : DifferentiableOn ℂ w₁ U)
    (hsol₁ : ∀ z ∈ U, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0) :
    let Φ : ℂ → ℂ := fun z => w₁ z * Complex.log (z - z₀)
    DifferentiableOn ℂ Φ U ∧
      ∀ z ∈ U, deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z =
        ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w₁ z + ((z - z₀) * f z - 1) * w₁ z) := by
  intro Φ
  have hw₁_at (z) (hz : z ∈ U) : DifferentiableAt ℂ w₁ z := hw₁.differentiableAt (hU.mem_nhds hz)
  refine ⟨fun z hz =>
      ((hw₁_at z hz).hasDerivAt.mul_log_sub (hU_slit z hz)).differentiableAt.differentiableWithinAt,
    fun z hz => ?_⟩
  have hw₁_ev : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w₁ u :=
    Eventually.mono (hU.mem_nhds hz) hw₁_at
  have hdw₁ : DifferentiableAt ℂ (deriv w₁) z :=
    (hw₁.deriv hU).differentiableAt (hU.mem_nhds hz)
  have hpt := deriv_deriv_add_mul_deriv_add_mul_mul_log_sub (f := f) (g := g)
    (hU_slit z hz) hw₁_ev hdw₁
  linear_combination hpt + Complex.log (z - z₀) * hsol₁ z hz

/-! ### Internal analytic and majorant helpers -/

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

/-- Convolution-sum majorant for a single step of an indicial recursion at radius `ρ > 0`. -/
private theorem indicial_conv_sum_bound {σ : ℂ} {ρ Mf Mg : ℝ} {fs gs d : ℕ → ℂ} {s : ℕ}
    (hρ_pos : 0 < ρ) (hs1 : 1 ≤ s)
    (hMf : ∀ k, ‖fs k‖ * ρ ^ k ≤ Mf) (hMg : ∀ k, ‖gs k‖ * ρ ^ k ≤ Mg) :
    (∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s) ≤
      ((Mf + Mg) * (‖σ‖ + 1) * s) * ∑ k ∈ range s, ‖d k‖ * ρ ^ k := by
  have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  rw [mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk_lt := mem_range.mp hk
  have hks : (k : ℝ) ≤ s := by exact_mod_cast hk_lt.le
  have htri : ‖(σ + k) * fs (s - k) + gs (s - k)‖ ≤ (‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
    have h1 := norm_add_le ((σ + k) * fs (s - k)) (gs (s - k))
    have h2 := norm_add_le σ (k : ℂ)
    rw [norm_mul] at h1; rw [Complex.norm_natCast] at h2; nlinarith [norm_nonneg (fs (s - k))]
  have hfgk :
      ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k) ≤ (Mf + Mg) * (‖σ‖ + 1) * s := by
    have hMf0 : 0 ≤ Mf := (by positivity : 0 ≤ ‖fs 0‖ * ρ ^ 0).trans (hMf 0)
    have hMg0 : 0 ≤ Mg := (by positivity : 0 ≤ ‖gs 0‖ * ρ ^ 0).trans (hMg 0)
    have hm := mul_le_mul_of_nonneg_right htri (pow_nonneg hρ_pos.le (s - k))
    have hMf' := hMf (s - k); have hMg' := hMg (s - k)
    nlinarith [norm_nonneg σ, le_mul_of_one_le_right (norm_nonneg σ) hs_ge1]
  have hρs : ρ ^ s = ρ ^ (s - k) * ρ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_lt.le]
  calc ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s
      = (‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k)) * (‖d k‖ * ρ ^ k) := by
          rw [norm_mul, hρs]; ring
    _ ≤ ((Mf + Mg) * (‖σ‖ + 1) * s) * (‖d k‖ * ρ ^ k) :=
        mul_le_mul_of_nonneg_right hfgk (by positivity)

/-- One-step majorant inequality for a perturbed indicial convolution recursion at radius
`ρ > 0`. -/
private theorem indicial_rec_step_bound {σ : ℂ} {ρ Mf Mg CE : ℝ} {fs gs d E : ℕ → ℂ} {s K : ℕ}
    (hρ_pos : 0 < ρ) (hs1 : 1 ≤ s)
    (hMf : ∀ k, ‖fs k‖ * ρ ^ k ≤ Mf) (hMg : ∀ k, ‖gs k‖ * ρ ^ k ≤ Mg)
    (hCE : ‖E s‖ * ρ ^ s ≤ CE * (s + 1))
    (hK : 2 * ((Mf + Mg) * (‖σ‖ + 1) + 2 * CE) < K)
    (hQs : (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly (fs 0) (gs 0) (σ + s)‖)
    (hds : indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ‖d s‖ * ρ ^ s ≤ (K : ℝ) / s * (1 + ∑ k ∈ range s, ‖d k‖ * ρ ^ k) := by
  -- 1. Nonnegativity of majorant constants and weighted norms `μ k = ‖d k‖ * ρ ^ k`.
  have hCE0 : 0 ≤ CE := nonneg_of_mul_nonneg_left
    ((by positivity : 0 ≤ ‖E s‖ * ρ ^ s).trans hCE) (by positivity : (0 : ℝ) < s + 1)
  set C₁ : ℝ := (Mf + Mg) * (‖σ‖ + 1); set μ : ℕ → ℝ := fun k => ‖d k‖ * ρ ^ k
  set S : ℝ := 1 + ∑ k ∈ range s, μ k
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hμ_nn : ∀ k, 0 ≤ μ k := fun _ => by positivity
  -- 2. Apply triangle inequality to the recurrence and bound the convolution plus error `E s`.
  have hconv := indicial_conv_sum_bound (σ := σ) (d := d) hρ_pos hs1 hMf hMg
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
  -- 3. Combine the lower bound `s² / 2 ≤ ‖Q(σ + s)‖` with `2 * (C₁ + 2 * CE) < K`.
  have hsum_nn : 0 ≤ ∑ k ∈ range s, μ k := sum_nonneg fun k _ => hμ_nn k
  have hMf0 : 0 ≤ Mf := (by positivity : 0 ≤ ‖fs 0‖ * ρ ^ 0).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (by positivity : 0 ≤ ‖gs 0‖ * ρ ^ 0).trans (hMg 0)
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
    (hE : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∃ C : ℝ, ∀ s : ℕ, ‖E s‖ * ρ ^ s ≤ C * (s + 1))
    (hd : ∀ s : ℕ, s₁ ≤ s → indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ∀ z, ‖z - z₀‖ < r → Summable fun s => d s * (z - z₀) ^ s := by
  intro z hz
  set ρ : ℝ := (‖z - z₀‖ + r) / 2
  have hρ_gt : ‖z - z₀‖ < ρ := by dsimp [ρ]; linarith
  have hρ_pos : 0 < ρ := (norm_nonneg _).trans_lt hρ_gt
  have hρ_lt : ρ < r := by dsimp [ρ]; linarith
  obtain ⟨Mf, _, hMf⟩ :=
    FormalMultilinearSeries.exists_norm_mul_pow_le_of_norm_sub_lt fs z₀ hρ_pos.le hρ_lt hf
  obtain ⟨Mg, _, hMg⟩ :=
    FormalMultilinearSeries.exists_norm_mul_pow_le_of_norm_sub_lt gs z₀ hρ_pos.le hρ_lt hg
  obtain ⟨CE, hCE⟩ := hE ρ hρ_pos hρ_lt
  obtain ⟨s₂, hs₂1, hQ⟩ := exists_sq_div_two_le_norm_indicialPoly (fs 0) (gs 0) σ
  set s₀ : ℕ := max s₁ s₂; have hs₀1 : 1 ≤ s₀ := hs₂1.trans (le_max_right _ _)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ((Mf + Mg) * (‖σ‖ + 1) + 2 * CE))
  set μ : ℕ → ℝ := fun s => ‖d s‖ * ρ ^ s; set S₀ : ℝ := 1 + ∑ k ∈ range s₀, μ k
  have hμ0 : ∀ s, 0 ≤ μ s := fun _ => by positivity
  have hS₀_pos : 1 ≤ S₀ := by dsimp [S₀]; linarith [sum_nonneg fun k (_ : k ∈ range s₀) => hμ0 k]
  have hpoly := add_sum_range_le_mul_pow_of_le_div hs₀1 zero_le_one hμ0 fun s hs =>
    indicial_rec_step_bound hρ_pos (hs₀1.trans hs) hMf hMg (hCE s) hK
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

/-- Absolute summability on `‖u‖ < r` from summability on a punctured disc `0 < ‖z - z₀‖ < r`. -/
private theorem summable_norm_of_punctured {z₀ : ℂ} {r : ℝ} {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) : Summable fun s : ℕ => ‖fs s * u ^ s‖ :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt fs z₀
    ((norm_nonneg u).trans_lt hu) hf).summable_norm_mul_pow_ofScalars
    (eNorm_lt_ofReal_iff.mpr hu)

/-- Shared `HasFPowerSeriesOnBall`, norm summability, and first Euler-derivative sums for
`A(w) = ∑' s, c s * w ^ s` at `u` with `‖u‖ < r`. -/
private theorem hasSum_ofScalars_and_mul_deriv {z₀ : ℂ} {r : ℝ} {c : ℕ → ℂ}
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A : ℂ → ℂ := fun w => ∑' s, c s * w ^ s
    HasFPowerSeriesOnBall A (FormalMultilinearSeries.ofScalars ℂ c) 0 (ENNReal.ofReal r) ∧
      Summable (fun s : ℕ => ‖c s * u ^ s‖) ∧
      Summable (fun s : ℕ => ‖(s : ℂ) * c s * u ^ s‖) ∧
      HasSum (fun s : ℕ => c s * u ^ s) (A u) ∧
      HasSum (fun s : ℕ => (s : ℂ) * c s * u ^ s) (u * deriv A u) := by
  intro A
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt c z₀ hr
    fun z _ hzr => hc z hzr
  refine ⟨hpA, hpA.summable_norm_mul_pow_ofScalars hue, ?_, ?_, hpA.hasSum_mul_deriv_ofScalars hue⟩
  · simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      c (hue.trans_le hpA.r_le) 1
  · simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
      hpA.hasSum (mem_eball_zero_iff.mpr hue)

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
  obtain ⟨hpA, hc_norm, hsc_norm, hA0, hA1⟩ := hasSum_ofScalars_and_mul_deriv hc hu
  have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ := summable_norm_of_punctured hf hu
  have hg_norm : Summable fun s : ℕ => ‖gs s * u ^ s‖ := summable_norm_of_punctured hg hu
  have hA2 : HasSum (fun s : ℕ => (s : ℂ) * ((s : ℂ) - 1) * c s * u ^ s)
      (u ^ 2 * deriv (deriv A) u) := by
    have hraw :=
      hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv (eNorm_lt_ofReal_iff.mpr hu) 2
    rw [iteratedDeriv_succ, iteratedDeriv_one, zero_add] at hraw
    simpa only [Nat.cast_descFactorial_two ℂ] using hraw
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

/-! ### Slit punctured disc and `LinearEquation` setup -/

/-- The slit punctured open disc `{z : ℂ | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}` as an
open subset of `ℂ`. -/
def regularSingularSlitDisc (z₀ : ℂ) (r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r},
    isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r⟩

/-- Membership in `regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem mem_regularSingularSlitDisc {z₀ z : ℂ} {r : ℝ} :
    z ∈ regularSingularSlitDisc z₀ r ↔ z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r :=
  Iff.rfl

/-- Carrier set of `regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem coe_regularSingularSlitDisc (z₀ : ℂ) (r : ℝ) :
    (regularSingularSlitDisc z₀ r : Set ℂ) = {z : ℂ | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} :=
  (rfl)

/-- Preconnectedness of `regularSingularSlitDisc z₀ r`. -/
theorem isPreconnected_regularSingularSlitDisc (z₀ : ℂ) (r : ℝ) :
    IsPreconnected (regularSingularSlitDisc z₀ r : Set ℂ) :=
  isPreconnected_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r

/-- Construct the second-order `LinearEquation (regularSingularSlitDisc z₀ r) 2` associated with
`w'' + f w' + g w = 0` from regular-singularity series expansions of `(z - z₀) f(z)` and
`(z - z₀)² g(z)` on `0 < ‖z - z₀‖ < r`. -/
def regularSingularEquation {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z)) :
    LinearEquation (regularSingularSlitDisc z₀ r) 2 :=
  LinearEquation.ofTwo f g
    ((FormalMultilinearSeries.analyticOnNhd_of_hasSum_ofScalars_of_norm_sub_lt z₀
      (k := 1) fun w hw0 hwr => by simpa only [pow_one] using hf w hw0 hwr).differentiableOn.mono
        fun _ hz => ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hz.2,
          sub_ne_zero.mp (Complex.slitPlane_ne_zero hz.1)⟩)
    ((FormalMultilinearSeries.analyticOnNhd_of_hasSum_ofScalars_of_norm_sub_lt z₀
      (k := 2) hg).differentiableOn.mono fun _ hz =>
        ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hz.2,
          sub_ne_zero.mp (Complex.slitPlane_ne_zero hz.1)⟩)

/-- The order-zero coefficient of `regularSingularEquation hf hg` evaluates to `g` on
`regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem extend_regularSingularEquation_coeff_zero {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    {z : ℂ} (hz : z ∈ regularSingularSlitDisc z₀ r) :
    HolomorphicFunctions.extend ((regularSingularEquation hf hg).coeff 0) z = g z :=
  LinearEquation.extend_ofTwo_coeff_zero _ _ hz

/-- The order-one coefficient of `regularSingularEquation hf hg` evaluates to `f` on
`regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem extend_regularSingularEquation_coeff_one {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    {z : ℂ} (hz : z ∈ regularSingularSlitDisc z₀ r) :
    HolomorphicFunctions.extend ((regularSingularEquation hf hg).coeff 1) z = f z :=
  LinearEquation.extend_ofTwo_coeff_one _ _ hz

/-- Solutions of `regularSingularEquation hf hg` are precisely complex-differentiable functions on
`regularSingularSlitDisc z₀ r` satisfying `w'' + f w' + g w = 0` there. -/
@[simp]
theorem isSolution_regularSingularEquation_iff {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (y : ℂ → ℂ) :
    (regularSingularEquation hf hg).IsSolution y ↔
      DifferentiableOn ℂ y (regularSingularSlitDisc z₀ r) ∧
        ∀ z ∈ regularSingularSlitDisc z₀ r,
          deriv (deriv y) z + f z * deriv y z + g z * y z = 0 :=
  LinearEquation.isSolution_ofTwo_iff _ _ y

/-! ### Primary series solution at a regular singularity -/

/-- Canonical Frobenius series solution
`(z - z₀)^ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀)^s` attached to an indicial
root `ρ`. -/
def regularSingularSolution (fs gs : ℕ → ℂ) (z₀ ρ z : ℂ) : ℂ :=
  (z - z₀) ^ ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀) ^ s

/-- Application formula for `regularSingularSolution`. -/
theorem regularSingularSolution_apply (fs gs : ℕ → ℂ) (z₀ ρ z : ℂ) :
    regularSingularSolution fs gs z₀ ρ z =
      (z - z₀) ^ ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀) ^ s :=
  (rfl)

/-- Function-level formula for `regularSingularSolution`. -/
theorem regularSingularSolution_eq (fs gs : ℕ → ℂ) (z₀ ρ : ℂ) :
    regularSingularSolution fs gs z₀ ρ = fun z =>
      (z - z₀) ^ ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀) ^ s :=
  funext fun z => regularSingularSolution_apply fs gs z₀ ρ z

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
    (fun _ _ _ => ⟨0, fun _ => by simp⟩) (fun s hs => by simp [ha s hs])
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

/-- Specialization of `regularSingular_solution` to the canonical normalized series
`regularSingularSolution fs gs z₀ ρ` (`a₀ = 1`) attached to a non-resonant indicial root `ρ`,
yielding series convergence on `‖z - z₀‖ < r` and `IsSolution` for
`regularSingularEquation hf hg`. -/
theorem regularSingularCoeff_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s => regularSingularCoeff fs gs ρ s * (z - z₀) ^ s) ∧
      (regularSingularEquation hf hg).IsSolution (regularSingularSolution fs gs z₀ ρ) := by
  obtain ⟨hsum, hdiff, hsol⟩ := regularSingular_solution hf hg hρ fun _ hs =>
    indicialPoly_mul_regularSingularCoeff hs (hres _ hs)
  exact ⟨hsum, (isSolution_regularSingularEquation_iff hf hg _).mpr
    ⟨hdiff, fun z hz => hsol z hz.1 hz.2⟩⟩

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
theorem hasSum_regularSingularLogForcing_mul_pow {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ}
    {fs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (ha : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A₁ : ℂ → ℂ := fun w => ∑' s, a s * w ^ s
    HasSum (fun s => regularSingularLogForcing fs a α₂ N s * u ^ s)
      (u ^ N * (2 * u * deriv A₁ u +
        (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u)) := by
  intro A₁
  obtain ⟨_, ha_norm, _, hA0, hA1⟩ := hasSum_ofScalars_and_mul_deriv ha hu
  have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ := summable_norm_of_punctured hf hu
  have hprod := hasSum_sum_range_mul_of_summable_norm ha_norm hf_norm
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
  -- Shift by `N`: terms below `N` vanish by `regularSingularLogForcing_of_lt`.
  rw [← hasSum_nat_add_iff' N]
  have hprefix : ∑ s ∈ range N, regularSingularLogForcing fs a α₂ N s * u ^ s = 0 :=
    sum_eq_zero fun s hs => by simp [regularSingularLogForcing_of_lt _ _ _ (mem_range.mp hs)]
  rw [hprefix, sub_zero]
  refine (hunshifted.mul_left (u ^ N)).congr_fun fun m => ?_
  rw [regularSingularLogForcing_of_le _ _ _ (Nat.le_add_left N m), Nat.add_sub_cancel, pow_add]
  push_cast; ring

/-- Algebraic recombination of `(z - z₀)^α` powers when adding the `(z - z₀)^α₂` series part
to `c'` times the logarithmic forcing of `w₁(z) = (z - z₀)^{α₂ + N} A₁(z - z₀)`. -/
private theorem operator_second_ansatz_cpow_recombine {u α₂ : ℂ} {N : ℕ} (hu0 : u ≠ 0)
    (c' A₁ dA₁ fz S : ℂ) :
    u ^ (α₂ - 2) * S + c' * ((u ^ 2)⁻¹ *
      (2 * u * (u ^ (α₂ + (N : ℂ) - 1) * ((α₂ + N) * A₁ + u * dA₁)) +
        (u * fz - 1) * (u ^ (α₂ + (N : ℂ)) * A₁))) =
      u ^ (α₂ - 2) *
        (S + c' * (u ^ N * (2 * u * dA₁ + (2 * (α₂ + N) + u * fz - 1) * A₁))) := by
  have hcpow1 : u ^ (α₂ + (N : ℂ)) = u ^ (α₂ + (N : ℂ) - 1) * u := by
    simpa [Nat.cast_one, pow_one] using cpow_eq_cpow_sub_natCast_mul_pow hu0 (α₂ + (N : ℂ)) 1
  have hcpow2 : u ^ α₂ = u ^ (α₂ - 2) * u ^ 2 := by
    simpa using cpow_eq_cpow_sub_natCast_mul_pow hu0 α₂ 2
  have hcpow_N : (u ^ 2)⁻¹ * u ^ (α₂ + (N : ℂ)) = u ^ (α₂ - 2) * u ^ N := by
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_natCast, hcpow2]
    field_simp [hu0]
  linear_combination
    c' * (2 * (u ^ 2)⁻¹ * ((α₂ + ↑N) * A₁ + u * dA₁)) * hcpow1.symm +
    c' * (2 * u * dA₁ + (2 * (α₂ + ↑N) + u * fz - 1) * A₁) * hcpow_N

/-- Shared operator formula for any second-solution candidate
`w₂'(z) = (z - z₀)^{α₂} ∑ b' s * (z - z₀)^s + c' * w₁(z) * log(z - z₀)` when `α₁ = α₂ + N`. -/
private theorem operator_second_ansatz_eq {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs b' : ℕ → ℂ} {c' : ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (ha_sum : ∀ z, ‖z - z₀‖ < r →
      Summable fun s => regularSingularCoeff fs gs (α₂ + N) s * (z - z₀) ^ s)
    (hw₁_sol : (regularSingularEquation hf hg).IsSolution
      (regularSingularSolution fs gs z₀ (α₂ + N)))
    (hlog_sum : ∀ u : ℂ, ‖u‖ < r →
      let a := regularSingularCoeff fs gs (α₂ + N)
      HasSum (fun s => regularSingularLogForcing fs a α₂ N s * u ^ s)
        (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s)))
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
  -- 1. Unpack holomorphy and the ODE for `w₁`, and derive the forcing on `Φ = w₁ * log(· - z₀)`.
  obtain ⟨hw₁_diff, hw₁_op⟩ := (isSolution_regularSingularEquation_iff hf hg _).mp hw₁_sol
  have hopen := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  obtain ⟨hΦ_diff, hΦ_op⟩ := operator_mul_log (z₀ := z₀) hopen (fun _ hz => hz.1) hw₁_diff hw₁_op
  set ψ : ℂ → ℂ := fun w => (w - z₀) ^ α₂ * ∑' s, b' s * (w - z₀) ^ s
  set Φ : ℂ → ℂ := fun w => regularSingularSolution fs gs z₀ (α₂ + N) w * Complex.log (w - z₀)
  have hψ_diff : DifferentiableOn ℂ ψ U := fun w hw =>
    (hasDerivAt_cpow_mul_tsum hb'_sum hw.1 hw.2).differentiableAt.differentiableWithinAt
  have hw₁_fn : w₁ = regularSingularSolution fs gs z₀ (α₂ + N) :=
    (regularSingularSolution_eq fs gs z₀ (α₂ + N)).symm
  have hw₂'_eq : w₂' = fun w => ψ w + c' * Φ w := by
    dsimp only [w₂', ψ, Φ]; rw [hw₁_fn]; simp only [mul_assoc]
  -- 2. Sum the series contributions from `ψ` and the logarithmic forcing series `D`.
  have hD_hasSum : ∀ u : ℂ, ‖u‖ < r → HasSum (fun s => D s * u ^ s)
      ((∑' s : ℕ, (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) * u ^ s) +
        c' * (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s))) := fun u hu =>
    (((hasSum_operator_cpow_series (σ := α₂) (fun w hw0 hwr => (hf w hw0 hwr).summable)
        (fun w hw0 hwr => (hg w hw0 hwr).summable) hb'_sum hu).summable.hasSum).add
      ((hlog_sum u hu).mul_left c')).congr_fun fun _ => by dsimp [D]; ring
  refine ⟨by rw [hw₂'_eq]; exact hψ_diff.add (hΦ_diff.const_mul c'),
    fun u hu => (hD_hasSum u hu).summable, fun z ⟨hzs, hzb⟩ => ?_⟩
  -- 3. Apply operator linearity to `ψ + c' Φ` and recombine the `cpow` prefactors.
  have hzU : z ∈ U := ⟨hzs, hzb⟩
  have hlin := secondOrder_operator_add_const_mul (f := f) (g := g) (c' := c') (z := z)
    (Eventually.mono (hopen.mem_nhds hzU) fun _ hw => hψ_diff.differentiableAt (hopen.mem_nhds hw))
    (Eventually.mono (hopen.mem_nhds hzU) fun _ hw => hΦ_diff.differentiableAt (hopen.mem_nhds hw))
    ((hψ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
    ((hΦ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
  rw [hw₂'_eq, hlin, operator_cpow_mul_tsum_eq (σ := α₂) hf hg hb'_sum hzs hzb,
    hΦ_op z hzU, (hD_hasSum (z - z₀) hzb).tsum_eq]
  have hu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hdw₁ : deriv w₁ z = (z - z₀) ^ (α₂ + (N : ℂ) - 1) *
      ((α₂ + N) * (∑' s, a s * (z - z₀) ^ s) +
        (z - z₀) * deriv (fun w => ∑' s, a s * w ^ s) (z - z₀)) :=
    (hasDerivAt_cpow_mul_tsum ha_sum hzs hzb).deriv
  rw [(hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq, ← hw₁_fn, hdw₁]
  exact operator_second_ansatz_cpow_recombine hu0 c' _ _ (f z) _

/-- Canonical logarithmic second Frobenius solution attached to indicial roots `α₁ = α₂ + N`:
`(z - z₀)^{α₂} ∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀)^s +`
`regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *`
`Complex.log (z - z₀)`. -/
def regularSingularSecondSolution (fs gs : ℕ → ℂ) (z₀ α₂ : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (z - z₀) ^ α₂ * (∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) +
    regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *
      Complex.log (z - z₀)

/-- Application formula for `regularSingularSecondSolution`. -/
theorem regularSingularSecondSolution_apply (fs gs : ℕ → ℂ) (z₀ α₂ : ℂ) (N : ℕ) (z : ℂ) :
    regularSingularSecondSolution fs gs z₀ α₂ N z =
      (z - z₀) ^ α₂ * (∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) +
        regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *
          Complex.log (z - z₀) :=
  (rfl)

/-- Function-level formula for `regularSingularSecondSolution`. -/
theorem regularSingularSecondSolution_eq (fs gs : ℕ → ℂ) (z₀ α₂ : ℂ) (N : ℕ) :
    regularSingularSecondSolution fs gs z₀ α₂ N = fun z =>
      (z - z₀) ^ α₂ * (∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) +
        regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *
          Complex.log (z - z₀) :=
  funext fun z => regularSingularSecondSolution_apply fs gs z₀ α₂ N z

/-- In the resonant case `α₁ = α₂ + N` (`N : ℕ`), the primary root `α₂ + N` satisfies the
non-resonance condition, so `regularSingularCoeff fs gs (α₂ + N)` converges on `‖z - z₀‖ < r`,
`regularSingularSolution fs gs z₀ (α₂ + N)` solves `regularSingularEquation hf hg`, and the
shifted logarithmic forcing coefficients sum to the Euler–Frobenius forcing series. -/
theorem regularSingularCoeff_solution_add_nat {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂)) :
    (∀ z, ‖z - z₀‖ < r →
        Summable fun s => regularSingularCoeff fs gs (α₂ + N) s * (z - z₀) ^ s) ∧
      (regularSingularEquation hf hg).IsSolution
        (regularSingularSolution fs gs z₀ (α₂ + N)) ∧
      ∀ u : ℂ, ‖u‖ < r →
        let a := regularSingularCoeff fs gs (α₂ + N)
        HasSum (fun s => regularSingularLogForcing fs a α₂ N s * u ^ s)
          (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
            (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s)) := by
  obtain ⟨ha_sum, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  exact ⟨ha_sum, hw₁_sol, fun u hu => hasSum_regularSingularLogForcing_mul_pow (α₂ := α₂) (N := N)
    (fun w hw0 hwr => (hf w hw0 hwr).summable) ha_sum hu⟩

/-- **Logarithmic second solution at a regular singularity** (DLMF 2.7.6). When the indicial
polynomial factors as `(α - α₁)(α - α₂)` with `α₁ - α₂ = N ∈ ℕ`, the series
`∑ regularSingularSecondCoeff fs gs α₂ N s * (z - z₀)^s` converges on `‖z - z₀‖ < r`, and
`regularSingularSecondSolution fs gs z₀ α₂ N` solves `regularSingularEquation hf hg` on
`regularSingularSlitDisc z₀ r`. -/
theorem regularSingular_second_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    (∀ z, ‖z - z₀‖ < r →
        Summable fun s => regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) ∧
      (regularSingularEquation hf hg).IsSolution
        (regularSingularSecondSolution fs gs z₀ α₂ N) := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨ha_sum, hw₁_sol, hlog_sum⟩ := regularSingularCoeff_solution_add_nat hf hg hfact
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
      (regularSingularLogForcing fs a α₂ N) z₀ hρ0.le hρr fun z _ hzr => (hlog_sum _ hzr).summable
    refine ⟨‖c‖ * CF, fun s => ?_⟩
    rw [norm_mul, norm_neg, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      ((hCF s).trans (le_mul_of_one_le_right hCF0.le (le_add_of_nonneg_left (Nat.cast_nonneg s))))
      (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm
  obtain ⟨hw₂_diff, _, hw₂_op⟩ :=
    operator_second_ansatz_eq (c' := c) hf hg ha_sum hw₁_sol hlog_sum hb_sum
  have hw₂_eq : regularSingularSecondSolution fs gs z₀ α₂ N = fun w =>
      (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) +
        c * ((w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s) * Complex.log (w - z₀) := by
    rw [regularSingularSecondSolution_eq, regularSingularSolution_eq]
  rw [← hw₂_eq] at hw₂_diff hw₂_op
  refine ⟨hb_sum, (isSolution_regularSingularEquation_iff hf hg _).mpr ⟨hw₂_diff, fun z hz => ?_⟩⟩
  rw [hw₂_op z hz]
  simp only [b, c, regularSingularSecondCoeff_rec hfact, zero_mul, tsum_zero, mul_zero]

/-- **Analytic uniqueness of the second solution's coefficients**: for `0 < r` and
`α₁ - α₂ = N ∈ ℕ`, if `b' : ℕ → ℂ` and `c' : ℂ` satisfy `b' N = 0`, the normalization
`(N = 0 → c' = 1) ∧ (1 ≤ N → b' 0 = 1)`, convergence of `∑ b'_s (z - z₀)^s` on `‖z - z₀‖ < r`,
and `(z - z₀)^{α₂} ∑ b'_s (z - z₀)^s + c' * regularSingularSolution fs gs z₀ α₁ z * log(z - z₀)`
solves `w'' + f w' + g w = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, then
`b' = regularSingularSecondCoeff fs gs α₂ N` and `c' = regularSingularLogMultiplier fs gs α₂ N`. -/
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
      let w₂' := fun w =>
        (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) +
          c' * regularSingularSolution fs gs z₀ α₁ w * Complex.log (w - z₀)
      deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z = 0) :
    b' = regularSingularSecondCoeff fs gs α₂ N ∧
      c' = regularSingularLogMultiplier fs gs α₂ N := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨ha_sum, hw₁_sol, hlog_sum⟩ := regularSingularCoeff_solution_add_nat hf hg hfact
  obtain ⟨_, hD_sum, hD_op⟩ :=
    operator_second_ansatz_eq (c' := c') hf hg ha_sum hw₁_sol hlog_sum hb'_sum
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
