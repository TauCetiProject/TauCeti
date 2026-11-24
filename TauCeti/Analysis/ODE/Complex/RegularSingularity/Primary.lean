/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall.Polynomial

/-!
# Frobenius series solutions at a regular singularity

Consider the equation `w'' + f(z) w' + g(z) w = 0` near a point `z₀` at which `f` has at most a
simple pole and `g` at most a double pole, so that on a punctured disc `0 < |z - z₀| < r`

* `(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and
* `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ`,

with both series convergent there. Its indicial polynomial is
`Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α = α (α - 1) + f₀ α + g₀`.
Let `ρ` be a root of `Q` such that no `ρ + s` with `s ≥ 1` is a root, and let `a₀ = 1` and

`Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`

(DLMF 2.7.5). Then the series `∑ aₛ (z - z₀)ˢ` converges on the whole disc `|z - z₀| < r`
(`TauCeti.le_radius_ofScalars_of_regularSingular`, a specialization of the perturbed convergence
theorem `TauCeti.le_radius_ofScalars_of_perturbed_regularSingular`), and the Frobenius series
`w(z) = (z - z₀)^ρ ∑ aₛ (z - z₀)ˢ`, with the principal power, is holomorphic and solves the equation
on the slit punctured disc `{z | z - z₀ ∈ slitPlane, |z - z₀| < r}` (DLMF 2.7.4;
`TauCeti.regularSingular_solution`).

The root `ρ` always qualifies when it is the root of larger real part, and so does the other root
when the two roots do not differ by an integer. The normalization `a₀ = 1` is customary; the
statements hold for every `a₀`. For example, Bessel's equation, with `f(z) = 1/z` and
`g(z) = 1 - ν²/z²` at `z₀ = 0`, has the indicial roots `±ν`, and when `2ν` is not a negative
integer the solution at `ρ = ν` is a constant multiple of the Bessel function `J_ν`.

## Implementation notes

Convergence is proved by a polynomial-growth majorant via
`TauCeti.add_sum_range_le_mul_pow_of_le_div`: for `s` sufficiently large,
`|Q(σ + s)| ≥ s² / 2`, so on any sub-radius `t < r` the weighted coefficients `|dₛ| tˢ` grow at
most polynomially (`≤ S₀ s^K`), yielding convergence on `|z - z₀| < r` even in the presence of a
convergent forcing perturbation `Eₛ`. The equation is verified on coefficients: in terms of the
Euler operator `ζ d/dζ`, `(z - z₀)^{2 - σ}` times the left-hand side applied to
`(z - z₀)^σ ∑ cₛ (z - z₀)ˢ` is the power series whose `s`-th coefficient is
`Q(σ + s) cₛ + ∑_{k < s} ((σ + k) f_{s-k} + g_{s-k}) cₖ`, a Cauchy product of absolutely convergent
series (`TauCeti.hasSum_eulerOperator_ofScalars`,
`TauCeti.deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum`).

## References

* NIST Digital Library of Mathematical Functions, §2.7(i), equations (2.7.2)–(2.7.5),
  <https://dlmf.nist.gov/2.7.i>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 4, §§3–4.
-/

public section

open Complex Filter Finset FormalMultilinearSeries Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Convergence of Frobenius series (perturbed and unperturbed) -/

/-- Lower bound `s² / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖` for sufficiently large `s : ℕ`. -/
private theorem exists_sq_div_two_le_norm_indicialPoly (f₀ g₀ σ : ℂ) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ := by
  set B : ℝ := ‖2 * σ + f₀ - 1‖ + ‖indicialPoly f₀ g₀ σ‖
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B + 1)
  refine ⟨max N 1, le_max_right _ _, fun s hs ↦ ?_⟩
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
    calc ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖
        ≤ ‖2 * σ + f₀ - 1‖ * s + ‖indicialPoly f₀ g₀ σ‖ := by
          simpa only [norm_mul, Complex.norm_natCast] using
            norm_add_le ((2 * σ + f₀ - 1) * (s : ℂ)) (indicialPoly f₀ g₀ σ)
      _ ≤ ‖2 * σ + f₀ - 1‖ * s + ‖indicialPoly f₀ g₀ σ‖ * s := by
          gcongr
          exact le_mul_of_one_le_right (norm_nonneg _) hs1
      _ = B * s := by dsimp only [B]; ring
  calc (s : ℝ) ^ 2 / 2
      = (s : ℝ) ^ 2 - ((s : ℝ) / 2) * s := by ring
    _ ≤ (s : ℝ) ^ 2 - B * s := by
        gcongr
        linarith
    _ ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ := by linarith

/-- Convolution-sum majorant for a single step of an indicial recursion at radius `ρ > 0`. -/
private theorem indicial_conv_sum_bound {σ : ℂ} {ρ Mf Mg : ℝ} {fs gs d : ℕ → ℂ} {s : ℕ}
    (hρ_pos : 0 < ρ) (hs1 : 1 ≤ s)
    (hMf : ∀ k, ‖fs k‖ * ρ ^ k ≤ Mf) (hMg : ∀ k, ‖gs k‖ * ρ ^ k ≤ Mg) :
    (∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s) ≤
      ((Mf + Mg) * (‖σ‖ + 1) * s) * ∑ k ∈ range s, ‖d k‖ * ρ ^ k := by
  have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hMf0 : 0 ≤ Mf := (by positivity : 0 ≤ ‖fs 0‖ * ρ ^ 0).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (by positivity : 0 ≤ ‖gs 0‖ * ρ ^ 0).trans (hMg 0)
  rw [mul_sum]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hk_lt := mem_range.mp hk
  have hks : (k : ℝ) ≤ s := by exact_mod_cast hk_lt.le
  have htri : ‖(σ + k) * fs (s - k) + gs (s - k)‖ ≤ (‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
    calc ‖(σ + k) * fs (s - k) + gs (s - k)‖
        ≤ ‖σ + k‖ * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
          simpa only [norm_mul] using norm_add_le ((σ + k) * fs (s - k)) (gs (s - k))
      _ ≤ (‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
          gcongr
          simpa only [Complex.norm_natCast] using norm_add_le σ (k : ℂ)
  have hfgk :
      ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k) ≤ (Mf + Mg) * (‖σ‖ + 1) * s := by
    have h1s : (1 : ℝ) ≤ (‖σ‖ + 1) * s :=
      one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg σ]) hs_ge1
    calc ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k)
        ≤ ((‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖) * ρ ^ (s - k) := by gcongr
      _ = (‖σ‖ + k) * (‖fs (s - k)‖ * ρ ^ (s - k)) + ‖gs (s - k)‖ * ρ ^ (s - k) := by ring
      _ ≤ (‖σ‖ + s) * Mf + Mg := by gcongr; exacts [hMf (s - k), hMg (s - k)]
      _ ≤ (‖σ‖ + 1) * s * Mf + (‖σ‖ + 1) * s * Mg := by
          gcongr
          · calc ‖σ‖ + s ≤ ‖σ‖ * s + s := by
                  gcongr; exact le_mul_of_one_le_right (norm_nonneg _) hs_ge1
              _ = (‖σ‖ + 1) * s := by ring
          · exact le_mul_of_one_le_left hMg0 h1s
      _ = (Mf + Mg) * (‖σ‖ + 1) * s := by ring
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
    (hCE : ‖E s‖ * ρ ^ s ≤ CE)
    (hK : 2 * ((Mf + Mg) * (‖σ‖ + 1) + CE) < K)
    (hQs : (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly (fs 0) (gs 0) (σ + s)‖)
    (hds : indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ‖d s‖ * ρ ^ s ≤ (K : ℝ) / s * (1 + ∑ k ∈ range s, ‖d k‖ * ρ ^ k) := by
  have hCE0 : 0 ≤ CE := (by positivity : 0 ≤ ‖E s‖ * ρ ^ s).trans hCE
  set C₁ : ℝ := (Mf + Mg) * (‖σ‖ + 1)
  set μ : ℕ → ℝ := fun k ↦ ‖d k‖ * ρ ^ k
  set S : ℝ := 1 + ∑ k ∈ range s, μ k
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hμ_nn : ∀ k, 0 ≤ μ k := fun _ ↦ by positivity
  have hconv := indicial_conv_sum_bound (σ := σ) (d := d) hρ_pos hs1 hMf hMg
  have hrec : ‖indicialPoly (fs 0) (gs 0) (σ + s)‖ * μ s =
      ‖-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s‖ * ρ ^ s := by
    simpa [μ, norm_mul, mul_assoc] using congrArg (fun w ↦ ‖w‖ * ρ ^ s) hds
  have htri_tot := mul_le_mul_of_nonneg_right
    (norm_add_le (-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k)) (E s))
    (pow_nonneg hρ_pos.le s)
  rw [norm_neg, add_mul] at htri_tot
  have hnorm_sum : ‖∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s ≤
      ∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
  have hsum_nn : 0 ≤ ∑ k ∈ range s, μ k := sum_nonneg fun k _ ↦ hμ_nn k
  have hMf0 : 0 ≤ Mf := (by positivity : 0 ≤ ‖fs 0‖ * ρ ^ 0).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (by positivity : 0 ≤ ‖gs 0‖ * ρ ^ 0).trans (hMg 0)
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hsum_le : C₁ * s * (∑ k ∈ range s, μ k) + CE ≤ (C₁ + CE) * s * S := by
    have hCEs : CE ≤ (C₁ + CE) * s := by
      calc CE ≤ CE * s := le_mul_of_one_le_right hCE0 hs_ge1
        _ ≤ (C₁ + CE) * s := by gcongr; exact le_add_of_nonneg_left hC₁0
    calc C₁ * s * (∑ k ∈ range s, μ k) + CE
        ≤ (C₁ + CE) * s * (∑ k ∈ range s, μ k) + (C₁ + CE) * s := by
          gcongr; exact le_add_of_nonneg_right hCE0
      _ = (C₁ + CE) * s * S := by dsimp only [S]; ring
  have hprod_le : ((s : ℝ) ^ 2 / 2) * μ s ≤ ((K : ℝ) / 2 * s) * S := by
    have h1 := (mul_le_mul_of_nonneg_right hQs (hμ_nn s)).trans_eq hrec
    have hK' : (C₁ + CE) * s * S ≤ ((K : ℝ) / 2 * s) * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs_pos.le)
        (by dsimp [S]; linarith)
    linarith [h1, htri_tot, hnorm_sum, hconv, hCE, hsum_le, hK']
  have hprod' : ((s : ℝ) / 2) * (μ s * (s : ℝ)) ≤ ((s : ℝ) / 2) * ((K : ℝ) * S) := by
    calc ((s : ℝ) / 2) * (μ s * (s : ℝ)) = ((s : ℝ) ^ 2 / 2) * μ s := by ring
      _ ≤ ((K : ℝ) / 2 * s) * S := hprod_le
      _ = ((s : ℝ) / 2) * ((K : ℝ) * S) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hs_pos]
  exact le_of_mul_le_mul_left hprod' (by positivity)

/-- **Perturbed convergence of Frobenius series.** If `r` bounds from below the radii of
convergence of `∑ fₛ zˢ`, `∑ gₛ zˢ`, and a forcing series `∑ Eₛ zˢ`, and `dₛ` satisfies the
perturbed indicial recursion `Q(σ + s) dₛ = -∑_{k < s} ((σ + k) f_{s - k} + g_{s - k}) dₖ + Eₛ`
for all `s ≥ s₁`, then `r ≤ (ofScalars ℂ d).radius`. -/
theorem le_radius_ofScalars_of_perturbed_regularSingular {σ : ℂ} {fs gs d E : ℕ → ℂ}
    {r : ℝ≥0∞} {s₁ : ℕ}
    (hfs : r ≤ (ofScalars ℂ fs).radius) (hgs : r ≤ (ofScalars ℂ gs).radius)
    (hE : r ≤ (ofScalars ℂ E).radius)
    (hd : ∀ s : ℕ, s₁ ≤ s → indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    r ≤ (ofScalars ℂ d).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_
  rcases eq_or_ne R 0 with rfl | hR0
  · simp
  obtain ⟨t, hRt_coe, htr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hRr
  have hRt : (R : ℝ) < t := ENNReal.coe_lt_coe.mp hRt_coe
  have hR : (0 : ℝ) < R := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hR0)
  have ht : (0 : ℝ) < t := hR.trans hRt
  obtain ⟨Mf, -, hMf⟩ := (ofScalars ℂ fs).norm_mul_pow_le_of_lt_radius (htr.trans_le hfs)
  obtain ⟨Mg, -, hMg⟩ := (ofScalars ℂ gs).norm_mul_pow_le_of_lt_radius (htr.trans_le hgs)
  obtain ⟨CE, -, hCE⟩ := (ofScalars ℂ E).norm_mul_pow_le_of_lt_radius (htr.trans_le hE)
  simp only [ofScalars_norm] at hMf hMg hCE
  obtain ⟨s₂, hs₂1, hQ⟩ := exists_sq_div_two_le_norm_indicialPoly (fs 0) (gs 0) σ
  set s₀ : ℕ := max s₁ s₂
  have hs₀1 : 1 ≤ s₀ := hs₂1.trans (le_max_right _ _)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ((Mf + Mg) * (‖σ‖ + 1) + CE))
  set μ : ℕ → ℝ := fun s ↦ ‖d s‖ * (t : ℝ) ^ s
  set S₀ : ℝ := 1 + ∑ k ∈ range s₀, μ k
  have hμ0 : ∀ s, 0 ≤ μ s := fun _ ↦ by positivity
  have hS₀_pos : 0 ≤ S₀ := by dsimp [S₀]; linarith [sum_nonneg fun k (_ : k ∈ range s₀) ↦ hμ0 k]
  have hpoly := add_sum_range_le_mul_pow_of_le_div hs₀1 zero_le_one hμ0 fun s hs ↦
    indicial_rec_step_bound ht (hs₀1.trans hs) hMf hMg (hCE s) hK
      (hQ s ((le_max_right _ _).trans hs)) (hd s ((le_max_left _ _).trans hs))
  set q : ℝ := R / t
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_lt_one ht).mpr hRt
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_pow_mul_geometric_of_norm_lt_one K hq).mul_left (S₀ * 2 ^ K)) ?_
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (hs₀1.trans hs)
  have h2s : ((s + 1 : ℕ) : ℝ) ^ K ≤ 2 ^ K * (s : ℝ) ^ K := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) K
  have hμ_le_sum : μ s ≤ 1 + ∑ k ∈ range (s + 1), μ k := by
    rw [sum_range_succ]; linarith [sum_nonneg fun k (_ : k ∈ range s) ↦ hμ0 k]
  have hμ_le : μ s ≤ S₀ * (2 ^ K * (s : ℝ) ^ K) :=
    (hμ_le_sum.trans (hpoly (s + 1) (hs.trans (Nat.le_succ s)))).trans
      (mul_le_mul_of_nonneg_left h2s hS₀_pos)
  rw [Real.norm_of_nonneg (by positivity), ofScalars_norm,
    show (R : ℝ) = t * q from (mul_div_cancel₀ _ ht.ne').symm, mul_pow, ← mul_assoc, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hμ_le (by positivity)).trans_eq (by ring)

/-- **Convergence of the Frobenius series.** Let `ρ` be a root of the indicial polynomial
`Q(α) = indicialPoly (fs 0) (gs 0) α` such that no `ρ + s` with `s ≥ 1` is a root, and let the
coefficients `aₛ` satisfy `Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`
(DLMF 2.7.5). Then the radius of convergence of `∑ aₛ zˢ` is at least every `r` that bounds
from below the radii of convergence of both `∑ fₛ zˢ` and `∑ gₛ zˢ`. -/
theorem le_radius_ofScalars_of_regularSingular {ρ : ℂ} {fs gs a : ℕ → ℂ} {r : ℝ≥0∞}
    (hfs : r ≤ (ofScalars ℂ fs).radius) (hgs : r ≤ (ofScalars ℂ gs).radius)
    (_hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (_hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
    r ≤ (ofScalars ℂ a).radius :=
  le_radius_ofScalars_of_perturbed_regularSingular (E := 0) (s₁ := 1) hfs hgs (by simp)
    fun s hs ↦ by simpa using ha s hs

/-! ### The Frobenius series solves the equation -/

/-- Coefficient expansion for the Euler–Frobenius operator applied to `S(ζ) = ∑ c_s ζ^s`:
inside the radii of convergence of `S`, `fs`, and `gs`,
`σ (σ - 1) S(ζ) + 2 σ ζ S'(ζ) + ζ² S''(ζ) + F (σ S(ζ) + ζ S'(ζ)) + G S(ζ)`
is the sum of the series with `s`-th coefficient
`indicialPoly (fs 0) (gs 0) (σ + s) * c_s + ∑_{k < s} ((σ + k) fs_{s - k} + gs_{s - k}) c_k`. -/
theorem hasSum_eulerOperator_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {σ ζ F G : 𝕜} {fs gs c : ℕ → 𝕜} {S : 𝕜 → 𝕜} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars 𝕜 c) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars 𝕜 fs).radius) (hζg : ‖ζ‖ₑ < (ofScalars 𝕜 gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) (hG : HasSum (fun s ↦ gs s * ζ ^ s) G) :
    HasSum (fun s : ℕ ↦ (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
        ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * ζ ^ s)
      (σ * (σ - 1) * S ζ + 2 * σ * (ζ * deriv S ζ) + ζ ^ 2 * deriv (deriv S) ζ +
        F * (σ * S ζ + ζ * deriv S ζ) + G * S ζ) := by
  -- the series of `S`, of `ζ S'` and of `ζ² S''`
  have h0 : HasSum (fun n ↦ c n * ζ ^ n) (S ζ) := by
    simpa [ofScalars_apply_eq, mul_comm] using hS.hasSum (mem_eball_zero_iff.mpr hζ)
  have h1 := hS.hasSum_mul_deriv_ofScalars hζ
  have h2 := hS.hasSum_sq_mul_deriv_deriv_ofScalars hζ
  -- absolute convergence of the factors of the two Cauchy products
  have hA := summable_norm_mul_pow_of_lt_radius c (hζ.trans_le hS.r_le)
  have hP : Summable fun n : ℕ ↦ ‖(σ + n) * c n * ζ ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((hA.mul_left ‖σ‖).add (summable_norm_natCast_mul_ofScalars c (hζ.trans_le hS.r_le)))
    rw [add_mul, add_mul]
    refine (norm_add_le _ _).trans_eq ?_
    rw [mul_assoc σ, norm_mul]
  have hfN := summable_norm_mul_pow_of_lt_radius fs hζf
  have hgN := summable_norm_mul_pow_of_lt_radius gs hζg
  have hPsum : HasSum (fun n : ℕ ↦ (σ + n) * c n * ζ ^ n) (σ * S ζ + ζ * deriv S ζ) := by
    convert (h0.mul_left σ).add h1 using 1
    ext n
    ring
  have hC1 := hasSum_sum_range_mul_of_summable_norm hP hfN
  have hC2 := hasSum_sum_range_mul_of_summable_norm hA hgN
  rw [hPsum.tsum_eq, hF.tsum_eq] at hC1
  rw [h0.tsum_eq, hG.tsum_eq] at hC2
  -- combine the Euler-operator terms and Cauchy products into the shifted coefficient sum
  have htotal := ((((h0.mul_left (σ * (σ - 1))).add (h1.mul_left (2 * σ))).add h2).add hC1).add hC2
  rw [mul_comm (σ * S ζ + ζ * deriv S ζ) F, mul_comm (S ζ) G] at htotal
  refine htotal.congr_fun fun s ↦ ?_
  rw [sum_range_succ_mul_pow (fun k ↦ (σ + k) * c k) fs ζ s, sum_range_succ_mul_pow c gs ζ s]
  have hsum : ((∑ k ∈ range s, (σ + k) * c k * fs (s - k)) +
      ∑ k ∈ range s, c k * gs (s - k)) * ζ ^ s =
      (∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * ζ ^ s := by
    rw [← sum_add_distrib]
    exact congrArg (· * ζ ^ s) (sum_congr rfl fun _ _ ↦ by ring)
  simp only [indicialPoly_def]
  linear_combination -hsum

/-- Power-series identity for the Euler–Frobenius operator applied to `A(u) = ∑' s, c s * u ^ s`
on `‖u‖ < r`. -/
theorem hasSum_eulerOperator_ofScalars_of_norm_sub_lt {z₀ σ : ℂ} {r : ℝ} {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s ↦ fs s * (z - z₀) ^ s)
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s ↦ gs s * (z - z₀) ^ s)
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ c s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A : ℂ → ℂ := fun w ↦ ∑' s, c s * w ^ s
    HasSum (fun s : ℕ ↦ (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
        ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s)
      ((u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) +
        (u * deriv A u + σ * A u) * (∑' s, fs s * u ^ s) +
        A u * (∑' s, gs s * u ^ s)) := by
  intro A
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt c z₀ hr fun z _ hzr ↦ hc z hzr
  have hfr := (hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt fs z₀ hr hf).r_le
  have hgr := (hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt gs z₀ hr hg).r_le
  have hf_sum := (summable_norm_mul_pow_of_norm_sub_lt fs z₀ hf hu).of_norm
  have hg_sum := (summable_norm_mul_pow_of_norm_sub_lt gs z₀ hg hu).of_norm
  have heul := hasSum_eulerOperator_ofScalars (σ := σ) hpA hue (hue.trans_le hfr) (hue.trans_le hgr)
    hf_sum.hasSum hg_sum.hasSum
  convert heul using 1
  ring

/-- Operator evaluation for `ψ(z) = (z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit punctured
disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`:
`ψ''(z) + f(z) ψ'(z) + g(z) ψ(z)` equals `(z - z₀)^(σ - 2)` times the indicial-operator
power series. -/
theorem deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum {z₀ σ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ c s * (z - z₀) ^ s)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    let ψ : ℂ → ℂ := fun w ↦ (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s
    deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z =
      (z - z₀) ^ (σ - 2) * ∑' s : ℕ,
        (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
          ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * (z - z₀) ^ s := by
  intro ψ
  set A : ℂ → ℂ := fun u ↦ ∑' s, c s * u ^ s
  set u : ℂ := z - z₀
  have hr : 0 < r := (norm_nonneg u).trans_lt hzb
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  have han := analyticOnNhd_tsum_ofScalars_of_norm_sub_lt c z₀ hr fun w _ ↦ hc w
  have hsub : HasDerivAt (fun w : ℂ ↦ w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hinner := (((han u (mem_ball_zero_iff.mpr hzb)).differentiableAt.hasDerivAt.comp_sub_const
    z z₀).const_mul σ).add (hsub.mul
      ((han.deriv u (mem_ball_zero_iff.mpr hzb)).differentiableAt.hasDerivAt.comp_sub_const z z₀))
  have hev : deriv ψ =ᶠ[𝓝 z] ((fun w : ℂ ↦ (w - z₀) ^ (σ - 1)) *
      ((fun w : ℂ ↦ σ * A (w - z₀)) + (fun w : ℂ ↦ w - z₀) * fun w : ℂ ↦ deriv A (w - z₀))) := by
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
  rw [(hasSum_eulerOperator_ofScalars_of_norm_sub_lt (σ := σ)
        (fun w hw0 hwr ↦ (hf w hw0 hwr).summable)
        (fun w hw0 hwr ↦ (hg w hw0 hwr).summable) hc hzb).tsum_eq,
    (hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq, (hg z (norm_pos_iff.mpr hu0) hzb).tsum_eq, hderiv2,
    (hasDerivAt_cpow_mul_tsum hc hzs hzb).deriv]
  dsimp only [ψ, A, u]; rw [hcpow1, hcpow2]; ring

/-- **The Frobenius series solution at a regular singularity** (DLMF 2.7.2–2.7.5). Suppose that
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ` on the punctured disc
`0 < ‖z - z₀‖ < r`. Let `ρ` be a root of the indicial polynomial
`Q(α) = indicialPoly (fs 0) (gs 0) α` such that no `ρ + s` with `s ≥ 1` is a root, and let
`Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`. Then `∑ aₛ (z - z₀)ˢ`
converges on the disc `‖z - z₀‖ < r`, and `w(z) = (z - z₀) ^ ρ ∑ aₛ (z - z₀)ˢ` is holomorphic on
the slit punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}` and solves
`w'' + f w' + g w = 0` there. The usual normalization `a₀ = 1` is not needed. -/
theorem regularSingular_solution {z₀ ρ : ℂ} {r : ℝ} {f g w : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k)
    (hw : w = fun z ↦ (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  have hfr := le_radius_ofScalars_of_summable fs fun ζ hζ0 hζ ↦ by
    simpa using (hf (ζ + z₀) (by simpa using hζ0)
      (by simpa using (eNorm_lt_ofReal_iff (x := ζ) (r := r)).mp hζ)).summable
  have hgr := le_radius_ofScalars_of_summable gs fun ζ hζ0 hζ ↦ by
    simpa using (hg (ζ + z₀) (by simpa using hζ0)
      (by simpa using (eNorm_lt_ofReal_iff (x := ζ) (r := r)).mp hζ)).summable
  have har := le_radius_ofScalars_of_regularSingular hfr hgr hρ hres ha
  have hsum : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s := fun z hz ↦
    (summable_norm_mul_pow_of_lt_radius a ((eNorm_lt_ofReal_iff.mpr hz).trans_le har)).of_norm
  refine ⟨hsum, fun z hz ↦ ?_, fun z hzs hz ↦ ?_⟩
  · rw [hw]
    exact (hasDerivAt_cpow_mul_tsum hsum hz.1 hz.2).differentiableAt.differentiableWithinAt
  · rw [hw, deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum (σ := ρ) hf hg hsum hzs hz]
    have hcoeff : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (ρ + s) * a s +
        ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k = 0 := fun s ↦ by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp [hρ]
      · simp [ha s hs]
    simp [hcoeff]

/-- A check of the hypotheses: for `w'' - 2 z⁻² w = 0` at `z₀ = 0` the indicial roots are `2` and
`-1`, and at `ρ = 2` the recursion gives `a₀ = 1` and `aₛ = 0` for `s ≥ 1`, so the Frobenius series
is `z ^ 2`. -/
example {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv fun z ↦ z ^ (2 : ℂ) * ∑' s, (if s = 0 then 1 else 0) * z ^ s) z +
        0 * deriv (fun z ↦ z ^ (2 : ℂ) * ∑' s, (if s = 0 then 1 else 0) * z ^ s) z +
      -2 / z ^ 2 * (z ^ (2 : ℂ) * ∑' s, (if s = 0 then 1 else 0) * z ^ s) = 0 := by
  have hgs (y : ℂ) (hy : y ≠ 0) :
      HasSum (fun s ↦ (if s = 0 then -2 else 0) * y ^ s) (y ^ 2 * (-2 / y ^ 2)) := by
    convert hasSum_ite_eq 0 (-2 : ℂ) using 1
    · ext s
      split_ifs <;> simp_all
    · field_simp
  refine (regularSingular_solution (z₀ := 0) (ρ := 2) (r := ‖z‖ + 1) (f := 0)
    (g := fun y ↦ -2 / y ^ 2) (fs := 0) (gs := fun s ↦ if s = 0 then -2 else 0)
    (a := fun s ↦ if s = 0 then 1 else 0) (fun y _ _ ↦ by simp [hasSum_zero])
    (fun y hy _ ↦ by simpa using hgs y (by simpa using hy)) (by norm_num [indicialPoly_def])
    (fun s hs ↦ ?_) (fun s hs ↦ ?_) (by simp)).2.2 z (by simpa using hz) (by simp)
  · have h1 : (s : ℂ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
    have h2 : (s : ℂ) + 3 ≠ 0 := by exact_mod_cast (by omega : s + 3 ≠ 0)
    convert mul_ne_zero h1 h2 using 1
    simp only [indicialPoly_def, Pi.zero_apply, ↓reduceIte]
    ring
  · have hs0 : s ≠ 0 := by omega
    simp only [hs0, ↓reduceIte, mul_zero]
    rw [eq_comm, neg_eq_zero]
    exact sum_eq_zero fun k hk ↦ by simp [Nat.sub_ne_zero_of_lt (mem_range.1 hk)]

end TauCeti
