/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Linear differential equations at ordinary points in the complex domain

At an ordinary point `z₀ ∈ ℂ`, a linear differential equation whose coefficients are holomorphic on
an open disc `Metric.eball z₀ r` (`0 < r ≤ ∞`) admits a unique holomorphic solution for any
prescribed initial data at `z₀`, and the Taylor series of that solution around `z₀` converges on the
entire disc (including `r = ∞`, when the coefficients are entire).

We establish global disc convergence directly by Cauchy's method of majorants for first-order linear
systems `v'(z) = A(z) (v(z)) + b(z)` in a complex Banach space `E`:

1. Holomorphic maps on `Metric.eball z₀ r` (`0 < r`) expand on the whole disc into Taylor series.
2. Equating power-series coefficients defines `TauCeti.linearSystemCoeff A b v₀`. On every smaller
   radius `ρ < r`, Cauchy bounds yield a scalar majorant `μ_{n+1} = ((n + 1 + α) / (n + 1)) μ_n`
   whose ratio tends to `1`, forcing the formal solution series to have radius at least `r`.
3. Termwise differentiation (`HasFPowerSeriesOnBall.fderiv`) and the Banach-space Cauchy product
   prove both solutionhood on `Metric.eball z₀ r` and uniqueness on preconnected open sets.

From the Banach-space theorem we deduce:
* For `TauCeti.LinearEquation U n`, `LinearEquation.initialJet` is injective on preconnected domains
  and a linear equivalence `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)` on every disc `Metric.eball a r`.
* For second-order equations `w'' + f(z) w' + g(z) w = 0`, `TauCeti.ordinaryPointCoeff` satisfies
  the two-step Cauchy-product recursion, converges on the whole disc `Metric.eball z₀ r` (and
  `Metric.ball z₀ R`), and gives unique solutions on preconnected domains and on `ℂ`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §1.1.
* NIST Digital Library of Mathematical Functions, §2.7(i), <https://dlmf.nist.gov/2.7>.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 3, §6.
-/

public noncomputable section

open Complex Filter Finset Metric Set TopologicalSpace Topology
open scoped BigOperators ENNReal Matrix NNReal Nat

namespace TauCeti

/-! ### Private Banach-space power-series and companion-matrix helpers -/

section PrivateHelpers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private def mkPiRingSeries (c : ℕ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)

@[simp]
private theorem mkPiRingSeries_coeff (c : ℕ → E) (n : ℕ) :
    (mkPiRingSeries c).coeff n = c n := by
  simp [mkPiRingSeries, FormalMultilinearSeries.coeff]

private theorem mkPiRingSeries_apply (c : ℕ → E) (n : ℕ) (y : ℂ) :
    mkPiRingSeries c n (fun _ ↦ y) = y ^ n • c n := by
  simp [mkPiRingSeries]

private theorem mkPiRingSeries_norm (c : ℕ → E) (n : ℕ) :
    ‖mkPiRingSeries c n‖ = ‖c n‖ :=
  ContinuousMultilinearMap.norm_mkPiRing (c n)

private theorem eq_mkPiRingSeries_coeff (p : FormalMultilinearSeries ℂ ℂ E) :
    p = mkPiRingSeries p.coeff := by
  ext1 n; exact (p.mkPiRing_coeff_eq n).symm

private theorem mkPiRingSeries_add (a b : ℕ → E) :
    mkPiRingSeries a + mkPiRingSeries b = mkPiRingSeries (a + b) := by
  rw [eq_mkPiRingSeries_coeff (mkPiRingSeries a + mkPiRingSeries b)]
  congr 1; ext n
  simp [FormalMultilinearSeries.coeff, mkPiRingSeries]

private theorem mkPiRingSeries_eq_ofScalars (c : ℕ → ℂ) :
    mkPiRingSeries c = FormalMultilinearSeries.ofScalars ℂ c := by
  rw [eq_mkPiRingSeries_coeff (FormalMultilinearSeries.ofScalars ℂ c)]
  congr 1; ext n
  exact (FormalMultilinearSeries.coeff_ofScalars (p := c) (n := n)).symm

private theorem sub_mem_eball_zero {z z₀ : ℂ} {r : ℝ≥0∞} (hz : z ∈ Metric.eball z₀ r) :
    z - z₀ ∈ Metric.eball (0 : ℂ) r := by
  rw [mem_eball_zero_iff, ← eDist_eq_eNorm_sub]; exact Metric.mem_eball.mp hz

private theorem exists_eball_subset_of_isOpen {U : Set ℂ} {z₀ : ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U) :
    ∃ r : ℝ≥0∞, 0 < r ∧ Metric.eball z₀ r ⊆ U := by
  obtain ⟨r, hr_pos, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  exact ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.mpr hr_pos, Metric.eball_ofReal.trans_subset hrU⟩

private theorem hasFPowerSeriesOnBall_eball [CompleteSpace E] {f : ℂ → E} {z₀ : ℂ} {r : ℝ≥0∞}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (Metric.eball z₀ r)) :
    HasFPowerSeriesOnBall f
      (mkPiRingSeries fun n ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n f z₀) z₀ r := by
  let c : ℕ → E := fun n ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n f z₀
  have hsum : ∀ {y : ℂ}, y ∈ Metric.eball (0 : ℂ) r →
      HasSum (fun n ↦ mkPiRingSeries c n fun _ ↦ y) (f (z₀ + y)) := by
    intro y hy
    have hzy : z₀ + y ∈ Metric.eball z₀ r := by
      rw [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_left]
      exact mem_eball_zero_iff.mp hy
    convert Complex.hasSum_taylorSeries_on_eball hf hzy using 1
    ext n; simp [c, smul_comm ((n ! : ℂ)⁻¹) (y ^ n)]
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_, hr, fun {y} hy ↦ hsum hy⟩
  have hR_mem : ((R : ℝ) : ℂ) ∈ Metric.eball (0 : ℂ) r := by
    rw [mem_eball_zero_iff]; simpa [eNorm_eq_nnNorm] using hRr
  have htend : Tendsto (fun n ↦ ‖mkPiRingSeries c n fun _ ↦ ((R : ℝ) : ℂ)‖) atTop (𝓝 0) := by
    simpa using (hsum hR_mem).summable.tendsto_atTop_zero.norm
  refine (mkPiRingSeries c).le_radius_of_tendsto (htend.congr fun n ↦ ?_)
  simp [norm_smul, mul_comm]

private theorem hasFPowerSeriesOnBall_deriv [CompleteSpace E] {f : ℂ → E} {c : ℕ → E}
    {z₀ : ℂ} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f (mkPiRingSeries c) z₀ r) :
    HasFPowerSeriesOnBall (deriv f) (mkPiRingSeries fun n ↦ ((n + 1 : ℂ)) • c (n + 1)) z₀ r := by
  have hfd := (ContinuousLinearMap.apply ℂ E (1 : ℂ)).comp_hasFPowerSeriesOnBall hf.fderiv
  convert hfd using 1
  · ext z; rfl
  · rw [eq_mkPiRingSeries_coeff ((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries
      (mkPiRingSeries c).derivSeries)]
    congr 1; ext n
    have hcoeff : (((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries
        (mkPiRingSeries c).derivSeries).coeff n) = ((mkPiRingSeries c).derivSeries.coeff n) 1 := rfl
    rw [hcoeff, (mkPiRingSeries c).derivSeries_coeff_one, mkPiRingSeries_coeff,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add_one]

private theorem hasSum_clm_apply_range [CompleteSpace F]
    {f : ℕ → E →L[ℂ] F} {g : ℕ → E} {A : E →L[ℂ] F} {v : E}
    (hf : HasSum f A) (hg : HasSum g v)
    (hfn : Summable fun n ↦ ‖f n‖) (hgn : Summable fun n ↦ ‖g n‖) :
    HasSum (fun n ↦ ∑ k ∈ range (n + 1), f (n - k) (g k)) (A v) := by
  have hprod_norm : Summable fun p : ℕ × ℕ ↦ ‖f p.1‖ * ‖g p.2‖ :=
    hfn.mul_of_nonneg hgn (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hprod : Summable fun p : ℕ × ℕ ↦ f p.1 (g p.2) :=
    .of_norm_bounded hprod_norm fun p ↦ (f p.1).le_opNorm (g p.2)
  have hrow : ∀ m : ℕ, HasSum (fun k ↦ f m (g k)) (f m v) := fun m ↦ hg.mapL (f m)
  have hcol : HasSum (fun m ↦ f m v) (A v) := hf.mapL (ContinuousLinearMap.apply ℂ F v)
  have hAv : HasSum (fun p : ℕ × ℕ ↦ f p.1 (g p.2)) (A v) := by
    obtain ⟨u, hu⟩ := hprod
    exact (HasSum.prod_fiberwise hu hrow).unique hcol ▸ hu
  have hsigma : HasSum (fun x : Σ n : ℕ, antidiagonal n ↦ f x.2.1.1 (g x.2.1.2)) (A v) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr hAv
  have hanti : HasSum (fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 (g kl.2)) (A v) := by
    convert hsigma.sigma fun n ↦ hasSum_fintype _ using 1
    ext n; exact (Finset.sum_finset_coe (fun kl : ℕ × ℕ ↦ f kl.1 (g kl.2)) (antidiagonal n)).symm
  refine hanti.congr_fun fun n ↦ ?_
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k m ↦ f m (g k)) n).symm

private theorem hasFPowerSeriesOnBall_clm_apply [CompleteSpace F]
    {A : ℂ → E →L[ℂ] F} {v : ℂ → E} {a : ℕ → E →L[ℂ] F} {c : ℕ → E} {z₀ : ℂ} {r : ℝ≥0∞}
    (hA : HasFPowerSeriesOnBall A (mkPiRingSeries a) z₀ r)
    (hv : HasFPowerSeriesOnBall v (mkPiRingSeries c) z₀ r) :
    HasFPowerSeriesOnBall (fun z ↦ A z (v z))
      (mkPiRingSeries fun n ↦ ∑ k ∈ range (n + 1), a (n - k) (c k)) z₀ r := by
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_, hA.r_pos, fun {y} hy ↦ ?_⟩
  · have hsumA : Summable fun n ↦ ‖a n‖ * (R : ℝ) ^ n := by
      simpa only [mkPiRingSeries_norm] using
        (mkPiRingSeries a).summable_norm_mul_pow (hRr.trans_le hA.r_le)
    have hsumv : Summable fun n ↦ ‖c n‖ * (R : ℝ) ^ n := by
      simpa only [mkPiRingSeries_norm] using
        (mkPiRingSeries c).summable_norm_mul_pow (hRr.trans_le hv.r_le)
    have hconv := summable_sum_mul_range_of_summable_mul
      (f := fun k ↦ ‖c k‖ * (R : ℝ) ^ k) (g := fun m ↦ ‖a m‖ * (R : ℝ) ^ m)
      (hsumv.mul_of_nonneg hsumA (fun _ ↦ by positivity) (fun _ ↦ by positivity))
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hconv
    rw [mkPiRingSeries_norm]
    calc
      ‖∑ k ∈ range (n + 1), a (n - k) (c k)‖ * (R : ℝ) ^ n
          ≤ ∑ k ∈ range (n + 1), ‖a (n - k) (c k)‖ * (R : ℝ) ^ n := by
            rw [← Finset.sum_mul]; gcongr; exact norm_sum_le _ _
      _ ≤ ∑ k ∈ range (n + 1), (‖c k‖ * (R : ℝ) ^ k) * (‖a (n - k)‖ * (R : ℝ) ^ (n - k)) := by
            refine Finset.sum_le_sum fun k hk ↦ ?_
            have hkn : k + (n - k) = n := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk))
            calc
              ‖a (n - k) (c k)‖ * (R : ℝ) ^ n
                  ≤ (‖a (n - k)‖ * ‖c k‖) * (R : ℝ) ^ (k + (n - k)) := by
                    rw [hkn]; gcongr; exact (a (n - k)).le_opNorm (c k)
              _ = (‖c k‖ * (R : ℝ) ^ k) * (‖a (n - k)‖ * (R : ℝ) ^ (n - k)) := by
                    rw [pow_add]; ring
  · have hyA := Metric.eball_subset_eball hA.r_le hy
    have hyv := Metric.eball_subset_eball hv.r_le hy
    have hprod := hasSum_clm_apply_range (hA.hasSum hy) (hv.hasSum hy)
      ((mkPiRingSeries a).summable_norm_apply hyA)
      ((mkPiRingSeries c).summable_norm_apply hyv)
    refine hprod.congr_fun fun n ↦ ?_
    rw [mkPiRingSeries_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k + (n - k) = n := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk))
    simp only [mkPiRingSeries_apply, smul_apply, map_smul, smul_smul]
    rw [← pow_add, hkn]

private theorem hasFPowerSeriesOnBall_mul_scalar {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {z₀ : ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f (mkPiRingSeries fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (mkPiRingSeries gs) z₀ r) :
    HasFPowerSeriesOnBall (fun z ↦ f z * g z)
      (mkPiRingSeries fun n ↦ ∑ k ∈ range (n + 1), fs (n - k) * gs k) z₀ r := by
  have hf_mul : HasFPowerSeriesOnBall (fun z ↦ ContinuousLinearMap.mul ℂ ℂ (f z))
      (mkPiRingSeries fun n ↦ ContinuousLinearMap.mul ℂ ℂ (fs n)) z₀ r := by
    convert (ContinuousLinearMap.mul ℂ ℂ).comp_hasFPowerSeriesOnBall hf using 1
    · rfl
    · rw [eq_mkPiRingSeries_coeff ((ContinuousLinearMap.mul ℂ ℂ).compFormalMultilinearSeries
        (mkPiRingSeries fs))]
      congr 1; ext n
      simp [FormalMultilinearSeries.coeff, mkPiRingSeries]
  exact hasFPowerSeriesOnBall_clm_apply hf_mul hg

private def matrixCLM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ∑ i : Fin n, ∑ j : Fin n,
    M i j • ((ContinuousLinearMap.single ℂ (fun _ : Fin n ↦ ℂ) i).comp
      (ContinuousLinearMap.proj j))

@[simp]
private theorem matrixCLM_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    matrixCLM M v = M *ᵥ v := by
  ext k; simp [matrixCLM, Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem differentiableOn_matrixCLM {n : ℕ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {U : Set ℂ}
    (hM : ∀ i j, DifferentiableOn ℂ (fun z ↦ M z i j) U) :
    DifferentiableOn ℂ (fun z ↦ matrixCLM (M z)) U :=
  DifferentiableOn.fun_sum fun i _ ↦ DifferentiableOn.fun_sum fun j _ ↦ (hM i j).smul_const _

end PrivateHelpers

/-! ### First-order complex linear ODE systems in a Banach space -/

section FirstOrderSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Formal Taylor coefficients of the solution to `v'(z) = A(z) (v(z)) + b(z)` with `v(z₀) = v₀`,
given the Taylor coefficient sequences `A` and `b` around `z₀`. -/
def linearSystemCoeff (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) : ℕ → E
  | 0 => v₀
  | n + 1 => ((n + 1 : ℂ))⁻¹ • (b n + ∑ k : Fin (n + 1), A (n - k) (linearSystemCoeff A b v₀ k))

/-- The zeroth Taylor coefficient of the system solution is the initial value `v₀`. -/
@[simp]
theorem linearSystemCoeff_zero (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) :
    linearSystemCoeff A b v₀ 0 = v₀ := by
  rw [linearSystemCoeff]

/-- Recurrence for the `(n + 1)`-st Taylor coefficient of a first-order linear system. -/
theorem linearSystemCoeff_succ (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) (n : ℕ) :
    linearSystemCoeff A b v₀ (n + 1) =
      ((n + 1 : ℂ))⁻¹ • (b n + ∑ k ∈ range (n + 1), A (n - k) (linearSystemCoeff A b v₀ k)) := by
  rw [linearSystemCoeff, Fin.sum_univ_eq_sum_range (fun k ↦ A (n - k) (linearSystemCoeff A b v₀ k))]

/-- Cleared-denominator form of `TauCeti.linearSystemCoeff_succ`. -/
theorem natCast_succ_smul_linearSystemCoeff_succ (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E)
    (n : ℕ) :
    ((n + 1 : ℂ)) • linearSystemCoeff A b v₀ (n + 1) =
      b n + ∑ k ∈ range (n + 1), A (n - k) (linearSystemCoeff A b v₀ k) := by
  rw [linearSystemCoeff_succ, smul_inv_smul₀ (Nat.cast_add_one_ne_zero n)]

/-- Homogeneous linear systems with zero initial value have identically zero Taylor coefficients. -/
@[simp]
theorem linearSystemCoeff_zero_zero (A : ℕ → E →L[ℂ] E) (n : ℕ) :
    linearSystemCoeff A 0 0 n = 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · exact linearSystemCoeff_zero A 0 0
    · rw [linearSystemCoeff_succ, Pi.zero_apply, zero_add,
        Finset.sum_eq_zero fun k hk ↦ by simp [ih k (mem_range.mp hk)], smul_zero]

private def majorantSeq (μ₀ α : ℝ) : ℕ → ℝ
  | 0 => μ₀
  | k + 1 => ((k + 1 + α) / (k + 1)) * majorantSeq μ₀ α k

private theorem le_radius_mkPiRingSeries_linearSystemCoeff
    {A : ℕ → E →L[ℂ] E} {b : ℕ → E} (v₀ : E) {r : ℝ≥0∞}
    (hA : r ≤ (mkPiRingSeries A).radius) (hb : r ≤ (mkPiRingSeries b).radius) :
    r ≤ (mkPiRingSeries (linearSystemCoeff A b v₀)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_
  obtain ⟨ρ, hRρ_coe, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hRr
  have hRρ : (R : ℝ) < ρ := ENNReal.coe_lt_coe.mp hRρ_coe
  have hρ_pos : (0 : ℝ) < ρ := R.2.trans_lt hRρ
  obtain ⟨CA, hCA_pos, hCA⟩ := (mkPiRingSeries A).norm_mul_pow_le_of_lt_radius (hρr.trans_le hA)
  obtain ⟨Cb, _, hCb⟩ := (mkPiRingSeries b).norm_mul_pow_le_of_lt_radius (hρr.trans_le hb)
  simp only [mkPiRingSeries_norm] at hCA hCb
  let α : ℝ := ρ * CA
  let μ₀ : ℝ := max ‖v₀‖ (ρ * Cb) + 1
  have hα : 0 ≤ α := mul_nonneg ρ.2 hCA_pos.le
  have hμ_pos : ∀ n, 0 < majorantSeq μ₀ α n := fun n ↦ by
    induction n <;> dsimp [majorantSeq] <;> positivity
  have hμ_step : ∀ n : ℕ, (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) =
      (n + 1 + α) * majorantSeq μ₀ α n := fun n ↦ by
    dsimp [majorantSeq]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn1]
  have hμ_sum : ∀ n, μ₀ + α * ∑ k ∈ range (n + 1), majorantSeq μ₀ α k ≤
      (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) := fun n ↦ by
    induction n with
    | zero =>
      rw [hμ_step 0]
      simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, majorantSeq]; linarith
    | succ n ih =>
      rw [sum_range_succ, mul_add, hμ_step (n + 1)]; push_cast; linarith [hμ_pos (n + 1)]
  have hd_le : ∀ n, ‖linearSystemCoeff A b v₀ n‖ * (ρ : ℝ) ^ n ≤ majorantSeq μ₀ α n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | n
      · simp only [linearSystemCoeff_zero, pow_zero, mul_one, majorantSeq]
        exact (le_max_left _ _).trans (lt_add_one _).le
      · have hn_norm : ‖((n + 1 : ℂ))‖ = (n + 1 : ℝ) := by exact_mod_cast Complex.norm_natCast _
        have hlhs : ((n + 1 : ℝ)) * (‖linearSystemCoeff A b v₀ (n + 1)‖ * (ρ : ℝ) ^ (n + 1)) =
            ‖((n + 1 : ℂ)) • linearSystemCoeff A b v₀ (n + 1)‖ * (ρ : ℝ) ^ (n + 1) := by
          rw [norm_smul, hn_norm, mul_assoc]
        have hbound : ((n + 1 : ℝ)) * (‖linearSystemCoeff A b v₀ (n + 1)‖ * (ρ : ℝ) ^ (n + 1)) ≤
            (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) := by
          rw [hlhs, natCast_succ_smul_linearSystemCoeff_succ]
          calc
            ‖b n + ∑ k ∈ range (n + 1), A (n - k) (linearSystemCoeff A b v₀ k)‖ * (ρ : ℝ) ^ (n + 1)
                ≤ (‖b n‖ + ∑ k ∈ range (n + 1),
                    ‖A (n - k) (linearSystemCoeff A b v₀ k)‖) * (ρ : ℝ) ^ (n + 1) := by
                  gcongr
                  exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
            _ = (ρ : ℝ) * (‖b n‖ * (ρ : ℝ) ^ n) + (ρ : ℝ) * ∑ k ∈ range (n + 1),
                    ‖A (n - k) (linearSystemCoeff A b v₀ k)‖ * (ρ : ℝ) ^ n := by
                  rw [pow_succ, add_mul, Finset.sum_mul, Finset.mul_sum]
                  exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ ↦ by ring)
            _ ≤ (ρ : ℝ) * Cb + (ρ : ℝ) * ∑ k ∈ range (n + 1), CA * majorantSeq μ₀ α k := by
                  refine add_le_add (mul_le_mul_of_nonneg_left (hCb n) ρ.2)
                    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk ↦ ?_) ρ.2)
                  have hkn : n - k + k = n :=
                    Nat.sub_add_cancel (Nat.lt_succ_iff.mp (mem_range.mp hk))
                  calc
                    ‖A (n - k) (linearSystemCoeff A b v₀ k)‖ * (ρ : ℝ) ^ n
                        ≤ (‖A (n - k)‖ * ‖linearSystemCoeff A b v₀ k‖) *
                            (ρ : ℝ) ^ (n - k + k) := by
                          rw [hkn]; gcongr; exact (A (n - k)).le_opNorm _
                    _ = (‖A (n - k)‖ * (ρ : ℝ) ^ (n - k)) *
                          (‖linearSystemCoeff A b v₀ k‖ * (ρ : ℝ) ^ k) := by rw [pow_add]; ring
                    _ ≤ CA * majorantSeq μ₀ α k :=
                          mul_le_mul (hCA (n - k)) (ih k (mem_range.mp hk))
                            (by positivity) hCA_pos.le
            _ = (ρ : ℝ) * Cb + α * ∑ k ∈ range (n + 1), majorantSeq μ₀ α k := by
                  rw [← Finset.mul_sum]; dsimp [α]; ring
            _ ≤ μ₀ + α * ∑ k ∈ range (n + 1), majorantSeq μ₀ α k := by
                  gcongr; exact (le_max_right _ _).trans (lt_add_one _).le
            _ ≤ (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) := hμ_sum n
        exact le_of_mul_le_mul_left hbound (by positivity)
  rcases eq_or_ne R 0 with rfl | hR0
  · simp
  have hR_pos : (0 : ℝ) < R := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hR0)
  let q : ℝ := R / ρ
  have hq_pos : 0 < q := div_pos hR_pos hρ_pos
  have hq_lt : q < 1 := (div_lt_one hρ_pos).mpr hRρ
  have hμq_sum : Summable fun n ↦ majorantSeq μ₀ α n * q ^ n := by
    refine summable_of_ratio_test_tendsto_lt_one hq_lt
      (Eventually.of_forall fun n ↦ ne_of_gt (mul_pos (hμ_pos n) (pow_pos hq_pos n))) ?_
    have hrat : (fun n : ℕ ↦ ‖majorantSeq μ₀ α (n + 1) * q ^ (n + 1)‖ /
        ‖majorantSeq μ₀ α n * q ^ n‖) = fun n : ℕ ↦ (1 + α / (n + 1 : ℝ)) * q := by
      ext n
      have h1 := hμ_pos n
      have h3 := pow_pos hq_pos n
      rw [Real.norm_of_nonneg (mul_pos (hμ_pos (n + 1)) (pow_pos hq_pos (n + 1))).le,
        Real.norm_of_nonneg (mul_pos h1 h3).le]
      dsimp [majorantSeq]
      rw [pow_succ]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [h1.ne', h3.ne', hn1]
    rw [hrat]
    have hinv : Tendsto (fun n : ℕ ↦ α / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).mul (tendsto_const_nhds (x := q))
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hμq_sum
  rw [mkPiRingSeries_norm]
  have hR_eq : (R : ℝ) = ρ * q := by dsimp [q]; field_simp [hρ_pos.ne']
  rw [hR_eq, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hd_le n) (pow_nonneg hq_pos.le n)

variable [CompleteSpace E]

/-- Any holomorphic solution of `v'(z) = A(z) (v(z)) + b(z)` near `z₀` has Taylor coefficients
equal to `TauCeti.linearSystemCoeff`. -/
theorem eq_linearSystemCoeff_of_hasDerivAt {A : ℂ → E →L[ℂ] E} {b v : ℂ → E} {U : Set ℂ}
    {z₀ : ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hA : DifferentiableOn ℂ A U)
    (hb : DifferentiableOn ℂ b U) (hv : ∀ z ∈ U, HasDerivAt v (A z (v z) + b z) z) (n : ℕ) :
    (n ! : ℂ)⁻¹ • iteratedDeriv n v z₀ =
      linearSystemCoeff (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m A z₀)
        (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀) (v z₀) n := by
  obtain ⟨r, hr_pos, hrU⟩ := exists_eball_subset_of_isOpen hU hz₀
  have hv_diff : DifferentiableOn ℂ v U :=
    fun z hz ↦ (hv z hz).differentiableAt.differentiableWithinAt
  have hA_ps := hasFPowerSeriesOnBall_eball hr_pos (hA.mono hrU)
  have hb_ps := hasFPowerSeriesOnBall_eball hr_pos (hb.mono hrU)
  have hv_ps := hasFPowerSeriesOnBall_eball hr_pos (hv_diff.mono hrU)
  have hlhs_ps := hasFPowerSeriesOnBall_deriv hv_ps
  have hrhs_ps : HasFPowerSeriesOnBall (fun z ↦ A z (v z) + b z)
      (mkPiRingSeries fun m ↦ (∑ k ∈ range (m + 1),
        (((m - k)! : ℂ)⁻¹ • iteratedDeriv (m - k) A z₀) ((k ! : ℂ)⁻¹ • iteratedDeriv k v z₀)) +
        (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀) z₀ r := by
    convert (hasFPowerSeriesOnBall_clm_apply hA_ps hv_ps).add hb_ps using 1
    rw [mkPiRingSeries_add]; rfl
  have heq : deriv v =ᶠ[𝓝 z₀] fun z ↦ A z (v z) + b z := by
    filter_upwards [hU.mem_nhds hz₀] with z hz using (hv z hz).deriv
  have hser := hlhs_ps.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hrhs_ps.hasFPowerSeriesAt heq
  have hstep : ∀ m : ℕ, ((m + 1 : ℂ)) • ((m + 1)! : ℂ)⁻¹ • iteratedDeriv (m + 1) v z₀ =
      (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀ + ∑ k ∈ range (m + 1),
        (((m - k)! : ℂ)⁻¹ • iteratedDeriv (m - k) A z₀) ((k ! : ℂ)⁻¹ • iteratedDeriv k v z₀) :=
    fun m ↦ by simpa only [mkPiRingSeries_coeff, add_comm] using congrArg (fun p ↦ p.coeff m) hser
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · simp
    · have hn : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
      rw [linearSystemCoeff_succ, ← inv_smul_smul₀ hn (((n + 1)! : ℂ)⁻¹ • _), hstep n]
      congr 2; exact Finset.sum_congr rfl fun k hk ↦ by rw [ih k (mem_range.mp hk)]

/-- Two solutions of `v'(z) = A(z) (v(z)) + b(z)` on an open preconnected set `U ⊆ ℂ` that agree
at a point `z₀ ∈ U` agree throughout `U`. No regularity hypothesis on `b` is needed. -/
theorem eqOn_of_hasDerivAt_clm_apply {A : ℂ → E →L[ℂ] E} {b v₁ v₂ : ℂ → E} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U) (hA : DifferentiableOn ℂ A U)
    (hv₁ : ∀ z ∈ U, HasDerivAt v₁ (A z (v₁ z) + b z) z)
    (hv₂ : ∀ z ∈ U, HasDerivAt v₂ (A z (v₂ z) + b z) z) (h₀ : v₁ z₀ = v₂ z₀) :
    EqOn v₁ v₂ U := by
  let u : ℂ → E := v₁ - v₂
  have hu_deriv : ∀ z ∈ U, HasDerivAt u (A z (u z) + 0) z := fun z hz ↦ by
    simpa [u, map_sub, add_sub_add_right_eq_sub] using (hv₁ z hz).sub (hv₂ z hz)
  have hu_diff : DifferentiableOn ℂ u U :=
    fun z hz ↦ (hu_deriv z hz).differentiableAt.differentiableWithinAt
  obtain ⟨r, hr_pos, hrU⟩ := exists_eball_subset_of_isOpen hU hz₀
  have hu_ps := hasFPowerSeriesOnBall_eball hr_pos (hu_diff.mono hrU)
  have hu_coeff : ∀ n, (n ! : ℂ)⁻¹ • iteratedDeriv n u z₀ = 0 := fun n ↦ by
    rw [eq_linearSystemCoeff_of_hasDerivAt hU hz₀ hA (differentiableOn_const 0) hu_deriv n]
    have hb0 : (fun m : ℕ ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m (fun _ : ℂ ↦ (0 : E)) z₀) = 0 := by
      ext m; simp
    have hu0 : u z₀ = 0 := sub_eq_zero.mpr h₀
    rw [hu0, hb0, linearSystemCoeff_zero_zero]
  have hu_zero_eball : EqOn u 0 (Metric.eball z₀ r) := fun z hz ↦ by
    have hsum := hu_ps.hasSum (sub_mem_eball_zero hz)
    rw [add_sub_cancel] at hsum
    simp only [mkPiRingSeries_apply, hu_coeff, smul_zero] at hsum
    exact hsum.unique hasSum_zero
  have hu_ev : u =ᶠ[𝓝 z₀] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Metric.eball z₀ r, Metric.isOpen_eball.mem_nhds (mem_eball_self hr_pos), hu_zero_eball⟩
  have hu_zero : EqOn u 0 U :=
    (hu_diff.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_conn hz₀ hu_ev
  exact fun z hz ↦ sub_eq_zero.mp (hu_zero hz)

/-- If `A : ℂ → E →L[ℂ] E` and `b : ℂ → E` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`),
then for every `v₀ : E` there is a unique holomorphic solution `v` of `v'(z) = A(z) (v(z)) + b(z)`
on `Metric.eball z₀ r` with `v z₀ = v₀`, represented on the whole disc by `linearSystemCoeff`. -/
theorem exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply {A : ℂ → E →L[ℂ] E} {b : ℂ → E}
    {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r) (hA : DifferentiableOn ℂ A (Metric.eball z₀ r))
    (hb : DifferentiableOn ℂ b (Metric.eball z₀ r)) (v₀ : E) :
    let c := linearSystemCoeff (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m A z₀)
      (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀) v₀
    ∃ v : ℂ → E,
      HasFPowerSeriesOnBall v
        (fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)) z₀ r ∧
      v z₀ = v₀ ∧ (∀ z ∈ Metric.eball z₀ r, HasDerivAt v (A z (v z) + b z) z) ∧
      ∀ u : ℂ → E, (∀ z ∈ Metric.eball z₀ r, HasDerivAt u (A z (u z) + b z) z) →
        u z₀ = v₀ → EqOn u v (Metric.eball z₀ r) := by
  intro c
  have hA_ps := hasFPowerSeriesOnBall_eball hr hA
  have hb_ps := hasFPowerSeriesOnBall_eball hr hb
  have hr_le : r ≤ (mkPiRingSeries c).radius :=
    le_radius_mkPiRingSeries_linearSystemCoeff v₀ hA_ps.r_le hb_ps.r_le
  let v : ℂ → E := fun z ↦ (mkPiRingSeries c).sum (z - z₀)
  have hv_ps : HasFPowerSeriesOnBall v (mkPiRingSeries c) z₀ r := by
    simpa [v] using ((mkPiRingSeries c).hasFPowerSeriesOnBall (hr.trans_le hr_le)
      |>.mono hr hr_le).comp_sub z₀
  have hv₀ : v z₀ = v₀ := by simpa [mkPiRingSeries, c] using (hv_ps.coeff_zero 1).symm
  have hlhs_ps := hasFPowerSeriesOnBall_deriv hv_ps
  have hrhs_ps := (hasFPowerSeriesOnBall_clm_apply hA_ps hv_ps).add hb_ps
  have hser_eq : mkPiRingSeries (fun n ↦ ((n + 1 : ℂ)) • c (n + 1)) =
      mkPiRingSeries (fun n ↦ ∑ k ∈ range (n + 1),
        (((n - k)! : ℂ)⁻¹ • iteratedDeriv (n - k) A z₀) (c k)) +
      mkPiRingSeries (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀) := by
    rw [mkPiRingSeries_add]; congr 1; ext n
    simp only [Pi.add_apply]; rw [natCast_succ_smul_linearSystemCoeff_succ, add_comm]
  have hv_ode : ∀ z ∈ Metric.eball z₀ r, HasDerivAt v (A z (v z) + b z) z := fun z hz ↦ by
    have hy := sub_mem_eball_zero hz
    have h1 := hlhs_ps.hasSum hy
    have h2 := hrhs_ps.hasSum hy
    rw [add_sub_cancel] at h1 h2; rw [hser_eq] at h1
    exact (hv_ps.analyticAt_of_mem hz).differentiableAt.hasDerivAt.congr_deriv (h1.unique h2)
  refine ⟨v, hv_ps, hv₀, hv_ode, fun u hu hu₀ ↦ ?_⟩
  exact eqOn_of_hasDerivAt_clm_apply Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hr) hA hu hv_ode (hu₀.trans hv₀.symm)

/-- If `A : ℂ → E →L[ℂ] E` and `b : ℂ → E` are entire, then for every `z₀ : ℂ` and `v₀ : E` there
is a unique `v : ℂ → E` satisfying `HasDerivAt v (A z (v z) + b z) z` everywhere and `v z₀ = v₀`. -/
theorem existsUnique_hasDerivAt_clm_apply {A : ℂ → E →L[ℂ] E} {b : ℂ → E}
    (hA : Differentiable ℂ A) (hb : Differentiable ℂ b) (z₀ : ℂ) (v₀ : E) :
    ∃! v : ℂ → E, (∀ z, HasDerivAt v (A z (v z) + b z) z) ∧ v z₀ = v₀ := by
  obtain ⟨v, -, hv₀, hv_ode, hv_uniq⟩ :=
    exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply (z₀ := z₀) (r := ∞) ENNReal.coe_lt_top
      hA.differentiableOn hb.differentiableOn v₀
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  refine ⟨v, ⟨fun z ↦ hv_ode z (hall z), hv₀⟩, fun u ⟨hu, hu₀⟩ ↦ funext fun z ↦ ?_⟩
  exact hv_uniq u (fun w _ ↦ hu w) hu₀ (hall z)

end FirstOrderSystem

/-! ### Initial-jet equivalence for `TauCeti.LinearEquation` -/

namespace LinearEquation

variable {U : Opens ℂ} {n : ℕ}

private theorem differentiableOn_companionCLM (E : LinearEquation U n) :
    DifferentiableOn ℂ (fun z ↦ matrixCLM (E.companion z)) U :=
  differentiableOn_matrixCLM fun i j ↦ (E.analyticOnNhd_companion i j).differentiableOn

/-- On a preconnected open domain, scalar solutions of `E` are uniquely determined by their
initial `n`-jet at any point of the domain. -/
theorem IsSolution.eqOn_of_isPreconnected {E : LinearEquation U n} {y₁ y₂ : ℂ → ℂ}
    (hy₁ : E.IsSolution y₁) (hy₂ : E.IsSolution y₂) (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) (hjet : ∀ j < n, iteratedDeriv j y₁ a = iteratedDeriv j y₂ a) :
    EqOn y₁ y₂ U := by
  have heq := eqOn_of_hasDerivAt_clm_apply (b := 0) U.isOpen hU ha E.differentiableOn_companionCLM
    (fun z hz ↦ by simpa using hy₁.isCompanionSolution.hasDerivAt z hz)
    (fun z hz ↦ by simpa using hy₂.isCompanionSolution.hasDerivAt z hz)
    (funext fun j ↦ hjet j j.isLt)
  exact fun z hz ↦ by simpa using congrFun (heq hz) ⟨0, E.order_pos⟩

/-- On a preconnected open domain, the initial-jet map on `E.solutionSpace` is injective. -/
theorem initialJet_injective (E : LinearEquation U n) (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) : Function.Injective (E.initialJet ha) := by
  intro f₁ f₂ h
  have hjet : ∀ j < n, iteratedDeriv j (HolomorphicFunctions.extend f₁.val) a =
      iteratedDeriv j (HolomorphicFunctions.extend f₂.val) a := fun j hj ↦ by
    simpa [initialJet_apply] using congrFun h ⟨j, hj⟩
  have heq := IsSolution.eqOn_of_isPreconnected
    ((E.mem_solutionSpace f₁.1).mp f₁.2) ((E.mem_solutionSpace f₂.1).mp f₂.2) hU ha hjet
  apply Subtype.ext; apply Subtype.ext; ext ⟨z, hz⟩
  simpa [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩] using heq hz

/-- On an open disc `Metric.eball a r` (`0 < r ≤ ∞`), the initial-jet map `E.initialJet ha` is a
`ℂ`-linear equivalence between `E.solutionSpace` and `Fin n → ℂ`. -/
def initialJetEquivOfEqEBall (E : LinearEquation U n) {a : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hU : (U : Set ℂ) = Metric.eball a r)
    (ha : a ∈ U := by rw [← SetLike.mem_coe, hU]; exact mem_eball_self hr) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet ha)
    ⟨E.initialJet_injective (hU ▸ isPreconnected_eball) ha, fun v₀ ↦ by
      have hA : DifferentiableOn ℂ (fun z ↦ matrixCLM (E.companion z)) (Metric.eball a r) :=
        hU ▸ E.differentiableOn_companionCLM
      obtain ⟨v, hv_ps, hv₀, hv_ode, -⟩ :=
        exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply (b := 0) hr hA
          (differentiableOn_const 0) v₀
      have hv_comp : E.IsCompanionSolution v :=
        (E.isCompanionSolution_iff v).mpr
          ⟨hU.symm ▸ hv_ps.analyticOnNhd, fun z hz ↦ by simpa using hv_ode z (hU ▸ hz)⟩
      exact ⟨hv_comp.toSolutionSpace, (hv_comp.initialJet_toSolutionSpace ha).trans hv₀⟩⟩

/-- Applying `initialJetEquivOfEqEBall` agrees with `E.initialJet ha`. -/
@[simp]
theorem initialJetEquivOfEqEBall_apply (E : LinearEquation U n) {a : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hU : (U : Set ℂ) = Metric.eball a r) (ha : a ∈ U) (f : E.solutionSpace) :
    E.initialJetEquivOfEqEBall hr hU ha f = E.initialJet ha f :=
  (rfl)

/-- On the entire complex plane `⊤ : Opens ℂ`, the initial-jet map at any point `a` is a linear
equivalence `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)`. -/
def initialJetEquivTop (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  E.initialJetEquivOfEqEBall ENNReal.coe_lt_top (by ext z; simp) (Set.mem_univ a)

/-- Applying `initialJetEquivTop` agrees with `E.initialJet`. -/
@[simp]
theorem initialJetEquivTop_apply (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    (f : E.solutionSpace) :
    E.initialJetEquivTop a f = E.initialJet (Set.mem_univ a) f :=
  (rfl)

end LinearEquation

/-! ### Second-order linear differential equations at an ordinary point -/

section SecondOrder

/-- Formal Taylor coefficients around `z₀` of the solution to `w'' + f(z) w' + g(z) w = 0` with
`w(z₀) = w₀` and `w'(z₀) = w₁`, given the Taylor coefficient sequences `f` and `g` around `z₀`. -/
def ordinaryPointCoeff (f g : ℕ → ℂ) (w₀ w₁ : ℂ) : ℕ → ℂ
  | 0 => w₀
  | 1 => w₁
  | n + 2 => -((((n + 2 : ℂ) * (n + 1 : ℂ))⁻¹) *
      ∑ k : Fin (n + 1), (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
        g (n - k) * ordinaryPointCoeff f g w₀ w₁ k))

/-- The constant Taylor coefficient `ordinaryPointCoeff f g w₀ w₁ 0` is `w₀`. -/
@[simp]
theorem ordinaryPointCoeff_zero (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g w₀ w₁ 0 = w₀ := by
  rw [ordinaryPointCoeff]

/-- The linear Taylor coefficient `ordinaryPointCoeff f g w₀ w₁ 1` is `w₁`. -/
@[simp]
theorem ordinaryPointCoeff_one (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g w₀ w₁ 1 = w₁ := by
  rw [ordinaryPointCoeff]

/-- Explicit two-step Cauchy-product recurrence for `ordinaryPointCoeff`. -/
theorem ordinaryPointCoeff_add_two (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ordinaryPointCoeff f g w₀ w₁ (n + 2) =
      -((((n + 2 : ℂ) * (n + 1 : ℂ))⁻¹) *
        ∑ k ∈ range (n + 1), (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)) := by
  rw [ordinaryPointCoeff, Fin.sum_univ_eq_sum_range (fun k ↦
    ((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
      g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)]

/-- Cleared-denominator coefficient-equating recurrence for `w'' + f(z) w' + g(z) w = 0`:
`(n + 2)(n + 1) a_{n+2} = -∑_{k=0}^n ((k + 1) f_{n-k} a_{k+1} + g_{n-k} a_k)`. -/
theorem mul_ordinaryPointCoeff_add_two (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ((n + 2 : ℂ) * (n + 1 : ℂ)) * ordinaryPointCoeff f g w₀ w₁ (n + 2) =
      -∑ k ∈ range (n + 1), (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
        g (n - k) * ordinaryPointCoeff f g w₀ w₁ k) := by
  have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hn2 : (n + 2 : ℂ) ≠ 0 := mod_cast Nat.succ_ne_zero (n + 1)
  rw [ordinaryPointCoeff_add_two, mul_neg, mul_inv_cancel_left₀ (mul_ne_zero hn2 hn1)]

/-- Zero initial values produce identically zero formal Taylor coefficients. -/
@[simp]
theorem ordinaryPointCoeff_zero_zero (f g : ℕ → ℂ) (n : ℕ) :
    ordinaryPointCoeff f g 0 0 n = 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | n
    · exact ordinaryPointCoeff_zero f g 0 0
    · exact ordinaryPointCoeff_one f g 0 0
    · rw [ordinaryPointCoeff_add_two, Finset.sum_eq_zero fun k hk ↦ ?_, mul_zero, neg_zero]
      have hk_le : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      simp [ih (k + 1) (by omega), ih k (by omega)]

private def secondOrderMatrix (f g : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ if i = 0 then (if j = 0 then 0 else 1) else (if j = 0 then -g z else -f z)

@[simp]
private theorem secondOrderMatrix_mulVec (f g : ℂ → ℂ) (z : ℂ) (v : Fin 2 → ℂ) :
    secondOrderMatrix f g z *ᵥ v = fun i ↦ if i = 0 then v 1 else -g z * v 0 - f z * v 1 := by
  ext i
  fin_cases i <;>
    simp [secondOrderMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

private theorem differentiableOn_secondOrderCLM {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun z ↦ matrixCLM (secondOrderMatrix f g z)) U := by
  refine differentiableOn_matrixCLM fun i j ↦ ?_
  dsimp only [secondOrderMatrix]
  split_ifs
  · exact differentiableOn_const 0
  · exact differentiableOn_const 1
  · exact hg.neg
  · exact hf.neg

private theorem hasDerivAt_secondOrder_vec {f g h w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : DifferentiableOn ℂ w U)
    (hode : ∀ z ∈ U, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) :
    ∀ z ∈ U, HasDerivAt (fun z (i : Fin 2) ↦ if i = 0 then w z else deriv w z)
      (matrixCLM (secondOrderMatrix f g z) (fun i ↦ if i = 0 then w z else deriv w z) +
        fun i ↦ if i = 0 then 0 else h z) z := by
  have hwd : DifferentiableOn ℂ (deriv w) U := hw.deriv hU
  intro z hz
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using (hw.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  · refine (hwd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.congr_deriv ?_
    simp only [matrixCLM_apply, secondOrderMatrix_mulVec, Pi.add_apply, Fin.mk_one, Fin.isValue,
      one_ne_zero, ↓reduceIte]
    linear_combination hode z hz

private theorem secondOrder_of_hasDerivAt_vec {f g : ℂ → ℂ} {b v : ℂ → Fin 2 → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hb0 : ∀ z ∈ U, b z 0 = 0)
    (hv : ∀ z ∈ U, HasDerivAt v (matrixCLM (secondOrderMatrix f g z) (v z) + b z) z) :
    DifferentiableOn ℂ (fun z ↦ v z 0) U ∧
      (∀ z ∈ U, deriv (fun w ↦ v w 0) z = v z 1) ∧
      ∀ z ∈ U, deriv (deriv fun w ↦ v w 0) z + f z * deriv (fun w ↦ v w 0) z +
        g z * v z 0 = b z 1 := by
  have hv_fst : ∀ z ∈ U, HasDerivAt (fun w ↦ v w 0) (v z 1) z := fun z hz ↦ by
    simpa [hb0 z hz] using hasDerivAt_pi.mp (hv z hz) 0
  have hv_snd : ∀ z ∈ U, deriv (fun w ↦ v w 0) z = v z 1 := fun z hz ↦ (hv_fst z hz).deriv
  refine ⟨fun z hz ↦ (hv_fst z hz).differentiableAt.differentiableWithinAt, hv_snd, fun z hz ↦ ?_⟩
  have hd2 := (hasDerivAt_pi.mp (hv z hz) 1).deriv
  have hcongr : (fun u ↦ v u 1) =ᶠ[𝓝 z] deriv (fun w ↦ v w 0) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, fun u hu ↦ (hv_snd u hu).symm⟩
  have hddw : deriv (deriv fun w ↦ v w 0) z =
      -g z * v z 0 - f z * deriv (fun w ↦ v w 0) z + b z 1 := by
    rw [← hcongr.deriv_eq, hv_snd z hz]; simpa using hd2
  rw [hddw]; ring

/-- If `f` and `g` are holomorphic on an open preconnected set `U ⊆ ℂ` and two holomorphic
functions `w₁, w₂` on `U` have the same `w'' + f w' + g w` on `U` and agree to first order at some
`z₀ ∈ U`, then `EqOn w₁ w₂ U`. -/
theorem eqOn_of_secondOrder_linear_ode {f g w₁ w₂ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hw₁ : DifferentiableOn ℂ w₁ U) (hw₂ : DifferentiableOn ℂ w₂ U)
    (hode : ∀ z ∈ U, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z =
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z)
    (hw₀ : w₁ z₀ = w₂ z₀) (hdw₀ : deriv w₁ z₀ = deriv w₂ z₀) :
    EqOn w₁ w₂ U := by
  let h : ℂ → ℂ := fun z ↦ deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z
  have hp₁ := hasDerivAt_secondOrder_vec hU hw₁ (h := h) hode
  have hp₂ := hasDerivAt_secondOrder_vec hU hw₂ (h := h) (fun _ _ ↦ rfl)
  have hinit : (fun i : Fin 2 ↦ if i = 0 then w₁ z₀ else deriv w₁ z₀) =
      (fun i : Fin 2 ↦ if i = 0 then w₂ z₀ else deriv w₂ z₀) := by
    ext i; fin_cases i <;> simp [hw₀, hdw₀]
  have heq := eqOn_of_hasDerivAt_clm_apply hU hU_conn hz₀
    (differentiableOn_secondOrderCLM hf hg) hp₁ hp₂ hinit
  exact fun z hz ↦ congrFun (heq hz) 0

/-- Two entire functions `w₁, w₂` having the same `w'' + f w' + g w` for entire `f, g` and agreeing
to first order at a point `z₀` are equal everywhere on `ℂ`. -/
theorem eq_of_entire_secondOrder_linear_ode {f g w₁ w₂ : ℂ → ℂ} {z₀ : ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hw₁ : Differentiable ℂ w₁) (hw₂ : Differentiable ℂ w₂)
    (hode : ∀ z, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z =
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z)
    (hw₀ : w₁ z₀ = w₂ z₀) (hdw₀ : deriv w₁ z₀ = deriv w₂ z₀) :
    w₁ = w₂ := by
  ext z
  exact eqOn_of_secondOrder_linear_ode isOpen_univ isPreconnected_univ (mem_univ z₀)
    hf.differentiableOn hg.differentiableOn hw₁.differentiableOn hw₂.differentiableOn
    (fun w _ ↦ hode w) hw₀ hdw₀ (mem_univ z)

/-- Any holomorphic solution of `w'' + f(z) w' + g(z) w = 0` on `Metric.eball z₀ r` (`0 < r`),
where `f` and `g` have scalar power series `fs` and `gs` around `z₀`, is represented on the whole
disc by `FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs (w z₀) (deriv w z₀))`. -/
theorem hasFPowerSeriesOnBall_of_ordinaryPoint_solution {f g w : ℂ → ℂ} {fs gs : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ gs) z₀ r)
    (hw : DifferentiableOn ℂ w (Metric.eball z₀ r))
    (hode : ∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) :
    HasFPowerSeriesOnBall w
      (FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs (w z₀) (deriv w z₀)))
      z₀ r := by
  let a : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n w z₀
  have hw_ps : HasFPowerSeriesOnBall w (mkPiRingSeries a) z₀ r := by
    simpa [a, smul_eq_mul] using hasFPowerSeriesOnBall_eball hf.r_pos hw
  have hdw_ps : HasFPowerSeriesOnBall (deriv w)
      (mkPiRingSeries fun n ↦ ((n + 1 : ℂ)) * a (n + 1)) z₀ r := by
    simpa [smul_eq_mul] using hasFPowerSeriesOnBall_deriv hw_ps
  have hddw_ps : HasFPowerSeriesOnBall (deriv (deriv w))
      (mkPiRingSeries fun n ↦ ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2)) z₀ r := by
    convert hasFPowerSeriesOnBall_deriv hdw_ps using 2
    ext n; simp only [smul_eq_mul]; push_cast; ring
  have hf' : HasFPowerSeriesOnBall f (mkPiRingSeries fs) z₀ r := by
    rwa [mkPiRingSeries_eq_ofScalars]
  have hg' : HasFPowerSeriesOnBall g (mkPiRingSeries gs) z₀ r := by
    rwa [mkPiRingSeries_eq_ofScalars]
  have hsum_ps : HasFPowerSeriesOnBall
      (deriv (deriv w) + (fun z ↦ f z * deriv w z) + (fun z ↦ g z * w z))
      (mkPiRingSeries fun n ↦ ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2) +
        (∑ k ∈ range (n + 1), fs (n - k) * (((k : ℂ) + 1) * a (k + 1))) +
        ∑ k ∈ range (n + 1), gs (n - k) * a k) z₀ r := by
    convert ((hddw_ps.add (hasFPowerSeriesOnBall_mul_scalar hf' hdw_ps)).add
      (hasFPowerSeriesOnBall_mul_scalar hg' hw_ps)) using 1
    rw [mkPiRingSeries_add, mkPiRingSeries_add]; rfl
  have hzero_ev : (deriv (deriv w) + (fun z ↦ f z * deriv w z) + (fun z ↦ g z * w z)) =ᶠ[𝓝 z₀] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Metric.eball z₀ r, Metric.isOpen_eball.mem_nhds (mem_eball_self hf.r_pos), hode⟩
  have hser_zero := hsum_ps.hasFPowerSeriesAt.eq_zero_of_eventually hzero_ev
  have ha_rec : ∀ n : ℕ, ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2) +
      ∑ k ∈ range (n + 1), (((k : ℂ) + 1) * fs (n - k) * a (k + 1) + gs (n - k) * a k) = 0 := by
    intro n
    have hn : (mkPiRingSeries fun m ↦ ((m + 2 : ℂ) * (m + 1 : ℂ)) * a (m + 2) +
        (∑ k ∈ range (m + 1), fs (m - k) * (((k : ℂ) + 1) * a (k + 1))) +
        ∑ k ∈ range (m + 1), gs (m - k) * a k).coeff n = 0 := by rw [hser_zero]; rfl
    rw [mkPiRingSeries_coeff, add_assoc, ← Finset.sum_add_distrib] at hn
    convert hn using 2
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have ha_eq : a = ordinaryPointCoeff fs gs (w z₀) (deriv w z₀) := by
    ext n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | _ | n
      · simp [a]
      · simp [a]
      · have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
        have hn2 : (n + 2 : ℂ) ≠ 0 := mod_cast Nat.succ_ne_zero (n + 1)
        rw [ordinaryPointCoeff_add_two, ← inv_mul_cancel_left₀ (mul_ne_zero hn2 hn1) (a (n + 2)),
          eq_neg_of_add_eq_zero_left (ha_rec n), mul_neg]
        congr 2
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [ih (k + 1) (by omega), ih k (by omega)]
  rw [← mkPiRingSeries_eq_ofScalars, ← ha_eq]; exact hw_ps

/-- If `f` and `g` admit scalar power series `fs` and `gs` on `Metric.eball z₀ r`, then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, given by `ordinaryPointCoeff`. -/
theorem exists_ordinaryPoint_solution_of_hasFPowerSeriesOnBall {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ gs) z₀ r) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff fs gs w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  intro a
  have hf_diff := hf.differentiableOn
  have hg_diff := hg.differentiableOn
  obtain ⟨v, -, hv₀, hv_ode, -⟩ :=
    exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply (b := 0) hf.r_pos
      (differentiableOn_secondOrderCLM hf_diff hg_diff) (differentiableOn_const 0)
      (fun i : Fin 2 ↦ if i = 0 then w₀ else w₁)
  obtain ⟨hw_diff, hv_snd, hw_ode⟩ :=
    secondOrder_of_hasDerivAt_vec Metric.isOpen_eball (fun _ _ ↦ rfl) hv_ode
  let w : ℂ → ℂ := fun z ↦ v z 0
  have hw₀ : w z₀ = w₀ := by simpa [w] using congrFun hv₀ 0
  have hdw₀ : deriv w z₀ = w₁ :=
    (hv_snd z₀ (mem_eball_self hf.r_pos)).trans (by simpa using congrFun hv₀ 1)
  have hw_ps : HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r := by
    dsimp only [a]; rw [← hw₀, ← hdw₀]
    exact hasFPowerSeriesOnBall_of_ordinaryPoint_solution hf hg hw_diff hw_ode
  have hw_sum : ∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z) := fun z hz ↦ by
    have hs := hw_ps.hasSum (sub_mem_eball_zero hz)
    rw [add_sub_cancel] at hs
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hs
  refine ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  exact eqOn_of_secondOrder_linear_ode Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hf.r_pos) hf_diff hg_diff hu hw_diff
    (fun z hz ↦ (hu_ode z hz).trans (hw_ode z hz).symm)
    (hu₀.trans hw₀.symm) (hdu₀.trans hdw₀.symm)

/-- If `f` and `g` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then for all `w₀, w₁ : ℂ`
there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, given by `ordinaryPointCoeff`. -/
theorem exists_ordinaryPoint_solution_eball {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  have hf_ps : HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀) z₀ r := by
    rw [← mkPiRingSeries_eq_ofScalars]; simpa [smul_eq_mul] using hasFPowerSeriesOnBall_eball hr hf
  have hg_ps : HasFPowerSeriesOnBall g
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) z₀ r := by
    rw [← mkPiRingSeries_eq_ofScalars]; simpa [smul_eq_mul] using hasFPowerSeriesOnBall_eball hr hg
  exact exists_ordinaryPoint_solution_of_hasFPowerSeriesOnBall hf_ps hg_ps w₀ w₁

/-- If `f` and `g` are holomorphic on a finite open disc `Metric.ball z₀ r` (`0 < r`), then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.ball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, converging on the whole disc. -/
theorem exists_ordinaryPoint_solution_ball {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ r)) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      DifferentiableOn ℂ w (Metric.ball z₀ r) ∧
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ (ENNReal.ofReal r) ∧
      (∀ z ∈ Metric.ball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.ball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball z₀ r) →
        (∀ z ∈ Metric.ball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.ball z₀ r) := by
  have heball : Metric.eball z₀ (ENNReal.ofReal r) = Metric.ball z₀ r := Metric.eball_ofReal
  have hr_enn : (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
  obtain ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_ordinaryPoint_solution_eball hr_enn (heball.symm ▸ hf) (heball.symm ▸ hg) w₀ w₁
  refine ⟨w, heball ▸ hw_ps.differentiableOn, hw_ps, fun z hz ↦ hw_sum z (heball.symm ▸ hz),
    hw₀, hdw₀, fun z hz ↦ hw_ode z (heball.symm ▸ hz), fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  simpa only [heball] using hw_uniq u (heball.symm ▸ hu)
    (fun z hz ↦ hu_ode z (heball ▸ hz)) hu₀ hdu₀

/-- For entire `f, g, h : ℂ → ℂ`, every initial-value problem `w'' + f(z) w' + g(z) w = h(z)` with
`w z₀ = w₀` and `deriv w z₀ = w₁` has a unique entire solution. -/
theorem existsUnique_entire_secondOrder_linear_ode {f g h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (z₀ w₀ w₁ : ℂ) :
    ∃! w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  have hA : Differentiable ℂ (fun z ↦ matrixCLM (secondOrderMatrix f g z)) :=
    differentiableOn_univ.mp
      (differentiableOn_secondOrderCLM hf.differentiableOn hg.differentiableOn)
  have hb : Differentiable ℂ (fun z (i : Fin 2) ↦ if i = 0 then (0 : ℂ) else h z) := by
    rw [differentiable_pi]; intro i; fin_cases i <;> simp [hh]
  obtain ⟨v, ⟨hv_ode, hv₀⟩, -⟩ := existsUnique_hasDerivAt_clm_apply hA hb z₀
    (fun i : Fin 2 ↦ if i = 0 then w₀ else w₁)
  obtain ⟨hw_diff_on, hv_snd, hw_ode_on⟩ :=
    secondOrder_of_hasDerivAt_vec isOpen_univ (fun _ _ ↦ rfl) (fun z _ ↦ hv_ode z)
  let w : ℂ → ℂ := fun z ↦ v z 0
  have hw_diff : Differentiable ℂ w := differentiableOn_univ.mp hw_diff_on
  have hw₀ : w z₀ = w₀ := by simpa [w] using congrFun hv₀ 0
  have hdw₀ : deriv w z₀ = w₁ :=
    (hv_snd z₀ (mem_univ z₀)).trans (by simpa using congrFun hv₀ 1)
  have hw_ode : ∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = h z :=
    fun z ↦ hw_ode_on z (mem_univ z)
  refine ⟨w, ⟨hw_diff, hw_ode, hw₀, hdw₀⟩, fun u ⟨hu_diff, hu_ode, hu₀, hdu₀⟩ ↦ ?_⟩
  exact eq_of_entire_secondOrder_linear_ode hf hg hu_diff hw_diff
    (fun z ↦ (hu_ode z).trans (hw_ode z).symm) (hu₀.trans hw₀.symm) (hdu₀.trans hdw₀.symm)

/-- For entire `f, g : ℂ → ℂ`, every initial-value problem `w'' + f(z) w' + g(z) w = 0` with
`w z₀ = w₀` and `deriv w z₀ = w₁` has a unique entire solution `w`, and its Taylor series around
`z₀` with coefficients `ordinaryPointCoeff` converges everywhere on `ℂ`. -/
theorem exists_entire_ordinaryPoint_solution {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (z₀ w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      Differentiable ℂ w ∧
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ ∞ ∧
      (∀ z : ℂ, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z : ℂ, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, Differentiable ℂ u →
        (∀ z : ℂ, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → u = w := by
  obtain ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, -⟩ :=
    exists_ordinaryPoint_solution_eball (z₀ := z₀) (r := ∞) ENNReal.coe_lt_top
      hf.differentiableOn hg.differentiableOn w₀ w₁
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  have hw_diff : Differentiable ℂ w :=
    differentiableOn_univ.mp (by simpa using hw_ps.differentiableOn)
  refine ⟨w, hw_diff, hw_ps, fun z ↦ hw_sum z (hall z), hw₀, hdw₀,
    fun z ↦ hw_ode z (hall z), fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  exact eq_of_entire_secondOrder_linear_ode hf hg hu hw_diff
    (fun z ↦ (hu_ode z).trans (hw_ode z (hall z)).symm) (hu₀.trans hw₀.symm)
    (hdu₀.trans hdw₀.symm)

/-! ### Sign, normalization, and recurrence checks -/

-- Check 1: `w'' = 0` produces `a₀ = w₀`, `a₁ = w₁`, and `a_{n+2} = 0`.
example (w₀ w₁ : ℂ) (n : ℕ) : ordinaryPointCoeff 0 0 w₀ w₁ (n + 2) = 0 := by
  simp [ordinaryPointCoeff_add_two]

-- Check 2: For `w'' - w = 0` (`f = 0`, `g = -1`), `a₂ = w₀ / 2`, fixing the minus sign in the
-- coefficient recurrence.
example (w₀ w₁ : ℂ) :
    ordinaryPointCoeff 0 (Pi.single 0 (-1)) w₀ w₁ 2 = w₀ / 2 := by
  rw [ordinaryPointCoeff_add_two]; norm_num; ring

-- Check 3: Airy's equation `w'' - z w = 0` around `z₀ = 0` (`f = 0`, `g(z) = -z`, so `g₁ = -1`
-- and `g_m = 0` for `m ≠ 1`) has `a₂ = 0` and `(n + 3)(n + 2) a_{n+3} = a_n` (DLMF 9.4.1).
example (w₀ w₁ : ℂ) :
    ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ 2 = 0 := by
  rw [ordinaryPointCoeff_add_two]; simp

example (w₀ w₁ : ℂ) (n : ℕ) :
    ((n + 3 : ℂ) * (n + 2 : ℂ)) *
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ (n + 3) =
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ n := by
  have h := mul_ordinaryPointCoeff_add_two 0 (Pi.single 1 (-1)) w₀ w₁ (n + 1)
  have hlhs : ((n + 3 : ℂ) * (n + 2 : ℂ)) *
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ (n + 3) =
      (((n + 1 : ℕ) + 2 : ℂ) * ((n + 1 : ℕ) + 1 : ℂ)) *
        ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ ((n + 1) + 2) := by
    push_cast; ring_nf
  rw [hlhs, h, Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hne : n + 1 - k ≠ 1 := by omega
    simp [Pi.single_eq_of_ne hne]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

end SecondOrder

end TauCeti
