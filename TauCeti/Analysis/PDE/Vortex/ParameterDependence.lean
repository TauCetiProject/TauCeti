/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Minimizer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.PDE.Vortex.Variational
import TauCeti.Analysis.Polynomial.Coeff.Convergence
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Continuous dependence of Taubes's minimizers on the polynomial

For a complex polynomial `P` of degree `m ≥ 1`, Taubes's functional `I_P` on `H¹(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional P`) attains its minimum
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), and its minimizers solve the reduced
equation of the vortex with zero divisor `P`. Through the elementary symmetric chart
`Sym.coeffHomeomorph`, the effective divisors of degree `m` correspond to the monic polynomials
of degree `m`, with the topology of `Sym ℂ m` given by the coefficients. This file shows that the
variational problem depends continuously on these coefficients.

Let `P i` be polynomials, indexed along a countably generated filter `l`, whose coefficients
converge to those of `P₀`, with `deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually. Let `u i` be a
minimizer of `I_(P i)`. Then:

* the sublevel sets of `I_(P i)`, in particular the minimizers, are eventually contained in a
  fixed ball of `H¹(ℂ)` (`TauCeti.Vortex.exists_eventually_norm_le_of_sobolevReducedFunctional_le`);
* the minimum values converge, `I_(P i)(u i) → min I_(P₀)`
  (`TauCeti.Vortex.tendsto_sobolevReducedFunctional_of_tendsto_coeff`);
* every weak cluster point of `u i` minimizes `I_(P₀)`
  (`TauCeti.Vortex.forall_sobolevReducedFunctional_le_of_mapClusterPt`), and when `l` is
  nontrivial such a cluster point exists
  (`TauCeti.Vortex.exists_mapClusterPt_forall_sobolevReducedFunctional_le`).

The degree condition is necessary: the coefficients of `z + z ^ 2 / i` converge to those of `z`,
but its second zero `-i` escapes to infinity.

The proof is a Γ-convergence argument with three ingredients.

* **Uniform coefficients.** Along the family, the weights `h_i = ‖P i‖² / (1 + ‖P i‖²)`
  (`TauCeti.Vortex.backgroundWeight`) satisfy `h_i ≥ h₀ - ε` everywhere, eventually for each
  `ε > 0`, and the coefficients `c_i = 2 ‖(P i)'‖² / (1 + ‖P i‖²)² - (1 + ‖P i‖²)⁻¹ / 8`
  (`TauCeti.Vortex.backgroundSource`) of the linear term are dominated by
  a fixed multiple of `(1 + ‖z‖)⁻²` and converge to `c₀` in `L²`. These follow from the uniform
  polynomial bounds of `TauCeti.Analysis.Polynomial.Coeff.Convergence`. They also make the
  coercivity of `TauCeti.Vortex.exists_forall_norm_le_of_sobolevReducedFunctional_le` uniform.
* **The lower bound.** Since eventually `h_i ≥ h₀ - ε`, replacing `h_i` by `h₀ - ε` can only
  lower the potential, so the functional `I_(P₀),ε` with weight `h₀ - ε` and linear coefficient
  `c_i` is at most `I_(P i)`. Separately, replacing `c_i` by `c₀` changes the linear term on a
  bounded set of `H¹(ℂ)` by an error tending to zero, by the `L²` convergence of the coefficients.
  The functional with weight `h₀ - ε` and coefficient `c₀` is weakly lower semicontinuous
  (`TauCeti.Vortex.lowerSemicontinuous_add_lintegral_ofReal_mul_exp_sub_one_sub`). Finally, as
  `ε → 0` it increases to `I_(P₀)` pointwise by monotone convergence. Together these bound
  `I_(P i)` below near any weak limit point by `I_(P₀)` there.
* **The upper bound.** For `v ∈ H¹(ℂ)` of finite energy, the smooth caps
  `v_k = v - log (1 + exp (v - k)) + log (1 + exp (-k))` are bounded above, so their potential is
  integrable without the weight, and `I_(P i)(v_k) → I_(P₀)(v_k)` by dominated convergence; as
  `k → ∞`, `I_(P₀)(v_k) → I_(P₀)(v)`. No exponential integrability of `H¹` functions is needed.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
* A. Braides, *Γ-convergence for Beginners*, Oxford Lecture Series in Mathematics and its
  Applications 22, Oxford University Press, 2002, Chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti.Vortex

variable {ι : Type*} {l : Filter ι} {P : ι → Polynomial ℂ} {P₀ : Polynomial ℂ}

/-! ### The coefficients of Taubes's functional along a converging family -/

section Coefficients

variable (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
  (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
include hm hdeg hP

/-- The weights are eventually bounded below by `h₀ - ε`, uniformly on the plane. -/
private theorem eventually_forall_backgroundWeight_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ z, backgroundWeight P₀.eval z - ε ≤ backgroundWeight (P i).eval z := by
  obtain ⟨A, hA⟩ := Polynomial.exists_eventually_forall_inv_one_add_norm_eval_sq_le hm hdeg hP
  -- Outside a disc both weights are within `ε` of `1`; on the disc `P i → P₀` uniformly.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ A ≤ ε * (1 + R) ^ 2 := by
    refine ⟨|A| / ε, by positivity, ?_⟩
    have h1 : |A| / ε ≤ (1 + |A| / ε) ^ 2 := by nlinarith [abs_nonneg A, sq_nonneg (|A| / ε)]
    calc A ≤ |A| := le_abs_self A
      _ = ε * (|A| / ε) := by field_simp
      _ ≤ ε * (1 + |A| / ε) ^ 2 := by gcongr
  have hunif := Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff hdeg le_rfl hP R
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hA, hunif ε hε] with i hi hu z
  by_cases hz : ‖z‖ ≤ R
  · have h := abs_backgroundWeight_sub_backgroundWeight_le (P i).eval P₀.eval z
    have hd := hu z (mem_closedBall_zero_iff.mpr hz)
    rw [dist_eq_norm, norm_sub_rev] at hd
    linarith [neg_abs_le (backgroundWeight (P i).eval z - backgroundWeight P₀.eval z)]
  · rw [not_le] at hz
    have h1 := one_sub_backgroundWeight (P i).eval z
    have h2 : (1 + ‖(P i).eval z‖ ^ 2)⁻¹ ≤ ε := by
      refine (hi z).trans ?_
      rw [div_le_iff₀ (by positivity)]
      exact hR.2.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [hR.1]) (by linarith) 2) hε.le)
    linarith [(backgroundWeight_lt_one P₀.eval z).le]

/-- The linear coefficients are eventually dominated by a fixed multiple of `(1 + ‖z‖)⁻²`. -/
private theorem exists_eventually_forall_abs_backgroundSource_le :
    ∃ K : ℝ, ∀ᶠ i in l, ∀ z, |backgroundSource (P i).eval z| ≤ K / (1 + ‖z‖) ^ 2 := by
  obtain ⟨A, hA⟩ := Polynomial.exists_eventually_forall_inv_one_add_norm_eval_sq_le hm hdeg hP
  obtain ⟨B, hB⟩ := Polynomial.exists_eventually_forall_norm_derivative_eval_sq_le hm hdeg hP
  refine ⟨(2 * B + 1 / 8) * A, ?_⟩
  filter_upwards [hA, hB] with i hAi hBi z
  set q := (1 + ‖(P i).eval z‖ ^ 2)⁻¹
  have hq : 0 ≤ q := by positivity
  have hpos : 0 < 1 + ‖(P i).eval z‖ ^ 2 := by positivity
  have hB0 : 0 ≤ B := by
    have := (sq_nonneg _).trans (hBi z)
    exact nonneg_of_mul_nonneg_left this hpos
  -- `|c| ≤ 2 ‖P'‖² / (1 + ‖P‖²)² + (1 + ‖P‖²)⁻¹ / 8 ≤ (2 B + 1 / 8) (1 + ‖P‖²)⁻¹`.
  have hder : 2 * ‖(P i).derivative.eval z‖ ^ 2 / (1 + ‖(P i).eval z‖ ^ 2) ^ 2 ≤ 2 * B * q := by
    rw [div_le_iff₀ (by positivity)]
    have : q * (1 + ‖(P i).eval z‖ ^ 2) = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith [hBi z]
  have hc : |backgroundSource (P i).eval z| ≤ (2 * B + 1 / 8) * q := by
    rw [backgroundSource_eval, abs_le]
    constructor <;> nlinarith [div_nonneg (mul_nonneg zero_le_two
      (sq_nonneg ‖(P i).derivative.eval z‖)) (sq_nonneg (1 + ‖(P i).eval z‖ ^ 2))]
  calc |backgroundSource (P i).eval z| ≤ (2 * B + 1 / 8) * q := hc
    _ ≤ (2 * B + 1 / 8) * (A / (1 + ‖z‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (hAi z) (by positivity)
    _ = (2 * B + 1 / 8) * A / (1 + ‖z‖) ^ 2 := by ring

omit hm in
/-- The values of the polynomials and of their derivatives converge at every point, hence so do
the weights and the linear coefficients. -/
private theorem tendsto_backgroundWeight (z : ℂ) :
    Tendsto (fun i ↦ backgroundWeight (P i).eval z) l (𝓝 (backgroundWeight P₀.eval z)) := by
  have h := ((Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff hdeg le_rfl hP
    ‖z‖).tendsto_at (mem_closedBall_zero_iff.mpr le_rfl)).norm
  simp only [backgroundWeight_def]
  exact (h.pow 2).div (tendsto_const_nhds.add (h.pow 2)) (by positivity)

omit hm in
private theorem tendsto_backgroundSource (z : ℂ) :
    Tendsto (fun i ↦ backgroundSource (P i).eval z) l (𝓝 (backgroundSource P₀.eval z)) := by
  have h := ((Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff hdeg le_rfl hP
    ‖z‖).tendsto_at (mem_closedBall_zero_iff.mpr le_rfl)).norm
  have hd := ((Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff
    (P := fun i ↦ (P i).derivative)
    (N := P₀.natDegree) (hdeg.mono fun i hi ↦ (Polynomial.natDegree_derivative_le _).trans
      (Nat.sub_le_of_le_add (by omega)))
    ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _))
    (Polynomial.tendsto_coeff_derivative hP) ‖z‖).tendsto_at
    (mem_closedBall_zero_iff.mpr le_rfl)).norm
  simp only [backgroundSource_eval]
  exact (((hd.pow 2).const_mul 2).div ((tendsto_const_nhds.add (h.pow 2)).pow 2)
    (by positivity)).sub (((tendsto_const_nhds.add (h.pow 2)).inv₀ (by positivity)).div_const 8)

/-- A common bound `|c_i|, |c₀| ≤ K (1 + ‖z‖)⁻²` for the linear coefficients of the family and of
the limit. -/
private theorem exists_eventually_forall_abs_backgroundSource_le_and :
    ∃ K : ℝ, ∀ᶠ i in l, ∀ z,
      |backgroundSource (P i).eval z| ≤ K / (1 + ‖z‖) ^ 2 ∧
        |backgroundSource P₀.eval z| ≤ K / (1 + ‖z‖) ^ 2 := by
  obtain ⟨K, hK⟩ := exists_eventually_forall_abs_backgroundSource_le hm hdeg hP
  obtain ⟨K₀, hK₀⟩ := exists_eventually_forall_abs_backgroundSource_le (l := (⊤ : Filter Unit))
    (P := fun _ ↦ P₀) hm (Eventually.of_forall fun _ ↦ le_rfl) fun k ↦ tendsto_const_nhds
  have hK₀' := eventually_top.mp hK₀ ()
  refine ⟨max K K₀, ?_⟩
  filter_upwards [hK] with i hi z
  exact ⟨(hi z).trans (by gcongr; exact le_max_left _ _),
    (hK₀' z).trans (by gcongr; exact le_max_right _ _)⟩

/-- The linear coefficients converge in `L²`. -/
private theorem tendsto_integral_backgroundSource_sub_sq [l.IsCountablyGenerated] :
    Tendsto (fun i ↦ ∫ z, (backgroundSource (P i).eval z - backgroundSource P₀.eval z) ^ 2) l
      (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_eventually_forall_abs_backgroundSource_le_and hm hdeg hP
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i z ↦ (backgroundSource (P i).eval z - backgroundSource P₀.eval z) ^ 2)
    (f := fun _ ↦ 0)
    (fun z : ℂ ↦ (2 * K) ^ 2 * ((1 + ‖z‖) ^ 4)⁻¹)
    (Eventually.of_forall fun i ↦
      (((continuous_backgroundSource (P i).differentiable).sub
        (continuous_backgroundSource P₀.differentiable)).pow 2).aestronglyMeasurable)
    (hK.mono fun i hi ↦ ae_of_all _ fun z ↦ by
      obtain ⟨h1, h2⟩ := hi z
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h3 : |backgroundSource (P i).eval z - backgroundSource P₀.eval z| ≤
          2 * K / (1 + ‖z‖) ^ 2 := by
        have := abs_sub (backgroundSource (P i).eval z) (backgroundSource P₀.eval z)
        calc _ ≤ _ := this
          _ ≤ K / (1 + ‖z‖) ^ 2 + K / (1 + ‖z‖) ^ 2 := add_le_add h1 h2
          _ = 2 * K / (1 + ‖z‖) ^ 2 := by ring
      calc (backgroundSource (P i).eval z - backgroundSource P₀.eval z) ^ 2
          = |backgroundSource (P i).eval z - backgroundSource P₀.eval z| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * K / (1 + ‖z‖) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = (2 * K) ^ 2 * ((1 + ‖z‖) ^ 4)⁻¹ := by field_simp)
    ((integrable_inv_one_add_norm_pow (volume : Measure ℂ) (n := 4)
      (by simp [Complex.finrank_real_complex])).const_mul _)
    (ae_of_all _ fun z ↦ by
      simpa using
        ((tendsto_backgroundSource hdeg hP z).sub_const (backgroundSource P₀.eval z)).pow 2)
  simpa using hlim

/-- The squared `L²` norms of the linear coefficients are eventually bounded. -/
private theorem exists_eventually_integral_backgroundSource_sq_le :
    ∃ K : ℝ, ∀ᶠ i in l, ∫ z, backgroundSource (P i).eval z ^ 2 ≤ K := by
  obtain ⟨K, hK⟩ := exists_eventually_forall_abs_backgroundSource_le_and hm hdeg hP
  refine ⟨∫ z : ℂ, K ^ 2 * ((1 + ‖z‖) ^ 4)⁻¹, ?_⟩
  filter_upwards [hK] with i hi
  refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ sq_nonneg _)
    ((integrable_inv_one_add_norm_pow (volume : Measure ℂ) (n := 4)
      (by simp [Complex.finrank_real_complex])).const_mul _) (ae_of_all _ fun z ↦ ?_)
  calc backgroundSource (P i).eval z ^ 2 = |backgroundSource (P i).eval z| ^ 2 := (sq_abs _).symm
    _ ≤ (K / (1 + ‖z‖) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hi z).1 2
    _ = K ^ 2 * ((1 + ‖z‖) ^ 4)⁻¹ := by field_simp

end Coefficients

/-- The linear coefficient of a polynomial of degree at least one is square integrable. -/
private theorem memLp_backgroundSource_eval {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) :
    MemLp (backgroundSource Q.eval) 2 :=
  funext (backgroundSource_eval Q) ▸ memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hQ

/-- **Uniform bounded sublevel sets along a converging family.** If the coefficients of `P i`
converge to those of `P₀`, with `deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually, then for every
level `t` the sublevel sets `{u | I_(P i)(u) ≤ t}` of Taubes's functionals are eventually
contained in a fixed ball of `H¹(ℂ)`. In particular minimizers, which have `I_(P i)(u i) ≤ 0`,
are eventually bounded. -/
theorem exists_eventually_norm_le_of_sobolevReducedFunctional_le (hm : 0 < P₀.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) (t : ℝ) :
    ∃ C : ℝ, ∀ᶠ i in l, ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      sobolevReducedFunctional (P i) u ≤ t → ‖u‖ ≤ C := by
  obtain ⟨R, hR⟩ := Polynomial.exists_eventually_forall_one_le_norm_eval hm hdeg hP
  obtain ⟨K, hK⟩ := exists_eventually_integral_backgroundSource_sq_le hm hdeg hP
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_sobolevReducedFunctional_le R K t
  refine ⟨C, ?_⟩
  filter_upwards [Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff hP, hR, hK]
    with i hle hRi hKi
  exact hC (P i) (hm.trans_le hle) hRi (by simpa only [backgroundSource_eval] using hKi)

/-! ### Smooth caps

The cap `t ↦ t - log (1 + exp (t - k)) + log (1 + exp (-k))` is smooth, increasing with slope in
`(0, 1]`, vanishes at `0`, lies between `0` and `t`, and is at most `k + 1`. It tends to the
identity as `k → ∞`. Composing with it truncates an element of `H¹(ℂ)` from above without
increasing the potential of Taubes's functional. -/

/-- The smooth cap at level `k`. -/
private def cap (k t : ℝ) : ℝ :=
  t - Real.log (1 + Real.exp (t - k)) + Real.log (1 + Real.exp (-k))

private theorem hasDerivAt_cap (k t : ℝ) :
    HasDerivAt (cap k) (1 + Real.exp (t - k))⁻¹ t := by
  have h1 : HasDerivAt (fun s ↦ 1 + Real.exp (s - k)) (Real.exp (t - k)) t := by
    simpa using ((hasDerivAt_id t).sub_const k).exp.const_add 1
  have h3 : HasDerivAt (fun s ↦ s - Real.log (1 + Real.exp (s - k)))
      (1 - Real.exp (t - k) / (1 + Real.exp (t - k))) t :=
    (hasDerivAt_id t).sub (h1.log (by positivity))
  exact (h3.add_const _).congr_deriv (by field_simp; ring)

private theorem deriv_cap (k t : ℝ) : deriv (cap k) t = (1 + Real.exp (t - k))⁻¹ :=
  (hasDerivAt_cap k t).deriv

private theorem contDiff_cap (k : ℝ) : ContDiff ℝ 1 (cap k) := by
  unfold cap
  fun_prop (disch := intro x; positivity)

private theorem cap_zero (k : ℝ) : cap k 0 = 0 := by
  simp [cap]

private theorem nnnorm_deriv_cap_le (k t : ℝ) : ‖deriv (cap k) t‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnNorm, deriv_cap, Real.norm_of_nonneg (by positivity),
    NNReal.coe_one]
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (Real.exp_nonneg _))

private theorem cap_nonneg_and_le {k t : ℝ} (ht : 0 ≤ t) : 0 ≤ cap k t ∧ cap k t ≤ t := by
  unfold cap
  constructor
  · -- `log (1 + exp (t - k)) ≤ log (exp t (1 + exp (-k))) = t + log (1 + exp (-k))`.
    have h : 1 + Real.exp (t - k) ≤ Real.exp t * (1 + Real.exp (-k)) := by
      rw [mul_add, mul_one, ← Real.exp_add, ← sub_eq_add_neg]
      linarith [Real.one_le_exp ht]
    have := Real.log_le_log (by positivity) h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at this
    linarith
  · have h : 1 + Real.exp (-k) ≤ 1 + Real.exp (t - k) := by gcongr; linarith
    linarith [Real.log_le_log (by positivity) h]

private theorem le_cap_and_nonpos {k t : ℝ} (ht : t ≤ 0) : t ≤ cap k t ∧ cap k t ≤ 0 := by
  unfold cap
  constructor
  · have h : 1 + Real.exp (t - k) ≤ 1 + Real.exp (-k) := by gcongr; linarith
    linarith [Real.log_le_log (by positivity) h]
  · have h : Real.exp t * (1 + Real.exp (-k)) ≤ 1 + Real.exp (t - k) := by
      rw [mul_add, mul_one, ← Real.exp_add, ← sub_eq_add_neg]
      linarith [Real.exp_le_one_iff.mpr ht]
    have := Real.log_le_log (by positivity) h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at this
    linarith

private theorem cap_le {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : cap k t ≤ k + 1 := by
  unfold cap
  have h1 : t - k ≤ Real.log (1 + Real.exp (t - k)) := by
    have := Real.log_le_log (Real.exp_pos (t - k))
      (by linarith : Real.exp (t - k) ≤ 1 + Real.exp (t - k))
    rwa [Real.log_exp] at this
  have h2 : Real.log (1 + Real.exp (-k)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + Real.exp (-k))
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hk)
    linarith
  linarith

private theorem sq_cap_le (k t : ℝ) : cap k t ^ 2 ≤ t ^ 2 := by
  rcases le_total 0 t with ht | ht
  · obtain ⟨h1, h2⟩ := cap_nonneg_and_le (k := k) ht
    nlinarith
  · obtain ⟨h1, h2⟩ := le_cap_and_nonpos (k := k) ht
    nlinarith

private theorem tendsto_cap (t : ℝ) : Tendsto (fun k : ℕ ↦ cap k t) atTop (𝓝 t) := by
  have h1 := ((Real.tendsto_exp_sub_natCast_atTop_nhds_zero t).const_add 1).log (by norm_num)
  have h2 := ((Real.tendsto_exp_sub_natCast_atTop_nhds_zero 0).const_add 1).log (by norm_num)
  simp only [zero_sub] at h2
  simpa [cap] using (h1.const_sub t).add h2

private theorem tendsto_deriv_cap (t : ℝ) :
    Tendsto (fun k : ℕ ↦ deriv (cap k) t) atTop (𝓝 1) := by
  simpa [deriv_cap] using
    ((Real.tendsto_exp_sub_natCast_atTop_nhds_zero t).const_add 1).inv₀ (by norm_num)

/-! ### The potential of Taubes's functional -/

/-- Capping does not increase the integrand of the potential. -/
private theorem exp_two_mul_cap_sub_le (k t : ℝ) :
    Real.exp (2 * cap k t) - 1 - 2 * cap k t ≤ Real.exp (2 * t) - 1 - 2 * t := by
  rcases le_total 0 t with ht | ht
  · obtain ⟨h1, h2⟩ := cap_nonneg_and_le (k := k) ht
    exact Real.monotoneOn_exp_two_mul_sub_one_sub_two_mul h1 ht h2
  · obtain ⟨h1, h2⟩ := le_cap_and_nonpos (k := k) ht
    exact Real.antitoneOn_exp_two_mul_sub_one_sub_two_mul ht h2 h1

/-- The capped integrand of the potential is at most a multiple of `t²`. -/
private theorem exp_two_mul_cap_sub_le_mul_sq {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    Real.exp (2 * cap k t) - 1 - 2 * cap k t ≤ 4 * (Real.exp (2 * (k + 1)) + 2) * t ^ 2 :=
  (Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq (cap_le hk t)).trans
    (mul_le_mul_of_nonneg_left (sq_cap_le k t) (by positivity))

/-! ### Recovery sequences -/

/-- Taubes's functional, written with the weight `TauCeti.Vortex.backgroundWeight` and the
linear coefficient `TauCeti.Vortex.backgroundSource`. -/
private theorem sobolevReducedFunctional_eq_background (Q : Polynomial ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional Q u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, backgroundSource Q.eval z * W1p.value u z : ℝ) : EReal) +
        (((∫⁻ z, ENNReal.ofReal (backgroundWeight Q.eval z *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal) := by
  simp only [sobolevReducedFunctional_def, backgroundSource_eval, backgroundWeight_def]

/-- Taubes's functional, written with the weight and the linear coefficient, when the potential
is integrable. -/
private theorem sobolevReducedFunctional_eq_coe_background {Q : Polynomial ℂ}
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) :
    sobolevReducedFunctional Q u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, backgroundWeight Q.eval z *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, backgroundSource Q.eval z * W1p.value u z : ℝ) : EReal) := by
  simp only [backgroundWeight_def, backgroundSource_eval] at hu ⊢
  exact sobolevReducedFunctional_eq_coe hu

/-- The cap of an element of `H¹(ℂ)` at level `k`. -/
private def capH (k : ℝ) (v : W1p (volume : Measure ℂ) ⊤ 2) : W1p (volume : Measure ℂ) ⊤ 2 :=
  W1p.contDiffComp (M := 1) ENNReal.ofNat_ne_top (contDiff_cap k) (nnnorm_deriv_cap_le k)
    (cap_zero k) v

private theorem value_capH (k : ℝ) (v : W1p (volume : Measure ℂ) ⊤ 2) :
    (W1p.value (capH k v) : ℂ → ℝ) =ᵐ[volume] fun z ↦ cap k (W1p.value v z) := by
  unfold capH
  simpa using W1p.value_contDiffComp_ae (M := 1) ENNReal.ofNat_ne_top (contDiff_cap k)
    (nnnorm_deriv_cap_le k) (cap_zero k) v

private theorem norm_gradient_capH_sq (k : ℝ) (v : W1p (volume : Measure ℂ) ⊤ 2) :
    ‖W1p.gradient (capH k v)‖ ^ 2 =
      ∫ z, deriv (cap k) (W1p.value v z) ^ 2 * ‖W1p.gradient v z‖ ^ 2 := by
  unfold capH
  have h := W1p.gradient_contDiffComp_ae (M := 1) ENNReal.ofNat_ne_top (contDiff_cap k)
    (nnnorm_deriv_cap_le k) (cap_zero k) v
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae (h.mono fun z hz ↦ ?_)
  simp only [hz, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem continuous_deriv_cap (k : ℝ) : Continuous (deriv (cap k)) := by
  simp only [funext (deriv_cap k)]
  fun_prop (disch := intro x; positivity)

/-- The potential of a capped element is dominated by the potential of the element. -/
private theorem integrable_backgroundWeight_mul_capH {Q : Polynomial ℂ}
    {v : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)) (k : ℝ) :
    Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z) := by
  refine hv.mono' ((continuous_backgroundWeight Q.continuous).aestronglyMeasurable.mul
    (Real.continuous_exp_two_mul_sub_one_sub_two_mul.comp_aestronglyMeasurable
      (W1p.memLp_value (capH k v)).aestronglyMeasurable)) ?_
  filter_upwards [value_capH k v] with z hz
  rw [hz, Real.norm_of_nonneg (mul_nonneg (backgroundWeight_nonneg _ z)
    (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _))]
  exact mul_le_mul_of_nonneg_left (exp_two_mul_cap_sub_le k _) (backgroundWeight_nonneg _ z)

/-- The potential of an element capped at a level `k ≥ 0` is integrable for every weight between
`0` and `1`. -/
private theorem integrable_backgroundWeight_mul_capH_of_nonneg (Q : Polynomial ℂ) {k : ℝ}
    (hk : 0 ≤ k) (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z) := by
  refine (((W1p.memLp_value v).integrable_sq).const_mul
    (4 * (Real.exp (2 * (k + 1)) + 2))).mono'
    ((continuous_backgroundWeight Q.continuous).aestronglyMeasurable.mul
    (Real.continuous_exp_two_mul_sub_one_sub_two_mul.comp_aestronglyMeasurable
      (W1p.memLp_value (capH k v)).aestronglyMeasurable)) ?_
  filter_upwards [value_capH k v] with z hz
  have hφ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (cap k (W1p.value v z))
  rw [hz, Real.norm_of_nonneg (mul_nonneg (backgroundWeight_nonneg _ z) hφ)]
  calc backgroundWeight Q.eval z *
        (Real.exp (2 * cap k (W1p.value v z)) - 1 - 2 * cap k (W1p.value v z))
      ≤ 1 * (Real.exp (2 * cap k (W1p.value v z)) - 1 - 2 * cap k (W1p.value v z)) :=
        mul_le_mul_of_nonneg_right ((backgroundWeight_lt_one _ z).le) hφ
    _ ≤ 4 * (Real.exp (2 * (k + 1)) + 2) * W1p.value v z ^ 2 := by
        rw [one_mul]
        exact exp_two_mul_cap_sub_le_mul_sq hk _

/-- The Dirichlet energies of the caps of `v` converge to that of `v`. -/
private theorem tendsto_norm_gradient_capH_sq (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun k : ℕ ↦ ‖W1p.gradient (capH k v)‖ ^ 2) atTop (𝓝 (‖W1p.gradient v‖ ^ 2)) := by
  simp only [norm_gradient_capH_sq]
  rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [Opens.coe_top, Measure.restrict_univ]
  have hg := W1p.integrable_norm_gradient_sq v
  simp only [Opens.coe_top, Measure.restrict_univ] at hg
  refine tendsto_integral_of_dominated_convergence _ (fun k ↦
    (((continuous_deriv_cap _).comp_aestronglyMeasurable
      (W1p.memLp_value v).aestronglyMeasurable).pow 2).mul hg.aestronglyMeasurable) hg
    (fun k ↦ ae_of_all _ fun z ↦ ?_)
    (ae_of_all _ fun z ↦ by simpa using ((tendsto_deriv_cap _).pow 2).mul_const _)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : deriv (cap k) (W1p.value v z) ^ 2 ≤ 1 := by
    have := nnnorm_deriv_cap_le k (W1p.value v z)
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (deriv (cap k) (W1p.value v z)),
      sq_abs (deriv (cap k) (W1p.value v z))]
  nlinarith [sq_nonneg ‖W1p.gradient v z‖]

/-- If the potential of `v` is integrable, the potentials of its caps converge to it. -/
private theorem tendsto_integral_backgroundWeight_mul_capH {Q : Polynomial ℂ}
    {v : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)) :
    Tendsto (fun k : ℕ ↦ ∫ z, backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z)) atTop
      (𝓝 (∫ z, backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z))) := by
  refine tendsto_integral_of_dominated_convergence _
    (fun k ↦ (integrable_backgroundWeight_mul_capH hv k).aestronglyMeasurable) hv (fun k ↦ ?_) ?_
  · filter_upwards [value_capH k v] with z hz
    rw [hz, Real.norm_of_nonneg (mul_nonneg (backgroundWeight_nonneg _ z)
      (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _))]
    exact mul_le_mul_of_nonneg_left (exp_two_mul_cap_sub_le k _) (backgroundWeight_nonneg _ z)
  · filter_upwards [ae_all_iff.mpr fun k : ℕ ↦ value_capH k v] with z hz
    simp only [hz]
    exact tendsto_const_nhds.mul
      ((Real.continuous_exp_two_mul_sub_one_sub_two_mul.tendsto _).comp (tendsto_cap _))

/-- The linear terms of the caps of `v` converge to that of `v`. -/
private theorem tendsto_integral_backgroundSource_mul_capH {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun k : ℕ ↦ ∫ z, backgroundSource Q.eval z * W1p.value (capH k v) z) atTop
      (𝓝 (∫ z, backgroundSource Q.eval z * W1p.value v z)) := by
  have hint : Integrable fun z ↦ backgroundSource Q.eval z * W1p.value v z :=
    (memLp_backgroundSource_eval hQ).integrable_mul (W1p.memLp_value v)
  refine tendsto_integral_of_dominated_convergence _ (fun k ↦
    (continuous_backgroundSource Q.differentiable).aestronglyMeasurable.mul
      (W1p.memLp_value (capH k v)).aestronglyMeasurable) hint.norm (fun k ↦ ?_) ?_
  · filter_upwards [value_capH k v] with z hz
    rw [hz, norm_mul, norm_mul]
    gcongr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← sq_le_sq₀ (abs_nonneg _) (abs_nonneg _),
      sq_abs, sq_abs]
    exact sq_cap_le k _
  · filter_upwards [ae_all_iff.mpr fun k : ℕ ↦ value_capH k v] with z hz
    simp only [hz]
    exact tendsto_const_nhds.mul (tendsto_cap _)

/-- **Recovery in the level.** If `I_Q(v) < ∞`, then `I_Q(v_k) → I_Q(v)` for the caps `v_k` of `v`
at the levels `k → ∞`. -/
private theorem tendsto_sobolevReducedFunctional_capH {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    {v : W1p (volume : Measure ℂ) ⊤ 2} (hv : sobolevReducedFunctional Q v ≠ ⊤) :
    Tendsto (fun k : ℕ ↦ sobolevReducedFunctional Q (capH k v)) atTop
      (𝓝 (sobolevReducedFunctional Q v)) := by
  have hpot : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z) := by
    simpa only [backgroundWeight_def] using sobolevReducedFunctional_ne_top_iff.mp hv
  simp only [sobolevReducedFunctional_eq_coe_background
      (integrable_backgroundWeight_mul_capH hpot _),
    sobolevReducedFunctional_eq_coe_background hpot, EReal.tendsto_coe]
  exact (((tendsto_norm_gradient_capH_sq v).div_const 2).add
    ((tendsto_integral_backgroundWeight_mul_capH hpot).div_const 16)).add
    (tendsto_integral_backgroundSource_mul_capH hQ v)

/-- **Recovery along the family.** For a fixed level `k ≥ 0`, the values of Taubes's functionals
`I_(P i)` at the cap `v_k` converge to `I_(P₀)(v_k)`. -/
private theorem tendsto_sobolevReducedFunctional_capH_of_tendsto_coeff [l.IsCountablyGenerated]
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) {k : ℝ} (hk : 0 ≤ k)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun i ↦ sobolevReducedFunctional (P i) (capH k v)) l
      (𝓝 (sobolevReducedFunctional P₀ (capH k v))) := by
  simp only [sobolevReducedFunctional_eq_coe_background
      (integrable_backgroundWeight_mul_capH_of_nonneg _ hk v), EReal.tendsto_coe]
  refine (tendsto_const_nhds.add ?_).add ?_
  · -- The potentials converge by dominated convergence, with the unweighted bound `C v²`.
    refine (tendsto_integral_filter_of_dominated_convergence
      (fun z ↦ 4 * (Real.exp (2 * (k + 1)) + 2) * W1p.value v z ^ 2)
      (Eventually.of_forall fun i ↦
        (integrable_backgroundWeight_mul_capH_of_nonneg (P i) hk v).aestronglyMeasurable)
      (Eventually.of_forall fun i ↦ ?_)
      (((W1p.memLp_value v).integrable_sq).const_mul _)
      (ae_of_all _ fun z ↦ (tendsto_backgroundWeight hdeg hP z).mul_const _)).div_const 16
    filter_upwards [value_capH k v] with z hz
    have hφ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (cap k (W1p.value v z))
    rw [hz, Real.norm_of_nonneg (mul_nonneg (backgroundWeight_nonneg _ z) hφ)]
    calc backgroundWeight (P i).eval z * (Real.exp (2 * cap k (W1p.value v z)) - 1 -
          2 * cap k (W1p.value v z))
        ≤ 1 * (Real.exp (2 * cap k (W1p.value v z)) - 1 - 2 * cap k (W1p.value v z)) :=
          mul_le_mul_of_nonneg_right ((backgroundWeight_lt_one _ z).le) hφ
      _ ≤ 4 * (Real.exp (2 * (k + 1)) + 2) * W1p.value v z ^ 2 := by
          rw [one_mul]
          exact exp_two_mul_cap_sub_le_mul_sq hk _
  · -- The linear terms converge since the coefficients converge in `L²`.
    rw [← tendsto_sub_nhds_zero_iff]
    have hlim := (tendsto_integral_backgroundSource_sub_sq hm hdeg hP).mul_const
      (∫ z, W1p.value (capH k v) z ^ 2)
    rw [zero_mul] at hlim
    refine Real.tendsto_zero_of_eventually_sq_le ?_ hlim
    filter_upwards [Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff hP] with i hi
    exact sq_integral_mul_sub_integral_mul_le (memLp_backgroundSource_eval (hm.trans_le hi))
      (memLp_backgroundSource_eval hm) (W1p.memLp_value _)

/-! ### The lower bound -/

/-- Taubes's functional for `Q` with the weight `h` of its potential lowered to `h - ε`. -/
private def lowerFunctional (Q : Polynomial ℂ) (ε : ℝ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    EReal :=
  ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, backgroundSource Q.eval z * W1p.value u z : ℝ) : EReal) +
    (((∫⁻ z, ENNReal.ofReal ((backgroundWeight Q.eval z - ε) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal)

private theorem lowerSemicontinuous_lowerFunctional {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    (ε : ℝ) :
    LowerSemicontinuous fun u : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) ↦
      lowerFunctional Q ε ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm u) :=
  lowerSemicontinuous_add_lintegral_ofReal_mul_exp_sub_one_sub
    ((continuous_backgroundWeight Q.continuous).sub continuous_const).aemeasurable
    (memLp_backgroundSource_eval hQ)

/-- As `ε → 0`, the lowered functionals increase to Taubes's functional, by monotone
convergence in the potential. -/
private theorem tendsto_lowerFunctional (Q : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun n : ℕ ↦ lowerFunctional Q (1 / (n + 1)) u) atTop
      (𝓝 (sobolevReducedFunctional Q u)) := by
  set x : ℝ := ‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, backgroundSource Q.eval z * W1p.value u z
  have hφ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg
  have hmeas : AEStronglyMeasurable (fun z ↦
      Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
    Real.continuous_exp_two_mul_sub_one_sub_two_mul.comp_aestronglyMeasurable
      (W1p.memLp_value u).aestronglyMeasurable
  have hpot : Tendsto (fun n : ℕ ↦ ∫⁻ z, ENNReal.ofReal ((backgroundWeight Q.eval z - 1 / (n + 1)) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n ↦
      ((((continuous_backgroundWeight Q.continuous).sub continuous_const).aestronglyMeasurable.mul
        hmeas).aemeasurable.ennreal_ofReal)) (ae_of_all _ fun z n n' hnn' ↦ ?_)
      (ae_of_all _ fun z ↦ ?_)
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hφ _))
      have : (1 : ℝ) / (n' + 1) ≤ 1 / (n + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
      linarith
    · refine ENNReal.tendsto_ofReal ?_
      simpa using (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat).mul_const
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  have hcont : Tendsto (fun y : ℝ≥0∞ ↦ (x : EReal) + ((y / 16 : ℝ≥0∞) : EReal))
      (𝓝 (∫⁻ z, ENNReal.ofReal (backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))))
      (𝓝 ((x : EReal) + (((∫⁻ z, ENNReal.ofReal (backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal))) :=
    (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top x))
      (Or.inl (EReal.coe_ne_bot x))).tendsto.comp
      (tendsto_const_nhds.prodMk_nhds ((continuous_coe_ennreal_ereal.tendsto _).comp
        ((ENNReal.continuous_div_const 16 (by norm_num)).tendsto _)))
  rw [sobolevReducedFunctional_eq_background]
  exact hcont.comp hpot

/-- If the weight of `Q'` is at least that of `Q` minus `ε`, and the linear terms at `u` differ by
at most `δ`, then the lowered functional for `Q` at `u` is at most `I_(Q')(u) + δ`. -/
private theorem lowerFunctional_le_add {Q Q' : Polynomial ℂ} {ε δ : ℝ}
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ z, backgroundWeight Q.eval z - ε ≤ backgroundWeight Q'.eval z)
    (hl : (∫ z, backgroundSource Q.eval z * W1p.value u z) ≤
      (∫ z, backgroundSource Q'.eval z * W1p.value u z) + δ) :
    lowerFunctional Q ε u ≤ sobolevReducedFunctional Q' u + δ := by
  rw [lowerFunctional, sobolevReducedFunctional_eq_background, add_right_comm, ← EReal.coe_add]
  refine add_le_add (EReal.coe_le_coe_iff.mpr (by linarith)) ?_
  refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr (ENNReal.div_le_div_right ?_ _)
  refine lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (hw z) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)

/-- If the linear coefficients of `Q` and `Q'` are `L²`-close relative to `δ` and the radius `C`,
then on the ball of radius `C` the linear term of `Q` exceeds that of `Q'` by at most `δ`. -/
private theorem integral_backgroundSource_mul_le_add {Q Q' : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    (hQ' : 0 < Q'.natDegree) {C δ : ℝ} (hδ : 0 < δ)
    (hl : ∫ z, (backgroundSource Q'.eval z - backgroundSource Q.eval z) ^ 2 < (δ / (|C| + 1)) ^ 2)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : ‖u‖ ≤ C) :
    (∫ z, backgroundSource Q.eval z * W1p.value u z) ≤
      (∫ z, backgroundSource Q'.eval z * W1p.value u z) + δ := by
  have hval : ‖W1p.value u‖ ≤ |C| := (W1p.norm_value_le _).trans (hu.trans (le_abs_self C))
  have hle : ((∫ z, backgroundSource Q.eval z * W1p.value u z) -
      ∫ z, backgroundSource Q'.eval z * W1p.value u z) ^ 2 ≤ δ ^ 2 := by
    refine (sq_integral_mul_sub_integral_mul_le (memLp_backgroundSource_eval hQ)
      (memLp_backgroundSource_eval hQ') (W1p.memLp_value u)).trans ?_
    have h1 : (∫ z, (backgroundSource Q.eval z - backgroundSource Q'.eval z) ^ 2) =
        ∫ z, (backgroundSource Q'.eval z - backgroundSource Q.eval z) ^ 2 := by
      congr 1 with z
      ring
    have h2 : ‖W1p.value u‖ ^ 2 ≤ (|C| + 1) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    have e2 : ∫ z, W1p.value u z ^ 2 = ‖W1p.value u‖ ^ 2 := by
      simpa using W1p.integral_value_sq_eq_norm_value_sq u
    rw [h1, e2]
    calc (∫ z, (backgroundSource Q'.eval z - backgroundSource Q.eval z) ^ 2) * ‖W1p.value u‖ ^ 2
        ≤ (δ / (|C| + 1)) ^ 2 * (|C| + 1) ^ 2 :=
          mul_le_mul hl.le h2 (sq_nonneg _) (sq_nonneg _)
      _ = δ ^ 2 := by field_simp
  linarith [(abs_le_of_sq_le_sq' hle hδ.le).2]

/-- **The lower bound.** Near a weak limit point `a`, on a fixed ball of `H¹(ℂ)`, Taubes's
functionals `I_(P i)` eventually exceed every real number below `I_(P₀)(a)`. -/
private theorem exists_mem_nhds_eventually_lt [l.IsCountablyGenerated] (hm : 0 < P₀.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) (C : ℝ)
    (a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)) {b : ℝ}
    (hb : (b : EReal) <
      sobolevReducedFunctional P₀ ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a)) :
    ∃ U ∈ 𝓝 a, ∀ᶠ i in l, ∀ w ∈ U,
      ‖(toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm w‖ ≤ C →
        (b : EReal) <
          sobolevReducedFunctional (P i)
            ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm w) := by
  set e := (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm
  -- Lower the weight by a small `ε` while keeping `b` below the lowered functional at `a`.
  obtain ⟨n, hn⟩ := ((tendsto_lowerFunctional P₀ (e a)).eventually (lt_mem_nhds hb)).exists
  set ε : ℝ := 1 / (n + 1)
  have hε : 0 < ε := by positivity
  obtain ⟨b', hbb', hb'⟩ := EReal.lt_iff_exists_real_btwn.mp hn
  have hbb'' : b < b' := EReal.coe_lt_coe_iff.mp hbb'
  set δ := b' - b with hδdef
  have hδ : 0 < δ := sub_pos.mpr hbb''
  refine ⟨{w | (b' : EReal) < lowerFunctional P₀ ε (e w)},
    lowerSemicontinuous_lowerFunctional hm ε a b' hb', ?_⟩
  -- Eventually the weights are above `h₀ - ε` and the linear terms are `δ`-close on the ball.
  have hδC : 0 < (δ / (|C| + 1)) ^ 2 := by positivity
  filter_upwards [eventually_forall_backgroundWeight_sub_le hm hdeg hP hε,
    (tendsto_integral_backgroundSource_sub_sq hm hdeg hP).eventually (gt_mem_nhds hδC),
    Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff hP] with i hw hl hle w hwU hwC
  have hlin := integral_backgroundSource_mul_le_add hm (hm.trans_le hle) hδ hl hwC
  have hcomp := lowerFunctional_le_add (hw := hw) hlin
  -- `b' < lowered ≤ I_(P i) + δ` and `b' = b + δ` give `b < I_(P i)`.
  by_contra hlt
  have h1 := add_le_add (not_lt.mp hlt) (le_refl (δ : EReal))
  rw [← EReal.coe_add, hδdef, add_sub_cancel] at h1
  have h2 : (b' : EReal) < lowerFunctional P₀ ε (e w) := hwU
  exact (h2.trans_le hcomp).not_ge h1

/-! ### Convergence of the minimum values and of the minimizers -/

/-- **Convergence of the minimum values.** Let `P i` be polynomials whose coefficients converge,
along a countably generated filter, to those of a polynomial `P₀` of degree at least one, with
`deg P i ≤ deg P₀` eventually. If `u i` minimizes Taubes's functional `I_(P i)` eventually and
`u₀` minimizes `I_(P₀)`, then `I_(P i)(u i) → I_(P₀)(u₀)`. -/
theorem tendsto_sobolevReducedFunctional_of_tendsto_coeff [l.IsCountablyGenerated]
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤ sobolevReducedFunctional (P i) v)
    {u₀ : W1p (volume : Measure ℂ) ⊤ 2} (hu₀ : ∀ v, sobolevReducedFunctional P₀ u₀ ≤
      sobolevReducedFunctional P₀ v) :
    Tendsto (fun i ↦ sobolevReducedFunctional (P i) (u i)) l
      (𝓝 (sobolevReducedFunctional P₀ u₀)) := by
  set e := (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm
  have hu₀0 : sobolevReducedFunctional P₀ u₀ ≤ 0 := (hu₀ 0).trans_eq sobolevReducedFunctional_zero
  have hu₀top : sobolevReducedFunctional P₀ u₀ ≠ ⊤ := (hu₀0.trans_lt EReal.zero_lt_top).ne
  refine tendsto_order.mpr ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- The lower bound: otherwise a weak cluster point along a subfilter contradicts it.
    obtain ⟨x, hbx, hx⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    suffices h : ∀ᶠ i in l, (x : EReal) < sobolevReducedFunctional (P i) (u i) from
      h.mono fun i hi ↦ hbx.trans hi
    by_contra hne
    rw [not_eventually] at hne
    simp only [not_lt] at hne
    set l' := l ⊓ 𝓟 {i | sobolevReducedFunctional (P i) (u i) ≤ x}
    have : l'.NeBot := frequently_iff_neBot.mp hne
    have hl' : l' ≤ l := inf_le_left
    obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_sobolevReducedFunctional_le hm hdeg hP 0
    have hbound : ∀ᶠ i in l', ‖u i‖ ≤ C := by
      filter_upwards [hl' hC, hl' hu] with i hCi hui
      exact hCi _ ((hui 0).trans_eq sobolevReducedFunctional_zero)
    obtain ⟨a, -, ha⟩ := (isCompact_toWeakSpace_closedBall
      surjective_inclusionInDoubleDual_of_uniformConvexSpace 0 C).exists_mapClusterPt
      (u := fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i))
      (tendsto_principal.mpr (hbound.mono fun i hi ↦
        mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hi)))
    obtain ⟨U, hU, hUl⟩ := exists_mem_nhds_eventually_lt hm (hdeg.filter_mono hl')
      (fun k ↦ (hP k).mono_left hl') C a (b := x) (hx.trans_le (hu₀ (e a)))
    obtain ⟨i, hiU, ⟨hiU', hix⟩, hiC⟩ := ((ha.frequently hU).and_eventually
      ((hUl.and (inf_le_right (a := l) (b := 𝓟 _) (mem_principal_self _))).and hbound)).exists
    exact absurd ((hiU' _ hiU (by simpa [e] using hiC)).trans_le (by simpa [e] using hix))
      (lt_irrefl _)
  · -- The upper bound: compare with the caps of `u₀`.
    obtain ⟨k, hk⟩ := ((tendsto_sobolevReducedFunctional_capH hm hu₀top).eventually
      (gt_mem_nhds hb)).exists
    filter_upwards [hu, (tendsto_sobolevReducedFunctional_capH_of_tendsto_coeff hm hdeg hP
      (Nat.cast_nonneg k) u₀).eventually (gt_mem_nhds hk)] with i hui hi
    exact (hui _).trans_lt hi

/-- **Weak cluster points of minimizers are minimizers.** Let `P i` be polynomials whose
coefficients converge, along a countably generated filter, to those of a polynomial `P₀` of degree
at least one, with `deg P i ≤ deg P₀` eventually, and let `u i` minimize Taubes's functional
`I_(P i)` eventually. Then every weak cluster point of `u i` in `H¹(ℂ)` minimizes `I_(P₀)`. -/
theorem forall_sobolevReducedFunctional_le_of_mapClusterPt [l.IsCountablyGenerated]
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤ sobolevReducedFunctional (P i) v)
    {a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)}
    (ha : MapClusterPt a l fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i))
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P₀ ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a) ≤
      sobolevReducedFunctional P₀ v := by
  set e := (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm
  rcases eq_or_ne (sobolevReducedFunctional P₀ v) ⊤ with hv | hv
  · exact hv ▸ le_top
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_sobolevReducedFunctional_le hm hdeg hP 0
  have hbound : ∀ᶠ i in l, ‖u i‖ ≤ C := by
    filter_upwards [hC, hu] with i hCi hui
    exact hCi _ ((hui 0).trans_eq sobolevReducedFunctional_zero)
  -- It suffices to compare with every cap of `v`.
  refine ge_of_tendsto' (tendsto_sobolevReducedFunctional_capH hm hv) fun k ↦ ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨b, hb₁, hb₂⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨U, hU, hUl⟩ := exists_mem_nhds_eventually_lt hm hdeg hP C a hb₂
  obtain ⟨i, hiU, ⟨hiU', hui⟩, hik, hiC⟩ := ((ha.frequently hU).and_eventually
    ((hUl.and hu).and (((tendsto_sobolevReducedFunctional_capH_of_tendsto_coeff hm hdeg hP
      (Nat.cast_nonneg k) v).eventually (gt_mem_nhds hb₁)).and hbound))).exists
  have h1 := hiU' _ hiU (by simpa [e] using hiC)
  simp only [LinearEquiv.symm_apply_apply] at h1
  exact absurd ((h1.trans_le (hui _)).trans hik) (lt_irrefl _)

/-- **Existence of a minimizing weak cluster point.** Under the hypotheses of
`TauCeti.Vortex.forall_sobolevReducedFunctional_le_of_mapClusterPt`, for a nontrivial filter the
minimizers `u i` have a weak cluster point in `H¹(ℂ)`, and every such point minimizes `I_(P₀)`. -/
theorem exists_mapClusterPt_forall_sobolevReducedFunctional_le [l.IsCountablyGenerated] [l.NeBot]
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤
      sobolevReducedFunctional (P i) v) :
    ∃ a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2),
      MapClusterPt a l (fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i)) ∧
      ∀ v, sobolevReducedFunctional P₀ ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a) ≤
        sobolevReducedFunctional P₀ v := by
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_sobolevReducedFunctional_le hm hdeg hP 0
  have hbound : ∀ᶠ i in l, ‖u i‖ ≤ C := by
    filter_upwards [hC, hu] with i hCi hui
    exact hCi _ ((hui 0).trans_eq sobolevReducedFunctional_zero)
  obtain ⟨a, -, ha⟩ := (isCompact_toWeakSpace_closedBall
    surjective_inclusionInDoubleDual_of_uniformConvexSpace 0 C).exists_mapClusterPt
    (u := fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i))
    (tendsto_principal.mpr (hbound.mono fun i hi ↦
      mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hi)))
  exact ⟨a, ha, forall_sobolevReducedFunctional_le_of_mapClusterPt hm hdeg hP hu ha⟩

end TauCeti.Vortex
