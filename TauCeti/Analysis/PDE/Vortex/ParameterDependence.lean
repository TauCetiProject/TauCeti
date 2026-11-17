/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Minimizer
public import TauCeti.Analysis.PDE.Vortex.Variational
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Polynomial.Coeff.Convergence
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Stability of Taubes's variational problem under perturbation of the polynomial

For a complex polynomial `P` of degree `m ≥ 1`, Taubes's functional `I_P` on `H¹(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional P`) attains its minimum
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), and its minimizers solve the reduced
equation of the vortex with zero divisor `P`. Through the elementary symmetric chart
`Sym.coeffHomeomorph`, the effective divisors of degree `m` correspond to the monic polynomials
of degree `m`, with the topology of `Sym ℂ m` given by the coefficients. This file shows that the
variational problem is stable under perturbation of these coefficients: the minimum values
converge, and weak cluster points of minimizers are minimizers.

Let `P i` be polynomials, indexed along a filter `l`, whose coefficients
converge to those of `P₀`, with `deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually. Let `u i` be a
minimizer of `I_(P i)`. Then:

* the sublevel sets of `I_(P i)`, in particular the minimizers, are eventually contained in a
  fixed ball of `H¹(ℂ)` (`TauCeti.Vortex.exists_eventually_norm_le_of_sobolevReducedFunctional_le`);
* the minimum values converge, `I_(P i)(u i) → min I_(P₀)`
  (`TauCeti.Vortex.tendsto_sobolevReducedFunctional_of_tendsto_coeff`);
* every weak cluster point of `u i` minimizes `I_(P₀)`
  (`TauCeti.Vortex.sobolevReducedFunctional_le_of_mapClusterPt`), and when `l` is
  nontrivial such a cluster point exists
  (`TauCeti.Vortex.exists_mapClusterPt_forall_sobolevReducedFunctional_le`).

The degree condition is necessary: the coefficients of `z + z ^ 2 / i` converge to those of `z`,
but its second zero `-i` escapes to infinity.

The proof is a Γ-convergence argument with three ingredients.

* **Uniform coefficients.** Along the family, the weights `h_i = ‖P i‖² / (1 + ‖P i‖²)`
  (`TauCeti.Vortex.backgroundWeight`) converge to `h₀` uniformly on the plane
  (`TauCeti.Vortex.tendstoUniformly_backgroundWeight`), and the coefficients
  `c_i = 2 ‖(P i)'‖² / (1 + ‖P i‖²)² - (1 + ‖P i‖²)⁻¹ / 8` (`TauCeti.Vortex.backgroundSource`) of
  the linear term are dominated by a fixed multiple of `(1 + ‖z‖)⁻²` and converge to `c₀` in `L²`
  (`TauCeti.Vortex.tendsto_integral_backgroundSource_sub_sq`). These follow from the uniform
  polynomial bounds of `TauCeti.Analysis.Polynomial.Coeff.Convergence`. They also make the
  coercivity of `TauCeti.Vortex.exists_forall_norm_le_of_sobolevReducedFunctional_le` uniform.
  Dominated convergence needs a countably generated filter; since eventually `P i` is determined
  by its coefficient vector in `Fin (deg P₀ + 1) → ℂ`, whose neighbourhood filters are countably
  generated, it suffices to argue along those (`Polynomial.tendsto_of_isCountablyGenerated`).
* **The lower bound.** Fix `ε > 0`. The potential integrand is `ENNReal.ofReal (h φ)`, so a weight
  is cut off at zero where it is negative. Since eventually `h_i ≥ h₀ - ε`, replacing `h_i` by
  `h₀ - ε` can only lower the potential, so the functional with weight `h₀ - ε` and linear
  coefficient `c_i` is at most `I_(P i)`. Separately, replacing `c_i` by `c₀` changes the linear
  term on a bounded set of `H¹(ℂ)` by an error tending to zero, by the `L²` convergence of the
  coefficients. The resulting functional `I_(P₀),ε`, with weight `h₀ - ε` (cut off at zero) and
  coefficient `c₀`, is weakly lower semicontinuous
  (`TauCeti.Vortex.lowerSemicontinuous_add_lintegral_ofReal_mul_exp_sub_one_sub`). Finally, as
  `ε → 0`, `I_(P₀),ε` increases to `I_(P₀)` pointwise by monotone convergence. Together these
  bound `I_(P i)` below near any weak limit point by `I_(P₀)` there.
* **The upper bound.** For `v ∈ H¹(ℂ)` of finite energy, the truncations
  `v_k = v - (v - k)⁺ = min v k` (`TauCeti.W1p.posPartAbove`) are bounded above, so their
  potential is integrable without the weight, and `I_(P i)(v_k) → I_(P₀)(v_k)` by dominated
  convergence; as `k → ∞`, `I_(P₀)(v_k) → I_(P₀)(v)`. No exponential integrability of `H¹`
  functions is needed.

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

/-- **Uniform convergence of the weights.** If the coefficients of `P i` converge to those of
`P₀`, with `deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually, then the weights
`h_i = ‖P i‖² / (1 + ‖P i‖²)` converge to `h₀ = ‖P₀‖² / (1 + ‖P₀‖²)` uniformly on the plane. -/
theorem tendstoUniformly_backgroundWeight :
    TendstoUniformly (fun i ↦ backgroundWeight (P i).eval) (backgroundWeight P₀.eval) l := by
  obtain ⟨A, hA⟩ := Polynomial.exists_eventually_forall_inv_one_add_norm_eval_sq_le hm hdeg hP
  obtain ⟨A₀, hA₀⟩ := Polynomial.exists_eventually_forall_inv_one_add_norm_eval_sq_le
    (l := (⊤ : Filter Unit)) (P := fun _ ↦ P₀) hm (Eventually.of_forall fun _ ↦ le_rfl)
    fun k ↦ tendsto_const_nhds
  have hA₀' := eventually_top.mp hA₀ ()
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  -- Outside a disc both weights are within `δ` of `1`; on the disc `P i → P₀` uniformly.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ max A A₀ ≤ δ * (1 + R) ^ 2 := by
    refine ⟨|max A A₀| / δ, by positivity, ?_⟩
    have h1 : |max A A₀| / δ ≤ (1 + |max A A₀| / δ) ^ 2 := by
      nlinarith [abs_nonneg (max A A₀), sq_nonneg (|max A A₀| / δ)]
    calc max A A₀ ≤ |max A A₀| := le_abs_self _
      _ = δ * (|max A A₀| / δ) := by field_simp
      _ ≤ δ * (1 + |max A A₀| / δ) ^ 2 := by gcongr
  have hunif := Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff hdeg hP R
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hA, hunif ε hε] with i hi hu z
  rw [Real.dist_eq]
  by_cases hz : ‖z‖ ≤ R
  · have hd := hu z (mem_closedBall_zero_iff.mpr hz)
    rw [dist_eq_norm] at hd
    exact (abs_backgroundWeight_sub_backgroundWeight_le P₀.eval (P i).eval z).trans_lt hd
  · rw [not_le] at hz
    have hsmall : ∀ A' ≤ max A A₀, A' / (1 + ‖z‖) ^ 2 ≤ δ := fun A' hA' ↦ by
      rw [div_le_iff₀ (by positivity)]
      exact hA'.trans (hR.2.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [hR.1]) (by linarith) 2) hδ.le))
    have h1 := one_sub_backgroundWeight (P i).eval z
    have h2 := one_sub_backgroundWeight P₀.eval z
    have h3 := (hi z).trans (hsmall A (le_max_left _ _))
    have h4 := (hA₀' z).trans (hsmall A₀ (le_max_right _ _))
    rw [abs_lt]
    constructor <;>
      linarith [backgroundWeight_lt_one P₀.eval z, backgroundWeight_lt_one (P i).eval z]

/-- **Uniform decay of the linear coefficients.** If the coefficients of `P i` converge to those
of `P₀`, with `deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually, then the linear coefficients
`c_i = 2 ‖(P i)'‖² / (1 + ‖P i‖²)² - (1 + ‖P i‖²)⁻¹ / 8` are eventually dominated by a fixed
multiple of `(1 + ‖z‖)⁻²`. -/
theorem exists_eventually_forall_abs_backgroundSource_le :
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
/-- **Pointwise convergence of the linear coefficients.** If the coefficients of `P i` converge to
those of `P₀` and `deg P i ≤ deg P₀` eventually, then the linear coefficients
`c_i = 2 ‖(P i)'‖² / (1 + ‖P i‖²)² - (1 + ‖P i‖²)⁻¹ / 8` converge to `c₀` at every point. -/
theorem tendsto_backgroundSource (z : ℂ) :
    Tendsto (fun i ↦ backgroundSource (P i).eval z) l (𝓝 (backgroundSource P₀.eval z)) := by
  have h := ((Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff hdeg hP
    ‖z‖).tendsto_at (mem_closedBall_zero_iff.mpr le_rfl)).norm
  have hd := ((Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff
    (P := fun i ↦ (P i).derivative)
    (N := P₀.natDegree) (hdeg.mono fun i hi ↦ (Polynomial.natDegree_derivative_le _).trans
      (Nat.sub_le_of_le_add (by omega)))
    (fun k ↦ Polynomial.tendsto_coeff_derivative (hP (k + 1))) ‖z‖).tendsto_at
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

/-- The linear coefficients converge in `L²`, along a countably generated filter. -/
private theorem tendsto_integral_backgroundSource_sub_sq_of_isCountablyGenerated
    [l.IsCountablyGenerated] :
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

/-- **Convergence of the linear coefficients in `L²`.** If the coefficients of `P i` converge to
those of `P₀`, with `deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually, then
`∫ (c_i - c₀)² → 0` for the linear coefficients `c_i` of Taubes's functionals. -/
theorem tendsto_integral_backgroundSource_sub_sq :
    Tendsto (fun i ↦ ∫ z, (backgroundSource (P i).eval z - backgroundSource P₀.eval z) ^ 2) l
      (𝓝 0) :=
  Polynomial.tendsto_of_isCountablyGenerated
    (G := fun Q ↦ ∫ z, (backgroundSource Q.eval z - backgroundSource P₀.eval z) ^ 2)
    (fun hdeg hP ↦ tendsto_integral_backgroundSource_sub_sq_of_isCountablyGenerated hm hdeg hP)
    hdeg hP

/-- **Uniformly bounded `L²` norms.** If the coefficients of `P i` converge to those of `P₀`, with
`deg P₀ ≥ 1` and `deg P i ≤ deg P₀` eventually, then the squared `L²` norms `∫ c_i²` of the linear
coefficients of Taubes's functionals are eventually bounded. -/
theorem exists_eventually_integral_backgroundSource_sq_le :
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
  filter_upwards [Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff (hP _), hR, hK]
    with i hle hRi hKi
  exact hC (P i) (hm.trans_le hle) hRi (by simpa only [backgroundSource_eval] using hKi)

/-! ### Truncation from above

For a level `k ≥ 0`, the truncation `v_k = v - (v - k)⁺ = min v k` of `v ∈ H¹(ℂ)` from above
(`TauCeti.W1p.posPartAbove`) has gradient `1_{v ≤ k} ∇v`. Since `t ↦ exp (2t) - 1 - 2t` is
increasing on `[0, ∞)`, truncating does not increase the potential of Taubes's functional, and
`v_k` tends to `v` as `k → ∞`. -/

/-- Truncating at a level `k ≥ 0` does not increase the integrand of the potential. -/
private theorem exp_two_mul_min_sub_le {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    Real.exp (2 * min t k) - 1 - 2 * min t k ≤ Real.exp (2 * t) - 1 - 2 * t := by
  rcases le_total t k with htk | hkt
  · rw [min_eq_left htk]
  · rw [min_eq_right hkt]
    exact Real.monotoneOn_exp_two_mul_sub_one_sub_two_mul hk (hk.trans hkt) hkt

/-- The integrand of the potential, truncated at a level `k ≥ 0`, is at most a multiple of `t²`. -/
private theorem exp_two_mul_min_sub_le_mul_sq {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    Real.exp (2 * min t k) - 1 - 2 * min t k ≤ 4 * (Real.exp (2 * k) + 2) * t ^ 2 := by
  refine (Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq (min_le_right t k)).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases le_total t k with htk | hkt
  · rw [min_eq_left htk]
  · rw [min_eq_right hkt]
    exact pow_le_pow_left₀ hk hkt 2

/-! ### Recovery sequences -/

/-- Taubes's functional, written with the weight `TauCeti.Vortex.backgroundWeight` and the
linear coefficient `TauCeti.Vortex.backgroundSource`. -/
theorem sobolevReducedFunctional_eq_add_lintegral_ofReal_backgroundWeight_mul (Q : Polynomial ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional Q u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, backgroundSource Q.eval z * W1p.value u z : ℝ) : EReal) +
        (((∫⁻ z, ENNReal.ofReal (backgroundWeight Q.eval z *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal) := by
  simp only [sobolevReducedFunctional_def, backgroundSource_eval, backgroundWeight_def]

/-- Taubes's functional, written with the weight and the linear coefficient, when the potential
is integrable. -/
theorem sobolevReducedFunctional_eq_coe_of_integrable_backgroundWeight_mul {Q : Polynomial ℂ}
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) :
    sobolevReducedFunctional Q u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, backgroundWeight Q.eval z *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, backgroundSource Q.eval z * W1p.value u z : ℝ) : EReal) := by
  simp only [backgroundWeight_def, backgroundSource_eval] at hu ⊢
  exact sobolevReducedFunctional_eq_coe hu

/-- Taubes's functional is infinite when its potential, written with the weight
`TauCeti.Vortex.backgroundWeight`, is not integrable. -/
theorem sobolevReducedFunctional_eq_top_of_not_integrable_backgroundWeight_mul
    {Q : Polynomial ℂ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ¬Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) :
    sobolevReducedFunctional Q u = ⊤ := by
  simp only [backgroundWeight_def] at hu
  exact sobolevReducedFunctional_eq_top hu

/-- Taubes's functional is finite exactly when its potential, written with the weight
`TauCeti.Vortex.backgroundWeight`, is integrable. -/
theorem sobolevReducedFunctional_ne_top_iff_integrable_backgroundWeight_mul {Q : Polynomial ℂ}
    {u : W1p (volume : Measure ℂ) ⊤ 2} :
    sobolevReducedFunctional Q u ≠ ⊤ ↔ Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
  simp only [backgroundWeight_def]
  exact sobolevReducedFunctional_ne_top_iff

/-- For a polynomial `Q` of degree at least one, the linear coefficient
`TauCeti.Vortex.backgroundSource` of Taubes's functional is square integrable. -/
private theorem memLp_backgroundSource_eval {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) :
    MemLp (backgroundSource Q.eval) 2 := by
  simpa only [← backgroundSource_eval] using
    memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hQ

/-- The truncation `min v k` of an element of `H¹(ℂ)` from above at the level `k`. -/
private def capH (k : ℕ) (v : W1p (volume : Measure ℂ) ⊤ 2) : W1p (volume : Measure ℂ) ⊤ 2 :=
  v - W1p.posPartAbove ENNReal.ofNat_ne_top (Nat.cast_nonneg k) v

private theorem value_capH (k : ℕ) (v : W1p (volume : Measure ℂ) ⊤ 2) :
    (W1p.value (capH k v) : ℂ → ℝ) =ᵐ[volume] fun z ↦ min (W1p.value v z) k := by
  have h1 := W1p.value_sub_ae v (W1p.posPartAbove ENNReal.ofNat_ne_top (Nat.cast_nonneg k) v)
  have h2 := W1p.value_posPartAbove_ae ENNReal.ofNat_ne_top (Nat.cast_nonneg (α := ℝ) k) v
  simp only [Opens.coe_top, Measure.restrict_univ] at h1 h2
  filter_upwards [h1, h2] with z h1 h2
  rw [capH, h1, Pi.sub_apply, h2]
  rcases le_total (W1p.value v z) k with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h, sub_zero]
  · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h, sub_sub_cancel]

private theorem gradient_capH (k : ℕ) (v : W1p (volume : Measure ℂ) ⊤ 2) :
    (W1p.gradient (capH k v) : ℂ → ℂ) =ᵐ[volume]
      {z | W1p.value v z ≤ k}.indicator (W1p.gradient v) := by
  have h1 := Lp.coeFn_sub (W1p.gradient v)
    (W1p.gradient (W1p.posPartAbove ENNReal.ofNat_ne_top (Nat.cast_nonneg k) v))
  have h2 := W1p.gradient_posPartAbove_ae ENNReal.ofNat_ne_top (Nat.cast_nonneg (α := ℝ) k) v
  simp only [Opens.coe_top, Measure.restrict_univ] at h1 h2
  filter_upwards [h1, h2] with z h1 h2
  rw [capH, W1p.gradient_sub, h1, Pi.sub_apply, h2]
  by_cases h : W1p.value v z ≤ k
  · rw [Set.indicator_of_notMem (not_lt.mpr h), Set.indicator_of_mem h, sub_zero]
  · rw [Set.indicator_of_mem (not_le.mp h), Set.indicator_of_notMem h, sub_self]

private theorem aestronglyMeasurable_backgroundWeight_mul (Q : Polynomial ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    AEStronglyMeasurable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
  (continuous_backgroundWeight Q.continuous).aestronglyMeasurable.mul
    (Real.continuous_exp_two_mul_sub_one_sub_two_mul.comp_aestronglyMeasurable
      (W1p.memLp_value u).aestronglyMeasurable)

/-- Truncating does not increase the potential. -/
private theorem ae_norm_backgroundWeight_mul_capH_le (Q : Polynomial ℂ) (k : ℕ)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z, ‖backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z)‖ ≤
      backgroundWeight Q.eval z * (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z) := by
  filter_upwards [value_capH k v] with z hz
  rw [hz, Real.norm_of_nonneg (mul_nonneg (backgroundWeight_nonneg _ z)
    (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _))]
  exact mul_le_mul_of_nonneg_left (exp_two_mul_min_sub_le (Nat.cast_nonneg k) _)
    (backgroundWeight_nonneg _ z)

/-- The potential of a truncation at the level `k` is dominated by `C_k v²`, for every weight
between `0` and `1`. -/
private theorem ae_norm_backgroundWeight_mul_capH_le_mul_sq (Q : Polynomial ℂ) (k : ℕ)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z, ‖backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z)‖ ≤
      4 * (Real.exp (2 * k) + 2) * W1p.value v z ^ 2 := by
  filter_upwards [value_capH k v] with z hz
  have hφ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (min (W1p.value v z) k)
  rw [hz, Real.norm_of_nonneg (mul_nonneg (backgroundWeight_nonneg _ z) hφ)]
  exact (mul_le_of_le_one_left hφ (backgroundWeight_lt_one _ z).le).trans
    (exp_two_mul_min_sub_le_mul_sq (Nat.cast_nonneg k) _)

/-- The potential of a truncated element is dominated by the potential of the element. -/
private theorem integrable_backgroundWeight_mul_capH_of_integrable {Q : Polynomial ℂ}
    {v : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)) (k : ℕ) :
    Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z) :=
  hv.mono' (aestronglyMeasurable_backgroundWeight_mul Q _)
    (ae_norm_backgroundWeight_mul_capH_le Q k v)

/-- The potential of a truncated element is integrable for every weight between `0` and `1`. -/
private theorem integrable_backgroundWeight_mul_capH (Q : Polynomial ℂ) (k : ℕ)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z) :=
  (((W1p.memLp_value v).integrable_sq).const_mul _).mono'
    (aestronglyMeasurable_backgroundWeight_mul Q _)
    (ae_norm_backgroundWeight_mul_capH_le_mul_sq Q k v)

/-- The Dirichlet energies of the truncations of `v` converge to that of `v`. -/
private theorem tendsto_norm_gradient_capH_sq (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun k : ℕ ↦ ‖W1p.gradient (capH k v)‖ ^ 2) atTop (𝓝 (‖W1p.gradient v‖ ^ 2)) := by
  have h (u : W1p (volume : Measure ℂ) ⊤ 2) :
      ‖W1p.gradient u‖ ^ 2 = ∫ z, ‖W1p.gradient u z‖ ^ 2 := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    simp only [Opens.coe_top, Measure.restrict_univ]
  simp only [h]
  have hg := W1p.integrable_norm_gradient_sq v
  simp only [Opens.coe_top, Measure.restrict_univ] at hg
  refine tendsto_integral_of_dominated_convergence _ (fun k ↦ by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (W1p.integrable_norm_gradient_sq (capH k v)).aestronglyMeasurable) hg (fun k ↦ ?_) ?_
  · filter_upwards [gradient_capH k v] with z hz
    rw [hz, Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self _ _) 2
  · filter_upwards [ae_all_iff.mpr fun k : ℕ ↦ gradient_capH k v] with z hz
    simp only [hz]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (W1p.value v z)] with k hk
    rw [Set.indicator_of_mem (s := {z | W1p.value v z ≤ k}) hk]

/-- If the potential of `v` is integrable, the potentials of its truncations converge to it. -/
private theorem tendsto_integral_backgroundWeight_mul_capH {Q : Polynomial ℂ}
    {v : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)) :
    Tendsto (fun k : ℕ ↦ ∫ z, backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value (capH k v) z) - 1 - 2 * W1p.value (capH k v) z)) atTop
      (𝓝 (∫ z, backgroundWeight Q.eval z *
        (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z))) := by
  refine tendsto_integral_of_dominated_convergence _
    (fun k ↦ aestronglyMeasurable_backgroundWeight_mul Q _) hv
    (fun k ↦ ae_norm_backgroundWeight_mul_capH_le Q k v) ?_
  filter_upwards [ae_all_iff.mpr fun k : ℕ ↦ value_capH k v] with z hz
  simp only [hz]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (W1p.value v z)] with k hk
  rw [min_eq_left hk]

/-- The linear terms of the truncations of `v` converge to that of `v`. -/
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
    rcases le_total (W1p.value v z) k with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      exact pow_le_pow_left₀ (Nat.cast_nonneg k) h 2
  · filter_upwards [ae_all_iff.mpr fun k : ℕ ↦ value_capH k v] with z hz
    simp only [hz]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (W1p.value v z)] with k hk
    rw [min_eq_left hk]

/-- **Recovery in the level.** If `I_Q(v) < ∞`, then `I_Q(v_k) → I_Q(v)` for the truncations
`v_k = min v k` of `v` at the levels `k → ∞`. -/
private theorem tendsto_sobolevReducedFunctional_capH {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    {v : W1p (volume : Measure ℂ) ⊤ 2} (hv : sobolevReducedFunctional Q v ≠ ⊤) :
    Tendsto (fun k : ℕ ↦ sobolevReducedFunctional Q (capH k v)) atTop
      (𝓝 (sobolevReducedFunctional Q v)) := by
  have hpot : Integrable fun z ↦ backgroundWeight Q.eval z *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z) :=
    sobolevReducedFunctional_ne_top_iff_integrable_backgroundWeight_mul.mp hv
  simp only [sobolevReducedFunctional_eq_coe_of_integrable_backgroundWeight_mul
      (integrable_backgroundWeight_mul_capH_of_integrable hpot _),
    sobolevReducedFunctional_eq_coe_of_integrable_backgroundWeight_mul hpot, EReal.tendsto_coe]
  exact (((tendsto_norm_gradient_capH_sq v).div_const 2).add
    ((tendsto_integral_backgroundWeight_mul_capH hpot).div_const 16)).add
    (tendsto_integral_backgroundSource_mul_capH hQ v)

/-- For a fixed level `k`, the values of Taubes's functionals `I_(P i)` at the truncation `v_k`
converge to `I_(P₀)(v_k)`, along a countably generated filter. -/
private theorem tendsto_sobolevReducedFunctional_capH_of_isCountablyGenerated
    [l.IsCountablyGenerated]
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) (k : ℕ)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun i ↦ sobolevReducedFunctional (P i) (capH k v)) l
      (𝓝 (sobolevReducedFunctional P₀ (capH k v))) := by
  simp only [sobolevReducedFunctional_eq_coe_of_integrable_backgroundWeight_mul
      (integrable_backgroundWeight_mul_capH _ k v), EReal.tendsto_coe]
  refine (tendsto_const_nhds.add ?_).add ?_
  · -- The potentials converge by dominated convergence, with the unweighted bound `C_k v²`.
    exact (tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun i ↦ aestronglyMeasurable_backgroundWeight_mul (P i) _)
      (Eventually.of_forall fun i ↦ ae_norm_backgroundWeight_mul_capH_le_mul_sq (P i) k v)
      (((W1p.memLp_value v).integrable_sq).const_mul _)
      (ae_of_all _ fun z ↦
        ((tendstoUniformly_backgroundWeight hm hdeg hP).tendsto_at z).mul_const _)).div_const 16
  · -- The linear terms converge since the coefficients converge in `L²`.
    rw [← tendsto_sub_nhds_zero_iff]
    have hlim := (tendsto_integral_backgroundSource_sub_sq hm hdeg hP).mul_const
      (∫ z, W1p.value (capH k v) z ^ 2)
    rw [zero_mul] at hlim
    refine Real.tendsto_zero_of_eventually_sq_le ?_ hlim
    filter_upwards [Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff (hP _)] with i hi
    exact sq_integral_mul_sub_integral_mul_le (memLp_backgroundSource_eval (hm.trans_le hi))
      (memLp_backgroundSource_eval hm) (W1p.memLp_value _)

/-- **Recovery along the family.** For a fixed level `k`, the values of Taubes's functionals
`I_(P i)` at the truncation `v_k` converge to `I_(P₀)(v_k)`. -/
private theorem tendsto_sobolevReducedFunctional_capH_of_tendsto_coeff
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) (k : ℕ)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    Tendsto (fun i ↦ sobolevReducedFunctional (P i) (capH k v)) l
      (𝓝 (sobolevReducedFunctional P₀ (capH k v))) :=
  Polynomial.tendsto_of_isCountablyGenerated (G := fun Q ↦ sobolevReducedFunctional Q (capH k v))
    (fun hdeg hP ↦ tendsto_sobolevReducedFunctional_capH_of_isCountablyGenerated hm hdeg hP k v)
    hdeg hP

/-! ### The lower bound -/

/-- Taubes's functional for `Q` with the weight `h` of its potential lowered to `h - ε`. As in
Taubes's functional, the potential integrand is taken through `ENNReal.ofReal`, so it is cut off
at zero where `h - ε` is negative. -/
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
  rw [sobolevReducedFunctional_eq_add_lintegral_ofReal_backgroundWeight_mul]
  exact hcont.comp hpot

/-- If the weight of `Q'` is at least that of `Q` minus `ε`, and the linear terms at `u` differ by
at most `δ`, then the lowered functional for `Q` at `u` is at most `I_(Q')(u) + δ`. -/
private theorem lowerFunctional_le_add {Q Q' : Polynomial ℂ} {ε δ : ℝ}
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ z, backgroundWeight Q.eval z - ε ≤ backgroundWeight Q'.eval z)
    (hl : (∫ z, backgroundSource Q.eval z * W1p.value u z) ≤
      (∫ z, backgroundSource Q'.eval z * W1p.value u z) + δ) :
    lowerFunctional Q ε u ≤ sobolevReducedFunctional Q' u + δ := by
  rw [lowerFunctional, sobolevReducedFunctional_eq_add_lintegral_ofReal_backgroundWeight_mul,
    add_right_comm, ← EReal.coe_add]
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
private theorem exists_mem_nhds_eventually_lt (hm : 0 < P₀.natDegree)
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
  filter_upwards
    [Metric.tendstoUniformly_iff.mp (tendstoUniformly_backgroundWeight hm hdeg hP) ε hε,
    (tendsto_integral_backgroundSource_sub_sq hm hdeg hP).eventually (gt_mem_nhds hδC),
    Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff (hP _)] with i hd hl hle w hwU hwC
  have hw (z : ℂ) : backgroundWeight P₀.eval z - ε ≤ backgroundWeight (P i).eval z := by
    have := hd z
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hlin := integral_backgroundSource_mul_le_add hm (hm.trans_le hle) hδ hl hwC
  have hcomp := lowerFunctional_le_add (hw := hw) hlin
  -- `b' < lowered ≤ I_(P i) + δ` and `b' = b + δ` give `b < I_(P i)`.
  by_contra hlt
  have h1 := add_le_add (not_lt.mp hlt) (le_refl (δ : EReal))
  rw [← EReal.coe_add, hδdef, add_sub_cancel] at h1
  have h2 : (b' : EReal) < lowerFunctional P₀ ε (e w) := hwU
  exact (h2.trans_le hcomp).not_ge h1

/-- Under the hypotheses of the lower bound, if `u i` is eventually bounded by `C` in `H¹(ℂ)` and
`a` is a weak cluster point of `u i`, then `I_(P i)(u i)` is frequently above every real number
below `I_(P₀)(a)`. -/
private theorem frequently_lt_sobolevReducedFunctional_of_mapClusterPt (hm : 0 < P₀.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2} {C : ℝ} (hC : ∀ᶠ i in l, ‖u i‖ ≤ C)
    {a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)}
    (ha : MapClusterPt a l fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i)) {b : ℝ}
    (hb : (b : EReal) <
      sobolevReducedFunctional P₀ ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a)) :
    ∃ᶠ i in l, (b : EReal) < sobolevReducedFunctional (P i) (u i) := by
  obtain ⟨U, hU, hUl⟩ := exists_mem_nhds_eventually_lt hm hdeg hP C a hb
  refine ((ha.frequently hU).and_eventually (hUl.and hC)).mono fun i ⟨hiU, hiU', hiC⟩ ↦ ?_
  simpa using hiU' _ hiU (by simpa using hiC)

/-! ### Convergence of the minimum values and weak cluster points of the minimizers -/

/-- Minimizers of Taubes's functionals along a converging family are eventually bounded in
`H¹(ℂ)`. -/
private theorem exists_eventually_norm_le_of_forall_sobolevReducedFunctional_le
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤
      sobolevReducedFunctional (P i) v) :
    ∃ C : ℝ, ∀ᶠ i in l, ‖u i‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_sobolevReducedFunctional_le hm hdeg hP 0
  refine ⟨C, ?_⟩
  filter_upwards [hC, hu] with i hCi hui
  exact hCi _ ((hui 0).trans_eq sobolevReducedFunctional_zero)

/-- An eventually bounded family in `H¹(ℂ)` along a nontrivial filter has a weak cluster point. -/
private theorem exists_mapClusterPt_of_eventually_norm_le [l.NeBot]
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2} {C : ℝ} (hC : ∀ᶠ i in l, ‖u i‖ ≤ C) :
    ∃ a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2),
      MapClusterPt a l fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i) := by
  obtain ⟨a, -, ha⟩ := (isCompact_toWeakSpace_closedBall
    surjective_inclusionInDoubleDual_of_uniformConvexSpace 0 C).exists_mapClusterPt
    (u := fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i))
    (tendsto_principal.mpr (hC.mono fun i hi ↦
      mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hi)))
  exact ⟨a, ha⟩

/-- **Convergence of the minimum values.** Let `P i` be polynomials whose coefficients converge,
along a filter, to those of a polynomial `P₀` of degree at least one, with `deg P i ≤ deg P₀`
eventually. If `u i` minimizes Taubes's functional `I_(P i)` eventually and
`u₀` minimizes `I_(P₀)`, then `I_(P i)(u i) → I_(P₀)(u₀)`. -/
theorem tendsto_sobolevReducedFunctional_of_tendsto_coeff (hm : 0 < P₀.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤ sobolevReducedFunctional (P i) v)
    {u₀ : W1p (volume : Measure ℂ) ⊤ 2} (hu₀ : ∀ v, sobolevReducedFunctional P₀ u₀ ≤
      sobolevReducedFunctional P₀ v) :
    Tendsto (fun i ↦ sobolevReducedFunctional (P i) (u i)) l
      (𝓝 (sobolevReducedFunctional P₀ u₀)) := by
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
    obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_forall_sobolevReducedFunctional_le hm hdeg hP hu
    obtain ⟨a, ha⟩ := exists_mapClusterPt_of_eventually_norm_le (hl' hC)
    obtain ⟨i, hi, hix⟩ := ((frequently_lt_sobolevReducedFunctional_of_mapClusterPt hm
      (hdeg.filter_mono hl') (fun k ↦ (hP k).mono_left hl') (hl' hC) ha
      (hx.trans_le (hu₀ _))).and_eventually
      (inf_le_right (a := l) (b := 𝓟 _) (mem_principal_self _))).exists
    exact (hi.trans_le (by simpa using hix)).false
  · -- The upper bound: compare with the truncations of `u₀`.
    obtain ⟨k, hk⟩ := ((tendsto_sobolevReducedFunctional_capH hm hu₀top).eventually
      (gt_mem_nhds hb)).exists
    filter_upwards [hu, (tendsto_sobolevReducedFunctional_capH_of_tendsto_coeff hm hdeg hP
      k u₀).eventually (gt_mem_nhds hk)] with i hui hi
    exact (hui _).trans_lt hi

/-- **Weak cluster points of minimizers are minimizers.** Let `P i` be polynomials whose
coefficients converge, along a filter, to those of a polynomial `P₀` of degree at least one, with
`deg P i ≤ deg P₀` eventually, and let `u i` minimize Taubes's functional `I_(P i)` eventually.
Then every weak cluster point of `u i` in `H¹(ℂ)` minimizes `I_(P₀)`. -/
theorem sobolevReducedFunctional_le_of_mapClusterPt (hm : 0 < P₀.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤ sobolevReducedFunctional (P i) v)
    {a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)}
    (ha : MapClusterPt a l fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i))
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P₀ ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a) ≤
      sobolevReducedFunctional P₀ v := by
  rcases eq_or_ne (sobolevReducedFunctional P₀ v) ⊤ with hv | hv
  · exact hv ▸ le_top
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_forall_sobolevReducedFunctional_le hm hdeg hP hu
  -- It suffices to compare with every truncation of `v`.
  refine ge_of_tendsto' (tendsto_sobolevReducedFunctional_capH hm hv) fun k ↦ ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨b, hb₁, hb₂⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨i, hi, hui, hik⟩ := ((frequently_lt_sobolevReducedFunctional_of_mapClusterPt hm hdeg hP
    hC ha hb₂).and_eventually (hu.and ((tendsto_sobolevReducedFunctional_capH_of_tendsto_coeff
      hm hdeg hP k v).eventually (gt_mem_nhds hb₁)))).exists
  exact ((hi.trans_le (hui _)).trans hik).false

/-- **Existence of a minimizing weak cluster point.** Under the hypotheses of
`TauCeti.Vortex.sobolevReducedFunctional_le_of_mapClusterPt`, for a nontrivial filter the
minimizers `u i` have a weak cluster point in `H¹(ℂ)` that minimizes `I_(P₀)`. -/
theorem exists_mapClusterPt_forall_sobolevReducedFunctional_le [l.NeBot]
    (hm : 0 < P₀.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    {u : ι → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ i in l, ∀ v, sobolevReducedFunctional (P i) (u i) ≤
      sobolevReducedFunctional (P i) v) :
    ∃ a : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2),
      MapClusterPt a l (fun i ↦ toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) (u i)) ∧
      ∀ v, sobolevReducedFunctional P₀ ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a) ≤
        sobolevReducedFunctional P₀ v := by
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_of_forall_sobolevReducedFunctional_le hm hdeg hP hu
  obtain ⟨a, ha⟩ := exists_mapClusterPt_of_eventually_norm_le hC
  exact ⟨a, ha, sobolevReducedFunctional_le_of_mapClusterPt hm hdeg hP hu ha⟩

end TauCeti.Vortex
