/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import TauCeti.MeasureTheory.Integral.NormRpow
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Riesz potentials

Let `E` be a real normed space of finite dimension `n ≥ 1` with an additive Haar measure `μ`, and
let `ω = μ(B(0, 1))`. The **Riesz kernel** of order `α ∈ (0, n)` is `‖x - y‖ ^ (α - n)`, and the
Riesz potential of a function is its integral against this kernel. This file proves the two kinds
of `Lᵖ`-`L^q` estimates for Riesz potentials: the non-sharp ones on a set of finite measure, and
the sharp Hardy–Littlewood–Sobolev inequality on the whole space.

## Riesz potentials on sets of finite measure

Let `Ω ⊆ E` be measurable. For `0 < κ ≤ 1` consider the potential

`V f (x) = ∫_Ω ‖x - y‖ ^ (n (κ - 1)) f(y) dy`,

whose kernel is the Riesz kernel of order `n κ`. Its two main estimates are those of
Gilbarg–Trudinger, Lemma 7.12, which drive the Sobolev embeddings in the potential-theoretic
approach:

* the kernel integral `∫_Ω ‖x - y‖ ^ (n (κ - 1)) dy` is at most `κ⁻¹ ω ^ (1 - κ) μ(Ω) ^ κ`,
  uniformly in `x`;
* for `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < κ`, the potential maps `Lᵖ(Ω)` to `L^q(Ω)`:
  `‖V f‖_q ≤ ((1 - δ) / (κ - δ)) ^ (1 - δ) ω ^ (1 - κ) μ(Ω) ^ (κ - δ) ‖f‖_p`.

The kernel bound follows from a rearrangement inequality, valid in any metric measure space: a
radially nonincreasing function of `dist x y` integrates over `Ω` to at most its integral over a
closed ball about `x` of no smaller measure. The `Lᵖ`-`L^q` bound is then Young's inequality for
integral kernels (`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`), applied to the
kernel raised to the power `r = 1 / (1 - δ)`, which is again a Riesz kernel, of order
`n (κ - δ) / (1 - δ)`.

The case `κ = 1/n`, `p = n`, where the kernel is `‖x - y‖ ^ (1 - n)` and the bound holds for
every finite `q ≥ n` with a constant of order `q ^ (1 - 1/n)`, is the input to the borderline
Sobolev embedding of `W^{1,n}_0(Ω)`.

## The Hardy–Littlewood–Sobolev inequality

On the whole space, the **Riesz potential** of order `α` of a function `f` is

`I_α f (x) = ∫ ‖x - y‖ ^ (α - n) ‖f y‖ dμ(y)`,

the convolution of `‖f‖` with the locally integrable kernel `‖·‖ ^ (α - n)`
(`TauCeti.rieszPotential`). It is taken in `ℝ≥0∞`, so it is defined for every `f` without any
integrability hypothesis, and it dominates the potential of `f` itself for vector-valued `f`.
No normalising constant is included.

The **Hardy–Littlewood–Sobolev inequality** (`TauCeti.eLpNorm_rieszPotential_le`) says that
`I_α` is bounded from `Lᵖ` to `L^q` whenever `1 < p` and `1 / q = 1 / p - α / n`:

`‖I_α f‖_q ≤ C ‖f‖_p`,

with `C` depending only on `μ`, `α` and `p`. This is the endpoint `δ = κ` excluded on sets of
finite measure above, and the exponent `q` is forced by scaling. It is the fractional integration
theorem behind the non-endpoint Strichartz estimates, where it is applied in the time variable,
and behind the Sobolev embedding of the Bessel-potential spaces.

The proof is Hedberg's. Split the integral defining `I_α f (x)` into dyadic shells
`r ≤ ‖x - y‖ < 2 r` with `r = R 2ᵏ`, `k ∈ ℤ`. On a shell the kernel is at most `r ^ (α - n)`
and the shell lies in the ball `B(x, 2 r)`. For the shells inside `B(x, R)` the integral of `‖f‖`
over that ball is at most `μ (B(x, 2 r)) M f (x)`, where `M` is the Hardy–Littlewood maximal
function. Since `α > 0` these shells sum to at most a multiple of `R ^ α M f (x)`. For the shells
outside `B(x, R)` Hölder's inequality bounds the same integral by
`μ (B(x, 2 r)) ^ (1 - 1 / p) ‖f‖_p`. Since `α < n / p` these shells sum to at most a multiple of
`R ^ (α - n / p) ‖f‖_p`. Choosing the radius `R` that balances the two terms gives **Hedberg's
inequality** (`TauCeti.rieszPotential_le_mul_maximalFunction_rpow_mul_eLpNorm_rpow`)

`I_α f (x) ≤ C (M f (x)) ^ (1 - θ) ‖f‖_p ^ θ`, where `θ = α p / n`,

valid for `1 ≤ p < n / α`. Since `(1 - θ) q = p`, the strong-type `(p, p)` maximal inequality
`TauCeti.eLpNorm_maximalFunction_le` turns this pointwise bound into the
Hardy–Littlewood–Sobolev inequality when `p > 1`. The strong-type bound fails at `p = 1`.

## Main declarations

* `TauCeti.setLIntegral_le_setLIntegral_closedBall_of_antitone`: balls maximise the integrals of
  radially nonincreasing kernels among sets of no larger measure.
* `TauCeti.setLIntegral_enorm_sub_rpow_le`: the kernel bound.
* `TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`: the `Lᵖ`-`L^q` bound for the potential on
  a set of finite measure.
* `TauCeti.rieszPotential`: the Riesz potential `I_α f` of order `α` on the whole space.
* `TauCeti.rieszPotential_le_mul_maximalFunction_rpow_mul_eLpNorm_rpow`: Hedberg's inequality.
* `TauCeti.eLpNorm_rieszPotential_le`: the Hardy–Littlewood–Sobolev inequality.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.12.
* L. I. Hedberg, *On certain convolution inequalities*, Proc. Amer. Math. Soc. **36** (1972),
  505–510.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §1.2, Theorem 1.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Theorem 1.2.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

section Rearrangement

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X}

/-- **Balls maximise integrals of radially nonincreasing kernels.** If `f` is antitone and the
measurable set `Ω` has measure at most that of the closed ball `closedBall x R`, which is finite,
then `∫_Ω f (dist x y) dy ≤ ∫_{closedBall x R} f (dist x y) dy`. -/
theorem setLIntegral_le_setLIntegral_closedBall_of_antitone {f : ℝ → ℝ≥0∞} (hf : Antitone f)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (x : X) {R : ℝ} (hR : μ (closedBall x R) ≠ ∞)
    (hΩR : μ Ω ≤ μ (closedBall x R)) :
    ∫⁻ y in Ω, f (dist x y) ∂μ ≤ ∫⁻ y in closedBall x R, f (dist x y) ∂μ := by
  set B := closedBall x R
  have hB : MeasurableSet B := measurableSet_closedBall
  -- Off `B` the kernel is at most `f R`, and on `B` it is at least `f R`.
  have hout : ∫⁻ y in Ω \ B, f (dist x y) ∂μ ≤ f R * μ (Ω \ B) := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset (fun y hy => hy.2)
      (ae_restrict_of_forall_mem hB.compl fun y hy => hf ?_))
    exact (not_le.1 fun h => hy (mem_closedBall'.2 h)).le
  have hin : f R * μ (B \ Ω) ≤ ∫⁻ y in B \ Ω, f (dist x y) ∂μ := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset sdiff_subset
      (ae_restrict_of_forall_mem hB fun y hy => hf (mem_closedBall'.1 hy)))
  -- The part of `Ω` outside `B` is no larger than the part of `B` outside `Ω`.
  have hmeas : μ (Ω \ B) ≤ μ (B \ Ω) := by
    have h₁ := measure_inter_add_sdiff (μ := μ) Ω hB
    have h₂ := measure_inter_add_sdiff (μ := μ) B hΩ
    rw [inter_comm] at h₂
    have hfin : μ (Ω ∩ B) ≠ ∞ := ne_top_of_le_ne_top hR (measure_mono inter_subset_right)
    exact (ENNReal.add_le_add_iff_left hfin).1 (h₁.trans_le (hΩR.trans h₂.ge))
  calc
    ∫⁻ y in Ω, f (dist x y) ∂μ
        = ∫⁻ y in Ω ∩ B, f (dist x y) ∂μ + ∫⁻ y in Ω \ B, f (dist x y) ∂μ :=
      (lintegral_inter_add_sdiff _ Ω hB).symm
    _ ≤ ∫⁻ y in B ∩ Ω, f (dist x y) ∂μ + ∫⁻ y in B \ Ω, f (dist x y) ∂μ := by
      refine add_le_add (le_of_eq (by rw [inter_comm])) ?_
      exact hout.trans ((by gcongr : f R * μ (Ω \ B) ≤ f R * μ (B \ Ω)).trans hin)
    _ = ∫⁻ y in B, f (dist x y) ∂μ := lintegral_inter_add_sdiff _ B hΩ

end Rearrangement

section FiniteMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Set E}

/-- **The kernel bound for Riesz potentials.** For `0 < κ ≤ 1`, a measurable `Ω` and any pole
`x`, `∫_Ω ‖x - y‖ ^ (n (κ - 1)) dy ≤ κ⁻¹ ω ^ (1 - κ) μ(Ω) ^ κ`, where `n` is the dimension and
`ω = μ(B(0, 1))`. Equality holds when `Ω` is a ball about `x`. -/
theorem setLIntegral_enorm_sub_rpow_le {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΩ : MeasurableSet Ω) (x : E) :
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) ∂μ ≤
      ENNReal.ofReal (κ⁻¹ * μ.real (ball 0 1) ^ (1 - κ)) * μ Ω ^ κ := by
  set n := finrank ℝ E
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  set ω := μ.real (ball (0 : E) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  rcases eq_or_ne (μ Ω) ∞ with hΩt | hΩt
  · rw [hΩt, ENNReal.top_rpow_of_pos hκ, ENNReal.mul_top (by positivity)]
    exact le_top
  -- The closed ball about `x` with the same measure as `Ω`.
  set R := (μ.real Ω / ω) ^ (n : ℝ)⁻¹
  have hR : 0 ≤ R := by positivity
  have hRn : R ^ n = μ.real Ω / ω := Real.rpow_inv_natCast_pow (by positivity) finrank_pos.ne'
  have hball : μ (closedBall x R) = μ Ω := by
    rw [Measure.addHaar_closedBall μ x hR, hRn, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hω.ne', ofReal_measureReal hΩt]
  -- The kernel is a nonincreasing function of the distance to the pole.
  have hanti : Antitone fun t : ℝ => ENNReal.ofReal t ^ ((n : ℝ) * (κ - 1)) := by
    intro s t hst
    have hexp : (n : ℝ) * (κ - 1) = -((n : ℝ) * (1 - κ)) := by ring
    dsimp only
    rw [hexp, ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hst)
      (mul_nonneg hn.le (by linarith)))
  have hkernel : ∀ y, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) =
      ENNReal.ofReal (dist x y) ^ ((n : ℝ) * (κ - 1)) := fun y => by
    rw [dist_eq_norm, ofReal_norm]
  calc
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) ∂μ
        ≤ ∫⁻ y in closedBall x R, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) ∂μ := by
      simp_rw [hkernel]
      exact setLIntegral_le_setLIntegral_closedBall_of_antitone hanti hΩ x (hball ▸ hΩt)
        hball.ge
    _ = ENNReal.ofReal (n * ω * (R ^ ((n : ℝ) + n * (κ - 1)) / (n + n * (κ - 1)))) :=
      setLIntegral_closedBall_enorm_sub_rpow (by nlinarith) hR x
    _ = ENNReal.ofReal (κ⁻¹ * ω ^ (1 - κ)) * μ Ω ^ κ := by
      have hpow : R ^ ((n : ℝ) + n * (κ - 1)) = (μ.real Ω / ω) ^ κ := by
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        field_simp
        ring
      have hω' : ω ^ (1 - κ) = ω / ω ^ κ := by rw [Real.rpow_sub hω, Real.rpow_one]
      rw [hpow, Real.div_rpow measureReal_nonneg hω.le, ← ofReal_measureReal hΩt,
        ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg hκ.le,
        ← ENNReal.ofReal_mul (by positivity), hω']
      rw [show (n : ℝ) + n * (κ - 1) = n * κ by ring]
      congr 1
      field_simp

/-- **Riesz potentials on sets of finite measure map `Lᵖ` to `L^q`** (Gilbarg–Trudinger,
Lemma 7.12). Let `1 ≤ p ≤ q < ∞`, let `δ = 1/p - 1/q` and let `δ < κ ≤ 1`. For a measurable
`Ω` and `f` almost everywhere measurable on `Ω`, the potential
`V f (x) = ∫_Ω ‖x - y‖ ^ (n (κ - 1)) f(y) dy` satisfies

`‖V f‖_{L^q(Ω)} ≤ ((1 - δ) / (κ - δ)) ^ (1 - δ) ω ^ (1 - κ) μ(Ω) ^ (κ - δ) ‖f‖_{Lᵖ(Ω)}`,

where `n` is the dimension and `ω = μ(B(0, 1))`. -/
theorem eLpNorm_setLIntegral_enorm_sub_rpow_mul_le {p q : ℝ≥0} {κ δ : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hδ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = δ) (hκ : δ < κ) (hκ1 : κ ≤ 1)
    (hΩ : MeasurableSet Ω) {f : E → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict Ω)) :
    eLpNorm (fun x => ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ) q
        (μ.restrict Ω) ≤
      ENNReal.ofReal (((1 - δ) / (κ - δ)) ^ (1 - δ) * μ.real (ball 0 1) ^ (1 - κ)) *
        μ Ω ^ (κ - δ) * eLpNorm f p (μ.restrict Ω) := by
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hq0 : (0 : ℝ) < q := by linarith
  have hδ1 : δ < 1 := hκ.trans_le hκ1
  -- Young's inequality applies with the exponent `r = 1 / (1 - δ)`, and the `r`-th power of the
  -- kernel is the Riesz kernel of order `n κ'`, `κ' = (κ - δ) / (1 - δ)`.
  set r : ℝ := (1 - δ)⁻¹
  set κ' : ℝ := (κ - δ) / (1 - δ)
  have hκ'0 : 0 < κ' := div_pos (sub_pos.2 hκ) (sub_pos.2 hδ1)
  have hκ'1 : κ' ≤ 1 := (div_le_one (sub_pos.2 hδ1)).2 (by linarith)
  have hr : (p : ℝ)⁻¹ + r⁻¹ = 1 + (q : ℝ)⁻¹ := by rw [inv_inv]; linarith
  set A := ENNReal.ofReal (κ'⁻¹ * ω ^ (1 - κ')) * μ Ω ^ κ'
  have hA : ∀ x, ∫⁻ y in Ω, (‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1))) ^ r ∂μ ≤ A := fun x => by
    have hexp : (n : ℝ) * (κ - 1) * r = n * (κ' - 1) := by
      simp only [r, κ']
      field_simp [(sub_pos.2 hδ1).ne']
      ring
    simp_rw [← ENNReal.rpow_mul, hexp]
    exact setLIntegral_enorm_sub_rpow_le hκ'0 hκ'1 hΩ x
  have hk : Measurable (Function.uncurry fun x y : E => ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1))) := by
    fun_prop
  have hyoung := lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq hk.aemeasurable hf hp' hpq' hr
    (ae_of_all _ hA) (ae_of_all _ fun y => by simpa only [enorm_sub_rev y] using hA y)
  have hV : AEMeasurable
      (fun x => ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) * f y ∂μ) (μ.restrict Ω) :=
    (hk.aemeasurable.mul hf.comp_snd).lintegral_prod_right'
  rw [eLpNorm_nnreal_eq_lintegral (zero_lt_one.trans_le (hp.trans hpq)).ne'
      hV.aestronglyMeasurable,
    eLpNorm_nnreal_eq_lintegral (zero_lt_one.trans_le hp).ne' hf.aestronglyMeasurable]
  simp only [enorm_eq_self]
  calc
    _ ≤ (A ^ ((q : ℝ) * (1 - (p : ℝ)⁻¹)) * A *
          (∫⁻ y in Ω, f y ^ (p : ℝ) ∂μ) ^ ((q : ℝ) / p)) ^ (1 / (q : ℝ)) :=
      ENNReal.rpow_le_rpow hyoung (by positivity)
    _ = A ^ (1 - δ) * (∫⁻ y in Ω, f y ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
      have hb : 0 ≤ (q : ℝ) * (1 - (p : ℝ)⁻¹) :=
        mul_nonneg hq0.le (sub_nonneg.2 (inv_le_one_of_one_le₀ hp'))
      have hA1 : A ^ ((q : ℝ) * (1 - (p : ℝ)⁻¹)) * A = A ^ ((q : ℝ) * (1 - (p : ℝ)⁻¹) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ hb zero_le_one, ENNReal.rpow_one]
      rw [hA1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      congr 2
      · rw [← hδ]
        field_simp
        ring
      · field_simp
    _ = _ := by
      have hexp : κ' * (1 - δ) = κ - δ := by
        simp only [κ']
        field_simp [(sub_pos.2 hδ1).ne']
      have hexp' : (1 - κ') * (1 - δ) = 1 - κ := by
        simp only [κ']
        field_simp [(sub_pos.2 hδ1).ne']
        ring
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, hexp,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hω.le, hexp', inv_div]

end FiniteMeasure

section WholeSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

section Definition

variable [ENorm F]

/-- The **Riesz potential** of order `α` of `f` with respect to `μ`, without normalising constant:
`I_α f (x) = ∫⁻ ‖x - y‖ ^ (α - n) ‖f y‖ dμ(y)`, where `n` is the dimension of `E`.

It is taken in `ℝ≥0∞`, so it is defined for every `f`, taking the value `∞` where the integral
diverges. It is meant for `0 < α < n`, where the kernel `‖·‖ ^ (α - n)` is locally integrable
for a Haar measure. -/
noncomputable def rieszPotential (μ : Measure E) (α : ℝ) (f : E → F) (x : E) : ℝ≥0∞ :=
  ∫⁻ y, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ

variable {μ : Measure E} {α : ℝ} {f : E → F} {x : E}

theorem rieszPotential_def (μ : Measure E) (α : ℝ) (f : E → F) (x : E) :
    rieszPotential μ α f x = ∫⁻ y, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ := (rfl)

/-- If `‖f‖ₑ ≤ ‖g‖ₑ` almost everywhere, then `I_α f ≤ I_α g`. -/
theorem rieszPotential_mono_ae {F' : Type*} [ENorm F'] {g : E → F'}
    (h : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ ‖g y‖ₑ) : rieszPotential μ α f x ≤ rieszPotential μ α g x :=
  lintegral_mono_ae (h.mono fun _ hy => mul_le_mul_right hy _)

/-- Functions whose norms agree almost everywhere have the same Riesz potential. -/
theorem rieszPotential_congr_ae {F' : Type*} [ENorm F'] {g : E → F'}
    (h : ∀ᵐ y ∂μ, ‖f y‖ₑ = ‖g y‖ₑ) : rieszPotential μ α f x = rieszPotential μ α g x :=
  le_antisymm (rieszPotential_mono_ae (h.mono fun _ hy => hy.le))
    (rieszPotential_mono_ae (h.mono fun _ hy => hy.ge))

/-- Replacing a function by its extended norm leaves its Riesz potential unchanged. -/
@[simp]
theorem rieszPotential_enorm (μ : Measure E) (α : ℝ) (f : E → F) :
    rieszPotential μ α (fun y => ‖f y‖ₑ) = rieszPotential μ α f :=
  funext fun _ => rieszPotential_congr_ae (.of_forall fun _ => by simp)

end Definition

variable [BorelSpace E] [TopologicalSpace F] [ContinuousENorm F] {μ : Measure E} {α : ℝ}
  {f : E → F} {x : E}

/-- On the dyadic shell `r ≤ ‖x - y‖ < 2 r` the kernel `‖x - y‖ ^ (α - n)` is at most
`r ^ (α - n)`, and the shell lies in the ball `B(x, 2 r)`. -/
private theorem setLIntegral_shell_le (hα : α ≤ finrank ℝ E) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in ball x (2 * r) \ ball x r, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ ≤
      ENNReal.ofReal (r ^ (α - finrank ℝ E)) * ∫⁻ y in ball x (2 * r), ‖f y‖ₑ ∂μ := by
  calc ∫⁻ y in ball x (2 * r) \ ball x r, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ
      ≤ ∫⁻ y in ball x (2 * r) \ ball x r,
          ENNReal.ofReal (r ^ (α - finrank ℝ E)) * ‖f y‖ₑ ∂μ := by
        refine setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun y hy => ?_
        have hy' : r ≤ ‖x - y‖ := by
          simpa [mem_ball', dist_eq_norm, norm_sub_rev] using hy.2
        gcongr
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos (hr.trans_le hy')]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_nonpos hr hy' (sub_nonpos.2 hα))
    _ = ENNReal.ofReal (r ^ (α - finrank ℝ E)) *
          ∫⁻ y in ball x (2 * r) \ ball x r, ‖f y‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact sdiff_subset

/-- The Riesz potential of a function whose norm is almost everywhere measurable is almost
everywhere measurable. -/
theorem aemeasurable_rieszPotential [FiniteDimensional ℝ E] [SFinite μ]
    (hf : AEMeasurable (fun y => ‖f y‖ₑ) μ) : AEMeasurable (rieszPotential μ α f) μ := by
  have hk : Measurable fun z : E × E => ‖z.1 - z.2‖ₑ ^ (α - finrank ℝ E) := by fun_prop
  rw [show rieszPotential μ α f = fun x => ∫⁻ y, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ from
    funext (rieszPotential_def μ α f)]
  exact (hk.aemeasurable.mul hf.comp_snd).lintegral_prod_right'

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every point other than `x` lies in a dyadic shell `R 2ᵏ ≤ ‖x - y‖ < 2 R 2ᵏ`, `k ∈ ℤ`. -/
private theorem compl_singleton_subset_iUnion_shell {R : ℝ} (hR : 0 < R) :
    {x}ᶜ ⊆ ⋃ k : ℤ, ball x (2 * (R * 2 ^ k)) \ ball x (R * 2 ^ k) := by
  intro y hy
  have hxy : 0 < ‖x - y‖ / R := div_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hy))) hR
  obtain ⟨k, hk₁, hk₂⟩ := exists_mem_Ico_zpow hxy one_lt_two
  refine mem_iUnion.2 ⟨k, ?_, ?_⟩
  · rw [mem_ball', dist_eq_norm]
    rw [zpow_add_one₀ two_ne_zero, div_lt_iff₀ hR] at hk₂
    linarith
  · rw [mem_ball', dist_eq_norm, not_lt]
    rwa [le_div_iff₀ hR, mul_comm] at hk₁

/-- **The dyadic shell decomposition** of the Riesz potential: for every radius `R > 0`,
`I_α f (x)` is at most the sum over `k ∈ ℤ` of `(R 2ᵏ) ^ (α - n)` times the integral of `‖f‖`
over the ball `B(x, 2 R 2ᵏ)`. -/
private theorem rieszPotential_le_tsum [Nontrivial E] [FiniteDimensional ℝ E]
    [μ.IsAddHaarMeasure] (hα : α ≤ finrank ℝ E) {R : ℝ} (hR : 0 < R) :
    rieszPotential μ α f x ≤ ∑' k : ℤ, ENNReal.ofReal ((R * 2 ^ k) ^ (α - finrank ℝ E)) *
      ∫⁻ y in ball x (2 * (R * 2 ^ k)), ‖f y‖ₑ ∂μ := by
  have hnull : ({x}ᶜ : Set E) =ᵐ[μ] univ := by
    simp [ae_eq_univ, measure_singleton]
  calc rieszPotential μ α f x
      = ∫⁻ y in {x}ᶜ, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ := by
        rw [setLIntegral_congr hnull, setLIntegral_univ, rieszPotential_def]
    _ ≤ ∫⁻ y in ⋃ k : ℤ, ball x (2 * (R * 2 ^ k)) \ ball x (R * 2 ^ k),
          ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ :=
        lintegral_mono_set (compl_singleton_subset_iUnion_shell hR)
    _ ≤ ∑' k : ℤ, ∫⁻ y in ball x (2 * (R * 2 ^ k)) \ ball x (R * 2 ^ k),
          ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ :=
        lintegral_iUnion_le _ _
    _ ≤ _ := tsum_le_tsum fun k => setLIntegral_shell_le hα (by positivity)

/-- If every ball integral of `‖f‖` around `x` vanishes, so does `I_α f (x)`. -/
private theorem rieszPotential_eq_zero_of_forall_setLIntegral_ball [Nontrivial E]
    [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] (hα : α ≤ finrank ℝ E)
    (h : ∀ r > 0, ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ = 0) : rieszPotential μ α f x = 0 := by
  refine le_antisymm ((rieszPotential_le_tsum hα one_pos).trans ?_) zero_le
  refine (tsum_eq_zero_iff.2 fun k => ?_).le
  rw [h _ (by positivity), mul_zero]

/-- The shells inside `B(x, R)`: a shell of radius `r` contributes at most a multiple of
`r ^ α M f (x)`. -/
private theorem ofReal_rpow_mul_setLIntegral_ball_le_maximalFunction [Nontrivial E]
    [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ (α - finrank ℝ E)) * ∫⁻ y in ball x (2 * r), ‖f y‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ finrank ℝ E * r ^ α) * μ (ball 0 1) * maximalFunction μ f x := by
  calc ENNReal.ofReal (r ^ (α - finrank ℝ E)) * ∫⁻ y in ball x (2 * r), ‖f y‖ₑ ∂μ
      ≤ ENNReal.ofReal (r ^ (α - finrank ℝ E)) *
          (μ (ball x (2 * r)) * maximalFunction μ f x) := by
        gcongr
        exact setLIntegral_ball_le_measure_mul_maximalFunction (by positivity)
          measure_ball_lt_top.ne
    _ = ENNReal.ofReal (2 ^ finrank ℝ E * r ^ α) * μ (ball 0 1) * maximalFunction μ f x := by
        rw [Measure.addHaar_ball μ x (by positivity), ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub_natCast hr.ne', mul_pow]
        congr 3
        field_simp

/-- The shells outside `B(x, R)`: by Hölder's inequality a shell of radius `r` contributes at most
a multiple of `r ^ (α - n / p) ‖f‖_p`. -/
private theorem ofReal_rpow_mul_setLIntegral_ball_le_eLpNorm [Nontrivial E]
    [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] (hf : AEStronglyMeasurable f μ) {p : ℝ≥0}
    (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ (α - finrank ℝ E)) * ∫⁻ y in ball x (2 * r), ‖f y‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - 1 / p)) * r ^ (α - finrank ℝ E / p)) *
        μ (ball 0 1) ^ (1 - 1 / (p : ℝ)) * eLpNorm f p μ := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans_le hp
  have hs : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one hp₀]
    exact_mod_cast hp
  have hHolder : ∫⁻ y in ball x (2 * r), ‖f y‖ₑ ∂μ ≤
      eLpNorm f p μ * μ (ball x (2 * r)) ^ (1 - 1 / (p : ℝ)) := by
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict (ball x (2 * r)))
      (p := 1) (q := p) (by exact_mod_cast hp) hf.restrict
    rw [eLpNorm_one_eq_lintegral_enorm hf.restrict, Measure.restrict_apply_univ] at this
    simpa using this.trans (mul_le_mul_left (eLpNorm_restrict_le f _ _ _) _)
  calc ENNReal.ofReal (r ^ (α - finrank ℝ E)) * ∫⁻ y in ball x (2 * r), ‖f y‖ₑ ∂μ
      ≤ ENNReal.ofReal (r ^ (α - finrank ℝ E)) *
          (eLpNorm f p μ * μ (ball x (2 * r)) ^ (1 - 1 / (p : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - 1 / p)) * r ^ (α - finrank ℝ E / p)) *
          μ (ball 0 1) ^ (1 - 1 / (p : ℝ)) * eLpNorm f p μ := by
        rw [Measure.addHaar_ball μ x (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hs,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hs]
        have hreal : r ^ (α - finrank ℝ E) * ((2 * r) ^ finrank ℝ E) ^ (1 - 1 / (p : ℝ)) =
            2 ^ ((finrank ℝ E : ℝ) * (1 - 1 / p)) * r ^ (α - finrank ℝ E / p) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
            Real.mul_rpow (by norm_num) hr.le, mul_left_comm, ← Real.rpow_add hr]
          congr 2
          field_simp
          ring
        rw [← hreal, ENNReal.ofReal_mul (by positivity)]
        ring

/-- The constant in front of `R ^ α M f (x)` in Hedberg's splitting: the sum of the shells inside
`B(x, R)`, a geometric series of ratio `2 ^ (-α)`. -/
private noncomputable def hedbergNearConst (μ : Measure E) (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ finrank ℝ E) * μ (ball 0 1) *
    (ENNReal.ofReal (2 ^ α)⁻¹ * (1 - ENNReal.ofReal (2 ^ α)⁻¹)⁻¹)

/-- The constant in front of `R ^ (α - n / p) ‖f‖_p` in Hedberg's splitting: the sum of the shells
outside `B(x, R)`, a geometric series of ratio `2 ^ (α - n / p)`. -/
private noncomputable def hedbergFarConst (μ : Measure E) (α : ℝ) (p : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - 1 / p))) * μ (ball 0 1) ^ (1 - 1 / (p : ℝ)) *
    (1 - ENNReal.ofReal (2 ^ (α - finrank ℝ E / p)))⁻¹

/-- **Hedberg's splitting**: for every radius `R > 0`, the shells inside `B(x, R)` contribute at
most a multiple of `R ^ α M f (x)` and those outside at most a multiple of
`R ^ (α - n / p) ‖f‖_p`. -/
private theorem rieszPotential_le_add [Nontrivial E] [FiniteDimensional ℝ E]
    [μ.IsAddHaarMeasure] (hα : α ≤ finrank ℝ E) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0}
    (hp : 1 ≤ p) {R : ℝ} (hR : 0 < R) :
    rieszPotential μ α f x ≤
      hedbergNearConst μ α * ENNReal.ofReal (R ^ α) * maximalFunction μ f x +
        hedbergFarConst μ α p * ENNReal.ofReal (R ^ (α - finrank ℝ E / p)) * eLpNorm f p μ := by
  set g : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal ((R * 2 ^ k) ^ (α - finrank ℝ E)) *
    ∫⁻ y in ball x (2 * (R * 2 ^ k)), ‖f y‖ₑ ∂μ with hg
  have hpow (k : ℤ) (s : ℝ) : (R * 2 ^ k) ^ s = R ^ s * (2 ^ s) ^ k := by
    rw [Real.mul_rpow hR.le (by positivity), ← Real.rpow_intCast_mul (by norm_num),
      mul_comm (k : ℝ), Real.rpow_mul_intCast (by norm_num)]
  have hnear (n : ℕ) : g (-(n + 1)) ≤
      ENNReal.ofReal (2 ^ finrank ℝ E) * μ (ball 0 1) * ENNReal.ofReal (R ^ α) *
        maximalFunction μ f x * ENNReal.ofReal (2 ^ α)⁻¹ ^ (n + 1) := by
    refine (ofReal_rpow_mul_setLIntegral_ball_le_maximalFunction (by positivity)).trans_eq ?_
    rw [hpow, zpow_neg, ← inv_zpow,
      show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (2 ^ α)⁻¹)]
    ring
  have hfar (n : ℕ) : g n ≤
      ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - 1 / p))) * μ (ball 0 1) ^ (1 - 1 / (p : ℝ)) *
        ENNReal.ofReal (R ^ (α - finrank ℝ E / p)) * eLpNorm f p μ *
          ENNReal.ofReal (2 ^ (α - finrank ℝ E / p)) ^ n := by
    refine (ofReal_rpow_mul_setLIntegral_ball_le_eLpNorm hf hp (by positivity)).trans_eq ?_
    rw [hpow, zpow_natCast, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    ring
  calc rieszPotential μ α f x ≤ ∑' k : ℤ, g k := rieszPotential_le_tsum hα hR
    _ = ∑' n : ℕ, g n + ∑' n : ℕ, g (-(n + 1)) := by
        rw [← tsum_nat_add_neg_add_one CompleteLattice.summable, tsum_add]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - 1 / p))) *
            μ (ball 0 1) ^ (1 - 1 / (p : ℝ)) * ENNReal.ofReal (R ^ (α - finrank ℝ E / p)) *
              eLpNorm f p μ * ENNReal.ofReal (2 ^ (α - finrank ℝ E / p)) ^ n +
          ∑' n : ℕ, ENNReal.ofReal (2 ^ finrank ℝ E) * μ (ball 0 1) * ENNReal.ofReal (R ^ α) *
            maximalFunction μ f x * ENNReal.ofReal (2 ^ α)⁻¹ ^ (n + 1) := by
        gcongr with n n
        exacts [hfar n, hnear n]
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.tsum_geometric_add_one, hedbergNearConst, hedbergFarConst, add_comm]
        ring

omit [BorelSpace E] in
private theorem hedbergNearConst_ne_top [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    (hα : 0 < α) : hedbergNearConst μ α ≠ ∞ := by
  have hρ : ENNReal.ofReal (2 ^ α)⁻¹ < 1 := ENNReal.ofReal_lt_one.2
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hα))
  rw [hedbergNearConst]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hρ).ne'))

omit [BorelSpace E] in
private theorem hedbergNearConst_ne_zero [μ.IsAddHaarMeasure] :
    hedbergNearConst μ α ≠ 0 := by
  rw [hedbergNearConst]
  refine mul_ne_zero (mul_ne_zero (by positivity) (measure_ball_pos μ 0 one_pos).ne')
    (mul_ne_zero (by positivity) (ENNReal.inv_ne_zero.2 ?_))
  exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

omit [BorelSpace E] in
private theorem hedbergFarConst_ne_top [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] {p : ℝ≥0}
    (hp : 1 ≤ p) (hαp : α * p < finrank ℝ E) : hedbergFarConst μ α p ≠ ∞ := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans_le hp
  have hs : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one hp₀]
    exact_mod_cast hp
  have hσ : ENNReal.ofReal (2 ^ (α - finrank ℝ E / p)) < 1 := by
    refine ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two ?_)
    rw [sub_neg, lt_div_iff₀ hp₀]
    exact hαp
  rw [hedbergFarConst]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hs measure_ball_lt_top.ne))
    (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hσ).ne')

/-- The radius balancing the two terms of Hedberg's splitting: for `M, N ∈ (0, ∞)` the radius
`R = (N / M) ^ (p / n)` makes `R ^ α M` and `R ^ (α - n / p) N` both equal to
`M ^ (1 - θ) N ^ θ`, where `θ = α p / n`. -/
private theorem exists_ofReal_rpow_mul_eq {M N : ℝ≥0∞} (hM : M ≠ 0) (hMt : M ≠ ∞) (hN : N ≠ 0)
    (hNt : N ≠ ∞) {α p n : ℝ} (hp : 0 < p) (hn : 0 < n) (hθ₀ : 0 ≤ α * p / n)
    (hθ₁ : α * p / n ≤ 1) : ∃ R > 0,
      ENNReal.ofReal (R ^ α) * M = M ^ (1 - α * p / n) * N ^ (α * p / n) ∧
      ENNReal.ofReal (R ^ (α - n / p)) * N = M ^ (1 - α * p / n) * N ^ (α * p / n) := by
  have ha : 0 < M.toReal := ENNReal.toReal_pos hM hMt
  have hb : 0 < N.toReal := ENNReal.toReal_pos hN hNt
  set θ := α * p / n with hθ
  have hval : ENNReal.ofReal ((N.toReal / M.toReal) ^ θ * M.toReal) = M ^ (1 - θ) * N ^ θ := by
    have : (N.toReal / M.toReal) ^ θ * M.toReal = M.toReal ^ (1 - θ) * N.toReal ^ θ := by
      rw [Real.div_rpow hb.le ha.le, Real.rpow_sub ha, Real.rpow_one]
      field_simp
    rw [this, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ha.le (sub_nonneg.2 hθ₁),
      ← ENNReal.ofReal_rpow_of_nonneg hb.le hθ₀, ENNReal.ofReal_toReal hMt,
      ENNReal.ofReal_toReal hNt]
  refine ⟨(N.toReal / M.toReal) ^ (p / n), by positivity, ?_, ?_⟩
  · rw [← hval, ← ENNReal.ofReal_toReal hMt, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal ha.le, ← Real.rpow_mul (by positivity)]
    congr 3
    rw [hθ]
    ring
  · rw [← hval, ← ENNReal.ofReal_toReal hNt, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal hb.le, ← Real.rpow_mul (by positivity)]
    have hexp : p / n * (α - n / p) = θ - 1 := by
      rw [hθ]
      field_simp
    rw [hexp, Real.rpow_sub_one (by positivity)]
    congr 1
    field_simp

/-- Hedberg's inequality with the explicit constant of the splitting. -/
private theorem rieszPotential_le_hedbergConst [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    (hα : 0 < α) {p : ℝ≥0} (hp : 1 ≤ p) (hαp : α * p < finrank ℝ E) (f : E → F) (x : E) :
    rieszPotential μ α f x ≤ (hedbergNearConst μ α + hedbergFarConst μ α p) *
      maximalFunction μ f x ^ (1 - α * p / finrank ℝ E) *
        eLpNorm f p μ ^ (α * p / finrank ℝ E) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans_le hp
  have hd : (0 : ℝ) < finrank ℝ E := (mul_pos hα hp₀).trans hαp
  have : Nontrivial E := Module.finrank_pos_iff.1 (by exact_mod_cast hd)
  have hαd : α ≤ finrank ℝ E :=
    (le_mul_of_one_le_right hα.le (by exact_mod_cast hp)).trans hαp.le
  set θ := α * p / finrank ℝ E with hθ
  have hθ₀ : 0 < θ := by positivity
  have hθ₁ : 0 < 1 - θ := by rw [sub_pos, hθ, div_lt_one hd]; exact hαp
  have hC : hedbergNearConst μ α + hedbergFarConst μ α p ≠ 0 :=
    (add_pos_of_pos_of_nonneg (pos_iff_ne_zero.2 hedbergNearConst_ne_zero) zero_le).ne'
  set M := maximalFunction μ f x with hM_def
  set N := eLpNorm f p μ with hN_def
  -- If `M f (x) = 0`, every ball integral around `x` vanishes.
  rcases eq_or_ne M 0 with hM | hM
  · rw [rieszPotential_eq_zero_of_forall_setLIntegral_ball hαd fun r hr => le_antisymm
      ((setLIntegral_ball_le_measure_mul_maximalFunction hr measure_ball_lt_top.ne).trans_eq
        (by rw [← hM_def, hM, mul_zero])) zero_le]
    exact zero_le
  have hMθ : M ^ (1 - θ) ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    rintro (⟨h, _⟩ | ⟨_, h⟩) <;> [exact hM h; linarith]
  rcases eq_or_ne N ∞ with hN | hN
  · rw [hN, ENNReal.top_rpow_of_pos hθ₀, ENNReal.mul_top (mul_ne_zero hC hMθ)]
    exact le_top
  have hf : AEStronglyMeasurable f μ := aestronglyMeasurable_of_eLpNorm_ne_top hN
  -- If `‖f‖_p = 0`, then `f = 0` almost everywhere.
  rcases eq_or_ne N 0 with hN₀ | hN₀
  · have hf₀ : ∀ᵐ y ∂μ, ‖f y‖ₑ = ‖(0 : E → ℝ≥0∞) y‖ₑ := by
      filter_upwards [(eLpNorm_eq_zero_iff (f := fun y => ‖f y‖ₑ) (p := p) (by positivity)).1
        (by rw [eLpNorm_enorm _ hf]; exact hN₀)] with y hy
      simpa using hy
    rw [rieszPotential_congr_ae hf₀]
    simp [rieszPotential_def]
  rcases eq_or_ne M ∞ with hMt | hMt
  · rw [hMt, ENNReal.top_rpow_of_pos hθ₁, ENNReal.mul_top hC,
      ENNReal.top_mul (by
        rw [Ne, ENNReal.rpow_eq_zero_iff]
        rintro (⟨h, _⟩ | ⟨_, h⟩) <;> [exact hN₀ h; linarith])]
    exact le_top
  -- The main case: split at the radius balancing the two terms.
  obtain ⟨R, hR₀, hnear, hfar⟩ :=
    exists_ofReal_rpow_mul_eq hM hMt hN₀ hN hp₀ hd hθ₀.le (sub_nonneg.1 hθ₁.le)
  calc rieszPotential μ α f x
      ≤ hedbergNearConst μ α * ENNReal.ofReal (R ^ α) * M +
          hedbergFarConst μ α p * ENNReal.ofReal (R ^ (α - finrank ℝ E / p)) * N :=
        rieszPotential_le_add hαd hf hp hR₀
    _ = (hedbergNearConst μ α + hedbergFarConst μ α p) * M ^ (1 - θ) * N ^ θ := by
        rw [mul_assoc (hedbergNearConst μ α), hnear, mul_assoc (hedbergFarConst μ α p), hfar]
        ring

/-- **Hedberg's inequality**: for `0 < α`, `1 ≤ p` and `α p < n`, the Riesz potential is controlled
pointwise by the Hardy–Littlewood maximal function and the `Lᵖ` norm,

`I_α f (x) ≤ C (M f (x)) ^ (1 - θ) ‖f‖_p ^ θ`, where `θ = α p / n`,

with `C` depending only on `μ`, `α` and `p`. -/
theorem rieszPotential_le_mul_maximalFunction_rpow_mul_eLpNorm_rpow [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hα : 0 < α) {p : ℝ≥0} (hp : 1 ≤ p)
    (hαp : α * p < finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ (f : E → F) (x : E), rieszPotential μ α f x ≤
      C * maximalFunction μ f x ^ (1 - α * p / finrank ℝ E) *
        eLpNorm f p μ ^ (α * p / finrank ℝ E) := by
  refine ⟨(hedbergNearConst μ α + hedbergFarConst μ α p).toNNReal, fun f x => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.2
    ⟨hedbergNearConst_ne_top hα, hedbergFarConst_ne_top hp hαp⟩)]
  exact rieszPotential_le_hedbergConst hα hp hαp f x

omit [BorelSpace E] in
/-- In dimension zero the kernel `‖x - y‖ ^ α` vanishes identically for `α > 0`. -/
private theorem rieszPotential_eq_zero_of_subsingleton [Subsingleton E] (hα : 0 < α) :
    rieszPotential μ α f x = 0 := by
  have hk (y : E) : ‖x - y‖ₑ ^ (α - finrank ℝ E) = 0 := by
    rw [Subsingleton.elim x y, sub_self, enorm_zero, finrank_zero_of_subsingleton, Nat.cast_zero,
      sub_zero, ENNReal.zero_rpow_of_pos hα]
  simp [rieszPotential_def, hk]

/-- The Hardy–Littlewood–Sobolev exponents: if `1 / q = 1 / p - α / n` with `q ≠ 0`, then
`α p < n` and `q (1 - α p / n) = p`. -/
private theorem mul_lt_and_mul_ofReal_one_sub_eq {α n : ℝ} (hn : 0 < n) {p q : ℝ≥0} (hp : 0 < p)
    (hq : q ≠ 0) (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - α / n) :
    α * p < n ∧ (q : ℝ≥0∞) * ENNReal.ofReal (1 - α * p / n) = p := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast pos_iff_ne_zero.2 hq
  refine ⟨?_, ?_⟩
  · have : α / n < (p : ℝ)⁻¹ := by linarith [inv_pos.2 hq₀]
    calc α * p < (p : ℝ)⁻¹ * n * p := by
          gcongr
          rwa [div_lt_iff₀ hn] at this
      _ = n := by field_simp
  · have h₁ : 1 - α * p / n = p * (q : ℝ)⁻¹ := by
      rw [hpq]
      field_simp
    have : (q : ℝ) * (1 - α * p / n) = p := by
      rw [h₁]
      field_simp
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), this,
      ENNReal.ofReal_coe_nnreal]

/-- The Hardy–Littlewood–Sobolev inequality with an explicit constant, for `n > 0`: `K` is the
constant of the strong-type `(p, p)` maximal inequality. -/
private theorem eLpNorm_rieszPotential_le_mul [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    (hα : 0 < α) {p q : ℝ≥0} (hp : 1 < p) (hαp : α * p < finrank ℝ E)
    (hqp : (q : ℝ≥0∞) * ENNReal.ofReal (1 - α * p / finrank ℝ E) = p) (hq : q ≠ 0) {f : E → F}
    (hf : eLpNorm f p μ ≠ ∞) :
    eLpNorm (rieszPotential μ α f) q μ ≤ (hedbergNearConst μ α + hedbergFarConst μ α p) *
      ((ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / ((p : ℝ) - 1)) * 4 ^ finrank ℝ E) ^
        (1 / (p : ℝ))) ^ (1 - α * p / finrank ℝ E) * eLpNorm f p μ := by
  have hd : (0 : ℝ) < finrank ℝ E := (mul_pos hα (by exact_mod_cast zero_lt_one.trans hp)).trans hαp
  set θ := α * p / finrank ℝ E with hθ
  have hθ₀ : 0 < θ := by positivity
  have hθ₁ : 0 < 1 - θ := by rw [sub_pos, hθ, div_lt_one hd]; exact hαp
  set C₀ := hedbergNearConst μ α + hedbergFarConst μ α p with hC₀
  set K : ℝ≥0∞ := (ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / ((p : ℝ) - 1)) *
    4 ^ finrank ℝ E) ^ (1 / (p : ℝ)) with hK
  set N := eLpNorm f p μ with hN
  have hfm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_eLpNorm_ne_top hf
  have hM : AEStronglyMeasurable (maximalFunction μ f) μ :=
    (measurable_maximalFunction μ f).aestronglyMeasurable
  calc eLpNorm (rieszPotential μ α f) q μ
      ≤ eLpNorm (fun x => C₀ * N ^ θ * ‖maximalFunction μ f x‖ₑ ^ (1 - θ)) q μ := by
        refine eLpNorm_mono_enorm (aemeasurable_rieszPotential hfm.enorm).aestronglyMeasurable
          fun x => ?_
        simp only [enorm_eq_self]
        refine (rieszPotential_le_hedbergConst hα hp.le hαp f x).trans_eq ?_
        rw [← hθ, ← hC₀, ← hN]
        ring
    _ = C₀ * N ^ θ * eLpNorm (maximalFunction μ f) p μ ^ (1 - θ) := by
        rw [eLpNorm_const_mul_ennreal_of_pos (by positivity), eLpNorm_enorm_rpow _ hM hθ₁, hqp]
    _ ≤ C₀ * N ^ θ * (K * N) ^ (1 - θ) := by
        gcongr
        exact eLpNorm_maximalFunction_le μ hfm.enorm (by exact_mod_cast hp) ENNReal.coe_ne_top
    _ = C₀ * K ^ (1 - θ) * N := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hθ₁.le, show C₀ * N ^ θ * (K ^ (1 - θ) * N ^ (1 - θ)) =
          C₀ * K ^ (1 - θ) * (N ^ θ * N ^ (1 - θ)) by ring,
          ENNReal.rpow_mul_rpow_one_sub _ hθ₀.le (by linarith)]

/-- **The Hardy–Littlewood–Sobolev inequality**: for `0 < α`, `1 < p` and
`1 / q = 1 / p - α / n`, the Riesz potential is bounded from `Lᵖ` to `L^q`,

`‖I_α f‖_q ≤ C ‖f‖_p`,

with `C` depending only on `μ`, `α` and `p`. -/
theorem eLpNorm_rieszPotential_le [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hα : 0 < α) {p q : ℝ≥0} (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - α / finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ f : E → F, eLpNorm (rieszPotential μ α f) q μ ≤ C * eLpNorm f p μ := by
  -- At `q = 0` the left side vanishes.
  rcases eq_or_ne q 0 with rfl | hq
  · refine ⟨1, fun f => ?_⟩
    rcases eq_or_ne (eLpNorm f p μ) ∞ with hN | hN
    · simp [hN]
    rw [ENNReal.coe_zero, eLpNorm_exponent_zero (aemeasurable_rieszPotential
      (aestronglyMeasurable_of_eLpNorm_ne_top hN).enorm).aestronglyMeasurable]
    exact zero_le
  -- In dimension zero the potential vanishes.
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨0, fun f => ?_⟩
    have : rieszPotential μ α f = 0 := funext fun x => rieszPotential_eq_zero_of_subsingleton hα
    simp [this]
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨hαp, hqp⟩ := mul_lt_and_mul_ofReal_one_sub_eq (by exact_mod_cast Module.finrank_pos)
    (zero_lt_one.trans hp) hq hpq
  have hθ₁ : 0 < 1 - α * p / finrank ℝ E := by
    rw [sub_pos, div_lt_one (by exact_mod_cast Module.finrank_pos)]
    exact hαp
  -- The constant `C₀ K ^ (1 - θ)` is finite and nonzero.
  set K₀ := ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / ((p : ℝ) - 1)) * 4 ^ finrank ℝ E
  have hK₀ : K₀ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hK₀' : 0 < K₀ := by
    have : (0 : ℝ) < p - 1 := by linarith
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' (by simp)
  have hKtop : K₀ ^ (1 / (p : ℝ)) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK₀
  have hK : (K₀ ^ (1 / (p : ℝ))) ^ (1 - α * p / finrank ℝ E) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.rpow_pos hK₀' hK₀) hKtop).ne'
  have hC : (hedbergNearConst μ α + hedbergFarConst μ α p) *
      (K₀ ^ (1 / (p : ℝ))) ^ (1 - α * p / finrank ℝ E) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hedbergNearConst_ne_top hα,
      hedbergFarConst_ne_top hp.le hαp⟩) (ENNReal.rpow_ne_top_of_nonneg hθ₁.le hKtop)
  refine ⟨((hedbergNearConst μ α + hedbergFarConst μ α p) *
    (K₀ ^ (1 / (p : ℝ))) ^ (1 - α * p / finrank ℝ E)).toNNReal, fun f => ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  rcases eq_or_ne (eLpNorm f p μ) ∞ with hN | hN
  · rw [hN, ENNReal.mul_top (mul_ne_zero (add_pos_of_pos_of_nonneg
      (pos_iff_ne_zero.2 hedbergNearConst_ne_zero) zero_le).ne' hK)]
    exact le_top
  exact eLpNorm_rieszPotential_le_mul hα hp hαp hqp hq hN

end WholeSpace

end TauCeti
