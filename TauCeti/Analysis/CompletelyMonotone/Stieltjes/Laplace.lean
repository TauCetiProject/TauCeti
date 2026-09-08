/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Basic
public import TauCeti.Analysis.CompletelyMonotone.Bernstein.OpenHalfLine
-- Non-public: Tonelli swaps the two exponential integrations.
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Stieltjes functions are the Laplace transforms of completely monotone functions

The Stieltjes kernel factors through a second exponential integration,

`(t + x)⁻¹ = ∫₀^∞ e^{-s(t + x)} ds = ∫₀^∞ e^{-ts} e^{-sx} ds`,

so integrating it against a measure `ν` on `ℝ≥0` and swapping the two integrations turns the
Stieltjes transform of `ν` into the Laplace transform of the Laplace transform of `ν`.  Since the
Laplace transforms of measures on `ℝ≥0` are exactly the functions completely monotone on `(0, ∞)`
(`TauCeti.hausdorff_bernstein_widder_onIoi`), this identifies the Stieltjes functions:

**a function is a Stieltjes function if and only if it is a nonnegative constant plus the Laplace
transform of a function completely monotone on `(0, ∞)`.**

The additive constant is genuinely needed and cannot be absorbed: it is the coefficient `b` of the
Stieltjes representation, whose "representing measure" is a point mass of the outer variable at
`0`, which no density supplies.  The singular coefficient `a` of the Stieltjes formula, by
contrast, *is* absorbed: it is the constant part of the completely monotone integrand, since
`a / t = ∫₀^∞ e^{-ts} a ds`.

This is the converse half of the Stieltjes theory begun in
`TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompletelyMonotone` (a Stieltjes function is
completely monotone) and `TauCeti.Analysis.CompletelyMonotone.Stieltjes.Bernstein` (the product
with the parameter extends to a Bernstein function): those two run only from a Stieltjes
representation outwards, whereas the equivalence below also *produces* one.

## Main declarations

* `TauCeti.RepresentsLaplaceOnIoi.lintegral_ofReal_exp_neg_mul_mul`: the analytic core, the
  Tonelli identity `∫₀^∞ e^{-ts} g s ds = ∫ (t + x)⁻¹ ∂ν` in extended-real form, where `ν`
  represents `g` by its Laplace transform on `(0, ∞)`.
* `TauCeti.RepresentsLaplaceOnIoi.integrable_inv_add_of_integrableOn` and
  `TauCeti.RepresentsLaplaceOnIoi.integrableOn_exp_neg_mul_mul`: convergence of the outer Laplace
  integral and integrability of the Stieltjes kernel imply one another.
* `TauCeti.RepresentsLaplaceOnIoi.integral_exp_neg_mul_mul`: the Bochner form of the core
  identity.
* `TauCeti.isStieltjesFunction_const_add_integral_exp_neg_mul`: a constant plus the Laplace
  transform of a completely monotone function is a Stieltjes function.
* `TauCeti.RepresentsStieltjes.exists_isCompletelyMonotoneOnIoi`: conversely, a Stieltjes
  representation exhibits its function in that form.
* `TauCeti.isStieltjesFunction_iff_exists_isCompletelyMonotoneOnIoi`: the resulting
  characterization.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Theorem 2.2 and Remark 2.3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {ν : Measure ℝ≥0} {f g : ℝ → ℝ}

/-! ## The exponential kernel against a Stieltjes weight -/

/-- The exponential kernel is integrable against every measure carrying an integrable Stieltjes
weight: `e^{-tx} ≤ (1 + tx)⁻¹ ≤ (min 1 t)⁻¹ (1 + x)⁻¹`.  Together with
`TauCeti.integrable_inv_add` this says that a Stieltjes representing measure is also a Laplace
representing measure. -/
theorem integrable_exp_neg_mul_of_integrable_stieltjesWeight
    (hν : Integrable stieltjesWeight ν) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ)))) ν := by
  refine (hν.const_mul (min 1 t)⁻¹).mono' (by fun_prop) (.of_forall fun x => ?_)
  have hx : (0 : ℝ) ≤ (x : ℝ) := x.coe_nonneg
  have hm : (0 : ℝ) < min 1 t := lt_min one_pos ht
  have h1x : (0 : ℝ) < 1 + (x : ℝ) := by positivity
  have hkey : min 1 t * (1 + (x : ℝ)) ≤ Real.exp (t * (x : ℝ)) := by
    have h1 : min 1 t ≤ 1 := min_le_left 1 t
    have h2 : min 1 t * (x : ℝ) ≤ t * (x : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_right 1 t) hx
    have h3 : t * (x : ℝ) + 1 ≤ Real.exp (t * (x : ℝ)) := Real.add_one_le_exp _
    nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), stieltjesWeight_apply, ← mul_inv,
    Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hkey

/-! ## The inner exponential integral -/

/-- **The Stieltjes kernel is an iterated exponential integral.**  Swapping the two integrations
turns the outer Laplace integral of the inner one into the Stieltjes integral of `ν`. -/
private theorem lintegral_ofReal_exp_neg_mul_mul_lintegral (ν : Measure ℝ≥0) [SFinite ν] {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s))) *
        ∫⁻ x : ℝ≥0, ENNReal.ofReal (Real.exp (-(s * (x : ℝ)))) ∂ν
      = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
  have hmeas : AEMeasurable (Function.uncurry fun (s : ℝ) (x : ℝ≥0) =>
      ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s))))
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    refine Measurable.aemeasurable ?_
    simp only [Function.uncurry_def]
    fun_prop
  calc
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s))) *
          ∫⁻ x : ℝ≥0, ENNReal.ofReal (Real.exp (-(s * (x : ℝ)))) ∂ν
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x : ℝ≥0,
            ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s))) ∂ν := by
          refine lintegral_congr fun s => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
    _ = ∫⁻ x : ℝ≥0, (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s)))) ∂ν := lintegral_lintegral_swap hmeas
    _ = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
          refine lintegral_congr fun x => ?_
          exact lintegral_ofReal_exp_neg_mul_Ioi_zero
            (add_pos_of_pos_of_nonneg ht x.coe_nonneg)

/-! ## The two transforms of a Laplace representing measure -/

namespace RepresentsLaplaceOnIoi

/-- **The Stieltjes transform is the iterated Laplace transform**, in extended-real form: if `ν`
represents `g` by its Laplace transform on `(0, ∞)`, then the outer Laplace integral of `g`
is the Stieltjes integral of `ν`.  Both sides may be infinite. -/
theorem lintegral_ofReal_exp_neg_mul_mul (h : RepresentsLaplaceOnIoi ν g) {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s)) * g s)
      = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
  have := h.sigmaFinite
  rw [← lintegral_ofReal_exp_neg_mul_mul_lintegral ν ht]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := mem_Ioi.mp hs
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, h.eq_laplaceTransform hs', laplaceTransform_apply,
    ofReal_integral_eq_lintegral_ofReal (h.integrable hs')
      (.of_forall fun p => (Real.exp_pos _).le)]

/-- The outer Laplace integrand of a represented function is almost everywhere nonnegative on
`(0, ∞)`, so its Bochner and extended-real integrals agree. -/
private theorem nonneg_ae (h : RepresentsLaplaceOnIoi ν g) {t : ℝ} :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s : ℝ => Real.exp (-(t * s)) * g s :=
  (ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun _ hs =>
    mul_nonneg (Real.exp_pos _).le (h.isCompletelyMonotoneOnIoi.nonneg hs))

/-- Convergence of the outer Laplace integral forces the Stieltjes kernel to be integrable
against the representing measure. -/
theorem integrable_inv_add_of_integrableOn (h : RepresentsLaplaceOnIoi ν g) {t : ℝ} (ht : 0 < t)
    (hint : IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * g s) (Ioi 0)) :
    Integrable (fun x : ℝ≥0 => (t + (x : ℝ))⁻¹) ν := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x =>
    inv_nonneg.mpr (add_nonneg ht.le x.coe_nonneg)), ← h.lintegral_ofReal_exp_neg_mul_mul ht]
  exact (hasFiniteIntegral_iff_ofReal h.nonneg_ae).1 hint.2

/-- Integrability of the Stieltjes kernel against the representing measure makes the outer
Laplace integral converge. -/
theorem integrableOn_exp_neg_mul_mul (h : RepresentsLaplaceOnIoi ν g) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun x : ℝ≥0 => (t + (x : ℝ))⁻¹) ν) :
    IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * g s) (Ioi 0) := by
  refine ⟨(Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
    (h.isCompletelyMonotoneOnIoi.contDiffOn.continuousOn.aestronglyMeasurable
      measurableSet_Ioi), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal h.nonneg_ae, h.lintegral_ofReal_exp_neg_mul_mul ht]
  exact (hasFiniteIntegral_iff_ofReal (.of_forall fun x =>
    inv_nonneg.mpr (add_nonneg ht.le x.coe_nonneg))).1 hint.2

/-- **The Stieltjes transform is the iterated Laplace transform.**  Bochner form of
`TauCeti.RepresentsLaplaceOnIoi.lintegral_ofReal_exp_neg_mul_mul`. -/
theorem integral_exp_neg_mul_mul (h : RepresentsLaplaceOnIoi ν g) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun x : ℝ≥0 => (t + (x : ℝ))⁻¹) ν) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * g s = ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂ν := by
  have hnnr : 0 ≤ᵐ[ν] fun x : ℝ≥0 => (t + (x : ℝ))⁻¹ :=
    .of_forall fun x => inv_nonneg.mpr (add_nonneg ht.le x.coe_nonneg)
  refine (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae h.nonneg_ae)
    (integral_nonneg_of_ae hnnr)).1 ?_
  rw [ofReal_integral_eq_lintegral_ofReal (h.integrableOn_exp_neg_mul_mul ht hint) h.nonneg_ae,
    ofReal_integral_eq_lintegral_ofReal hint hnnr, h.lintegral_ofReal_exp_neg_mul_mul ht]

end RepresentsLaplaceOnIoi

/-! ## Stieltjes functions from completely monotone integrands -/

/-- **A constant plus the Laplace transform of a completely monotone function is a Stieltjes
function.**  The singular coefficient of the resulting Stieltjes representation is the mass that
the representing measure of `g` puts at the origin. -/
theorem isStieltjesFunction_const_add_integral_exp_neg_mul (b : ℝ≥0)
    (hg : IsCompletelyMonotoneOnIoi g)
    (hint : ∀ t : ℝ, 0 < t → IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * g s) (Ioi 0)) :
    IsStieltjesFunction fun t => (b : ℝ) + ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * g s := by
  obtain ⟨ν, hν⟩ := exists_representsLaplaceOnIoi_of_isCompletelyMonotoneOnIoi hg
  have hker : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ≥0 => (t + (x : ℝ))⁻¹) ν := fun t ht =>
    hν.integrable_inv_add_of_integrableOn ht (hint t ht)
  have hw : Integrable stieltjesWeight ν := by
    refine (hker 1 one_pos).congr (.of_forall fun x => ?_)
    simp
  -- Split off the atom at the origin: it is exactly the singular coefficient.
  have hzero : ν {0} ≠ ∞ := by
    refine ne_top_of_le_ne_top ((hker 1 one_pos).measure_ge_lt_top one_pos).ne ?_
    refine measure_mono fun x hx => ?_
    rw [mem_singleton_iff] at hx
    simp [hx]
  set a : ℝ≥0 := (ν {0}).toNNReal with ha
  refine isStieltjesFunction_iff.mpr ⟨a, b, ν.restrict {(0 : ℝ≥0)}ᶜ,
    representsStieltjes_iff.mpr ⟨?_, ?_, fun t ht => ?_⟩⟩
  · rw [Measure.restrict_apply (measurableSet_singleton _)]
    simp
  · exact hw.restrict
  -- Rewrite the Stieltjes integral of `ν` as its atomic and non-atomic parts.
  · have hsplit : ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂ν
        = (a : ℝ) / t + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂ν.restrict {(0 : ℝ≥0)}ᶜ := by
      conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := ν)
        (measurableSet_singleton (0 : ℝ≥0))]
      rw [integral_add_measure ((hker t ht).restrict) ((hker t ht).restrict),
        Measure.restrict_singleton, integral_smul_measure, integral_dirac]
      congr 1
      rw [ha, smul_eq_mul, div_eq_mul_inv]
      simp [ENNReal.toReal]
    rw [hν.integral_exp_neg_mul_mul ht (hker t ht), hsplit]
    ring

/-! ## Stieltjes representations as iterated Laplace transforms -/

variable {μ : Measure ℝ≥0} {a b : ℝ≥0}

/-- **A Stieltjes representation exhibits its function as a constant plus the Laplace transform
of a completely monotone function.**  The completely monotone integrand is the singular
coefficient plus the Laplace transform of the representing measure. -/
theorem RepresentsStieltjes.exists_isCompletelyMonotoneOnIoi (h : RepresentsStieltjes μ a b f) :
    ∃ g : ℝ → ℝ, IsCompletelyMonotoneOnIoi g ∧
      (∀ t : ℝ, 0 < t → IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * g s) (Ioi 0)) ∧
      ∀ t : ℝ, 0 < t → f t = (b : ℝ) + ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * g s := by
  have hexp : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ)))) μ :=
    fun _ ht => integrable_exp_neg_mul_of_integrable_stieltjesWeight h.integrable_weight ht
  have hμ : RepresentsLaplaceOnIoi μ (laplaceTransform μ) :=
    representsLaplaceOnIoi_iff.mpr ⟨hexp, fun _ _ => rfl⟩
  have hLint : ∀ t : ℝ, 0 < t →
      IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * laplaceTransform μ s) (Ioi 0) :=
    fun t ht => hμ.integrableOn_exp_neg_mul_mul ht (integrable_inv_add h.integrable_weight ht)
  have hconst : ∀ t : ℝ, 0 < t →
      IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * (a : ℝ)) (Ioi 0) := by
    intro t ht
    have hexpOn : IntegrableOn (fun s : ℝ => Real.exp (-(t * s))) (Ioi 0) := by
      simpa [neg_mul] using exp_neg_integrableOn_Ioi (0 : ℝ) ht
    exact hexpOn.mul_const _
  refine ⟨fun s => (a : ℝ) + laplaceTransform μ s, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact ((isCompletelyMonotone_const a.coe_nonneg).isCompletelyMonotoneOnIoi.add
      (hμ.isCompletelyMonotoneOnIoi)).congr fun _ _ => rfl
  · exact ((hconst t ht).add (hLint t ht)).congr (.of_forall fun s => by simp [mul_add])
  · rw [h.eq_div_add_add_integral_inv_add ht,
      ← hμ.integral_exp_neg_mul_mul ht (integrable_inv_add h.integrable_weight ht)]
    have hsplit : ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * ((a : ℝ) + laplaceTransform μ s)
        = (∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * (a : ℝ)) +
          ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * laplaceTransform μ s := by
      simpa only [mul_add] using integral_add (hconst t ht) (hLint t ht)
    rw [hsplit, integral_mul_const,
      integral_exp_neg_mul_Ioi_zero ht]
    rw [div_eq_inv_mul]
    ring

/-! ## The characterization -/

/-- **Stieltjes functions are exactly the Laplace transforms of completely monotone functions**,
up to an additive nonnegative constant.  The constant `b` cannot be absorbed into the integrand:
its representing data in the outer variable is a point mass at `0`, which no density supplies.

Compare `TauCeti.IsStieltjesFunction.isCompletelyMonotoneOnIoi`, which says that a Stieltjes
function is itself completely monotone -- a strictly weaker conclusion, since a completely
monotone function need not be Stieltjes. -/
theorem isStieltjesFunction_iff_exists_isCompletelyMonotoneOnIoi :
    IsStieltjesFunction f ↔
      ∃ (b : ℝ≥0) (g : ℝ → ℝ), IsCompletelyMonotoneOnIoi g ∧
        (∀ t : ℝ, 0 < t → IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * g s) (Ioi 0)) ∧
        ∀ t : ℝ, 0 < t → f t = (b : ℝ) + ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * g s := by
  constructor
  · intro hf
    obtain ⟨a, b, μ, hμ⟩ := isStieltjesFunction_iff.mp hf
    obtain ⟨g, hg, hint, hfg⟩ := hμ.exists_isCompletelyMonotoneOnIoi
    exact ⟨b, g, hg, hint, hfg⟩
  · rintro ⟨b, g, hg, hint, hf⟩
    exact (isStieltjesFunction_const_add_integral_exp_neg_mul b hg hint).congr fun t ht => hf t ht

end TauCeti
