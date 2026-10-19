/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gompertz.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Density

/-!
# Gompertz densities and support

The Gompertz density is `η * b * exp (b * x) * exp (-η * (exp (b * x) - 1))` on
the positive half-line. We derive its measure identity from the exponential pushforward,
following the change-of-variables pattern of `Gumbel/PDF.lean`. Its topological support is
`[0, ∞)`, although its variables are almost surely strictly positive.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {η b x : ℝ}

/-- The real Gompertz density, zero outside positive parameters and positive arguments. -/
def gompertzPDFReal (η b x : ℝ) : ℝ :=
  if 0 < η ∧ 0 < b ∧ 0 < x then
    η * b * exp (b * x) * exp (-η * (exp (b * x) - 1)) else 0

/-- The extended nonnegative Gompertz density. -/
def gompertzPDF (η b x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gompertzPDFReal η b x)

/-- The extended Gompertz density is the coercion of its real counterpart. -/
theorem gompertzPDF_eq_ofReal (η b x : ℝ) :
    gompertzPDF η b x = ENNReal.ofReal (gompertzPDFReal η b x) := (rfl)

/-- On its open support, the Gompertz density has its exponential formula. -/
@[simp]
theorem gompertzPDFReal_of_pos (hη : 0 < η) (hb : 0 < b) (hx : 0 < x) :
    gompertzPDFReal η b x = η * b * exp (b * x) * exp (-η * (exp (b * x) - 1)) := by
  rw [gompertzPDFReal, ite_eq_left ⟨hη, hb, hx⟩]

/-- The Gompertz density vanishes outside its parameter and support domain. -/
@[simp]
theorem gompertzPDFReal_of_not_pos (h : ¬ (0 < η ∧ 0 < b ∧ 0 < x)) :
    gompertzPDFReal η b x = 0 := by
  rw [gompertzPDFReal, ite_eq_right h]

/-- The Gompertz density is nonnegative everywhere. -/
theorem gompertzPDFReal_nonneg (η b x : ℝ) : 0 ≤ gompertzPDFReal η b x := by
  by_cases h : 0 < η ∧ 0 < b ∧ 0 < x
  · rcases h with ⟨hη, hb, hx⟩
    rw [gompertzPDFReal_of_pos hη hb hx]
    positivity
  · rw [gompertzPDFReal_of_not_pos h]

/-- Converting the extended density to a real number recovers the real density. -/
@[simp]
theorem toReal_gompertzPDF (η b x : ℝ) : (gompertzPDF η b x).toReal = gompertzPDFReal η b x :=
  ENNReal.toReal_ofReal (gompertzPDFReal_nonneg η b x)

/-- The real Gompertz density is jointly measurable in parameters and argument. -/
@[fun_prop]
theorem measurable_uncurry_gompertzPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ => gompertzPDFReal p.1.1 p.1.2 p.2 := by
  unfold gompertzPDFReal
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst.fst).inter
      ((measurableSet_lt measurable_const measurable_fst.snd).inter
        (measurableSet_lt measurable_const measurable_snd))) (by fun_prop) measurable_const

/-- The extended Gompertz density is jointly measurable in parameters and argument. -/
@[fun_prop]
theorem measurable_uncurry_gompertzPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ => gompertzPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_gompertzPDFReal.ennreal_ofReal

/-- The real Gompertz density is measurable in its argument. -/
@[fun_prop]
theorem measurable_gompertzPDFReal (η b : ℝ) : Measurable (gompertzPDFReal η b) :=
  measurable_uncurry_gompertzPDFReal.comp (measurable_prodMk_left (x := (η, b)))

/-- The extended Gompertz density is measurable in its argument. -/
@[fun_prop]
theorem measurable_gompertzPDF (η b : ℝ) : Measurable (gompertzPDF η b) :=
  (measurable_gompertzPDFReal η b).ennreal_ofReal

/-- The density is positive exactly on the positive half-line at valid parameters. -/
@[simp]
theorem support_gompertzPDF (hη : 0 < η) (hb : 0 < b) :
    Function.support (gompertzPDF η b) = Ioi 0 := by
  ext x
  rw [Function.mem_support, gompertzPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le, mem_Ioi]
  constructor
  · contrapose!
    intro hx
    rw [gompertzPDFReal_of_not_pos (by grind)]
  · intro hx
    rw [gompertzPDFReal_of_pos hη hb hx]
    positivity

private lemma gompertzTransform_image (hη : 0 < η) (hb : 0 < b) :
    (fun e : ℝ => log (1 + e / η) / b) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact div_pos (log_pos (by linarith [div_pos he hη])) hb
  · intro hx
    refine ⟨η * (exp (b * x) - 1), mul_pos hη (sub_pos.mpr ?_), ?_⟩
    · exact one_lt_exp_iff.mpr (mul_pos hb hx)
    · simp only [mul_div_cancel_left₀ _ hη.ne', add_sub_cancel, log_exp,
        mul_div_cancel_left₀ _ hb.ne']

/-- The Gompertz law is Lebesgue measure weighted by its named density, at all parameters. -/
theorem gompertzMeasure_eq_withDensity (η b : ℝ) :
    gompertzMeasure η b = volume.withDensity (gompertzPDF η b) := by
  by_cases h : 0 < η ∧ 0 < b
  · have hη := h.1
    have hb := h.2
    have hp (e : ℝ) (he : 0 < e) : 0 < 1 + e / η := by positivity
    have hinj : InjOn (fun e : ℝ => log (1 + e / η) / b) (Ioi 0) := by
      intro e he f hf hef
      have hh := (log_injOn_pos (hp e he) (hp f hf)) ((div_left_inj' h.2.ne').mp hef)
      exact (div_left_inj' h.1.ne').mp (by linarith)
    have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
      (s := Ioi (0 : ℝ)) (φ := fun e : ℝ => log (1 + e / η) / b)
      (φ' := fun e => (η + e)⁻¹ / b) (f := gompertzPDF η b)
      measurableSet_Ioi (by fun_prop) (fun e he => ?_) hinj
    · have hw : (fun e : ℝ => ENNReal.ofReal |(η + e)⁻¹ / b| *
          gompertzPDF η b (log (1 + e / η) / b)) =ᵐ[volume.restrict (Ioi 0)]
          exponentialPDF 1 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
        have hlog : 0 < log (1 + e / η) / b :=
          div_pos (log_pos (by linarith [div_pos he h.1])) h.2
        rw [gompertzPDF, gompertzPDFReal_of_pos h.1 h.2 hlog,
          mul_div_cancel₀ _ h.2.ne', exp_log (hp e he),
          abs_of_pos (div_pos (inv_pos.mpr (add_pos h.1 he)) h.2),
          ← ENNReal.ofReal_mul (div_nonneg (inv_nonneg.mpr (add_pos hη he).le) hb.le),
          exponentialPDF_of_nonneg he.le, one_mul]
        have hexp : -η * (1 + e / η - 1) = -e := by field_simp; ring
        rw [hexp]
        congr 1
        field_simp [(add_pos hη he).ne']
      rw [withDensity_congr_ae hw, gompertzTransform_image h.1 h.2] at hmap
      rw [gompertzMeasure_of_pos h.1 h.2, expMeasure_eq_withDensity_restrict_Ioi, hmap,
        ← withDensity_indicator measurableSet_Ioi]
      congr 1
      exact indicator_eq_self.mpr (support_gompertzPDF h.1 h.2).le
    · convert ((((hasDerivAt_id e).div_const η).const_add 1).log
        (hp e he).ne').div_const b |>.hasDerivWithinAt using 1
      · rfl
      · simp only [id_eq]
        field_simp
  · have hz : gompertzPDF η b = 0 := funext fun x => by
      rw [gompertzPDF, gompertzPDFReal_of_not_pos (by grind), ENNReal.ofReal_zero, Pi.zero_apply]
    rw [gompertzMeasure_of_not_pos h, hz, withDensity_zero]

/-- The topological support is the closed nonnegative half-line. -/
@[simp]
theorem support_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    (gompertzMeasure η b).support = Ici 0 := by
  rw [gompertzMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_gompertzPDF η b) isOpen_Ioi
      (support_gompertzPDF hη hb), closure_Ioi]

/-- Every Gompertz law is atomless. -/
instance nullSingletonClass_gompertzMeasure (η b : ℝ) :
    NullSingletonClass (gompertzMeasure η b) := by
  rw [gompertzMeasure_eq_withDensity]
  infer_instance

/-- A random variable with Gompertz law has a density. -/
theorem hasPDF_of_hasLaw_gompertzMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gompertzMeasure η b) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_gompertzPDF η b).aemeasurable
    (by rwa [gompertzMeasure_eq_withDensity] at hX)

/-- The canonical density of a Gompertz random variable equals its named density almost
everywhere. -/
theorem pdf_eq_gompertzPDF_of_hasLaw_gompertzMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gompertzMeasure η b) P) :
    pdf X P volume =ᵐ[volume] gompertzPDF η b :=
  pdf_eq_of_hasLaw_withDensity (measurable_gompertzPDF η b).aemeasurable
    (by rwa [gompertzMeasure_eq_withDensity] at hX)

/-- The Gompertz Radon–Nikodym derivative is its named density. -/
theorem rnDeriv_gompertzMeasure (η b : ℝ) :
    (gompertzMeasure η b).rnDeriv volume =ᵐ[volume] gompertzPDF η b := by
  rw [gompertzMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_gompertzPDF η b)

end TauCeti.Probability
