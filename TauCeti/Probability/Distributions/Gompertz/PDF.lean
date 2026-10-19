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

/-- The Gompertz density vanishes on the nonpositive half-line. -/
@[simp]
theorem gompertzPDFReal_of_nonpos (hx : x ≤ 0) (η b : ℝ) :
    gompertzPDFReal η b x = 0 := by
  rw [gompertzPDFReal, ite_eq_right fun h => hx.not_gt h.2.2]

/-- The Gompertz density vanishes at invalid parameters. -/
@[simp]
theorem gompertzPDFReal_of_not_pos (h : ¬ (0 < η ∧ 0 < b)) (x : ℝ) :
    gompertzPDFReal η b x = 0 := by
  rw [gompertzPDFReal, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]

/-- At positive parameters the Gompertz density is strictly positive on its open support. -/
theorem gompertzPDFReal_pos (hη : 0 < η) (hb : 0 < b) (hx : 0 < x) :
    0 < gompertzPDFReal η b x := by
  rw [gompertzPDFReal_of_pos hη hb hx]
  positivity

/-- The Gompertz density is nonnegative everywhere. -/
theorem gompertzPDFReal_nonneg (η b x : ℝ) : 0 ≤ gompertzPDFReal η b x := by
  by_cases h : 0 < η ∧ 0 < b
  · by_cases hx : 0 < x
    · exact (gompertzPDFReal_pos h.1 h.2 hx).le
    · rw [gompertzPDFReal_of_nonpos (le_of_not_gt hx)]
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
  exact ⟨fun h => lt_of_not_ge fun hx => h.ne' (gompertzPDFReal_of_nonpos hx η b),
    gompertzPDFReal_pos hη hb⟩

private lemma gompertzTransform_image (hη : 0 < η) (hb : 0 < b) :
    (fun e : ℝ => log (1 + e / η) / b) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact log_one_add_div_div_pos hη hb he
  · intro hx
    refine ⟨η * (exp (b * x) - 1), mul_pos hη (sub_pos.mpr ?_), ?_⟩
    · exact one_lt_exp_iff.mpr (mul_pos hb hx)
    · simp only [mul_div_cancel_left₀ _ hη.ne', add_sub_cancel, log_exp,
        mul_div_cancel_left₀ _ hb.ne']

private lemma injOn_gompertzTransform (hη : 0 < η) (hb : 0 < b) :
    InjOn (fun e : ℝ => log (1 + e / η) / b) (Ioi 0) := by
  intro e he f hf hef
  have hp (y : ℝ) (hy : 0 < y) : 0 < 1 + y / η := by positivity
  have hh := (log_injOn_pos (hp e he) (hp f hf)) ((div_left_inj' hb.ne').mp hef)
  exact (div_left_inj' hη.ne').mp (by linarith)

private lemma hasDerivAt_gompertzTransform (hη : 0 < η) (b : ℝ) {e : ℝ} (he : 0 < e) :
    HasDerivAt (fun y : ℝ => log (1 + y / η) / b) ((η + e)⁻¹ / b) e := by
  have hp : 0 < 1 + e / η := by positivity
  have hd : (1 / η) / (1 + e / η) / b = (η + e)⁻¹ / b := by
    field_simp
  simpa only [id_eq, hd] using
    ((((hasDerivAt_id e).div_const η).const_add 1).log hp.ne').div_const b

private lemma gompertzPDF_mul_abs_deriv (hη : 0 < η) (hb : 0 < b) {e : ℝ} (he : 0 < e) :
    ENNReal.ofReal |(η + e)⁻¹ / b| * gompertzPDF η b (log (1 + e / η) / b) =
      exponentialPDF 1 e := by
  have hp : 0 < 1 + e / η := by positivity
  have hd : 0 < (η + e)⁻¹ / b := div_pos (inv_pos.mpr (add_pos hη he)) hb
  simp only [gompertzPDF, gompertzPDFReal_of_pos hη hb (log_one_add_div_div_pos hη hb he),
    mul_div_cancel₀ _ hb.ne', exp_log hp, abs_of_pos hd,
    ← ENNReal.ofReal_mul hd.le, exponentialPDF_of_nonneg he.le, one_mul]
  have hexp : -η * (1 + e / η - 1) = -e := by field_simp; ring
  simp only [hexp]
  congr 1
  field_simp [(add_pos hη he).ne']

/-- The Gompertz law is Lebesgue measure weighted by its named density, at all parameters. -/
theorem gompertzMeasure_eq_withDensity (η b : ℝ) :
    gompertzMeasure η b = volume.withDensity (gompertzPDF η b) := by
  by_cases h : 0 < η ∧ 0 < b
  · obtain ⟨hη, hb⟩ := h
    have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
      (s := Ioi (0 : ℝ)) (φ := fun e : ℝ => log (1 + e / η) / b)
      (φ' := fun e => (η + e)⁻¹ / b) (f := gompertzPDF η b)
      measurableSet_Ioi (by fun_prop)
      (fun e he => (hasDerivAt_gompertzTransform hη b he).hasDerivWithinAt)
      (injOn_gompertzTransform hη hb)
    have hw : (fun e : ℝ => ENNReal.ofReal |(η + e)⁻¹ / b| *
        gompertzPDF η b (log (1 + e / η) / b)) =ᵐ[volume.restrict (Ioi 0)]
        exponentialPDF 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
      exact gompertzPDF_mul_abs_deriv hη hb he
    rw [withDensity_congr_ae hw, gompertzTransform_image hη hb] at hmap
    rw [gompertzMeasure_of_pos hη hb, expMeasure_eq_withDensity_restrict_Ioi, hmap,
      ← withDensity_indicator measurableSet_Ioi]
    congr 1
    exact indicator_eq_self.mpr (support_gompertzPDF hη hb).le
  · have hz : gompertzPDF η b = 0 := funext fun x => by
      simp [gompertzPDF, gompertzPDFReal_of_not_pos h]
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
