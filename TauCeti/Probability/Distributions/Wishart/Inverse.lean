/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Inv
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Wishart.Nonsingular

/-!
# The inverse-Wishart family

The inverse-Wishart law `TauCeti.inverseWishartMeasure n S` is the image of the Wishart law of the
inverted scale, `TauCeti.nonsingularWishartMeasure n S⁻¹`, under matrix inversion. Inversion is
totalized to zero on singular matrices, which is harmless: the source law lives on the
positive-definite cone, where inversion is a bijection.

Reading the density off the source law is the change of variables
`TauCeti.map_symmetricInv_symmetricLebesgue`, whose Jacobian weight `(det B) ^ (-(p + 1))` combines
with the Wishart exponent `(n - p - 1) / 2` at the inverted determinant to give the exponent
`-((n + p + 1) / 2)`, while the scale determinant moves from the denominator of the Wishart
constant to the numerator.

Since the source law is zero outside the classical parameter range — a scale that is not positive
definite, or a degree at most `p - 1` — so is the inverse-Wishart law, and positive definiteness of
`S` and of `S⁻¹` are equivalent, so the two families are invalid on exactly the same parameters.

## Main definitions

* `TauCeti.inverseWishartPDFReal` and `TauCeti.inverseWishartPDF` — the inverse-Wishart density,
  real- and `ℝ≥0∞`-valued.
* `TauCeti.inverseWishartMeasure` — the inverse-Wishart law.

## Main results

* `TauCeti.inverseWishartMeasure_of_posDef` — at a valid degree and scale the law is the density
  against `TauCeti.symmetricLebesgue`, while `TauCeti.inverseWishartMeasure_of_not_posDef` and
  `TauCeti.inverseWishartMeasure_of_le` describe the two invalid branches.
* `TauCeti.ae_posDef_inverseWishartMeasure` — the sampled matrix is positive definite almost
  everywhere.
* `TauCeti.inverseWishartMeasure_zero` — in dimension zero the law is the Dirac mass at the unique
  symmetric matrix.
* `TauCeti.measurable_inverseWishartMeasure` — the law is measurable jointly in its real degree and
  every coordinate of its scale matrix, and
  `TauCeti.measurable_inverseWishartMeasure_selfAdjoint` is the form with the scale ranging over
  the symmetric-matrix carrier.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapters 2 and 3.
* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes 53,
  chapter 8.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-! ### The density -/

open Classical in
/-- The **inverse-Wishart density** of degree `n` and scale `S`, as a real-valued function of a
symmetric matrix: on the positive-definite cone it is
`(det S) ^ (n / 2) * (det B) ^ (-((n + p + 1) / 2)) * exp (-trace (S * B⁻¹) / 2)` divided by the
constant `2 ^ (n p / 2) * Γ_p(n / 2)`, and it vanishes off the cone. -/
def inverseWishartPDFReal (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ :=
  if (B : Matrix (Fin p) (Fin p) ℝ).PosDef then
    S.det ^ (n / 2) * (B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((n + (p : ℝ) + 1) / 2)) *
        Real.exp (-Matrix.trace (S * (B : Matrix (Fin p) (Fin p) ℝ)⁻¹) / 2) /
      ((2 : ℝ) ^ (n * (p : ℝ) / 2) * multivariateGamma p (n / 2))
  else 0

open Classical in
/-- The defining branch expression of the real-valued inverse-Wishart density. -/
theorem inverseWishartPDFReal_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    inverseWishartPDFReal n S B =
      if (B : Matrix (Fin p) (Fin p) ℝ).PosDef then
        S.det ^ (n / 2) * (B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((n + (p : ℝ) + 1) / 2)) *
            Real.exp (-Matrix.trace (S * (B : Matrix (Fin p) (Fin p) ℝ)⁻¹) / 2) /
          ((2 : ℝ) ^ (n * (p : ℝ) / 2) * multivariateGamma p (n / 2))
      else 0 :=
  (rfl)

/-- On the positive-definite cone the inverse-Wishart density is its defining formula. -/
@[simp]
theorem inverseWishartPDFReal_of_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hB : (B : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseWishartPDFReal n S B =
      S.det ^ (n / 2) * (B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((n + (p : ℝ) + 1) / 2)) *
          Real.exp (-Matrix.trace (S * (B : Matrix (Fin p) (Fin p) ℝ)⁻¹) / 2) /
        ((2 : ℝ) ^ (n * (p : ℝ) / 2) * multivariateGamma p (n / 2)) := by
  classical
  rw [inverseWishartPDFReal, ite_eq_left hB]

/-- Off the positive-definite cone the inverse-Wishart density vanishes. -/
@[simp]
theorem inverseWishartPDFReal_of_not_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hB : ¬ (B : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseWishartPDFReal n S B = 0 := by
  classical
  rw [inverseWishartPDFReal, ite_eq_right hB]

/-- At a valid degree and scale the inverse-Wishart density is nonnegative. -/
theorem inverseWishartPDFReal_nonneg (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    0 ≤ inverseWishartPDFReal n S B := by
  by_cases hB : (B : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [inverseWishartPDFReal_of_posDef n S hB]
    refine div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hS.det_pos.le _)
      (Real.rpow_nonneg hB.det_pos.le _)) (Real.exp_nonneg _)) ?_
    exact mul_nonneg (Real.rpow_pos_of_pos two_pos _).le
      (multivariateGamma_pos (by linarith)).le
  · simp [hB]

/-- At a valid degree and scale the inverse-Wishart density is positive exactly on the
positive-definite cone. -/
theorem inverseWishartPDFReal_pos_iff (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < inverseWishartPDFReal n S B ↔ (B : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  refine ⟨fun h => ?_, fun hB => ?_⟩
  · by_contra hB
    simp [hB] at h
  · rw [inverseWishartPDFReal_of_posDef n S hB]
    refine div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hS.det_pos _)
      (Real.rpow_pos_of_pos hB.det_pos _)) (Real.exp_pos _)) ?_
    exact mul_pos (Real.rpow_pos_of_pos two_pos _) (multivariateGamma_pos (by linarith))

/-- The `ℝ≥0∞`-valued inverse-Wishart density, the one that defines the measure. -/
def inverseWishartPDF (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (inverseWishartPDFReal n S B)

/-- The `ℝ≥0∞`-valued inverse-Wishart density is `ENNReal.ofReal` of the real-valued one. -/
theorem inverseWishartPDF_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    inverseWishartPDF n S B = ENNReal.ofReal (inverseWishartPDFReal n S B) :=
  (rfl)

/-- On the positive-definite cone the `ℝ≥0∞`-valued inverse-Wishart density is its defining
formula. -/
@[simp]
theorem inverseWishartPDF_of_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hB : (B : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseWishartPDF n S B =
      ENNReal.ofReal (S.det ^ (n / 2) *
          (B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((n + (p : ℝ) + 1) / 2)) *
            Real.exp (-Matrix.trace (S * (B : Matrix (Fin p) (Fin p) ℝ)⁻¹) / 2) /
          ((2 : ℝ) ^ (n * (p : ℝ) / 2) * multivariateGamma p (n / 2))) := by
  rw [inverseWishartPDF_def, inverseWishartPDFReal_of_posDef n S hB]

/-- Off the positive-definite cone the `ℝ≥0∞`-valued inverse-Wishart density vanishes. -/
@[simp]
theorem inverseWishartPDF_of_not_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hB : ¬ (B : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseWishartPDF n S B = 0 := by
  simp [inverseWishartPDF_def, hB]

/-- The inverse-Wishart density is finite. -/
@[simp]
theorem inverseWishartPDF_ne_top (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    inverseWishartPDF n S B ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The real-valued inverse-Wishart density is measurable in the point. -/
@[fun_prop]
theorem measurable_inverseWishartPDFReal (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (inverseWishartPDFReal n S) := by
  have hrpow : Measurable fun z : ℝ × ℝ => z.1 ^ z.2 := by fun_prop
  have hcoe : Measurable fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (B : Matrix (Fin p) (Fin p) ℝ) := measurable_subtype_coe
  have hdet : Measurable fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (B : Matrix (Fin p) (Fin p) ℝ).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hcoe
  have hinv : Measurable fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (B : Matrix (Fin p) (Fin p) ℝ)⁻¹ := measurable_matrix_inv.comp hcoe
  -- Matrix multiplication has no `MeasurableMul₂` instance here, so read the trace entrywise, as
  -- `TauCeti.measurable_nonsingularWishartPDFReal` does.
  have htrace : Measurable fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      Matrix.trace (S * (B : Matrix (Fin p) (Fin p) ℝ)⁻¹) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
      (measurable_const.mul (hinv.eval_matrix (i := k) (j := i)))
  -- The equation lemma characterizes the fully applied density, so eta-expand before branching.
  rw [funext (inverseWishartPDFReal_def n S)]
  refine Measurable.ite (measurableSet_posDefMatrix p) ?_ measurable_const
  refine Measurable.div (Measurable.mul (Measurable.mul measurable_const ?_) ?_) measurable_const
  · exact hrpow.comp (hdet.prodMk measurable_const)
  · exact Real.measurable_exp.comp (htrace.neg.div_const 2)

/-- The `ℝ≥0∞`-valued inverse-Wishart density is measurable in the point. -/
@[fun_prop]
theorem measurable_inverseWishartPDF (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (inverseWishartPDF n S) :=
  (measurable_inverseWishartPDFReal n S).ennreal_ofReal

/-! ### The measure -/

/-- The **inverse-Wishart law** of real degree `n` and positive-definite scale `S`: the image of
the Wishart law of the inverted scale under matrix inversion. Mathlib's totalized inverse, which
is zero on singular matrices, is kept; the source law is carried by the positive-definite cone, on
which inversion is a bijection. Outside the classical parameter range the source law, and hence
this one, is zero. -/
def inverseWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (nonsingularWishartMeasure n S⁻¹).map symmetricInv

/-- The defining expression of the inverse-Wishart law. -/
theorem inverseWishartMeasure_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    inverseWishartMeasure n S = (nonsingularWishartMeasure n S⁻¹).map symmetricInv :=
  (rfl)

/-- At a scale that is not positive definite the inverse-Wishart law is zero: the inverted scale
is then not positive definite either, so the source Wishart law already vanishes. -/
@[simp]
theorem inverseWishartMeasure_of_not_posDef (n : ℝ) (hS : ¬ S.PosDef) :
    inverseWishartMeasure n S = 0 := by
  rw [inverseWishartMeasure_def,
    nonsingularWishartMeasure_of_not_posDef n (by rwa [Matrix.posDef_inv_iff]), Measure.map_zero]

/-- At a degree at most `p - 1` the inverse-Wishart law is zero, as the source Wishart law is. -/
@[simp]
theorem inverseWishartMeasure_of_le (S : Matrix (Fin p) (Fin p) ℝ) (hn : n ≤ (p : ℝ) - 1) :
    inverseWishartMeasure n S = 0 := by
  rw [inverseWishartMeasure_def, nonsingularWishartMeasure_of_le S⁻¹ hn, Measure.map_zero]

/-- The inverse-Wishart law gives no mass to the complement of the positive-definite cone. -/
@[simp]
theorem inverseWishartMeasure_compl_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    inverseWishartMeasure n S
        {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (B : Matrix (Fin p) (Fin p) ℝ).PosDef}ᶜ = 0 := by
  rw [inverseWishartMeasure_def,
    Measure.map_apply measurable_symmetricInv (measurableSet_posDefMatrix p).compl]
  refine measure_mono_null (fun A hA => ?_) (nonsingularWishartMeasure_compl_posDef n S⁻¹)
  -- Inversion maps the cone into itself, so a preimage point off the cone is itself off it.
  exact fun hAcone => hA (by simpa [coe_symmetricInv] using hAcone.inv)

/-- A matrix sampled from the inverse-Wishart law is almost surely positive definite. -/
theorem ae_posDef_inverseWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂inverseWishartMeasure n S,
      (B : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [ae_iff]
  exact inverseWishartMeasure_compl_posDef n S

/-! ### The density theorem -/

/-- The exponent bookkeeping behind the inverse-Wishart density. Multiplying by the Jacobian
`d ^ (-(q + 1))` of inversion turns the exponent `-((n + q + 1) / 2)` at the inverted determinant
`d⁻¹` into `(n - q - 1) / 2` at `d`, while the scale determinant `s` moves from the denominator of
the Wishart constant to the numerator. -/
private theorem rpow_neg_mul_rpow_inv_neg {d s E K G : ℝ} (hd : 0 < d) (hs : 0 < s) (hK : 0 < K)
    (hG : 0 < G) (n q : ℝ) :
    d ^ (-(q + 1)) * (s ^ (n / 2) * d⁻¹ ^ (-((n + q + 1) / 2)) * E / (K * G)) =
      d ^ ((n - q - 1) / 2) * E / (K * s⁻¹ ^ (n / 2) * G) := by
  have hsn : (0 : ℝ) < s ^ (n / 2) := Real.rpow_pos_of_pos hs _
  rw [Real.inv_rpow hd.le, ← Real.rpow_neg hd.le, neg_neg, Real.inv_rpow hs.le,
    show d ^ (-(q + 1)) * (s ^ (n / 2) * d ^ ((n + q + 1) / 2) * E / (K * G)) =
      d ^ (-(q + 1)) * d ^ ((n + q + 1) / 2) * (s ^ (n / 2) * E) / (K * G) by ring,
    ← Real.rpow_add hd, show -(q + 1) + (n + q + 1) / 2 = (n - q - 1) / 2 by ring]
  field_simp

/-- **The pointwise density identity behind the inverse-Wishart law.** At a positive-definite `A`,
the Jacobian weight of inversion times the inverse-Wishart density at `A⁻¹` is the Wishart density
of the inverted scale at `A`. -/
private theorem det_rpow_mul_inverseWishartPDFReal_symmetricInv (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    (A : Matrix (Fin p) (Fin p) ℝ).det ^ (-((p : ℝ) + 1)) *
        inverseWishartPDFReal n S (symmetricInv A) =
      nonsingularWishartPDFReal n S⁻¹ A := by
  have hAinv : ((symmetricInv A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ).PosDef := by
    rw [coe_symmetricInv]
    exact hA.inv
  rw [inverseWishartPDFReal_of_posDef n S hAinv, nonsingularWishartPDFReal_of_posDef n S⁻¹ hA,
    coe_symmetricInv, Matrix.nonsing_inv_nonsing_inv (A : Matrix (Fin p) (Fin p) ℝ)
      hA.det_pos.ne'.isUnit, Matrix.nonsing_inv_nonsing_inv S hS.det_pos.ne'.isUnit,
    Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact rpow_neg_mul_rpow_inv_neg hA.det_pos hS.det_pos (Real.rpow_pos_of_pos two_pos _)
    (multivariateGamma_pos (p := p) (a := n / 2) (by linarith)) n p

/-- **The inverse-Wishart density.** In the classical parameter range the inverse-Wishart law is
its density against `TauCeti.symmetricLebesgue`. -/
theorem inverseWishartMeasure_of_posDef (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    inverseWishartMeasure n S =
      (symmetricLebesgue p).withDensity (inverseWishartPDF n S) := by
  set C : Set (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    {A | (A : Matrix (Fin p) (Fin p) ℝ).PosDef}
  have hC : MeasurableSet C := measurableSet_posDefMatrix p
  set w : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ≥0∞ :=
    fun B => ENNReal.ofReal ((B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((p : ℝ) + 1))) with hw_def
  have hw : Measurable w := by
    have hrpow : Measurable fun z : ℝ × ℝ => z.1 ^ z.2 := by fun_prop
    have hdet : Measurable fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (B : Matrix (Fin p) (Fin p) ℝ).det :=
      (Continuous.matrix_det continuous_id).measurable.comp measurable_subtype_coe
    exact (hrpow.comp (hdet.prodMk measurable_const)).ennreal_ofReal
  -- A density supported on the cone may equally be taken against the restricted measure.
  have hrestrict : ∀ f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ≥0∞,
      (∀ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ¬ (A : Matrix (Fin p) (Fin p) ℝ).PosDef → f A = 0) →
      (symmetricLebesgue p).withDensity f =
        ((symmetricLebesgue p).restrict C).withDensity f := by
    intro f hf
    have hsupp : Function.support f ⊆ C := by
      intro A hA
      by_contra h
      exact hA (hf A h)
    rw [← withDensity_indicator hC, Set.indicator_eq_self.2 hsupp]
  -- Inversion is an involution of the cone, so it carries the weighted restriction back.
  have hmap : ((((symmetricLebesgue p).restrict C).withDensity w).map symmetricInv) =
      (symmetricLebesgue p).restrict C := by
    rw [← map_symmetricInv_symmetricLebesgue p,
      Measure.map_map measurable_symmetricInv measurable_symmetricInv]
    refine (Measure.map_congr ?_).trans (Measure.map_id)
    filter_upwards [ae_restrict_mem hC] with A hA
    exact symmetricInv_symmetricInv (Matrix.PosDef.det_pos hA).ne'
  have hfactor : ∀ᵐ A ∂((symmetricLebesgue p).restrict C),
      w A * inverseWishartPDF n S (symmetricInv A) = nonsingularWishartPDF n S⁻¹ A := by
    filter_upwards [ae_restrict_mem hC] with A hA
    have hA' : (A : Matrix (Fin p) (Fin p) ℝ).PosDef := hA
    rw [hw_def, inverseWishartPDF_def, nonsingularWishartPDF_def,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA'.det_pos.le _),
      det_rpow_mul_inverseWishartPDFReal_symmetricInv hS hn hA']
  calc inverseWishartMeasure n S
      = ((symmetricLebesgue p).withDensity (nonsingularWishartPDF n S⁻¹)).map symmetricInv := by
        rw [inverseWishartMeasure_def, nonsingularWishartMeasure_of_posDef hS.inv hn]
    _ = (((symmetricLebesgue p).restrict C).withDensity
          (nonsingularWishartPDF n S⁻¹)).map symmetricInv := by
        rw [hrestrict _ fun A hA => nonsingularWishartPDF_of_not_posDef n S⁻¹ hA]
    _ = ((symmetricLebesgue p).restrict C).withDensity (inverseWishartPDF n S) :=
        Measure.map_withDensity_eq_withDensity measurable_symmetricInv hw
          (measurable_inverseWishartPDF n S) hmap hfactor
    _ = (symmetricLebesgue p).withDensity (inverseWishartPDF n S) :=
        (hrestrict _ fun A hA => inverseWishartPDF_of_not_posDef n S hA).symm

/-! ### Dimension zero -/

/-- In dimension zero every valid inverse-Wishart law is the Dirac mass at the unique symmetric
matrix, the image under inversion of the Dirac Wishart law there. -/
theorem inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n) (S : Matrix (Fin 0) (Fin 0) ℝ) :
    inverseWishartMeasure n S = Measure.dirac 0 := by
  rw [inverseWishartMeasure_def, nonsingularWishartMeasure_zero hn,
    Measure.map_dirac' measurable_symmetricInv, Subsingleton.elim (symmetricInv (0 :
      selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ))) 0]

/-! ### Parameter measurability -/

/-- **Parameter measurability of the inverse-Wishart law.** The law is measurable jointly in its
real degree and every coordinate of its scale matrix, which is what an inverse-Wishart kernel with
a random degree and scale needs. -/
@[fun_prop]
theorem measurable_inverseWishartMeasure :
    Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      inverseWishartMeasure q.1 (Matrix.of q.2) := by
  have hcoords : Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      (q.1, (Matrix.ofMeasurableEquiv (Fin p) (Fin p) ℝ).symm ((Matrix.of q.2)⁻¹)) :=
    measurable_fst.prodMk
      ((Matrix.ofMeasurableEquiv (Fin p) (Fin p) ℝ).symm.measurable.comp
        (measurable_matrix_inv.comp ((Matrix.measurable_of (Fin p) (Fin p) ℝ).comp measurable_snd)))
  have hsource : Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      nonsingularWishartMeasure q.1 (Matrix.of q.2)⁻¹ := by
    simpa [Function.comp_def] using measurable_nonsingularWishartMeasure.comp hcoords
  simp only [inverseWishartMeasure_def]
  exact (Measure.measurable_map _ measurable_symmetricInv).comp hsource

/-- The inverse-Wishart law is measurable jointly in its real degree and a scale ranging over the
symmetric-matrix carrier. This is the form used to build a kernel with a random symmetric scale. -/
@[fun_prop]
theorem measurable_inverseWishartMeasure_selfAdjoint :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      inverseWishartMeasure q.1 (q.2 : Matrix (Fin p) (Fin p) ℝ) :=
  measurable_inverseWishartMeasure.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

end TauCeti
