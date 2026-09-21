/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Inv
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.InverseGamma
public import TauCeti.Probability.Distributions.Wishart.Congruence

import TauCeti.Analysis.Matrix.PosSemidef
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Integrable
import TauCeti.Probability.Distributions.Gamma.Sqrt
import TauCeti.Probability.Distributions.Wishart.Bartlett
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

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

The mean of the family is `(n - p - 1)⁻¹ • S`, and this is sharp within the valid family: for a
degree `p - 1 < n ≤ p + 1` the sampled matrix is not integrable at all in positive dimension. The
restriction to valid degrees is needed, since for `n ≤ p - 1` the law is the zero measure, against
which everything is integrable. Both statements come from the law of a single diagonal entry at
the standard scale. In the Cholesky coordinates of the source Wishart matrix that entry is the
inverse square of one diagonal coordinate, so it is inverse gamma of shape `(n - p + 1) / 2`,
whose mean exists exactly above the threshold. Congruence by an orthogonal matrix preserves the
standard law, which transports the value to every diagonal entry and makes the off-diagonal means
vanish; congruence by a square root of the scale then carries the standard mean to the general
one.

## Main definitions

* `TauCeti.inverseWishartPDFReal` and `TauCeti.inverseWishartPDF` — the inverse-Wishart density,
  real- and `ℝ≥0∞`-valued.
* `TauCeti.inverseWishartMeasure` — the inverse-Wishart law.

## Main results

* `TauCeti.inverseWishartMeasure_of_posDef` — at a valid degree and scale the law is the density
  against `TauCeti.symmetricLebesgue`, while `TauCeti.inverseWishartMeasure_of_not_posDef` and
  `TauCeti.inverseWishartMeasure_of_le` describe the two invalid branches.
* `TauCeti.isProbabilityMeasure_inverseWishartMeasure` — at those parameters the law has total
  mass one.
* `TauCeti.hasPDF_of_hasLaw_inverseWishartMeasure` and `TauCeti.rnDeriv_inverseWishartMeasure` —
  an inverse-Wishart random matrix has a density against `TauCeti.symmetricLebesgue`, and at
  those parameters the law's Radon–Nikodym derivative is `TauCeti.inverseWishartPDF`.
* `TauCeti.ae_posDef_inverseWishartMeasure` — the sampled matrix is positive definite almost
  everywhere.
* `TauCeti.map_symmetricCongruence_inverseWishartMeasure` — congruence by an invertible matrix
  carries the law of scale `S` to the law of scale `C * S * Cᵀ`.
* `TauCeti.map_coe_apply_inverseWishartMeasure_one` — at the standard scale every diagonal entry
  is inverse gamma of shape `(n - p + 1) / 2` and scale `1 / 2`.
* `TauCeti.integrable_id_inverseWishartMeasure` and
  `TauCeti.integral_id_inverseWishartMeasure` — above the degree `p + 1` the sampled matrix is
  integrable with mean `(n - p - 1)⁻¹ • S`, while
  `TauCeti.not_integrable_id_inverseWishartMeasure` shows that in positive dimension it is not
  integrable at a valid degree `p - 1 < n ≤ p + 1`.
* `TauCeti.inverseWishartMeasure_zero` — in dimension zero the law is the Dirac mass at the unique
  symmetric matrix, hence a probability measure whose mean is zero
  (`TauCeti.integral_id_inverseWishartMeasure_zero`).
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

open scoped ENNReal Matrix MatrixOrder

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

/-- At a valid degree and scale the `ℝ≥0∞`-valued inverse-Wishart density is positive exactly on
the positive-definite cone. -/
theorem inverseWishartPDF_pos_iff (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < inverseWishartPDF n S B ↔ (B : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [inverseWishartPDF_def, ENNReal.ofReal_pos]
  exact inverseWishartPDFReal_pos_iff hS hn

/-- The inverse-Wishart density is finite. -/
@[simp]
theorem inverseWishartPDF_ne_top (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    inverseWishartPDF n S B ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- At a valid degree and scale the `ℝ≥0∞`-valued density carries the real one. -/
theorem toReal_inverseWishartPDF (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (inverseWishartPDF n S B).toReal = inverseWishartPDFReal n S B :=
  ENNReal.toReal_ofReal (inverseWishartPDFReal_nonneg hS hn B)

/-- The real-valued inverse-Wishart density is measurable along any measurable family of degrees,
scale matrices and points. -/
private theorem measurable_inverseWishartPDFReal_comp {γ : Type*} [MeasurableSpace γ]
    {f : γ → ℝ} {T : γ → Matrix (Fin p) (Fin p) ℝ}
    {g : γ → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} (hf : Measurable f)
    (hT : Measurable T) (hg : Measurable g) :
    Measurable fun c => inverseWishartPDFReal (f c) (T c) (g c) := by
  classical
  have hrpow : Measurable fun z : ℝ × ℝ => z.1 ^ z.2 := by fun_prop
  have hg' : Measurable fun c => (g c : Matrix (Fin p) (Fin p) ℝ) :=
    measurable_subtype_coe.comp hg
  have hdetg : Measurable fun c => (g c : Matrix (Fin p) (Fin p) ℝ).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hg'
  have hdetT : Measurable fun c => (T c).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hT
  have hinv : Measurable fun c => (g c : Matrix (Fin p) (Fin p) ℝ)⁻¹ :=
    measurable_matrix_inv.comp hg'
  -- Matrix multiplication has no `MeasurableMul₂` instance here, so read the trace entrywise, as
  -- `TauCeti.measurable_nonsingularWishartPDFReal` does.
  have htrace : Measurable fun c =>
      Matrix.trace (T c * (g c : Matrix (Fin p) (Fin p) ℝ)⁻¹) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
      (hT.eval_matrix (i := i) (j := k)).mul (hinv.eval_matrix (i := k) (j := i))
  simp only [inverseWishartPDFReal]
  refine Measurable.ite (hg (measurableSet_posDefMatrix p)) ?_ measurable_const
  refine Measurable.div (Measurable.mul (Measurable.mul ?_ ?_) ?_) (Measurable.mul ?_ ?_)
  · exact hrpow.comp (hdetT.prodMk (by fun_prop))
  · exact hrpow.comp (hdetg.prodMk (by fun_prop))
  · exact Real.measurable_exp.comp (by fun_prop)
  · exact hrpow.comp (measurable_const.prodMk (by fun_prop))
  · exact (measurable_multivariateGamma p).comp (by fun_prop)

private theorem measurable_inverseWishartPDF_comp {γ : Type*} [MeasurableSpace γ] {f : γ → ℝ}
    {T : γ → Matrix (Fin p) (Fin p) ℝ}
    {g : γ → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} (hf : Measurable f)
    (hT : Measurable T) (hg : Measurable g) :
    Measurable fun c => inverseWishartPDF (f c) (T c) (g c) := by
  simp only [inverseWishartPDF_def]
  exact (measurable_inverseWishartPDFReal_comp hf hT hg).ennreal_ofReal

/-- The real-valued inverse-Wishart density is measurable in the point. -/
@[fun_prop]
theorem measurable_inverseWishartPDFReal (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (inverseWishartPDFReal n S) :=
  measurable_inverseWishartPDFReal_comp measurable_const measurable_const measurable_id

/-- The real-valued inverse-Wishart density is measurable jointly in its degree, its scale matrix
and the point. -/
@[fun_prop]
theorem measurable_uncurry_inverseWishartPDFReal (p : ℕ) :
    Measurable fun q : (ℝ × Matrix (Fin p) (Fin p) ℝ) ×
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      inverseWishartPDFReal q.1.1 q.1.2 q.2 :=
  measurable_inverseWishartPDFReal_comp (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) measurable_snd

/-- The `ℝ≥0∞`-valued inverse-Wishart density is measurable in the point. -/
@[fun_prop]
theorem measurable_inverseWishartPDF (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (inverseWishartPDF n S) :=
  measurable_inverseWishartPDF_comp measurable_const measurable_const measurable_id

/-- The `ℝ≥0∞`-valued inverse-Wishart density is measurable jointly in its degree, its scale
matrix and the point. -/
@[fun_prop]
theorem measurable_uncurry_inverseWishartPDF (p : ℕ) :
    Measurable fun q : (ℝ × Matrix (Fin p) (Fin p) ℝ) ×
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      inverseWishartPDF q.1.1 q.1.2 q.2 :=
  measurable_inverseWishartPDF_comp (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) measurable_snd

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

/-- **The inverse-Wishart law is a probability measure** at exactly the parameters where a density
defines it: a positive-definite scale and a degree above `p - 1`. -/
theorem isProbabilityMeasure_inverseWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    IsProbabilityMeasure (inverseWishartMeasure n S) := by
  have := isProbabilityMeasure_nonsingularWishartMeasure hS.inv hn
  rw [inverseWishartMeasure_def]
  infer_instance

/-! ### The density of an inverse-Wishart random matrix -/

section Density

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- A random symmetric matrix with an inverse-Wishart law has a density against
`TauCeti.symmetricLebesgue`, at every degree and scale: outside the classical parameter range the
law is zero, which trivially has one. -/
theorem hasPDF_of_hasLaw_inverseWishartMeasure (hX : HasLaw X (inverseWishartMeasure n S) P) :
    HasPDF X P (symmetricLebesgue p) := by
  by_cases hS : S.PosDef
  · by_cases hn : (p : ℝ) - 1 < n
    · exact Probability.hasPDF_of_hasLaw_withDensity
        (measurable_inverseWishartPDF n S).aemeasurable
        (by rwa [← inverseWishartMeasure_of_posDef hS hn])
    · refine Probability.hasPDF_of_hasLaw_withDensity (f := 0) aemeasurable_const ?_
      rwa [withDensity_zero, ← inverseWishartMeasure_of_le S (not_lt.1 hn)]
  · refine Probability.hasPDF_of_hasLaw_withDensity (f := 0) aemeasurable_const ?_
    rwa [withDensity_zero, ← inverseWishartMeasure_of_not_posDef n hS]

/-- The density against `TauCeti.symmetricLebesgue` of a random symmetric matrix with an
inverse-Wishart law is `TauCeti.inverseWishartPDF`. -/
theorem pdf_eq_inverseWishartPDF_of_hasLaw_inverseWishartMeasure (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (hX : HasLaw X (inverseWishartMeasure n S) P) :
    pdf X P (symmetricLebesgue p) =ᵐ[symmetricLebesgue p] inverseWishartPDF n S :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_inverseWishartPDF n S).aemeasurable
    (by rwa [← inverseWishartMeasure_of_posDef hS hn])

/-- **The Radon–Nikodym derivative of the inverse-Wishart law** against
`TauCeti.symmetricLebesgue` is the inverse-Wishart density. -/
theorem rnDeriv_inverseWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    (inverseWishartMeasure n S).rnDeriv (symmetricLebesgue p) =ᵐ[symmetricLebesgue p]
      inverseWishartPDF n S := by
  rw [inverseWishartMeasure_of_posDef hS hn]
  exact Measure.rnDeriv_withDensity _ (measurable_inverseWishartPDF n S)

end Density

/-! ### Congruence -/

/-- **Congruence carries the inverse-Wishart law of scale `S` to the one of scale `C * S * Cᵀ`.**
On the Wishart side the same change of scale is the congruence by the inverse transpose of `C`,
and inverting exchanges the two congruences. -/
theorem map_symmetricCongruence_inverseWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    (inverseWishartMeasure n S).map (Matrix.GeneralLinearGroup.symmetricCongruence C) =
      inverseWishartMeasure n
        ((C : Matrix (Fin p) (Fin p) ℝ) * S * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ) := by
  set M : Matrix (Fin p) (Fin p) ℝ := (C : Matrix (Fin p) (Fin p) ℝ)
  have hMdet : IsUnit M.det := isUnit_iff_ne_zero.2 (Matrix.GeneralLinearGroup.det_ne_zero C)
  -- the inverse transpose of `C`, as an invertible matrix
  set D : Matrix.GeneralLinearGroup (Fin p) ℝ :=
    ⟨(M⁻¹)ᵀ, Mᵀ, by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv M hMdet,
        Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul M hMdet, Matrix.transpose_one]⟩
  have hDcoe : (D : Matrix (Fin p) (Fin p) ℝ) = (M⁻¹)ᵀ := rfl
  have hDt : (D : Matrix (Fin p) (Fin p) ℝ)ᵀ = M⁻¹ := by rw [hDcoe, Matrix.transpose_transpose]
  have hcongrC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hcongrD : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence D) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence D).continuous.measurable
  have hfun : (Matrix.GeneralLinearGroup.symmetricCongruence C) ∘ symmetricInv =
      symmetricInv ∘ (Matrix.GeneralLinearGroup.symmetricCongruence D) := by
    funext A
    refine Subtype.ext ?_
    have hMt : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
    simp only [Function.comp_apply, Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply,
      coe_symmetricInv, hDcoe, Matrix.transpose_transpose]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv M hMdet,
      Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hMt, Matrix.mul_assoc]
  have hscale : (D : Matrix (Fin p) (Fin p) ℝ) * S⁻¹ * (D : Matrix (Fin p) (Fin p) ℝ)ᵀ =
      (M * S * Mᵀ)⁻¹ := by
    rw [hDcoe, hDt, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      Matrix.mul_assoc]
  rw [inverseWishartMeasure_def, inverseWishartMeasure_def,
    Measure.map_map hcongrC measurable_symmetricInv, hfun,
    ← Measure.map_map measurable_symmetricInv hcongrD,
    map_symmetricCongruence_nonsingularWishartMeasure n S⁻¹ D, hscale]

/-! ### The law of a diagonal entry at the standard scale -/

/-- The last diagonal entry of the inverse of the Gram matrix `L * Lᵀ` of a lower-triangular `L`
with positive diagonal is the inverse square of the last diagonal entry of `L`: the inverse of a
lower-triangular matrix is again lower triangular, so a single term of the Gram sum survives at
the last index. -/
private theorem inv_coe_lowerTriangleGram_apply_last {q : ℕ} {x : lowerTriangle (q + 1) → ℝ}
    (hx : x ∈ posDiagLowerRegion (q + 1)) :
    ((lowerTriangleGram (q + 1) x : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)⁻¹)
        (Fin.last q) (Fin.last q) = (x ⟨(Fin.last q, Fin.last q), le_rfl⟩ ^ 2)⁻¹ := by
  set L := lowerTriangleMatrix (q + 1) x with hLdef
  have htri : L.IsLowerTriangular := isLowerTriangular_lowerTriangleMatrix x
  have hdiag : ∀ i : Fin (q + 1), L i i = x ⟨(i, i), le_rfl⟩ :=
    fun i => lowerTriangleMatrix_apply_of_le x le_rfl
  have hpos : ∀ i : Fin (q + 1), 0 < L i i := by
    intro i
    rw [hdiag i]
    exact (mem_posDiagLowerRegion _).1 hx i
  have hdet : IsUnit L.det := by
    rw [Matrix.det_of_isLowerTriangular L htri, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (hpos i).ne'
  have hinvtri : L⁻¹.IsLowerTriangular := by
    have : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
    exact Matrix.blockTriangular_inv_of_blockTriangular htri
  have hne : L (Fin.last q) (Fin.last q) ≠ 0 := (hpos _).ne'
  have hinvdiag : L⁻¹ (Fin.last q) (Fin.last q) = (L (Fin.last q) (Fin.last q))⁻¹ := by
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul L hdet) (Fin.last q)) (Fin.last q)
    rw [Matrix.mul_apply_diag_of_isLowerTriangular hinvtri htri, Matrix.one_apply_eq] at h
    field_simp
    exact h
  have hgram : (lowerTriangleGram (q + 1) x : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)⁻¹ =
      L⁻¹ᵀ * L⁻¹ := by
    rw [coe_lowerTriangleGram, ← hLdef, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rw [hgram, Matrix.mul_apply, Finset.sum_eq_single (Fin.last q)]
  · rw [Matrix.transpose_apply, hinvdiag, hdiag]
    ring
  · intro k _ hk
    have hklt : k < Fin.last q := lt_of_le_of_ne (Fin.le_last k) hk
    rw [hinvtri (by simpa using hklt), mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **The last diagonal entry of an inverse-Wishart matrix of standard scale is inverse gamma.**
In Cholesky coordinates this entry is the inverse square of the last diagonal coordinate, whose
chi law with `n - p + 1` degrees of freedom passes to the inverse-gamma law on inverting its
square. -/
private theorem map_coe_apply_last_inverseWishartMeasure_one {q : ℕ} (hn : (q : ℝ) < n) :
    (inverseWishartMeasure n (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)).map
        (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =>
          (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q)) =
      Probability.inverseGammaMeasure ((n - (q : ℝ)) / 2) (1 / 2) := by
  have hn' : ((q + 1 : ℕ) : ℝ) - 1 < n := by push_cast; linarith
  have hk : 0 < n - (q : ℝ) := by linarith
  have : ∀ ij : lowerTriangle (q + 1), IsProbabilityMeasure (bartlettCoordinateMeasure n ij) :=
    fun ij => isProbabilityMeasure_bartlettCoordinateMeasure hn' ij
  have hIW : inverseWishartMeasure n (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =
      (Measure.pi (bartlettCoordinateMeasure (p := q + 1) n)).map
        (symmetricInv ∘ lowerTriangleGram (q + 1)) := by
    rw [inverseWishartMeasure_def, inv_one,
      nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hn',
      Measure.map_map measurable_symmetricInv (measurable_lowerTriangleGram _)]
  rw [hIW, Measure.map_map (selfAdjoint.measurable_coe_apply _ _)
    (measurable_symmetricInv.comp (measurable_lowerTriangleGram _))]
  have hcongr : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =>
        (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q)) ∘
        (symmetricInv ∘ lowerTriangleGram (q + 1)) =ᵐ[Measure.pi
          (bartlettCoordinateMeasure (p := q + 1) n)]
      (fun t : ℝ => (t ^ 2)⁻¹) ∘
        Function.eval (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1)) := by
    have hpos : ∀ᵐ x ∂(Measure.pi (bartlettCoordinateMeasure (p := q + 1) n)),
        x ∈ posDiagLowerRegion (q + 1) :=
      ae_iff.2 (pi_bartlettCoordinateMeasure_compl_posDiagLowerRegion hn')
    filter_upwards [hpos] with x hx
    simpa using inv_coe_lowerTriangleGram_apply_last hx
  have heval : (Measure.pi (bartlettCoordinateMeasure (p := q + 1) n)).map
      (Function.eval (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1))) =
      bartlettCoordinateMeasure n (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1)) :=
    (measurePreserving_eval (μ := bartlettCoordinateMeasure (p := q + 1) n) _).map_eq
  have hcomp := Measure.map_map (μ := Measure.pi (bartlettCoordinateMeasure (p := q + 1) n))
    (g := fun t : ℝ => (t ^ 2)⁻¹)
    (f := Function.eval (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1)))
    (by fun_prop) (measurable_pi_apply _)
  rw [Measure.map_congr hcongr, ← hcomp, heval, bartlettCoordinateMeasure_of_eq n rfl]
  -- squaring and then inverting, so that the chi law passes through the chi-squared law
  have hsq : (fun t : ℝ => (t ^ 2)⁻¹) = Inv.inv ∘ fun t : ℝ => t ^ 2 := rfl
  rw [hsq, ← Measure.map_map measurable_inv (by fun_prop)]
  simp only [Fin.val_last]
  rw [Probability.map_sq_withDensity_eq_chiSquaredMeasure hk,
    Probability.chiSquaredMeasure_eq_gammaMeasure hk,
    Probability.inverseGammaMeasure_of_pos (by linarith) (by norm_num)]

/-! ### The mean -/

/-- Congruence by an orthogonal matrix leaves the inverse-Wishart law of standard scale
unchanged. -/
private theorem map_symmetricCongruence_inverseWishartMeasure_one
    {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1) :
    (inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.GeneralLinearGroup.symmetricCongruence C) =
      inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [map_symmetricCongruence_inverseWishartMeasure, Matrix.mul_one, hC]

/-- Congruence by a swap matrix permutes the two indices of every entry. -/
private theorem coe_symmetricCongruence_swap_apply (i j a b : Fin p)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (Matrix.GeneralLinearGroup.symmetricCongruence (Matrix.GeneralLinearGroup.swap ℝ i j) B :
        Matrix (Fin p) (Fin p) ℝ) a b =
      (B : Matrix (Fin p) (Fin p) ℝ) (Equiv.swap i j a) (Equiv.swap i j b) := by
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply,
    Matrix.GeneralLinearGroup.val_swap, Matrix.transpose_swap, Matrix.swap,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

/-- **Every diagonal entry of an inverse-Wishart matrix of standard scale is inverse gamma**, with
shape `(n - p + 1) / 2` and scale `1 / 2`. Equivalently, the reciprocal of a diagonal entry is
chi-squared with `n - p + 1` degrees of freedom. -/
theorem map_coe_apply_inverseWishartMeasure_one (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    (inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (B : Matrix (Fin p) (Fin p) ℝ) i i) =
      Probability.inverseGammaMeasure ((n - (p : ℝ) + 1) / 2) (1 / 2) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := i.pos; omega⟩
  set C : Matrix.GeneralLinearGroup (Fin (q + 1)) ℝ :=
    Matrix.GeneralLinearGroup.swap ℝ i (Fin.last q) with hC
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hfun : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =>
        (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) i i) =
      (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =>
          (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q)) ∘
        (Matrix.GeneralLinearGroup.symmetricCongruence C) := by
    funext B
    rw [Function.comp_apply, hC, coe_symmetricCongruence_swap_apply, Equiv.swap_apply_right]
  have hcomp := Measure.map_map (μ := inverseWishartMeasure n
      (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ))
    (g := fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =>
      (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q))
    (f := (Matrix.GeneralLinearGroup.symmetricCongruence C))
    (selfAdjoint.measurable_coe_apply _ _) hmeasC
  have horth : (C : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) *
      (C : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)ᵀ = 1 := by
    rw [hC, Matrix.GeneralLinearGroup.val_swap, Matrix.transpose_swap]
    exact Matrix.swap_mul_self i (Fin.last q)
  rw [hfun, ← hcomp, map_symmetricCongruence_inverseWishartMeasure_one horth,
    map_coe_apply_last_inverseWishartMeasure_one (by push_cast at hn; linarith)]
  congr 2
  push_cast
  ring

/-- Congruence by the diagonal sign matrix that flips the index `k` changes the sign of exactly
the entries with one index equal to `k`. -/
private theorem coe_symmetricCongruence_sign_apply {D : Matrix.GeneralLinearGroup (Fin p) ℝ}
    {d : Fin p → ℝ} (hD : (D : Matrix (Fin p) (Fin p) ℝ) = Matrix.diagonal d) (a b : Fin p)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (Matrix.GeneralLinearGroup.symmetricCongruence D B : Matrix (Fin p) (Fin p) ℝ) a b =
      d a * (B : Matrix (Fin p) (Fin p) ℝ) a b * d b := by
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, hD, Matrix.diagonal_transpose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The diagonal sign matrix flipping the index `k` is an involution. -/
private theorem diagonal_sign_mul_self (k : Fin p) :
    (Matrix.diagonal fun j : Fin p => if j = k then (-1 : ℝ) else 1) *
      (Matrix.diagonal fun j : Fin p => if j = k then (-1 : ℝ) else 1) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (by funext j; by_cases h : j = k <;> simp [h])

/-- The diagonal sign matrix flipping the index `k`, as an invertible matrix. -/
private noncomputable def signCongruence (k : Fin p) : Matrix.GeneralLinearGroup (Fin p) ℝ :=
  ⟨Matrix.diagonal fun j => if j = k then -1 else 1,
    Matrix.diagonal fun j => if j = k then -1 else 1,
    diagonal_sign_mul_self k, diagonal_sign_mul_self k⟩

private theorem coe_signCongruence (k : Fin p) :
    (signCongruence k : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.diagonal fun j => if j = k then -1 else 1 := rfl

private theorem signCongruence_mul_transpose (k : Fin p) :
    (signCongruence k : Matrix (Fin p) (Fin p) ℝ) *
      (signCongruence k : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1 := by
  rw [coe_signCongruence, Matrix.diagonal_transpose]
  exact diagonal_sign_mul_self k

/-- An off-diagonal entry of an inverse-Wishart matrix of standard scale has mean zero, by the
sign symmetry of the law: flipping one index is a congruence that preserves the law and reverses
the sign of that entry. -/
private theorem integral_coe_apply_inverseWishartMeasure_one_of_ne {i j : Fin p} (hij : i ≠ j) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (B : Matrix (Fin p) (Fin p) ℝ) i j ∂inverseWishartMeasure n 1 = 0 := by
  have hmeas : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i)) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i)).continuous.measurable
  have h := integral_map (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (φ := Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i))
    (f := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (B : Matrix (Fin p) (Fin p) ℝ) i j)
    hmeas.aemeasurable (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable
  rw [map_symmetricCongruence_inverseWishartMeasure_one (signCongruence_mul_transpose i)] at h
  have hsign : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i) B :
        Matrix (Fin p) (Fin p) ℝ) i j) =
      fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        -((B : Matrix (Fin p) (Fin p) ℝ) i j) := by
    funext B
    rw [coe_symmetricCongruence_sign_apply (coe_signCongruence i)]
    simp [hij.symm]
  rw [hsign, integral_neg] at h
  linarith

/-- Each diagonal entry of an inverse-Wishart matrix of standard scale is integrable above the
degree threshold `p + 1`, its inverse-gamma law then having shape above one. -/
private theorem integrable_coe_apply_diag_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n)
    (i : Fin p) :
    Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (B : Matrix (Fin p) (Fin p) ℝ) i i) (inverseWishartMeasure n 1) := by
  have hmap := map_coe_apply_inverseWishartMeasure_one (by linarith : (p : ℝ) - 1 < n) i
  have hint : Integrable id (Probability.inverseGammaMeasure ((n - (p : ℝ) + 1) / 2) (1 / 2)) :=
    (Probability.integrable_id_inverseGammaMeasure_iff (by linarith) (by norm_num)).2 (by linarith)
  rw [← hmap] at hint
  simpa using (integrable_map_measure aestronglyMeasurable_id
    (selfAdjoint.measurable_coe_apply i i).aemeasurable).1 hint

/-- Every entry of an inverse-Wishart matrix of standard scale is integrable above the degree
threshold `p + 1`: positive semidefiniteness bounds an entry by the mean of the two diagonal
entries in its row and column. -/
private theorem integrable_coe_apply_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n)
    (i j : Fin p) :
    Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (B : Matrix (Fin p) (Fin p) ℝ) i j) (inverseWishartMeasure n 1) := by
  refine Integrable.mono' (((integrable_coe_apply_diag_inverseWishartMeasure_one hn i).add
      (integrable_coe_apply_diag_inverseWishartMeasure_one hn j)).div_const 2)
    (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable ?_
  filter_upwards [ae_posDef_inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)] with B hB
  have hsq : ((B : Matrix (Fin p) (Fin p) ℝ) i j) ^ 2 ≤
      (B : Matrix (Fin p) (Fin p) ℝ) i i * (B : Matrix (Fin p) (Fin p) ℝ) j j := by
    simpa [RCLike.normSq_apply, sq] using hB.posSemidef.normSq_le i j
  have hii : 0 ≤ (B : Matrix (Fin p) (Fin p) ℝ) i i := hB.posSemidef.diag_nonneg
  have hjj : 0 ≤ (B : Matrix (Fin p) (Fin p) ℝ) j j := hB.posSemidef.diag_nonneg
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs ((B : Matrix (Fin p) (Fin p) ℝ) i j),
    abs_nonneg ((B : Matrix (Fin p) (Fin p) ℝ) i j),
    sq_nonneg ((B : Matrix (Fin p) (Fin p) ℝ) i i - (B : Matrix (Fin p) (Fin p) ℝ) j j)]

/-- The entrywise mean of an inverse-Wishart matrix of standard scale: the diagonal entries have
the common value `(n - p - 1)⁻¹` and the off-diagonal entries vanish. -/
private theorem integral_coe_apply_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n) (i j : Fin p) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (B : Matrix (Fin p) (Fin p) ℝ) i j ∂inverseWishartMeasure n 1 =
      (n - (p : ℝ) - 1)⁻¹ * (1 : Matrix (Fin p) (Fin p) ℝ) i j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, mul_one]
    have h := integral_map (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
      (φ := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (B : Matrix (Fin p) (Fin p) ℝ) i i)
      (f := id) (selfAdjoint.measurable_coe_apply i i).aemeasurable aestronglyMeasurable_id
    rw [map_coe_apply_inverseWishartMeasure_one (by linarith : (p : ℝ) - 1 < n) i] at h
    simp only [id_eq] at h
    have hshape : (n - (p : ℝ) + 1) / 2 - 1 = (n - (p : ℝ) - 1) / 2 := by ring
    rw [← h, Probability.integral_id_inverseGammaMeasure (by norm_num) (by linarith), hshape]
    have hne : n - (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  · rw [Matrix.one_apply_ne hij, mul_zero]
    exact integral_coe_apply_inverseWishartMeasure_one_of_ne hij

/-- The mean of an inverse-Wishart matrix of standard scale is `(n - p - 1)⁻¹` times the
identity. -/
private theorem integral_id_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), B ∂inverseWishartMeasure n 1 =
      (n - (p : ℝ) - 1)⁻¹ •
        (⟨1, Matrix.isHermitian_iff_isSelfAdjoint.1 Matrix.isHermitian_one⟩ :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  have hcoords : Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      symmetricCoordinates p B) (inverseWishartMeasure n 1) :=
    (symmetricCoordinates p).toContinuousLinearMap.integrable_comp
      (integrable_iff_integrable_coe_apply.2
        fun i j => integrable_coe_apply_inverseWishartMeasure_one hn i j)
  apply (symmetricCoordinates p).injective
  funext ij
  rw [← (symmetricCoordinates p).integral_comp_comm, eval_integral fun ij => hcoords.eval ij]
  simp only [symmetricCoordinates_apply, Submodule.coe_smul, Matrix.smul_apply]
  rw [integral_coe_apply_inverseWishartMeasure_one hn]
  simp

/-- An inverse-Wishart law of positive-definite scale is the standard one transported by the
congruence with a square root of the scale. -/
private theorem inverseWishartMeasure_eq_map_symmetricCongruence
    {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = S) :
    inverseWishartMeasure n S =
      (inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.GeneralLinearGroup.symmetricCongruence C) := by
  rw [map_symmetricCongruence_inverseWishartMeasure, Matrix.mul_one, hC]

/-- **An inverse-Wishart matrix is integrable above the degree threshold `p + 1`.** -/
theorem integrable_id_inverseWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) + 1 < n) :
    Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => B)
      (inverseWishartMeasure n S) := by
  obtain ⟨C, hC⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hiff := integrable_map_measure
    (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (g := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => B)
    (f := Matrix.GeneralLinearGroup.symmetricCongruence C)
    aestronglyMeasurable_id hmeasC.aemeasurable
  rw [inverseWishartMeasure_eq_map_symmetricCongruence hC, hiff]
  exact (Matrix.GeneralLinearGroup.symmetricCongruence C).toContinuousLinearMap.integrable_comp
    (integrable_iff_integrable_coe_apply.2
      fun i j => integrable_coe_apply_inverseWishartMeasure_one hn i j)

/-- **The mean of an inverse-Wishart law** of degree `n` and positive-definite scale `S` is
`(n - p - 1)⁻¹ • S`, for a degree above the threshold `p + 1`; at a valid degree at or below the
threshold the identity is no longer integrable. -/
theorem integral_id_inverseWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) + 1 < n) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), B ∂inverseWishartMeasure n S =
      (n - (p : ℝ) - 1)⁻¹ •
        (⟨S, Matrix.isHermitian_iff_isSelfAdjoint.1 hS.1⟩ :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  obtain ⟨C, hC⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hint := integral_map (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (φ := Matrix.GeneralLinearGroup.symmetricCongruence C)
    (f := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => B)
    hmeasC.aemeasurable aestronglyMeasurable_id
  rw [inverseWishartMeasure_eq_map_symmetricCongruence hC, hint,
    (Matrix.GeneralLinearGroup.symmetricCongruence C).integral_comp_comm,
    integral_id_inverseWishartMeasure_one hn, map_smul]
  congr 1
  refine Subtype.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply]
  simpa using hC

/-- **Below the degree threshold `p + 1` an inverse-Wishart matrix is not integrable**, in every
positive dimension, as long as the degree is that of a genuine member of the family: a diagonal
entry then has an inverse-gamma law of shape at most one. Below the valid range the law is zero
and the statement fails for want of any mass. -/
theorem not_integrable_id_inverseWishartMeasure (hp : 0 < p) (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (hn' : n ≤ (p : ℝ) + 1) :
    ¬ Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => B)
      (inverseWishartMeasure n S) := by
  intro hint
  obtain ⟨C, hC⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hiff := integrable_map_measure
    (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (g := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => B)
    (f := Matrix.GeneralLinearGroup.symmetricCongruence C)
    aestronglyMeasurable_id hmeasC.aemeasurable
  rw [inverseWishartMeasure_eq_map_symmetricCongruence hC, hiff] at hint
  have hone : Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => B)
      (inverseWishartMeasure n 1) :=
    (((Matrix.GeneralLinearGroup.symmetricCongruence C).symm.toContinuousLinearMap).integrable_comp
      hint).congr (Filter.Eventually.of_forall fun x =>
        (Matrix.GeneralLinearGroup.symmetricCongruence C).symm_apply_apply x)
  have hdiag := integrable_iff_integrable_coe_apply.1 hone ⟨0, hp⟩ ⟨0, hp⟩
  have hgamma : Integrable id
      (Probability.inverseGammaMeasure ((n - (p : ℝ) + 1) / 2) (1 / 2)) := by
    rw [← map_coe_apply_inverseWishartMeasure_one hn ⟨0, hp⟩]
    exact (integrable_map_measure aestronglyMeasurable_id
      (selfAdjoint.measurable_coe_apply (⟨0, hp⟩ : Fin p) ⟨0, hp⟩).aemeasurable).2
      (by simpa using hdiag)
  exact Probability.not_integrable_id_inverseGammaMeasure (by linarith) (by norm_num)
    (by linarith) hgamma

/-! ### Dimension zero -/

/-- In dimension zero every valid inverse-Wishart law is the Dirac mass at the unique symmetric
matrix, the image under inversion of the Dirac Wishart law there. -/
theorem inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n) (S : Matrix (Fin 0) (Fin 0) ℝ) :
    inverseWishartMeasure n S = Measure.dirac 0 := by
  rw [inverseWishartMeasure_def, nonsingularWishartMeasure_zero hn,
    Measure.map_dirac' measurable_symmetricInv, Subsingleton.elim (symmetricInv (0 :
      selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ))) 0]

/-- In dimension zero the symmetric space is a single point and the real-valued inverse-Wishart
density is `1` there. -/
@[simp]
theorem inverseWishartPDFReal_zero (n : ℝ) (S : Matrix (Fin 0) (Fin 0) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    inverseWishartPDFReal n S B = 1 := by
  have hB : (B : Matrix (Fin 0) (Fin 0) ℝ).PosDef :=
    ⟨Subsingleton.elim _ _, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  rw [inverseWishartPDFReal_of_posDef n S hB]
  simp [Matrix.det_isEmpty, Matrix.trace]

/-- In dimension zero the symmetric space is a single point and the inverse-Wishart density is `1`
there. -/
@[simp]
theorem inverseWishartPDF_zero (n : ℝ) (S : Matrix (Fin 0) (Fin 0) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    inverseWishartPDF n S B = 1 := by
  rw [inverseWishartPDF_def, inverseWishartPDFReal_zero, ENNReal.ofReal_one]

/-- In dimension zero every valid inverse-Wishart law is a probability measure. -/
theorem isProbabilityMeasure_inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    IsProbabilityMeasure (inverseWishartMeasure n S) := by
  rw [inverseWishartMeasure_zero hn]
  infer_instance

/-- In dimension zero the identity is integrable against every valid inverse-Wishart law, the
whole mass sitting at a single point. -/
theorem integrable_id_inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    Integrable id (inverseWishartMeasure n S) := by
  rw [inverseWishartMeasure_zero hn]
  exact integrable_dirac (by simp)

/-- In dimension zero every valid inverse-Wishart law has mean zero, the unique symmetric
matrix. -/
theorem integral_id_inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    ∫ B, B ∂inverseWishartMeasure n S = 0 := by
  rw [inverseWishartMeasure_zero hn, integral_dirac]

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
