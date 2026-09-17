/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix

/-!
# The nonsingular Wishart family

The nonsingular Wishart law `TauCeti.nonsingularWishartMeasure n S` is the law on the
symmetric-matrix subspace whose density against `TauCeti.symmetricLebesgue` is
`(det A) ^ ((n - p - 1) / 2) * exp (-trace (S⁻¹ * A) / 2)`, normalized by
`2 ^ (n p / 2) * (det S) ^ (n / 2) * Γ_p(n / 2)` and supported on the positive-definite cone.
Its degree `n` is a real parameter, restricted to `p - 1 < n`, which in positive dimension is the
range where the density is integrable; its scale `S` is positive definite, since a singular
positive-semidefinite scale concentrates the law on a proper subspace, where it has no density at
all. Outside those two parameter conditions the definition sets the measure to zero.

The normalization is the one attached to `TauCeti.symmetricLebesgue`, whose coordinate unit cube
has measure one; no other Haar normalization of the symmetric matrices produces the classical
Wishart constants.

Dimension zero needs no separate definition: the symmetric space is then a single point,
`TauCeti.symmetricLebesgue 0` is a Dirac mass, and the empty determinants, trace and normalizing
constant leave the density equal to `1`, so for `-1 < n` the law is that Dirac mass.

## Main definitions

* `TauCeti.nonsingularWishartPDFReal` and `TauCeti.nonsingularWishartPDF` — the Wishart density,
  real- and `ℝ≥0∞`-valued.
* `TauCeti.nonsingularWishartMeasure` — the nonsingular Wishart law.

## Main results

* `TauCeti.nonsingularWishartPDFReal_pos_iff` — at a valid degree and scale the density is
  positive exactly on the positive-definite cone.
* `TauCeti.nonsingularWishartMeasure_of_posDef` — at a valid degree and scale the law is the
  density against `TauCeti.symmetricLebesgue`, while
  `TauCeti.nonsingularWishartMeasure_of_not_posDef` and
  `TauCeti.nonsingularWishartMeasure_of_le` describe the two invalid branches.
* `TauCeti.ae_posDef_nonsingularWishartMeasure` — the sampled matrix is positive definite almost
  everywhere, so by `TauCeti.map_subtype_val_comap_nonsingularWishartMeasure` the law is recovered
  from its lift to the cone.
* `TauCeti.nonsingularWishartMeasure_zero` — in dimension zero the law is the Dirac mass at
  the unique symmetric matrix, hence a probability measure.
* `TauCeti.measurable_nonsingularWishartMeasure` — the law is measurable jointly in its real
  degree and every coordinate of its scale matrix, and
  `TauCeti.measurable_nonsingularWishartMeasure_selfAdjoint` is the form with the scale ranging
  over the symmetric-matrix carrier.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
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
/-- The **nonsingular Wishart density** of degree `n` and scale `S`, as a real-valued function of
a symmetric matrix: on the positive-definite cone it is
`(det A) ^ ((n - p - 1) / 2) * exp (-trace (S⁻¹ * A) / 2)` divided by the Wishart constant
`2 ^ (n p / 2) * (det S) ^ (n / 2) * Γ_p(n / 2)`, and it vanishes off the cone. -/
def nonsingularWishartPDFReal (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ :=
  if (A : Matrix (Fin p) (Fin p) ℝ).PosDef then
    (A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - (p : ℝ) - 1) / 2) *
        Real.exp (-Matrix.trace (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)) / 2) /
      ((2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) * multivariateGamma p (n / 2))
  else 0

open Classical in
/-- The defining branch expression of the real-valued Wishart density. -/
theorem nonsingularWishartPDFReal_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    nonsingularWishartPDFReal n S A =
      if (A : Matrix (Fin p) (Fin p) ℝ).PosDef then
        (A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - (p : ℝ) - 1) / 2) *
            Real.exp (-Matrix.trace (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)) / 2) /
          ((2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) * multivariateGamma p (n / 2))
      else 0 :=
  (rfl)

/-- On the positive-definite cone the Wishart density is its defining formula. -/
@[simp]
theorem nonsingularWishartPDFReal_of_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    nonsingularWishartPDFReal n S A =
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - (p : ℝ) - 1) / 2) *
          Real.exp (-Matrix.trace (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)) / 2) /
        ((2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) * multivariateGamma p (n / 2)) := by
  classical
  rw [nonsingularWishartPDFReal, ite_eq_left hA]

/-- Off the positive-definite cone the Wishart density vanishes. -/
@[simp]
theorem nonsingularWishartPDFReal_of_not_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : ¬ (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    nonsingularWishartPDFReal n S A = 0 := by
  classical
  rw [nonsingularWishartPDFReal, ite_eq_right hA]

/-- The Wishart normalizing constant is positive in the classical parameter range. -/
private theorem nonsingularWishart_const_pos (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    0 < (2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) * multivariateGamma p (n / 2) := by
  refine mul_pos (mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos hS.det_pos _)) ?_
  exact multivariateGamma_pos (by linarith)

/-- At a valid degree and scale the Wishart density is nonnegative. -/
theorem nonsingularWishartPDFReal_nonneg (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    0 ≤ nonsingularWishartPDFReal n S A := by
  by_cases hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [nonsingularWishartPDFReal_of_posDef n S hA]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hA.det_pos.le _) (Real.exp_nonneg _))
      (nonsingularWishart_const_pos hS hn).le
  · simp [hA]

/-- At a valid degree and scale the Wishart density is positive exactly on the positive-definite
cone. -/
theorem nonsingularWishartPDFReal_pos_iff (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < nonsingularWishartPDFReal n S A ↔ (A : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  refine ⟨fun h => ?_, fun hA => ?_⟩
  · by_contra hA
    simp [hA] at h
  · rw [nonsingularWishartPDFReal_of_posDef n S hA]
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hA.det_pos _) (Real.exp_pos _))
      (nonsingularWishart_const_pos hS hn)

/-- The `ℝ≥0∞`-valued Wishart density, the one that defines the measure. -/
def nonsingularWishartPDF (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (nonsingularWishartPDFReal n S A)

/-- The `ℝ≥0∞`-valued Wishart density is `ENNReal.ofReal` of the real-valued one. -/
theorem nonsingularWishartPDF_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    nonsingularWishartPDF n S A = ENNReal.ofReal (nonsingularWishartPDFReal n S A) :=
  (rfl)

/-- On the positive-definite cone the `ℝ≥0∞`-valued Wishart density is its defining formula. -/
@[simp]
theorem nonsingularWishartPDF_of_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    nonsingularWishartPDF n S A =
      ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - (p : ℝ) - 1) / 2) *
          Real.exp (-Matrix.trace (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)) / 2) /
        ((2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) * multivariateGamma p (n / 2))) := by
  rw [nonsingularWishartPDF_def, nonsingularWishartPDFReal_of_posDef n S hA]

/-- Off the positive-definite cone the `ℝ≥0∞`-valued Wishart density vanishes. -/
@[simp]
theorem nonsingularWishartPDF_of_not_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : ¬ (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    nonsingularWishartPDF n S A = 0 := by
  simp [nonsingularWishartPDF_def, hA]

/-- At a valid degree and scale the `ℝ≥0∞`-valued Wishart density is positive exactly on the
positive-definite cone. -/
theorem nonsingularWishartPDF_pos_iff (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < nonsingularWishartPDF n S A ↔ (A : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [nonsingularWishartPDF_def, ENNReal.ofReal_pos]
  exact nonsingularWishartPDFReal_pos_iff hS hn

/-- The Wishart density is finite. -/
@[simp]
theorem nonsingularWishartPDF_ne_top (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    nonsingularWishartPDF n S A ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- At a valid degree and scale the `ℝ≥0∞`-valued density carries the real one. -/
theorem toReal_nonsingularWishartPDF (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (nonsingularWishartPDF n S A).toReal = nonsingularWishartPDFReal n S A :=
  ENNReal.toReal_ofReal (nonsingularWishartPDFReal_nonneg hS hn A)

/-- The Wishart density is measurable along any measurable family of degrees, scale matrices and
points. -/
private theorem measurable_nonsingularWishartPDFReal_comp {γ : Type*} [MeasurableSpace γ]
    {f : γ → ℝ} {T : γ → Matrix (Fin p) (Fin p) ℝ}
    {g : γ → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} (hf : Measurable f)
    (hT : Measurable T) (hg : Measurable g) :
    Measurable fun c => nonsingularWishartPDFReal (f c) (T c) (g c) := by
  classical
  have hrpow : Measurable fun z : ℝ × ℝ => z.1 ^ z.2 := by fun_prop
  have hg' : Measurable fun c => (g c : Matrix (Fin p) (Fin p) ℝ) :=
    measurable_subtype_coe.comp hg
  have hdetg : Measurable fun c => (g c : Matrix (Fin p) (Fin p) ℝ).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hg'
  have hdetT : Measurable fun c => (T c).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hT
  have hinv : Measurable fun c => (T c)⁻¹ := measurable_matrix_inv.comp hT
  -- Matrix multiplication has neither a `MeasurableMul₂` instance nor a usable continuous
  -- combinator here: `(continuous_fst.matrix_mul continuous_snd).measurable` needs
  -- `OpensMeasurableSpace (Matrix ι ι ℝ × Matrix ι ι ℝ)`, which fails to synthesize because
  -- Mathlib gives `Matrix` no `SecondCountableTopology` instance. So read the trace entrywise.
  have htrace : Measurable fun c =>
      Matrix.trace ((T c)⁻¹ * (g c : Matrix (Fin p) (Fin p) ℝ)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
      (hinv.eval_matrix (i := i) (j := k)).mul (hg'.eval_matrix (i := k) (j := i))
  simp only [nonsingularWishartPDFReal]
  refine Measurable.ite (hg (measurableSet_posDefMatrix p)) ?_ measurable_const
  refine Measurable.div (Measurable.mul ?_ ?_) (Measurable.mul (Measurable.mul ?_ ?_) ?_)
  · exact hrpow.comp (hdetg.prodMk (by fun_prop))
  · exact Real.measurable_exp.comp (by fun_prop)
  · exact hrpow.comp (measurable_const.prodMk (by fun_prop))
  · exact hrpow.comp (hdetT.prodMk (by fun_prop))
  · exact (measurable_multivariateGamma p).comp (by fun_prop)

private theorem measurable_nonsingularWishartPDF_comp {γ : Type*} [MeasurableSpace γ] {f : γ → ℝ}
    {T : γ → Matrix (Fin p) (Fin p) ℝ}
    {g : γ → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} (hf : Measurable f)
    (hT : Measurable T) (hg : Measurable g) :
    Measurable fun c => nonsingularWishartPDF (f c) (T c) (g c) := by
  simp only [nonsingularWishartPDF_def]
  exact (measurable_nonsingularWishartPDFReal_comp hf hT hg).ennreal_ofReal

/-- The real-valued Wishart density is measurable in the point. -/
@[fun_prop]
theorem measurable_nonsingularWishartPDFReal (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (nonsingularWishartPDFReal n S) :=
  measurable_nonsingularWishartPDFReal_comp measurable_const measurable_const measurable_id

/-- The real-valued Wishart density is measurable jointly in its degree, its scale matrix and the
point. -/
@[fun_prop]
theorem measurable_uncurry_nonsingularWishartPDFReal (p : ℕ) :
    Measurable fun q : (ℝ × Matrix (Fin p) (Fin p) ℝ) ×
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      nonsingularWishartPDFReal q.1.1 q.1.2 q.2 :=
  measurable_nonsingularWishartPDFReal_comp (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) measurable_snd

/-- The Wishart density is measurable in the point. -/
@[fun_prop]
theorem measurable_nonsingularWishartPDF (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (nonsingularWishartPDF n S) :=
  measurable_nonsingularWishartPDF_comp measurable_const measurable_const measurable_id

/-- The Wishart density is measurable jointly in its degree, its scale matrix and the point. -/
@[fun_prop]
theorem measurable_uncurry_nonsingularWishartPDF (p : ℕ) :
    Measurable fun q : (ℝ × Matrix (Fin p) (Fin p) ℝ) ×
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      nonsingularWishartPDF q.1.1 q.1.2 q.2 :=
  measurable_nonsingularWishartPDF_comp (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) measurable_snd

/-! ### The measure -/

open Classical in
/-- The **nonsingular Wishart law** of real degree `n` and positive-definite scale `S`: the
density `TauCeti.nonsingularWishartPDF` against `TauCeti.symmetricLebesgue`. Outside the
classical parameter range — a scale that is not positive definite, or a degree at most `p - 1`,
which in positive dimension is where the density stops being integrable — the definition sets the
measure to zero. -/
def nonsingularWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  if S.PosDef ∧ (p : ℝ) - 1 < n then
    (symmetricLebesgue p).withDensity (nonsingularWishartPDF n S)
  else 0

open Classical in
/-- The defining branch expression of the Wishart law. -/
theorem nonsingularWishartMeasure_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    nonsingularWishartMeasure n S =
      if S.PosDef ∧ (p : ℝ) - 1 < n then
        (symmetricLebesgue p).withDensity (nonsingularWishartPDF n S)
      else 0 :=
  (rfl)

/-- In the classical parameter range the Wishart law is its density against
`TauCeti.symmetricLebesgue`. -/
theorem nonsingularWishartMeasure_of_posDef (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    nonsingularWishartMeasure n S =
      (symmetricLebesgue p).withDensity (nonsingularWishartPDF n S) := by
  classical
  rw [nonsingularWishartMeasure, ite_eq_left ⟨hS, hn⟩]

/-- At a scale that is not positive definite there is no Wishart density to normalize, and the
law is zero. -/
@[simp]
theorem nonsingularWishartMeasure_of_not_posDef (n : ℝ) (hS : ¬ S.PosDef) :
    nonsingularWishartMeasure n S = 0 := by
  classical
  rw [nonsingularWishartMeasure, ite_eq_right (fun h => hS h.1)]

/-- At a degree at most `p - 1` the Wishart law is zero by definition; in positive dimension this
is the range where the density is not integrable. -/
@[simp]
theorem nonsingularWishartMeasure_of_le (S : Matrix (Fin p) (Fin p) ℝ)
    (hn : n ≤ (p : ℝ) - 1) :
    nonsingularWishartMeasure n S = 0 := by
  classical
  rw [nonsingularWishartMeasure, ite_eq_right (fun h => absurd h.2 (not_lt.2 hn))]

/-- The Wishart law gives no mass to the complement of the positive-definite cone. -/
@[simp]
theorem nonsingularWishartMeasure_compl_posDef (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    nonsingularWishartMeasure n S
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}ᶜ = 0 := by
  by_cases hval : S.PosDef ∧ (p : ℝ) - 1 < n
  · rw [nonsingularWishartMeasure_of_posDef hval.1 hval.2,
      withDensity_apply _ (measurableSet_posDefMatrix p).compl]
    refine setLIntegral_eq_zero (measurableSet_posDefMatrix p).compl fun A hA => ?_
    exact nonsingularWishartPDF_of_not_posDef n S hA
  · rw [not_and_or] at hval
    rcases hval with hS | hn
    · simp [nonsingularWishartMeasure_of_not_posDef n hS]
    · simp [nonsingularWishartMeasure_of_le S (not_lt.1 hn)]

/-- A matrix sampled from the Wishart law is almost surely positive definite. -/
theorem ae_posDef_nonsingularWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂nonsingularWishartMeasure n S,
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [ae_iff]
  exact nonsingularWishartMeasure_compl_posDef n S

/-- **The Wishart law read on the positive-definite cone.** Mapping the lift
`(nonsingularWishartMeasure n S).comap Subtype.val` back along the inclusion of the cone returns
the law itself, because the cone carries all of its mass. This is the form in which the Cholesky
equivalence, which is defined on the cone, acts on a Wishart matrix. -/
@[simp]
theorem map_subtype_val_comap_nonsingularWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    ((nonsingularWishartMeasure n S).comap
        (Subtype.val : PosDefMatrix p → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))).map
        Subtype.val = nonsingularWishartMeasure n S :=
  (map_comap_subtype_coe (measurableSet_posDefMatrix p) _).trans
    (Measure.restrict_eq_self_of_ae_mem (ae_posDef_nonsingularWishartMeasure n S))

/-! ### Dimension zero -/

/-- In dimension zero the symmetric space is a single point and the real-valued Wishart density
is `1` there. -/
@[simp]
theorem nonsingularWishartPDFReal_zero (n : ℝ) (S : Matrix (Fin 0) (Fin 0) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    nonsingularWishartPDFReal n S A = 1 := by
  have hA : (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef :=
    ⟨Subsingleton.elim _ _, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  rw [nonsingularWishartPDFReal_of_posDef n S hA]
  simp [Matrix.det_isEmpty, Matrix.trace]

/-- In dimension zero the symmetric space is a single point and the Wishart density is `1`
there. -/
@[simp]
theorem nonsingularWishartPDF_zero (n : ℝ) (S : Matrix (Fin 0) (Fin 0) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    nonsingularWishartPDF n S A = 1 := by
  rw [nonsingularWishartPDF_def, nonsingularWishartPDFReal_zero, ENNReal.ofReal_one]

/-- In dimension zero every valid Wishart law is the Dirac mass at the unique symmetric matrix.
The general definition already gives this: `TauCeti.symmetricLebesgue 0` is that Dirac mass and
the density is identically `1`. -/
theorem nonsingularWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    nonsingularWishartMeasure n S = Measure.dirac 0 := by
  have hS : S.PosDef := ⟨Subsingleton.elim _ _, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  rw [nonsingularWishartMeasure_of_posDef hS (by simpa using hn), symmetricLebesgue_zero,
    dirac_withDensity' (measurable_nonsingularWishartPDF n S),
    nonsingularWishartPDF_zero, one_smul]

/-- In dimension zero every valid Wishart law is a probability measure. -/
theorem isProbabilityMeasure_nonsingularWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    IsProbabilityMeasure (nonsingularWishartMeasure n S) := by
  rw [nonsingularWishartMeasure_zero hn]
  infer_instance

/-! ### Parameter measurability -/

/-- **Parameter measurability of the nonsingular Wishart law.** The law is measurable jointly in
its real degree and every coordinate of its scale matrix, which is what a Wishart kernel with a
random degree and scale needs. -/
@[fun_prop]
theorem measurable_nonsingularWishartMeasure :
    Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      nonsingularWishartMeasure q.1 (Matrix.of q.2) := by
  classical
  have hcone : MeasurableSet {q : ℝ × (Fin p → Fin p → ℝ) | (Matrix.of q.2).PosDef} :=
    ((Matrix.measurable_of (Fin p) (Fin p) ℝ).comp measurable_snd)
      measurableSet_setOfPred_posDef
  have hvalid : MeasurableSet
      {q : ℝ × (Fin p → Fin p → ℝ) | (Matrix.of q.2).PosDef ∧ (p : ℝ) - 1 < q.1} :=
    hcone.inter (measurableSet_lt measurable_const measurable_fst)
  have hdens : Measurable fun q : (ℝ × (Fin p → Fin p → ℝ)) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      nonsingularWishartPDF q.1.1 (Matrix.of q.1.2) q.2 :=
    measurable_nonsingularWishartPDF_comp (measurable_fst.comp measurable_fst)
      ((Matrix.measurable_of (Fin p) (Fin p) ℝ).comp (measurable_snd.comp measurable_fst))
      measurable_snd
  have hite : (fun q : ℝ × (Fin p → Fin p → ℝ) =>
      nonsingularWishartMeasure q.1 (Matrix.of q.2)) =
      fun q => if (Matrix.of q.2).PosDef ∧ (p : ℝ) - 1 < q.1 then
        (symmetricLebesgue p).withDensity (nonsingularWishartPDF q.1 (Matrix.of q.2))
      else 0 := by
    funext q
    simp only [nonsingularWishartMeasure]
  rw [hite]
  exact Measurable.ite hvalid (measurable_withDensity hdens) measurable_const

/-- The nonsingular Wishart law is measurable jointly in its real degree and a scale ranging over
the symmetric-matrix carrier. This is the form used to build a kernel with a random symmetric
scale. -/
@[fun_prop]
theorem measurable_nonsingularWishartMeasure_selfAdjoint :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      nonsingularWishartMeasure q.1 (q.2 : Matrix (Fin p) (Fin p) ℝ) :=
  measurable_nonsingularWishartMeasure.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

end TauCeti
