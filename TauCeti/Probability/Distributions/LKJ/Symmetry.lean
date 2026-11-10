/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import TauCeti.Probability.Distributions.Beta.Symmetric
public import TauCeti.Probability.Distributions.Beta.Reflection
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Analysis.Matrix.MeasurableSpace

import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Integrable
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Symmetries and moments of correlation-matrix laws

Relabelling the indices of a correlation matrix, `R ↦ P R Pᵀ` for a permutation matrix `P`, and
flipping the signs of some coordinate axes, `R ↦ D R D` for a diagonal matrix `D` with entries
`±1`, preserve both the reference measure `TauCeti.correlationLebesgue p` and the LKJ density
`det R ^ (η - 1) / lkjNormalizer p η`: such a congruence keeps the determinant and positive
definiteness. Hence every LKJ law is invariant under these two symmetry groups.

Sign symmetry determines the mean. Flipping the sign of axis `i` negates every off-diagonal entry
in row `i`, so these entries have mean zero, while the diagonal entries are almost surely one.
Every entry is bounded by one in absolute value, so the LKJ matrix is integrable, and for `η > 0`
its mean is the identity matrix.

## Main results

* `TauCeti.Probability.lkjPDF_symmetricCongruenceLinearMap`: congruence by a matrix of
  determinant `±1` preserves the LKJ density.
* `TauCeti.Probability.map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure`: permutation
  invariance.
* `TauCeti.Probability.map_symmetricCongruenceLinearMap_diagonal_lkjMeasure`: sign invariance.
* `TauCeti.Probability.integrable_id_lkjMeasure` and `TauCeti.Probability.integral_id_lkjMeasure`:
  the LKJ matrix is integrable with mean the identity.

Independent symmetric partial correlations give a Gram law invariant under conjugation by
any diagonal sign matrix. Off-diagonal integrals and covariances of distinct strictly lower
entries vanish for arbitrary sigma-finite symmetric marginals, using totalized integrals.
For centered symmetric Beta marginals, entries have all finite moments and the mean is the
identity. Zero covariance does not assert independence of correlation entries.

The proofs use `partialCorrelationGram_signChange`, the coordinatewise product pushforward,
and reflection symmetry of Beta laws. These results apply to the independent-Beta construction
of random correlation matrices without requiring a density change of variables.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped Matrix
open scoped Matrix.Norms.Elementwise ENNReal

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-! ### Invariance of the density and of the law -/

/-- Congruence by a square matrix of determinant `±1` preserves the real-valued LKJ density: it
preserves both the determinant and positive definiteness. -/
theorem lkjPDFReal_symmetricCongruenceLinearMap {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDFReal p η (Matrix.symmetricCongruenceLinearMap M R) = lkjPDFReal p η R := by
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 <| Ne.isUnit fun h ↦ by simp [h] at hM
  have hT : Mᵀ = star M := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hpos : (Matrix.symmetricCongruenceLinearMap M R : Matrix (Fin p) (Fin p) ℝ).PosDef ↔
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
    rw [Matrix.coe_symmetricCongruenceLinearMap_apply, hT]
    exact Matrix.IsUnit.posDef_star_right_conjugate_iff hU
  by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [lkjPDFReal_of_posDef p η (hpos.2 hR), lkjPDFReal_of_posDef p η hR,
      Matrix.det_coe_symmetricCongruenceLinearMap_apply, hM, one_mul]
  · rw [lkjPDFReal_of_not_posDef p η (hpos.not.2 hR), lkjPDFReal_of_not_posDef p η hR]

/-- Congruence by a square matrix of determinant `±1` preserves the LKJ density. -/
theorem lkjPDF_symmetricCongruenceLinearMap {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η (Matrix.symmetricCongruenceLinearMap M R) = lkjPDF p η R := by
  rw [lkjPDF_def, lkjPDFReal_symmetricCongruenceLinearMap hM, lkjPDF_def]

/-- Congruence by a square matrix of determinant `±1` that preserves the reference measure also
preserves every LKJ law. -/
private theorem map_symmetricCongruenceLinearMap_lkjMeasure {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1)
    (hμ : (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap M) =
      correlationLebesgue p) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap M) = lkjMeasure p η := by
  by_cases hη : 0 < η
  · rw [lkjMeasure_of_pos hη]
    refine Measure.map_withDensity_eq_withDensity (jac := 1)
      (LinearMap.continuous_of_finiteDimensional _).measurable measurable_const
      (measurable_lkjPDF p η) (by rwa [withDensity_one]) (ae_of_all _ fun R ↦ ?_)
    rw [Pi.one_apply, one_mul, lkjPDF_symmetricCongruenceLinearMap hM]
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

variable (p η) in
/-- **Permutation invariance of the LKJ law.** Relabelling the indices, `R ↦ P R Pᵀ` for a
permutation matrix `P`, preserves the LKJ law. -/
theorem map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure (σ : Equiv.Perm (Fin p)) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ)) =
      lkjMeasure p η := by
  refine map_symmetricCongruenceLinearMap_lkjMeasure ?_
    (map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue p σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [Matrix.det_permutation, h]

variable (p η) in
/-- **Sign invariance of the LKJ law.** Flipping the signs of coordinate axes, `R ↦ D R D` for a
diagonal matrix `D` with entries `±1`, preserves the LKJ law. -/
theorem map_symmetricCongruenceLinearMap_diagonal_lkjMeasure {s : Fin p → ℝ}
    (hs : ∀ i, |s i| = 1) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s)) =
      lkjMeasure p η := by
  refine map_symmetricCongruenceLinearMap_lkjMeasure ?_
    (map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue p hs)
  rw [Matrix.det_diagonal, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ ↦ by rw [← sq_abs, hs i, one_pow]

/-! ### The mean -/

/-- Every entry of an LKJ matrix is integrable: it lies in `[-1, 1]` almost surely. -/
private theorem integrable_coe_apply_lkjMeasure (i j : Fin p) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j) (lkjMeasure p η) := by
  by_cases hη : 0 < η
  · have := isProbabilityMeasure_lkjMeasure (p := p) hη
    refine Integrable.of_bound (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable 1 ?_
    filter_upwards [ae_posDef_lkjMeasure p η, ae_diag_eq_one_lkjMeasure p η] with R hR hdiag
    have hsq : ((R : Matrix (Fin p) (Fin p) ℝ) i j) ^ 2 ≤ 1 := by
      simpa [RCLike.normSq_apply, sq, hdiag] using hR.posSemidef.normSq_le i j
    rw [Real.norm_eq_abs]
    exact (sq_le_one_iff_abs_le_one _).1 hsq
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- An off-diagonal entry of an LKJ matrix has mean zero: flipping the sign of axis `i` preserves
the law and negates the entry. -/
private theorem integral_coe_apply_lkjMeasure_of_ne {i j : Fin p} (hij : i ≠ j) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ∂lkjMeasure p η = 0 := by
  set s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = i <;> simp [s, hk]
  have h := integral_map (μ := lkjMeasure p η)
    (φ := Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s))
    (f := fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j)
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
    (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable
  rw [map_symmetricCongruenceLinearMap_diagonal_lkjMeasure p η hs] at h
  simp only [Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.diagonal_transpose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, s, hij.symm, ↓reduceIte, neg_one_mul, mul_one,
    integral_neg] at h
  linarith

/-- The entrywise mean of an LKJ matrix is the identity matrix. -/
private theorem integral_coe_apply_lkjMeasure (hη : 0 < η) (i j : Fin p) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ∂lkjMeasure p η =
      (1 : Matrix (Fin p) (Fin p) ℝ) i j := by
  rcases eq_or_ne i j with rfl | hij
  · have := isProbabilityMeasure_lkjMeasure (p := p) hη
    rw [Matrix.one_apply_eq, integral_congr_ae ((ae_diag_eq_one_lkjMeasure p η).mono
      fun R hR ↦ hR i), integral_const, probReal_univ, one_smul]
  · rw [Matrix.one_apply_ne hij]
    exact integral_coe_apply_lkjMeasure_of_ne hij

variable (p η) in
/-- An LKJ matrix is integrable. -/
theorem integrable_id_lkjMeasure :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ R)
      (lkjMeasure p η) :=
  integrable_iff_integrable_coe_apply.2 integrable_coe_apply_lkjMeasure

/-- **The mean of an LKJ law** of positive shape is the identity matrix. -/
theorem integral_id_lkjMeasure (hη : 0 < η) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), R ∂lkjMeasure p η =
      (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  have hcoords : Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      symmetricCoordinates p R) (lkjMeasure p η) :=
    (symmetricCoordinates p).toContinuousLinearMap.integrable_comp (integrable_id_lkjMeasure p η)
  apply (symmetricCoordinates p).injective
  funext ij
  rw [← (symmetricCoordinates p).integral_comp_comm, eval_integral fun ij ↦ hcoords.eval ij]
  simp only [symmetricCoordinates_apply]
  exact integral_coe_apply_lkjMeasure hη ij.1.1 ij.1.2

/-! ### Sign symmetry and moments of partial-correlation Gram laws -/

/-- Independent negation-invariant partial correlations give a Gram law invariant under
conjugation by a diagonal sign matrix. The marginals need only be sigma-finite. -/
theorem map_signChange_map_partialCorrelationGram_pi
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant] {s : Fin p → ℝ} (hs : ∀ i, |s i| = 1) :
    ((Measure.pi μ).map partialCorrelationGram).map
        (fun R : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.of fun i j ↦ s i * R i j * s j) =
      (Measure.pi μ).map partialCorrelationGram := by
  have hmap (ij : strictLowerTriangle p) :
      (μ ij).map (fun x ↦ s ij.1.1 * s ij.1.2 * x) = μ ij := by
    have habs : |s ij.1.1 * s ij.1.2| = 1 := by simp [abs_mul, hs]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 habs with h | h
    · simp [h]
    · simp [h]
  have (ij : strictLowerTriangle p) : SigmaFinite
      ((μ ij).map (fun x ↦ s ij.1.1 * s ij.1.2 * x)) := by
    rw [hmap]
    infer_instance
  have hpi : (Measure.pi μ).map
      (fun z ij ↦ s ij.1.1 * s ij.1.2 * z ij) = Measure.pi μ := by
    rw [Measure.pi_map_pi (fun _ ↦ by fun_prop)]
    simp_rw [hmap]
  have hcomp :
      (fun R : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.of fun i j ↦ s i * R i j * s j) ∘
        partialCorrelationGram = partialCorrelationGram ∘
          (fun z ij ↦ s ij.1.1 * s ij.1.2 * z ij) := by
    funext z i j
    exact (partialCorrelationGram_signChange z hs i j).symm
  rw [Measure.map_map (by fun_prop) continuous_partialCorrelationGram.measurable, hcomp,
    ← Measure.map_map (g := partialCorrelationGram (p := p))
      continuous_partialCorrelationGram.measurable (by fun_prop), hpi]

/-- Off-diagonal entries of a Gram law with independent negation-invariant marginals have
zero integral. The marginals need only be sigma-finite; nonintegrable integrals are totalized
to zero. -/
@[simp]
theorem integral_apply_map_partialCorrelationGram_pi_of_ne
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant] {i j : Fin p} (hij : i ≠ j) :
    ∫ R : Matrix (Fin p) (Fin p) ℝ, R i j ∂((Measure.pi μ).map partialCorrelationGram) = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := by intro k; simp [s]; split_ifs <;> norm_num
  have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦ ∫ R, R i j ∂ν)
    (map_signChange_map_partialCorrelationGram_pi μ hs)
  rw [integral_map
    (by fun_prop : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦
      Matrix.of fun i j ↦ s i * R i j * s j)).aemeasurable
    Matrix.measurable_apply.aestronglyMeasurable] at h
  simp only [Matrix.of_apply] at h
  simp only [s, ite_true, ite_eq_right (Ne.symm hij), neg_one_mul, mul_one, integral_neg] at h
  linarith

/-- Distinct strictly lower entries of a Gram law with independent negation-invariant
marginals have zero covariance. The marginals need only be sigma-finite; the integrals in
covariance are totalized, so this does not assert integrability or independence. -/
@[simp]
theorem covariance_apply_map_partialCorrelationGram_pi
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant]
    {ij kl : strictLowerTriangle p} (hne : ij ≠ kl) :
    cov[fun R : Matrix (Fin p) (Fin p) ℝ ↦ R ij.1.1 ij.1.2,
        fun R : Matrix (Fin p) (Fin p) ℝ ↦ R kl.1.1 kl.1.2;
      (Measure.pi μ).map partialCorrelationGram] = 0 := by
  have hp : ij.1 ≠ kl.1 := Subtype.coe_injective.ne hne
  have hij := ij.2
  have hkl := kl.2
  obtain ⟨v, hv, hvk, hvl⟩ : ∃ v : Fin p,
      (v = ij.1.1 ∨ v = ij.1.2) ∧ v ≠ kl.1.1 ∧ v ≠ kl.1.2 := by
    by_cases h : ij.1.1 = kl.1.1 ∨ ij.1.1 = kl.1.2
    · refine ⟨ij.1.2, Or.inr rfl, ?_, ?_⟩
      all_goals rcases h with h | h
      all_goals intro h'
      all_goals first | exact hp (Prod.ext h h') | omega
    · exact ⟨ij.1.1, Or.inl rfl, fun h' ↦ h (Or.inl h'), fun h' ↦ h (Or.inr h')⟩
  let s : Fin p → ℝ := fun k ↦ if k = v then -1 else 1
  have hs : ∀ k, |s k| = 1 := by intro k; simp [s]; split_ifs <;> norm_num
  have hsign : s ij.1.1 * s ij.1.2 = -1 := by
    rcases hv with rfl | rfl <;> simp [s, hij.ne, hij.ne']
  have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦
      ∫ R, R ij.1.1 ij.1.2 * R kl.1.1 kl.1.2 ∂ν)
    (map_signChange_map_partialCorrelationGram_pi μ hs)
  rw [integral_map (f := fun R : Matrix (Fin p) (Fin p) ℝ ↦
      R ij.1.1 ij.1.2 * R kl.1.1 kl.1.2)
    (by fun_prop : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦
      Matrix.of fun i j ↦ s i * R i j * s j)).aemeasurable
    (Matrix.measurable_apply.mul Matrix.measurable_apply).aestronglyMeasurable] at h
  simp only [Matrix.of_apply] at h
  have he : ∀ R : Matrix (Fin p) (Fin p) ℝ,
      (s ij.1.1 * R ij.1.1 ij.1.2 * s ij.1.2) *
        (s kl.1.1 * R kl.1.1 kl.1.2 * s kl.1.2) =
          -(R ij.1.1 ij.1.2 * R kl.1.1 kl.1.2) := by
    intro R
    rw [mul_right_comm (s ij.1.1), hsign]
    simp [s, Ne.symm hvk, Ne.symm hvl]
  simp_rw [he, integral_neg] at h
  simp only [covariance, integral_apply_map_partialCorrelationGram_pi_of_ne μ hij.ne',
    integral_apply_map_partialCorrelationGram_pi_of_ne μ hkl.ne', sub_zero]
  linarith

/-- Every entry of the independent-Beta Gram construction belongs to every `Lᵠ`, including
`L∞`. This supplies absolute integrability for its moment and covariance formulas. -/
theorem memLp_apply_map_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i j : Fin p) (q : ℝ≥0∞) :
    MemLp (fun R : Matrix (Fin p) (Fin p) ℝ ↦ R i j) q
      ((Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
        (fun x ↦ -1 + 2 * x)).map partialCorrelationGram) := by
  rw [memLp_map_measure_iff Matrix.measurable_apply.aestronglyMeasurable
    continuous_partialCorrelationGram.measurable.aemeasurable]
  have (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  refine MemLp.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  have hz' : ∀ ij, |z ij| ≤ 1 := fun ij ↦ le_of_lt (hz ij)
  exact (posSemidef_partialCorrelationGram z).norm_le_one_of_apply_self_eq_one
    (partialCorrelationGram_apply_self hz' i) (partialCorrelationGram_apply_self hz' j)

/-- The entrywise mean of the independent centered symmetric Beta Gram law is the identity.
The shapes may vary independently across all strictly lower positions. -/
@[simp]
theorem integral_apply_map_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i j : Fin p) :
    ∫ R : Matrix (Fin p) (Fin p) ℝ, R i j
      ∂((Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
        (fun x ↦ -1 + 2 * x)).map partialCorrelationGram) = if i = j then 1 else 0 := by
  have (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  by_cases hij : i = j
  · subst j
    rw [integral_map continuous_partialCorrelationGram.measurable.aemeasurable
      Matrix.measurable_apply.aestronglyMeasurable]
    simp only [ite_true]
    calc
      _ = ∫ _, (1 : ℝ) ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
          (fun x ↦ -1 + 2 * x)) := integral_congr_ae <|
        (ae_abs_lt_one_pi_centered_betaMeasure ha).mono fun z hz ↦
          partialCorrelationGram_apply_self (fun ij ↦ le_of_lt (hz ij)) i
      _ = 1 := by simp
  · rw [ite_eq_right hij]
    exact integral_apply_map_partialCorrelationGram_pi_of_ne _ hij

end TauCeti.Probability
