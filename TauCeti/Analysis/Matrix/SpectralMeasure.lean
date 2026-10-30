/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import TauCeti.Analysis.Matrix.Resolvent
public import TauCeti.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Empirical spectral measures of matrices

For a Hermitian matrix `A` of positive size `n`, the empirical spectral measure
`L_A = n⁻¹ ∑ᵢ δ_{λᵢ(A)}` is the probability measure on `ℝ` putting mass `1/n` at each eigenvalue,
counted with multiplicity. For a general complex square matrix, the eigenvalue measure is the
probability measure `n⁻¹ ∑ δ_z` on `ℂ`, the sum running over the roots of the characteristic
polynomial with algebraic multiplicity. These are the basic objects of random matrix theory:
global laws such as the semicircle and circular laws are limit theorems for them.

Both measures are built from `TauCeti.Probability.empiricalMeasureOfFintype`, whose evaluation,
integration and pushforward API applies to them directly. The Hermitian measure depends only on the
characteristic polynomial, not on the basis or on the eigenvector choice, and its pushforward along
`ℝ → ℂ` is the eigenvalue measure. The eigenvalue measure of a nilpotent matrix is the Dirac mass at
`0`; this records that roots are counted with algebraic, not geometric, multiplicity.

The moments and the resolvent transform of the Hermitian spectral measure are normalized traces:
`∫ x ^ k dL_A = n⁻¹ Re tr (A ^ k)` and, off the spectrum, `m_{L_A}(z) = n⁻¹ tr (A - z • 1)⁻¹`.
These identities turn the moment method and the resolvent method for global laws into
computations with traces of matrices.

## Main definitions

* `Matrix.spectralMeasure A hA` — the empirical spectral measure of a Hermitian matrix;
* `Matrix.eigenvalueMeasure A` — the empirical measure of the characteristic roots of a complex
  square matrix.

## Main results

* `Matrix.spectralMeasure_eq_of_charpoly_eq` — Hermitian matrices with the same characteristic
  polynomial have the same spectral measure;
* `Matrix.spectralMeasure_units_conj`, `Matrix.eigenvalueMeasure_units_conj` — both measures are
  invariant under conjugation by an invertible matrix;
* `Matrix.eigenvalueMeasure_apply` — the eigenvalue measure of a set is the proportion of
  characteristic roots in it, counted with algebraic multiplicity;
* `Matrix.map_spectralMeasure_ofReal` — for a complex Hermitian matrix, the eigenvalue measure is
  the pushforward of the spectral measure along `ℝ → ℂ`;
* `Matrix.eigenvalueMeasure_toMeasure_of_isNilpotent` — a nilpotent matrix has eigenvalue measure
  `δ₀`;
* `Matrix.integral_pow_spectralMeasure` — the `k`-th moment of the spectral measure is the
  normalized trace of `A ^ k`;
* `Matrix.resolventTransform_spectralMeasure` — the resolvent transform of the spectral measure is
  the normalized trace of the resolvent `(A - z • 1)⁻¹`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.4.
-/

public section

noncomputable section

open MeasureTheory Polynomial TauCeti.Probability
open scoped ENNReal

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

variable [Nonempty n]

/-- The empirical spectral measure `L_A = (card n)⁻¹ ∑ᵢ δ_{λᵢ(A)}` of a Hermitian matrix of
positive size, with the eigenvalues counted with multiplicity. -/
def spectralMeasure (A : Matrix n n 𝕜) (hA : A.IsHermitian) : ProbabilityMeasure ℝ :=
  empiricalMeasureOfFintype hA.eigenvalues

/-- The spectral measure is the empirical measure of the eigenvalue family. -/
theorem spectralMeasure_def (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    A.spectralMeasure hA = empiricalMeasureOfFintype hA.eigenvalues :=
  (rfl)

/-- The spectral measure is the empirical measure of the decreasingly sorted eigenvalues. -/
theorem spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀ (A : Matrix n n 𝕜)
    (hA : A.IsHermitian) :
    A.spectralMeasure hA = empiricalMeasureOfFintype hA.eigenvalues₀ :=
  empiricalMeasureOfFintype_comp_equiv _ hA.eigenvalues₀

/-- The spectral measure of a set is the proportion of eigenvalues in it, counted with
multiplicity. -/
theorem spectralMeasure_apply (A : Matrix n n 𝕜) (hA : A.IsHermitian) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (A.spectralMeasure hA : Measure ℝ) s =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, s.indicator 1 (hA.eigenvalues i) :=
  empiricalMeasureOfFintype_apply hs

/-- Integrating against the spectral measure is averaging over the eigenvalues. -/
theorem integral_spectralMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : Matrix n n 𝕜) (hA : A.IsHermitian) (f : ℝ → E) :
    ∫ x, f x ∂(A.spectralMeasure hA : Measure ℝ) =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ • ∑ i, f (hA.eigenvalues i) := by
  rw [spectralMeasure_def, ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype,
    integral_empiricalFiniteMeasure_of_measurableSingletonClass]

/-- Integrating against the spectral measure is averaging over the decreasingly sorted
eigenvalues. -/
theorem integral_spectralMeasure_eq_sum_eigenvalues₀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : Matrix n n 𝕜) (hA : A.IsHermitian) (f : ℝ → E) :
    ∫ x, f x ∂(A.spectralMeasure hA : Measure ℝ) =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ • ∑ i, f (hA.eigenvalues₀ i) := by
  rw [spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀,
    ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype,
    integral_empiricalFiniteMeasure_of_measurableSingletonClass, Fintype.card_fin]

/-- Hermitian matrices with the same characteristic polynomial have the same spectral measure.
In particular the spectral measure does not depend on a choice of basis. -/
theorem spectralMeasure_eq_of_charpoly_eq {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    A.spectralMeasure hA = B.spectralMeasure hB := by
  rw [spectralMeasure_def, spectralMeasure_def, (hA.eigenvalues_eq_eigenvalues_iff hB).2 h]

/-- Conjugating a Hermitian matrix by an invertible matrix does not change its spectral measure,
provided the conjugate is again Hermitian. -/
@[simp]
theorem spectralMeasure_units_conj {A : Matrix n n 𝕜} (hA : A.IsHermitian) (M : (Matrix n n 𝕜)ˣ)
    (hMA : (M.val * A * M.val⁻¹).IsHermitian) :
    (M.val * A * M.val⁻¹).spectralMeasure hMA = A.spectralMeasure hA :=
  spectralMeasure_eq_of_charpoly_eq hMA hA (charpoly_units_conj M A)

/-- The Lebesgue integral against the spectral measure is the average over the eigenvalues. -/
theorem lintegral_spectralMeasure (A : Matrix n n 𝕜) (hA : A.IsHermitian) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(A.spectralMeasure hA : Measure ℝ) =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, f (hA.eigenvalues i) := by
  simp [spectralMeasure_def, lintegral_finsetSum_measure, lintegral_dirac, Finset.mul_sum]

/-- The empirical measure `(card n)⁻¹ ∑ δ_z` of a complex square matrix of positive size, the
sum running over the roots `z` of its characteristic polynomial with algebraic multiplicity. -/
def eigenvalueMeasure (A : Matrix n n ℂ) : ProbabilityMeasure ℂ :=
  empiricalMeasureOfFintype fun z : A.charpoly.roots => (z : ℂ)

/-- The eigenvalue measure is the empirical measure of the family of characteristic roots, indexed
by the elements of the root multiset. -/
theorem eigenvalueMeasure_def (A : Matrix n n ℂ) :
    A.eigenvalueMeasure = empiricalMeasureOfFintype fun z : A.charpoly.roots => (z : ℂ) :=
  (rfl)

/-- The measure underlying the eigenvalue measure is the normalized sum of the Dirac masses at the
characteristic roots, counted with algebraic multiplicity. -/
theorem eigenvalueMeasure_toMeasure (A : Matrix n n ℂ) :
    (A.eigenvalueMeasure : Measure ℂ) =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ • (A.charpoly.roots.map Measure.dirac).sum := by
  rw [eigenvalueMeasure_def, empiricalMeasureOfFintype_toMeasure, ← Finset.smul_sum,
    Finset.sum_eq_multiset_sum, Multiset.map_univ, Multiset.card_coe,
    IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]

/-- The eigenvalue measure of a set is the proportion of characteristic roots in it, counted with
algebraic multiplicity. -/
theorem eigenvalueMeasure_apply (A : Matrix n n ℂ) {s : Set ℂ} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) :
    (A.eigenvalueMeasure : Measure ℂ) s =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ * Multiset.card (A.charpoly.roots.filter (· ∈ s)) := by
  rw [eigenvalueMeasure_toMeasure, Measure.smul_apply, smul_eq_mul]
  congr 1
  induction A.charpoly.roots using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    by_cases hz : z ∈ s <;> simp [Measure.dirac_apply' _ hs, hz, ih, add_comm]

/-- Integrating against the eigenvalue measure is averaging over the characteristic roots,
counted with algebraic multiplicity. -/
theorem integral_eigenvalueMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : Matrix n n ℂ) (f : ℂ → E) :
    ∫ z, f z ∂(A.eigenvalueMeasure : Measure ℂ) =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ • (A.charpoly.roots.map f).sum := by
  rw [eigenvalueMeasure_def, ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype,
    integral_empiricalFiniteMeasure_of_measurableSingletonClass, Finset.sum_eq_multiset_sum,
    Multiset.map_univ, Multiset.card_coe, IsAlgClosed.card_roots_eq_natDegree,
    charpoly_natDegree_eq_dim]

/-- Conjugating a complex square matrix by an invertible matrix does not change its eigenvalue
measure. -/
@[simp]
theorem eigenvalueMeasure_units_conj (M : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    (M.val * A * M.val⁻¹).eigenvalueMeasure = A.eigenvalueMeasure := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [eigenvalueMeasure_toMeasure, eigenvalueMeasure_toMeasure, charpoly_units_conj]

/-- For a complex Hermitian matrix, the eigenvalue measure is the pushforward of the spectral
measure along `ℝ → ℂ`. -/
theorem map_spectralMeasure_ofReal (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (A.spectralMeasure hA).map Complex.ofReal = A.eigenvalueMeasure := by
  rw [spectralMeasure_def, map_empiricalMeasureOfFintype Complex.measurable_ofReal,
    eigenvalueMeasure_def]
  apply empiricalMeasureOfFintype_eq_of_map_univ_val_eq
  rw [Multiset.map_univ_coe, hA.roots_charpoly_eq_eigenvalues, RCLike.ofReal_eq_complex_ofReal]

/-- A nilpotent complex matrix of positive size has eigenvalue measure `δ₀`: its characteristic
polynomial is `X ^ n`, whose root `0` has algebraic multiplicity `n`. -/
theorem eigenvalueMeasure_toMeasure_of_isNilpotent {A : Matrix n n ℂ} (hA : IsNilpotent A) :
    (A.eigenvalueMeasure : Measure ℂ) = Measure.dirac 0 := by
  have hchar : A.charpoly = X ^ Fintype.card n :=
    sub_eq_zero.mp (isNilpotent_charpoly_sub_pow_of_isNilpotent hA).eq_zero
  rw [eigenvalueMeasure_toMeasure, hchar, roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_smul]

/-- The `k`-th moment of the spectral measure of a Hermitian matrix is the normalized trace of
`A ^ k`: `∫ x ^ k dL_A = (card n)⁻¹ * Re tr (A ^ k)`. -/
theorem integral_pow_spectralMeasure (A : Matrix n n 𝕜) (hA : A.IsHermitian) (k : ℕ) :
    ∫ x, x ^ k ∂(A.spectralMeasure hA : Measure ℝ) =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ * RCLike.re (A ^ k).trace := by
  rw [integral_spectralMeasure, smul_eq_mul, hA.trace_pow_eq_sum_eigenvalues_pow, map_sum]
  simp_rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Off the spectrum, the resolvent transform `m(z) = ∫ (x - z)⁻¹ dL_A(x)` of the spectral measure
of a complex Hermitian matrix is the normalized trace of its resolvent `(A - z • 1)⁻¹`. -/
theorem resolventTransform_spectralMeasure (A : Matrix n n ℂ) (hA : A.IsHermitian) {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    resolventTransform (A.spectralMeasure hA : Measure ℝ) z =
      ((Fintype.card n : ℕ) : ℂ)⁻¹ * (A - z • 1)⁻¹.trace := by
  rw [resolventTransform_apply, integral_spectralMeasure, hA.trace_inv_sub_smul_one hz,
    Complex.real_smul]
  simp [resolvent, Ring.inverse_eq_inv']

end Matrix
