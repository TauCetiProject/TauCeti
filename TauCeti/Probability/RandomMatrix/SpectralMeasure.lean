/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Empirical spectral measures of matrices

For a Hermitian matrix `A` over `ℝ` or `ℂ` indexed by a finite type of size `n`, the empirical
spectral measure `Matrix.spectralMeasure A hA` is `L_A = n⁻¹ ∑ᵢ δ_{λᵢ(A)}` on `ℝ`, the eigenvalues
counted with multiplicity. It is the empirical finite measure of the eigenvalue family, hence a
probability measure as soon as the matrix has positive size, and the zero measure for the empty
matrix. Integrals against it are eigenvalue averages, and it depends only on the characteristic
polynomial, so it is invariant under conjugation.

For an arbitrary complex square matrix, `Matrix.eigenvalueMeasure A` is the empirical measure
`n⁻¹ ∑ δ_z` on `ℂ`, the sum running over the roots of the characteristic polynomial with algebraic
multiplicity. For a Hermitian matrix it is the pushforward of the spectral measure along `ℝ → ℂ`,
and for a nilpotent matrix of positive size it is the Dirac mass at `0`.

These measures are the objects whose large-dimension limits are the semicircle, Marchenko–Pastur
and circular laws.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1 (the empirical measure of eigenvalues).
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.4.
-/

public section

noncomputable section

open MeasureTheory Polynomial TauCeti.Probability
open scoped ENNReal

namespace Matrix

variable {𝕜 n E : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Hermitian

variable {A B : Matrix n n 𝕜}

/-- The empirical spectral measure `L_A = n⁻¹ ∑ᵢ δ_{λᵢ(A)}` of a Hermitian matrix `A`, the
eigenvalues counted with multiplicity. It is a probability measure when the matrix has positive
size and the zero measure for the empty matrix. -/
def spectralMeasure (A : Matrix n n 𝕜) (hA : A.IsHermitian) : Measure ℝ :=
  empiricalFiniteMeasure hA.eigenvalues

theorem spectralMeasure_def (hA : A.IsHermitian) :
    A.spectralMeasure hA = empiricalFiniteMeasure hA.eigenvalues :=
  (rfl)

/-- The spectral measure is the empirical finite measure of the decreasingly sorted eigenvalues
`Matrix.IsHermitian.eigenvalues₀`. -/
theorem spectralMeasure_eq_empiricalFiniteMeasure_eigenvalues₀ (hA : A.IsHermitian) :
    A.spectralMeasure hA = empiricalFiniteMeasure hA.eigenvalues₀ := by
  rw [spectralMeasure_def, ← empiricalFiniteMeasure_comp_equiv hA.eigenvalues
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)))]
  congr 1
  funext i
  exact hA.eigenvalues_apply_equivOfCardEq i

/-- For a matrix of positive size, the spectral measure is the measure underlying the empirical
probability measure of the eigenvalues. -/
theorem spectralMeasure_eq_empiricalMeasureOfFintype [Nonempty n] (hA : A.IsHermitian) :
    A.spectralMeasure hA = (empiricalMeasureOfFintype hA.eigenvalues : Measure ℝ) := by
  rw [spectralMeasure_def, empiricalMeasureOfFintype_toMeasure]

instance isProbabilityMeasure_spectralMeasure [Nonempty n] (hA : A.IsHermitian) :
    IsProbabilityMeasure (A.spectralMeasure hA) := by
  rw [spectralMeasure_def]
  infer_instance

instance isFiniteMeasure_spectralMeasure (hA : A.IsHermitian) :
    IsFiniteMeasure (A.spectralMeasure hA) := by
  rw [spectralMeasure_def]
  infer_instance

/-- The spectral measure of the empty matrix is zero. -/
@[simp]
theorem spectralMeasure_of_isEmpty [IsEmpty n] (hA : A.IsHermitian) :
    A.spectralMeasure hA = 0 := by
  rw [spectralMeasure_def, empiricalFiniteMeasure_of_isEmpty]

/-- The spectral measure of a set is the proportion of eigenvalues, counted with multiplicity,
lying in it. -/
theorem spectralMeasure_apply (hA : A.IsHermitian) (s : Set ℝ) :
    A.spectralMeasure hA s =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ * Nat.card {i // hA.eigenvalues i ∈ s} := by
  classical
  simp only [spectralMeasure_def, empiricalFiniteMeasure_def, Measure.coe_finsetSum,
    Measure.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Measure.dirac_apply,
    ← Finset.mul_sum, Set.indicator_apply, Pi.one_apply, Finset.sum_boole,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Integrating against the spectral measure averages the integrand over the eigenvalues. -/
theorem integral_spectralMeasure (hA : A.IsHermitian) (f : ℝ → E) :
    ∫ x, f x ∂A.spectralMeasure hA =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ • ∑ i, f (hA.eigenvalues i) := by
  rw [spectralMeasure_def, integral_empiricalFiniteMeasure]

/-- The Lebesgue integral against the spectral measure is the average over the eigenvalues. -/
theorem lintegral_spectralMeasure (hA : A.IsHermitian) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂A.spectralMeasure hA =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, f (hA.eigenvalues i) := by
  rw [spectralMeasure_def, lintegral_empiricalFiniteMeasure hf]

/-- Hermitian matrices with the same characteristic polynomial have the same spectral measure. -/
theorem spectralMeasure_eq_of_charpoly_eq (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) :
    A.spectralMeasure hA = B.spectralMeasure hB := by
  rw [spectralMeasure_def, spectralMeasure_def, (hA.eigenvalues_eq_eigenvalues_iff hB).2 h]

/-- The spectral measure is invariant under conjugation: it depends only on the spectrum, not on
the basis. -/
@[simp]
theorem spectralMeasure_units_conj (hA : A.IsHermitian) (M : (Matrix n n 𝕜)ˣ)
    (hMA : (M.val * A * M.val⁻¹).IsHermitian) :
    (M.val * A * M.val⁻¹).spectralMeasure hMA = A.spectralMeasure hA :=
  spectralMeasure_eq_of_charpoly_eq hMA hA (charpoly_units_conj M A)

end Hermitian

section Complex

variable {A : Matrix n n ℂ}

/-- The empirical eigenvalue measure `n⁻¹ ∑ δ_z` of a complex square matrix of size `n`, the sum
running over the roots of its characteristic polynomial with algebraic multiplicity. It is a
probability measure when the matrix has positive size. -/
def eigenvalueMeasure (A : Matrix n n ℂ) : Measure ℂ :=
  ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ • (A.charpoly.roots.map Measure.dirac).sum

theorem eigenvalueMeasure_def (A : Matrix n n ℂ) :
    A.eigenvalueMeasure =
      ((Fintype.card n : ℕ) : ℝ≥0∞)⁻¹ • (A.charpoly.roots.map Measure.dirac).sum :=
  (rfl)

/-- The eigenvalue measure is the empirical finite measure of the family of roots of the
characteristic polynomial, indexed by the multiset of roots. -/
theorem eigenvalueMeasure_eq_empiricalFiniteMeasure (A : Matrix n n ℂ) :
    A.eigenvalueMeasure = empiricalFiniteMeasure (fun z : A.charpoly.roots ↦ (z : ℂ)) := by
  rw [eigenvalueMeasure_def, empiricalFiniteMeasure_def, ← Finset.smul_sum, Multiset.card_coe,
    IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Finset.sum_eq_multiset_sum,
    Multiset.map_univ]

instance isProbabilityMeasure_eigenvalueMeasure [Nonempty n] (A : Matrix n n ℂ) :
    IsProbabilityMeasure A.eigenvalueMeasure := by
  have : Nonempty A.charpoly.roots := by
    rw [← Fintype.card_pos_iff, Multiset.card_coe, IsAlgClosed.card_roots_eq_natDegree,
      charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  rw [eigenvalueMeasure_eq_empiricalFiniteMeasure]
  infer_instance

instance isFiniteMeasure_eigenvalueMeasure (A : Matrix n n ℂ) :
    IsFiniteMeasure A.eigenvalueMeasure := by
  rw [eigenvalueMeasure_eq_empiricalFiniteMeasure]
  infer_instance

/-- Integrating against the eigenvalue measure averages the integrand over the roots of the
characteristic polynomial, counted with algebraic multiplicity. -/
theorem integral_eigenvalueMeasure (A : Matrix n n ℂ) (f : ℂ → E) :
    ∫ z, f z ∂A.eigenvalueMeasure =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ • (A.charpoly.roots.map f).sum := by
  rw [eigenvalueMeasure_eq_empiricalFiniteMeasure, integral_empiricalFiniteMeasure,
    Multiset.card_coe, IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim,
    Finset.sum_eq_multiset_sum, Multiset.map_univ]

/-- The eigenvalue measure is invariant under conjugation. -/
@[simp]
theorem eigenvalueMeasure_units_conj (M : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    (M.val * A * M.val⁻¹).eigenvalueMeasure = A.eigenvalueMeasure := by
  rw [eigenvalueMeasure_def, eigenvalueMeasure_def, charpoly_units_conj]

/-- The eigenvalue measure of a Hermitian matrix is the pushforward of its spectral measure along
the inclusion `ℝ → ℂ`. -/
theorem eigenvalueMeasure_eq_map_spectralMeasure (hA : A.IsHermitian) :
    A.eigenvalueMeasure = (A.spectralMeasure hA).map ((↑) : ℝ → ℂ) := by
  rw [spectralMeasure_def, map_empiricalFiniteMeasure Complex.measurable_ofReal,
    eigenvalueMeasure_def, empiricalFiniteMeasure_def, ← Finset.smul_sum,
    hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- The eigenvalue measure of a nilpotent matrix of positive size is the Dirac mass at `0`: the
root `0` carries algebraic multiplicity `n`. -/
theorem eigenvalueMeasure_of_isNilpotent [Nonempty n] (hA : IsNilpotent A) :
    A.eigenvalueMeasure = Measure.dirac 0 := by
  have hchar : A.charpoly = X ^ Fintype.card n :=
    sub_eq_zero.1 (isNilpotent_charpoly_sub_pow_of_isNilpotent hA).eq_zero
  rw [eigenvalueMeasure_def, hchar, roots_X_pow, Multiset.map_nsmul, Multiset.map_singleton,
    Multiset.sum_nsmul, Multiset.sum_singleton, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_smul]

end Complex

end Matrix
