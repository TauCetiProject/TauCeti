/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.Seed.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.FormMutation

/-!
# Seed mutation and admissibility

The one-step mutation relation prescribes the new state, form and coordinates. The
coordinates determine the based chart, so there is at most one seed related by a
mutation in a fixed direction. Every mutation preserves admissibility, the unit
condition on the scalar sums of the exchange polynomials at zero columns. In a
division semiring, admissibility is equivalent to invertibility of all exchange elements.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4, for mutation of the form and the based chart.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific Journal of
  Mathematics 277 (2015), §2, for polynomial exchange and coefficient normalization.
-/

public section

namespace TauCeti.Seed

variable {𝕂 R I K B : Type*} [CommMonoidWithZero 𝕂] [CommSemiring R] [Fintype I]
  [DecidableEq I] [Semiring B] [Algebra R B]
  {c : CoefficientSystem 𝕂 R} {row : K ↪ I} {u : Rˣ}

/-- The admissibility condition on a seed requires the realized coefficient sum
of each zero-column exchange polynomial to be a unit in the ambient algebra. -/
def Admissible (s : Seed c row u B) : Prop :=
  ∀ k, (∀ i, s.state.exchange.matrix i k = 0) →
    IsUnit (algebraMap R B (s.state.valueAtOne c k))

theorem admissible_iff {s : Seed c row u B} :
    s.Admissible ↔ ∀ k, (∀ i, s.state.exchange.matrix i k = 0) →
      IsUnit (algebraMap R B (s.state.valueAtOne c k)) :=
  (Iff.rfl)

/-- In a zero column, the scalar sum of coefficients controls the invertibility
of the exchange element even in a noncommutative ambient semiring. -/
theorem isUnit_exchangeElement_iff_of_column_eq_zero (s : Seed c row u B) {k : K}
    (h : ∀ i, s.state.exchange.matrix i k = 0) :
    IsUnit (s.exchangeElement k) ↔ IsUnit (algebraMap R B (s.state.valueAtOne c k)) := by
  rw [s.exchangeElement_of_column_eq_zero h, Algebra.smul_def, Units.isUnit_mul_units]

section Mutation

variable [DecidableEq K] {s t t' : Seed c row u B} {k : K}

/-- Mutation updates the normalized state and alternating form, retains the weights,
and replaces exactly the chosen coordinate by the exchange element. Its invertibility
is forced by equality with a coordinate of the target based chart. -/
structure IsMutation (s : Seed c row u B) (k : K) (t : Seed c row u B) : Prop where
  state_eq : t.state = s.state.mutation c k
  formMatrix_eq : t.formMatrix = formMutation row s.state.exchange.matrix s.formMatrix k
  coordinate_eq : (↑(t.chart.monomial (Finsupp.single (row k) 1)) : B) = s.exchangeElement k
  coordinate_eq_of_ne : ∀ i, i ≠ row k →
    t.chart.monomial (Finsupp.single i 1) = s.chart.monomial (Finsupp.single i 1)

/-- A direction with a mutation target has an invertible exchange element. -/
theorem IsMutation.isUnit_exchangeElement (h : s.IsMutation k t) :
    IsUnit (s.exchangeElement k) :=
  h.coordinate_eq ▸ (t.chart.monomial (Finsupp.single (row k) 1)).isUnit

/-- Mutating the matrix and the form of a seed together keeps column compatibility with the
same weights. -/
theorem isColumnCompatible_formMutation (s : Seed c row u B) (k : K) :
    (matrixMutation row s.state.exchange.matrix k).IsColumnCompatible row
      (formMutation row s.state.exchange.matrix s.formMatrix k) s.weights := by
  have hs : s.state.exchange.matrix.transpose * s.formMatrix =
      Matrix.of fun i j ↦ if j = row i then s.weights i else 0 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, eq_comm,
      Seed.formMatrix_def] using Matrix.isColumnCompatible_iff.mp s.compatibility i j
  have hm := transpose_matrixMutation_mul_formMutation row s.state.exchange.matrix
    s.isAlt_formMatrix s.state.exchange.isSkewSymmetrizer hs k
  refine Matrix.isColumnCompatible_iff.mpr fun i j ↦ ?_
  simpa [Matrix.mul_apply, eq_comm] using congrFun (congrFun hm i) j

/-- Compatibility determines the same weights after mutation. -/
theorem IsMutation.weights_eq (h : s.IsMutation k t) : t.weights = s.weights := by
  funext j
  rw [t.weights_apply, h.state_eq, ExchangeData.mutation_exchange,
    ExchangeMatrix.mutation_matrix, h.formMatrix_eq]
  simpa using Matrix.isColumnCompatible_iff.mp (s.isColumnCompatible_formMutation k) j (row j)

/-- The mutation relation is single-valued. -/
theorem IsMutation.eq (h : s.IsMutation k t) (h' : s.IsMutation k t') : t = t' := by
  refine Seed.ext_coordinate (h.state_eq.trans h'.state_eq.symm) ?_ ?_
  · apply (LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne).injective
    rw [← Seed.formMatrix_def, ← Seed.formMatrix_def, h.formMatrix_eq, h'.formMatrix_eq]
  · intro i
    obtain rfl | hi := eq_or_ne i (row k)
    · exact Units.ext (h.coordinate_eq.trans h'.coordinate_eq.symm)
    · exact (h.coordinate_eq_of_ne i hi).trans (h'.coordinate_eq_of_ne i hi).symm

/-- Mutation preserves and reflects admissibility since the zero columns and
their realized coefficient sums stay fixed. -/
theorem IsMutation.admissible_iff (h : s.IsMutation k t) : t.Admissible ↔ s.Admissible := by
  rw [Seed.admissible_iff, Seed.admissible_iff, h.state_eq]
  refine forall_congr' fun j ↦ ?_
  have hcol : (∀ i, (s.state.mutation c k).exchange.matrix i j = 0) ↔
      ∀ i, s.state.exchange.matrix i j = 0 := by
    simpa only [ExchangeData.mutation_exchange, ExchangeMatrix.mutation_matrix] using
      (matrixMutation_column_eq_zero_iff (row := row) (B := s.state.exchange.matrix) (j := j) k)
  rw [hcol]
  exact imp_congr_ctx Iff.rfl fun hj ↦ by
    rw [ExchangeData.valueAtOne_mutation_of_column_eq_zero s.isNormalized hj k]

/-- Applying an injective ambient algebra map to both seeds preserves mutation. -/
theorem IsMutation.map {B' : Type*} [Semiring B'] [Algebra R B']
    (h : s.IsMutation k t) (f : B →ₐ[R] B') (hf : Function.Injective f) :
    (s.map f hf).IsMutation k (t.map f hf) where
  state_eq := by simpa using h.state_eq
  formMatrix_eq := by simpa [Seed.formMatrix_def] using h.formMatrix_eq
  coordinate_eq := by simpa using congrArg f h.coordinate_eq
  coordinate_eq_of_ne i hi := by simp [h.coordinate_eq_of_ne i hi]

/-- A morphism of coefficient systems preserves mutation in the same ambient algebra. -/
theorem IsMutation.mapCoefficients {𝕂' : Type*} [CommMonoidWithZero 𝕂']
    {c' : CoefficientSystem 𝕂' R} (h : s.IsMutation k t) (f : c.Hom c') :
    (s.mapCoefficients f).IsMutation k (t.mapCoefficients f) where
  state_eq := by simp [h.state_eq]
  formMatrix_eq := by simpa [Seed.formMatrix_def] using h.formMatrix_eq
  coordinate_eq := by simpa using h.coordinate_eq
  coordinate_eq_of_ne i hi := by simpa using h.coordinate_eq_of_ne i hi

end Mutation

section DivisionSemiring

variable {D : Type*} [DivisionSemiring D] [Algebra R D]

/-- Over a division semiring, a seed is admissible exactly when its exchange
elements in all mutable directions are units. -/
theorem admissible_iff_isUnit_exchangeElement (s : Seed c row u D) :
    s.Admissible ↔ ∀ k, IsUnit (s.exchangeElement k) := by
  rw [admissible_iff]
  constructor
  · intro h k
    by_cases hz : ∀ i, s.state.exchange.matrix i k = 0
    · exact (s.isUnit_exchangeElement_iff_of_column_eq_zero hz).mpr (h k hz)
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      let _ : Nontrivial R := (algebraMap R D).domain_nontrivial
      exact (s.exchangeElement_ne_zero_of_matrix_ne_zero hi).isUnit
  · intro h k hz
    exact (s.isUnit_exchangeElement_iff_of_column_eq_zero hz).mp (h k)

end DivisionSemiring

end TauCeti.Seed
