/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.Algebra.Cluster.ExchangeData.Numerator
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Compatibility
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Compatible seeds and exchange elements

A `Seed` combines normalized exchange data, an alternating integral form compatible
with its extended matrix, and a faithful based chart. The compatibility weights can
vanish; they are separate from the positive symmetrizer of the exchange matrix.
The ambient algebra is only a semiring algebra: invertibility of exchange elements
is a further condition, rather than part of the chart or the seed data.
The form matrix also defines an alternating form in the function-space presentation.

`Seed.exchangeElement` is the finite sum of normalized monomials specified by the
exchange polynomial. A nonzero extended column guarantees that this element is
nonzero over any nontrivial scalar semiring. A zero column instead gives the scalar
value of the exchange polynomial at one times the inverse coordinate monomial.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, Journal of the
  American Mathematical Society 15 (2002), §2.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific Journal
  of Mathematics 277 (2015), §2.
-/

public section

namespace TauCeti

/-- A compatible seed with normalized polynomial coefficients and a faithful chart.
The caller's finite enumeration is retained in the matrix compatibility condition. -/
structure Seed {𝕂 R I K : Type*} [CommMonoidWithZero 𝕂] [CommSemiring R]
    [Fintype I] [DecidableEq I] (c : CoefficientSystem 𝕂 R) (row : K ↪ I)
    (u : Rˣ) (B : Type*) [Semiring B] [Algebra R B] where
  /-- The extended exchange matrix and polynomial data. -/
  state : ExchangeData 𝕂 row
  /-- The coefficient data are normalized in the chosen coefficient system. -/
  isNormalized : state.IsNormalized c
  /-- The integral bilinear form on the exponent lattice. -/
  form : LinearMap.BilinForm ℤ (I →₀ ℤ)
  /-- The form is alternating. -/
  isAlt : form.IsAlt
  /-- The diagonal compatibility weights, possibly zero. -/
  weights : K → ℤ
  /-- Compatibility uses the actual matrix of the lattice form in the standard basis. -/
  compatibility : state.exchange.matrix.IsColumnCompatible row
    (form.toMatrix Finsupp.basisSingleOne) weights
  /-- The faithful normalized monomials in the ambient algebra. -/
  chart : BasedChart u form B

namespace Seed

variable {𝕂 R I K B C D : Type*} [CommMonoidWithZero 𝕂] [CommSemiring R]
  [Fintype I] [DecidableEq I] {c : CoefficientSystem 𝕂 R} {row : K ↪ I} {u : Rˣ}
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]

/-- The matrix of the seed's integral form in the standard exponent basis. -/
noncomputable def formMatrix (s : Seed c row u B) : Matrix I I ℤ :=
  s.form.toMatrix Finsupp.basisSingleOne

/-- The form matrix is the native matrix representation of the integral form. -/
theorem formMatrix_def (s : Seed c row u B) :
    s.formMatrix = s.form.toMatrix Finsupp.basisSingleOne :=
  (rfl)

/-- The form matrix records its values on the standard lattice generators. -/
theorem formMatrix_apply (s : Seed c row u B) (i j : I) :
    s.formMatrix i j = s.form (Finsupp.single i 1) (Finsupp.single j 1) :=
  by simp [formMatrix, LinearMap.BilinForm.toMatrix_apply, Finsupp.coe_basisSingleOne]

/-- The form matrix defines an alternating form in the function-space presentation. -/
theorem isAlt_formMatrix (s : Seed c row u B) : s.formMatrix.toBilin'.IsAlt := by
  apply (Matrix.isAlt_toBilin'_iff s.formMatrix).mpr
  constructor
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, formMatrix_apply]
    exact (s.isAlt.neg_eq _ _).symm
  · intro i
    rw [formMatrix_apply]
    exact s.isAlt _

/-- Each weight is the pairing of its exchange column with the corresponding basis vector. -/
theorem weights_apply (s : Seed c row u B) (k : K) :
    s.weights k = ∑ j, s.state.exchange.matrix j k * s.formMatrix j (row k) := by
  symm
  simpa [formMatrix_def] using
    Matrix.isColumnCompatible_iff.mp s.compatibility k (row k)

private theorem weights_eq_of_state_eq_of_form_eq {s t : Seed c row u B}
    (hstate : s.state = t.state) (hform : s.form = t.form) : s.weights = t.weights := by
  funext k
  rw [weights_apply, weights_apply]
  simp only [formMatrix_def, hstate, hform]

/-- A seed is determined by its exchange data, form and normalized monomials. -/
@[ext]
theorem ext {s t : Seed c row u B} (hstate : s.state = t.state)
    (hform : s.form = t.form)
    (hmonomial : ∀ a, s.chart.monomial a = t.chart.monomial a) : s = t := by
  have hweights := weights_eq_of_state_eq_of_form_eq hstate hform
  cases s
  cases t
  cases hstate
  cases hform
  cases hweights
  congr
  exact BasedChart.ext hmonomial

/-- Standard coordinate units suffice for seed extensionality. -/
theorem ext_coordinate {s t : Seed c row u B} (hstate : s.state = t.state)
    (hform : s.form = t.form)
    (hcoordinate : ∀ i, s.chart.monomial (Finsupp.single i 1) =
      t.chart.monomial (Finsupp.single i 1)) : s = t := by
  have hweights := weights_eq_of_state_eq_of_form_eq hstate hform
  cases s
  cases t
  cases hstate
  cases hform
  cases hweights
  congr
  apply BasedChart.ext_coordinate Finsupp.basisSingleOne
  simpa only [BasedChart.coordinate_def, Finsupp.coe_basisSingleOne] using hcoordinate

/-- The exchange element in direction `k`, expressed in normalized chart monomials. -/
noncomputable def exchangeElement (s : Seed c row u B) (k : K) : B :=
  ∑ l ∈ Finset.range ((s.state.polynomial k).degree + 1),
    c.toScalar ((s.state.polynomial k).coeff l) •
      (s.chart.monomial (s.state.exchangeExponent k l) : B)

/-- The characteristic finite-sum formula for the exchange element. -/
theorem exchangeElement_def (s : Seed c row u B) (k : K) :
    s.exchangeElement k =
      ∑ l ∈ Finset.range ((s.state.polynomial k).degree + 1),
        c.toScalar ((s.state.polynomial k).coeff l) •
          (s.chart.monomial (s.state.exchangeExponent k l) : B) :=
  (rfl)

/-- The exchange element is the evaluation of its formal based-torus sum. -/
theorem exchangeElement_eq_eval (s : Seed c row u B) (k : K) :
    s.exchangeElement k = s.chart.eval
      (∑ l ∈ Finset.range ((s.state.polynomial k).degree + 1),
        c.toScalar ((s.state.polynomial k).coeff l) •
          QuantumTorus.monomial u s.form (s.state.exchangeExponent k l)) := by
  simp [exchangeElement]

/-- Distinct exchange exponents prevent cancellation when the extended column is nonzero. -/
theorem exchangeElement_ne_zero_of_matrix_ne_zero [Nontrivial R] (s : Seed c row u B)
    {k : K} {i : I} (hi : s.state.exchange.matrix i k ≠ 0) : s.exchangeElement k ≠ 0 := by
  intro hzero
  rw [exchangeElement_eq_eval, s.chart.eval_eq_zero_iff] at hzero
  have hc := congrArg (fun z ↦ (QuantumTorus.basis u s.form).repr z
    (s.state.exchangeExponent k 0)) hzero
  simp only [map_sum, map_smul, QuantumTorus.basis_repr_monomial,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
    Finsupp.zero_apply] at hc
  rw [Finset.sum_eq_single_of_mem 0 (by simp)] at hc
  · exact ((s.state.polynomial k).isUnit_coeff_zero.map c.toScalar).ne_zero (by simpa using hc)
  · intro l hl hl0
    have hl : l ≤ (s.state.polynomial k).degree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hne := (s.state.injOn_exchangeExponent_of_matrix_ne_zero hi).ne hl
      (Nat.zero_le _) hl0
    simp [hne]

/-- For a zero column, the exchange element is the realized polynomial value at one
acting by scalars on the inverse coordinate monomial. -/
theorem exchangeElement_of_column_eq_zero (s : Seed c row u B) {k : K}
    (h0 : ∀ i, s.state.exchange.matrix i k = 0) :
    s.exchangeElement k = s.state.valueAtOne c k •
      (s.chart.monomial (Finsupp.single (row k) (-1)) : B) := by
  simp only [exchangeElement, s.state.exchangeExponent_of_column_eq_zero h0]
  rw [← Finset.sum_smul]
  rw [s.state.valueAtOne_def]

/-- Transport a seed through an injective map of ambient algebras. -/
noncomputable def map (s : Seed c row u B) (f : B →ₐ[R] C)
    (hf : Function.Injective f) :
    Seed c row u C where
  state := s.state
  isNormalized := s.isNormalized
  form := s.form
  isAlt := s.isAlt
  weights := s.weights
  compatibility := s.compatibility
  chart := s.chart.map f hf

@[simp]
theorem map_state (s : Seed c row u B) (f : B →ₐ[R] C) (hf : Function.Injective f) :
    (s.map f hf).state = s.state := (rfl)

@[simp]
theorem map_form (s : Seed c row u B) (f : B →ₐ[R] C) (hf : Function.Injective f) :
    (s.map f hf).form = s.form := (rfl)

@[simp]
theorem map_weights (s : Seed c row u B) (f : B →ₐ[R] C) (hf : Function.Injective f) :
    (s.map f hf).weights = s.weights := (rfl)

/-- Ambient transport applies the given homomorphism to each normalized monomial. -/
@[simp]
theorem map_monomial (s : Seed c row u B) (f : B →ₐ[R] C) (hf : Function.Injective f)
    (a : I →₀ ℤ) : (s.map f hf).chart.monomial a = Units.map f (s.chart.monomial a) := by
  simp only [map, BasedChart.map_monomial]

/-- Ambient transport commutes with exchange evaluation. -/
@[simp]
theorem exchangeElement_map (s : Seed c row u B) (f : B →ₐ[R] C) (hf : Function.Injective f)
    (k : K) : (s.map f hf).exchangeElement k = f (s.exchangeElement k) := by
  simp [exchangeElement]

@[simp]
theorem map_id (s : Seed c row u B) : s.map (AlgHom.id R B) Function.injective_id = s := by
  apply ext (s := s.map (AlgHom.id R B) Function.injective_id) (t := s) rfl rfl
  intro a
  exact congrArg (fun M : BasedChart u s.form B ↦ M.monomial a) (BasedChart.map_id s.chart)

/-- Successive ambient transports agree with transport along the composite. -/
@[simp]
theorem map_map (s : Seed c row u B) (f : B →ₐ[R] C) (hf : Function.Injective f)
    (g : C →ₐ[R] D) (hg : Function.Injective g) :
    (s.map f hf).map g hg = s.map (g.comp f) (hg.comp hf) := by
  apply ext (s := (s.map f hf).map g hg) (t := s.map (g.comp f) (hg.comp hf)) rfl rfl
  intro a
  exact congrArg (fun M : BasedChart u s.form D ↦ M.monomial a)
    (BasedChart.map_map s.chart f hf g hg)

section Coefficients

variable {𝕂' : Type*} [CommMonoidWithZero 𝕂'] {c' : CoefficientSystem 𝕂' R}

/-- Transport the coefficient presentation along a morphism of coefficient systems.
The ambient chart and integral compatibility data are preserved. -/
noncomputable def mapCoefficients (s : Seed c row u B) (f : c.Hom c') : Seed c' row u B where
  state := s.state.map f.toMonoidWithZeroHom
  isNormalized := s.isNormalized.map f
  form := s.form
  isAlt := s.isAlt
  weights := s.weights
  compatibility := by simpa using s.compatibility
  chart := s.chart

@[simp]
theorem mapCoefficients_state (s : Seed c row u B) (f : c.Hom c') :
    (s.mapCoefficients f).state = s.state.map f.toMonoidWithZeroHom :=
  (rfl)

@[simp]
theorem mapCoefficients_form (s : Seed c row u B) (f : c.Hom c') :
    (s.mapCoefficients f).form = s.form :=
  (rfl)

@[simp]
theorem mapCoefficients_weights (s : Seed c row u B) (f : c.Hom c') :
    (s.mapCoefficients f).weights = s.weights :=
  (rfl)

/-- Coefficient transport preserves all normalized chart monomials. -/
@[simp]
theorem mapCoefficients_monomial (s : Seed c row u B) (f : c.Hom c') (a : I →₀ ℤ) :
    (s.mapCoefficients f).chart.monomial a = s.chart.monomial a :=
  (rfl)

/-- A change of coefficient presentation preserves the evaluated exchange element. -/
@[simp]
theorem exchangeElement_mapCoefficients (s : Seed c row u B) (f : c.Hom c') (k : K) :
    (s.mapCoefficients f).exchangeElement k = s.exchangeElement k := by
  simp [exchangeElement, CoefficientSystem.Hom.toScalar_comp_apply]

@[simp]
theorem mapCoefficients_id (s : Seed c row u B) :
    s.mapCoefficients (CoefficientSystem.Hom.id c) = s := by
  apply ext (s := s.mapCoefficients (CoefficientSystem.Hom.id c)) (t := s)
  · simp
  · simp
  · intro a
    simp

/-- Successive coefficient transports agree with transport along the composite. -/
@[simp]
theorem mapCoefficients_mapCoefficients {𝕂'' : Type*} [CommMonoidWithZero 𝕂'']
    {c'' : CoefficientSystem 𝕂'' R} (s : Seed c row u B) (f : c.Hom c') (g : c'.Hom c'') :
    (s.mapCoefficients f).mapCoefficients g = s.mapCoefficients (g.comp f) := by
  apply ext (s := (s.mapCoefficients f).mapCoefficients g)
    (t := s.mapCoefficients (g.comp f))
  · simp
  · simp
  · intro a
    simp

end Coefficients

end Seed

end TauCeti
