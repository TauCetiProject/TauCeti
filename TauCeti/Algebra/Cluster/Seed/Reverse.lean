/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.Seed.Mutation

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Reversing seed mutation

The exchange relation reverses in an arbitrary ambient semiring. The target chart
already supplies the unit needed to cancel the mutated coordinate.

This extends the involutivity of quantum seed mutation in Berenstein and Zelevinsky,
*Quantum cluster algebras*, Advances in Mathematics 195 (2005), Proposition 4.10.
Reversal of the selected polynomial matches its reflected coefficients with the
original exchange terms one by one.
-/

public section

namespace TauCeti.Seed

variable {𝕂 R I K B : Type*} [CommMonoidWithZero 𝕂] [CommSemiring R] [Fintype I]
  [DecidableEq I] [DecidableEq K] [Semiring B] [Algebra R B]
  {c : CoefficientSystem 𝕂 R} {row : K ↪ I} {u : Rˣ}
  {s t : Seed c row u B} {k : K}

private noncomputable def latticeMutation (s : Seed c row u B) (k : K) :
    (I →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ) :=
  Matrix.toLin Finsupp.basisSingleOne Finsupp.basisSingleOne
    (matrixMutationLeft row s.state.exchange.matrix k 1)

omit [DecidableEq K] in
private theorem latticeMutation_apply (s : Seed c row u B) (k : K) (a : I →₀ ℤ) :
    latticeMutation s k a = a + a (row k) •
      (Finsupp.equivFunOnFinite.symm (fun i ↦ (-s.state.exchange.matrix i k)⁺) -
        (2 : ℤ) • Finsupp.single (row k) 1) := by
  classical
  ext i
  have h := congrFun (Matrix.repr_toLin Finsupp.basisSingleOne Finsupp.basisSingleOne
    (matrixMutationLeft row s.state.exchange.matrix k 1) a) i
  simp only [Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply] at h
  have hcol := congrArg (fun M : Matrix I Unit ℤ ↦ M i ())
    (Matrix.replicateCol_mulVec (ι := Unit)
      (matrixMutationLeft row s.state.exchange.matrix k 1) (a : I → ℤ))
  simp only [Matrix.replicateCol_apply] at hcol
  rw [latticeMutation, h, hcol, matrixMutationLeft_mul_apply]
  by_cases hi : i = row k
  · subst i
    simp [s.state.exchange.matrix_row_self k]
    ring
  · simp [hi, Finsupp.single_eq_of_ne hi, mul_comm]

private theorem mutation_form (h : s.IsMutation k t) :
    t.form = s.form.comp (latticeMutation s k) (latticeMutation s k) := by
  apply (LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne).injective
  rw [LinearMap.BilinForm.toMatrix_comp Finsupp.basisSingleOne Finsupp.basisSingleOne]
  simpa only [← formMatrix_def, latticeMutation, LinearMap.toMatrix_toLin,
    formMutation_def] using h.formMatrix_eq

private theorem mutation_form_off (h : s.IsMutation k t) {a b : I →₀ ℤ}
    (ha : a (row k) = 0) (hb : b (row k) = 0) : t.form a b = s.form a b := by
  rw [mutation_form h, LinearMap.BilinForm.comp_apply,
    latticeMutation_apply, latticeMutation_apply, ha, hb]
  simp

/-- Seed mutation fixes every normalized monomial whose exponent avoids the changed coordinate. -/
theorem IsMutation.monomial_eq_of_apply_eq_zero (h : s.IsMutation k t) {a : I →₀ ℤ}
    (ha : a (row k) = 0) : t.chart.monomial a = s.chart.monomial a := by
  let f := Finsupp.lmapDomain ℤ ℤ (Subtype.val : {i : I // i ≠ row k} → I)
  have hf : Function.Injective f := Finsupp.mapDomain_injective Subtype.val_injective
  have hzero (b : {i : I // i ≠ row k} →₀ ℤ) : f b (row k) = 0 := by
    exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  have he : ∀ a b, t.form (f a) (f b) = (s.form.comp f f) a b :=
    fun a b ↦ mutation_form_off h (hzero a) (hzero b)
  have hs : ∀ a b, s.form (f a) (f b) = (s.form.comp f f) a b := by
    intro a b
    rw [LinearMap.BilinForm.comp_apply]
  have hh : t.chart.comap f hf he = s.chart.comap f hf hs := by
    apply BasedChart.ext_coordinate Finsupp.basisSingleOne
    intro i
    rw [BasedChart.coordinate_def, BasedChart.coordinate_def, BasedChart.comap_monomial,
      BasedChart.comap_monomial]
    simpa only [Finsupp.coe_basisSingleOne,
      BasedChart.comap_monomial, f, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single] using h.coordinate_eq_of_ne i.val i.property
  obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff
    (Subtype.val : {i : I // i ≠ row k} → I) Subtype.val_injective a).mpr fun i hi ↦ by
      have hrow : i = row k := by simpa using hi
      exact hrow ▸ ha
  have hmon := congrArg (fun M ↦ M.monomial b) hh
  simpa only [BasedChart.comap_monomial, f, Finsupp.lmapDomain_apply, hb] using hmon

private noncomputable def dividedVector (s : Seed c row u B) (k : K) : I →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (s.state.dividedColumn k)

private noncomputable def negativeVector (s : Seed c row u B) (k : K) : I →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (s.state.dividedColumn k i)⁻)

omit [DecidableEq K] in
private theorem negative_matrix (s : Seed c row u B) (k : K) :
    Finsupp.equivFunOnFinite.symm (fun i ↦ (-s.state.exchange.matrix i k)⁺) =
      ((s.state.polynomial k).degree : ℤ) • negativeVector s k := by
  ext i
  simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.smul_apply, smul_eq_mul,
    negativeVector]
  rw [← s.state.mul_dividedColumn k i]
  simp only [posPart_def, negPart_def, ← mul_neg]
  simpa only [mul_zero] using
    (mul_max_of_nonneg (-s.state.dividedColumn k i) 0 (s.state.degree_pos_int k).le).symm

omit [DecidableEq K] in
private theorem numerator_vector (s : Seed c row u B) (k : K) {l : ℕ}
    (hl : l ≤ (s.state.polynomial k).degree) :
    s.state.exchangeExponent k l + Finsupp.single (row k) 1 =
      (l : ℤ) • dividedVector s k +
        ((s.state.polynomial k).degree : ℤ) • negativeVector s k := by
  ext i
  simp only [dividedVector, negativeVector, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul]
  by_cases hi : i = row k
  · subst i
    simp
  · rw [s.state.exchangeExponent_apply_of_ne k l hi, Finsupp.single_eq_of_ne hi,
      Nat.cast_sub hl]
    have hp := posPart_sub_negPart (s.state.dividedColumn k i)
    linear_combination (l : ℤ) * hp

omit [DecidableEq K] in
private theorem dividedVector_pair (s : Seed c row u B) (k : K) {a : I →₀ ℤ}
    (ha : a (row k) = 0) : s.form (dividedVector s k) a = 0 := by
  have hb (i : I) (hi : i ≠ row k) :
      s.form (dividedVector s k) (Finsupp.single i 1) = 0 := by
    have hsum : s.form (dividedVector s k) (Finsupp.single i 1) =
        ∑ j, dividedVector s k j * s.form (Finsupp.single j 1) (Finsupp.single i 1) := by
      conv_lhs => rw [← Finsupp.univ_sum_single (dividedVector s k)]
      simp only [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finsupp.smul_single_one j (dividedVector s k j), map_smul, LinearMap.smul_apply,
        smul_eq_mul]
    apply (mul_left_cancel₀ (s.state.degree_ne_zero_int k))
    rw [mul_zero, hsum, Finset.mul_sum]
    simp only [dividedVector, Finsupp.coe_equivFunOnFinite_symm, ← mul_assoc,
      s.state.mul_dividedColumn, ← s.formMatrix_apply]
    have hc := Matrix.isColumnCompatible_iff.mp s.compatibility k i
    simpa only [ite_eq_right (Ne.symm hi), ← s.formMatrix_def] using hc
  rw [← Finsupp.univ_sum_single a, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = row k
  · subst i
    simp [ha]
  · rw [← Finsupp.smul_single_one i (a i), map_smul, hb i hi, smul_zero]

omit [DecidableEq K] in
private theorem numerator_pair (s : Seed c row u B) (k : K) {l : ℕ}
    (hl : l ≤ (s.state.polynomial k).degree) :
    s.form (s.state.exchangeExponent k l + Finsupp.single (row k) 1)
      (negativeVector s k) = 0 := by
  rw [numerator_vector s k hl, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    s.isAlt.self_eq_zero, dividedVector_pair s k, smul_zero, smul_zero, add_zero]
  simp [negativeVector]

private theorem mutation_numerator_pair (h : s.IsMutation k t) {l : ℕ}
    (hl : l ≤ (s.state.polynomial k).degree) :
    t.form (s.state.exchangeExponent k l + Finsupp.single (row k) 1)
        (Finsupp.single (row k) 1) =
      s.form (Finsupp.single (row k) 1)
        (s.state.exchangeExponent k l + Finsupp.single (row k) 1) := by
  have hn : (s.state.exchangeExponent k l + Finsupp.single (row k) 1 : I →₀ ℤ)
      (row k) = 0 := by
    simp
  rw [mutation_form h, LinearMap.BilinForm.comp_apply,
    latticeMutation_apply, latticeMutation_apply, hn, zero_smul, add_zero,
    Finsupp.single_eq_same, one_smul, negative_matrix]
  have he : Finsupp.single (row k) 1 +
      (((s.state.polynomial k).degree : ℤ) • negativeVector s k -
        (2 : ℤ) • Finsupp.single (row k) 1) =
      -Finsupp.single (row k) 1 +
        ((s.state.polynomial k).degree : ℤ) • negativeVector s k := by module
  rw [he, map_add, map_neg, map_smul, numerator_pair s k hl, smul_zero, add_zero]
  exact s.isAlt.neg_eq _ _

private theorem mutation_exchange_term (h : s.IsMutation k t) {l : ℕ}
    (hl : l ≤ (s.state.polynomial k).degree) :
    (t.chart.monomial (s.state.exchangeExponent k l) : B) *
        t.chart.monomial (Finsupp.single (row k) 1) =
      (s.chart.monomial (Finsupp.single (row k) 1) : B) *
        s.chart.monomial (s.state.exchangeExponent k l) := by
  rw [t.chart.val_monomial_mul, s.chart.val_monomial_mul]
  have hp := mutation_numerator_pair h hl
  simp only [map_add, LinearMap.add_apply, s.isAlt.self_eq_zero,
    t.isAlt.self_eq_zero, add_zero] at hp
  rw [hp, h.monomial_eq_of_apply_eq_zero (by simp), add_comm]

private theorem mutation_exchangeElement_mul_coordinate (h : s.IsMutation k t) :
    t.exchangeElement k * (t.chart.monomial (Finsupp.single (row k) 1) : B) =
      (s.chart.monomial (Finsupp.single (row k) 1) : B) * s.exchangeElement k := by
  rw [t.exchangeElement_def, s.exchangeElement_def, Finset.sum_mul, Finset.mul_sum]
  simp only [h.state_eq, ExchangeData.mutation_polynomial,
    ExchangeData.mutatedPolynomial_self, ExchangePolynomial.degree_reverse]
  have hterm (l : ℕ) (hl : l ∈ Finset.range ((s.state.polynomial k).degree + 1)) :
      c.toScalar (((s.state.polynomial k).reverse).coeff l) •
          (t.chart.monomial ((s.state.mutation c k).exchangeExponent k l) : B) *
          t.chart.monomial (Finsupp.single (row k) 1) =
        (s.chart.monomial (Finsupp.single (row k) 1) : B) *
          (c.toScalar ((s.state.polynomial k).coeff ((s.state.polynomial k).degree - l)) •
            (s.chart.monomial (s.state.exchangeExponent k
              ((s.state.polynomial k).degree - l)) : B)) := by
    have hl' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [ExchangePolynomial.coeff_reverse, ite_eq_left hl',
      ExchangeData.exchangeExponent_mutation_self c s.state hl', smul_mul_assoc,
      Algebra.mul_smul_comm, mutation_exchange_term h (Nat.sub_le _ _)]
  rw [Finset.sum_congr rfl hterm]
  simpa only [Nat.add_sub_cancel] using
    (Finset.sum_range_reflect (fun l ↦
      (s.chart.monomial (Finsupp.single (row k) 1) : B) *
        c.toScalar ((s.state.polynomial k).coeff l) •
          (s.chart.monomial (s.state.exchangeExponent k l) : B))
      ((s.state.polynomial k).degree + 1))

/-- Mutating a based seed reverses the exchange relation in every ambient semiring. -/
theorem IsMutation.exchangeElement_eq_coordinate (h : s.IsMutation k t) :
    t.exchangeElement k = (s.chart.monomial (Finsupp.single (row k) 1) : B) := by
  apply (t.chart.monomial (Finsupp.single (row k) 1)).isUnit.mul_right_cancel
  rw [mutation_exchangeElement_mul_coordinate h, h.coordinate_eq]

/-- One-step mutation is symmetric, including zero columns and zero compatibility weights. -/
theorem IsMutation.symm (h : s.IsMutation k t) : t.IsMutation k s := by
  refine ⟨?_, ?_, h.exchangeElement_eq_coordinate.symm, fun i hi ↦
    (h.coordinate_eq_of_ne i hi).symm⟩
  · rw [h.state_eq, ExchangeData.mutation_mutation s.isNormalized]
  · rw [h.state_eq, ExchangeData.mutation_exchange, ExchangeMatrix.mutation_matrix,
      h.formMatrix_eq]
    exact (formMutation_formMutation row s.state.exchange.matrix s.isAlt_formMatrix k
      (s.state.exchange.matrix_row_self k) (fun j hj ↦ by
        have hc := Matrix.isColumnCompatible_iff.mp s.compatibility k j
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, s.formMatrix_def,
          ite_eq_right (Ne.symm hj)] using hc)).symm

end TauCeti.Seed
