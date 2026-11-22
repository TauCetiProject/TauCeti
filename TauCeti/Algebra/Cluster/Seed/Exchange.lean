/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.Seed.Mutation
public import TauCeti.Algebra.Cluster.OneExchange.BasedChart

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Constructing and reversing seed mutation

When the exchange element of a seed in direction `k` is a unit of the ambient algebra, the
mutated seed exists (`Seed.mutation`), and it is the only seed related to the original one by
mutation in direction `k` (`Seed.existsUnique_isMutation`). Its form is the pullback of the
original form along the lattice involution `a ↦ a + a_k ([-b_k]₊ - 2 e_k)`, whose matrix
congruence is `formMutation`. Its chart exchanges the coordinate at `row k` for the exchange
element (`BasedChart.exchange`): column compatibility makes the exchange element quasi-commute
with the monomials in the other coordinates (`Seed.exchangeElement_mul_monomial`), and the
faithfulness of the new chart is a consequence, not an assumption. No commutativity, division
ring or rank hypothesis is needed.

Conversely, the exchange relation reverses in an arbitrary ambient semiring: the target chart
already supplies the unit needed to cancel the mutated coordinate, so mutating twice in the same
direction recovers the seed. Reversal of the selected polynomial matches its reflected
coefficients with the original exchange terms one by one.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), Propositions 4.9 and 4.10, for the mutated toric frame and the
  involutivity of quantum seed mutation, which this extends to polynomial exchange and
  arbitrary ambient semirings.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific Journal of
  Mathematics 277 (2015), §2, for polynomial exchange.
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

omit [DecidableEq K] in
private theorem toMatrix_comp_latticeMutation (s : Seed c row u B) (k : K) :
    LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne
        (s.form.comp (latticeMutation s k) (latticeMutation s k)) =
      formMutation row s.state.exchange.matrix s.formMatrix k := by
  rw [LinearMap.BilinForm.toMatrix_comp Finsupp.basisSingleOne Finsupp.basisSingleOne]
  simp only [← formMatrix_def, latticeMutation, LinearMap.toMatrix_toLin, formMutation_def]

private theorem mutation_form (h : s.IsMutation k t) :
    t.form = s.form.comp (latticeMutation s k) (latticeMutation s k) := by
  apply (LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne).injective
  rw [toMatrix_comp_latticeMutation, ← formMatrix_def, h.formMatrix_eq]

omit [DecidableEq K] in
private theorem comp_latticeMutation_apply_of_apply_eq_zero (s : Seed c row u B) (k : K)
    {a b : I →₀ ℤ} (ha : a (row k) = 0) (hb : b (row k) = 0) :
    s.form.comp (latticeMutation s k) (latticeMutation s k) a b = s.form a b := by
  rw [LinearMap.BilinForm.comp_apply, latticeMutation_apply, latticeMutation_apply, ha, hb]
  simp

private theorem mutation_form_off (h : s.IsMutation k t) {a b : I →₀ ℤ}
    (ha : a (row k) = 0) (hb : b (row k) = 0) : t.form a b = s.form a b := by
  rw [mutation_form h]
  exact comp_latticeMutation_apply_of_apply_eq_zero s k ha hb

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

/-! ### Existence of mutation -/

omit [DecidableEq K] in
private theorem latticeMutation_single_row_self (s : Seed c row u B) (k : K) :
    latticeMutation s k (Finsupp.single (row k) 1) = s.state.exchangeExponent k 0 := by
  have h := numerator_vector s k (Nat.zero_le _)
  rw [latticeMutation_apply, negative_matrix, Finsupp.single_eq_same, one_smul]
  linear_combination (norm := module) -h

omit [DecidableEq K] in
/-- The pairing of an exchange exponent with an exponent in the other coordinates does not
depend on the summand. -/
private theorem form_exchangeExponent_of_apply_eq_zero (s : Seed c row u B) (k : K) {l : ℕ}
    (hl : l ≤ (s.state.polynomial k).degree) {a : I →₀ ℤ} (ha : a (row k) = 0) :
    s.form (s.state.exchangeExponent k l) a = s.form (s.state.exchangeExponent k 0) a := by
  have hl' := numerator_vector s k hl
  have h0 := numerator_vector s k (Nat.zero_le _)
  have hsub : s.state.exchangeExponent k l =
      s.state.exchangeExponent k 0 + (l : ℤ) • dividedVector s k := by
    linear_combination (norm := module) hl' - h0
  rw [hsub, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    dividedVector_pair s k ha, smul_zero, add_zero]

omit [DecidableEq K] in
/-- The exchange element quasi-commutes with every monomial in the coordinates other
than `row k`. -/
theorem exchangeElement_mul_monomial (s : Seed c row u B) (k : K) {a : I →₀ ℤ}
    (ha : a (row k) = 0) :
    s.exchangeElement k * s.chart.monomial a =
      ((u ^ (2 * s.form (s.state.exchangeExponent k 0) a) : Rˣ) : R) •
        ((s.chart.monomial a : B) * s.exchangeElement k) := by
  rw [exchangeElement_def, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [smul_mul_assoc, s.chart.val_monomial_mul_monomial_eq_smul_mul s.isAlt,
    form_exchangeExponent_of_apply_eq_zero s k hl' ha, Algebra.mul_smul_comm, smul_comm]

omit [DecidableEq K] in
private theorem exchangeElement_mul_coordinate_mem (s : Seed c row u B) (k : K) :
    s.exchangeElement k * s.chart.monomial (Finsupp.single (row k) 1) ∈
      Submodule.span R
        (Set.range fun a : {a : I →₀ ℤ // a (row k) = 0} ↦ (s.chart.monomial a : B)) := by
  rw [exchangeElement_def, Finset.sum_mul]
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  rw [smul_mul_assoc, BasedChart.val_monomial_mul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨_, by simp⟩, rfl⟩))

omit [DecidableEq K] in
private theorem comp_latticeMutation_single_row_self (s : Seed c row u B) (k : K) {a : I →₀ ℤ}
    (ha : a (row k) = 0) :
    s.form.comp (latticeMutation s k) (latticeMutation s k) (Finsupp.single (row k) 1) a =
      s.form (s.state.exchangeExponent k 0) a := by
  rw [LinearMap.BilinForm.comp_apply, latticeMutation_single_row_self, latticeMutation_apply, ha,
    zero_smul, add_zero]

omit [DecidableEq K] in
private theorem isAlt_comp_latticeMutation (s : Seed c row u B) (k : K) :
    (s.form.comp (latticeMutation s k) (latticeMutation s k)).IsAlt := by
  intro a
  exact s.isAlt _

/-- The mutation of a seed in a direction whose exchange element is a unit. It has the
mutated state and form and the same weights; its chart replaces the coordinate at `row k`
by the exchange element and keeps the other coordinates. -/
noncomputable def mutation (s : Seed c row u B) (k : K) (hE : IsUnit (s.exchangeElement k)) :
    Seed c row u B where
  state := s.state.mutation c k
  isNormalized := s.isNormalized.mutation k
  form := s.form.comp (latticeMutation s k) (latticeMutation s k)
  isAlt := isAlt_comp_latticeMutation s k
  weights := s.weights
  compatibility := by
    rw [toMatrix_comp_latticeMutation, ExchangeData.mutation_exchange,
      ExchangeMatrix.mutation_matrix]
    exact s.isColumnCompatible_formMutation k
  chart := s.chart.exchange s.isAlt (isAlt_comp_latticeMutation s k) (row k) hE.unit
    (fun _ _ ha hb ↦ comp_latticeMutation_apply_of_apply_eq_zero s k ha hb)
    (fun a ha ↦ by
      rw [comp_latticeMutation_single_row_self s k ha, IsUnit.unit_spec]
      exact s.exchangeElement_mul_monomial k ha)
    (by simpa using exchangeElement_mul_coordinate_mem s k)

section Mutation

variable (s : Seed c row u B) (k : K)

@[simp]
theorem mutation_state (hE : IsUnit (s.exchangeElement k)) :
    (s.mutation k hE).state = s.state.mutation c k :=
  (rfl)

@[simp]
theorem mutation_weights (hE : IsUnit (s.exchangeElement k)) :
    (s.mutation k hE).weights = s.weights :=
  (rfl)

@[simp]
theorem formMatrix_mutation (hE : IsUnit (s.exchangeElement k)) :
    (s.mutation k hE).formMatrix = formMutation row s.state.exchange.matrix s.formMatrix k := by
  rw [formMatrix_def]
  exact toMatrix_comp_latticeMutation s k

/-- The monomials of the mutated seed: with `a° = a.erase (row k)`, the monomial at `a` is
`u ^ (-(a (row k) * Λ (α_{k,0}, a°))) • X'_k ^ (a (row k)) * M a°`, where `X'_k` is the
exchange element and `α_{k,0}` its exponent of index zero. -/
theorem mutation_chart_monomial (hE : IsUnit (s.exchangeElement k)) (a : I →₀ ℤ) :
    (s.mutation k hE).chart.monomial a =
      Units.map (algebraMap R B)
          (u ^ (-(a (row k) * s.form (s.state.exchangeExponent k 0) (a.erase (row k))))) *
        hE.unit ^ a (row k) * s.chart.monomial (a.erase (row k)) := by
  dsimp only [mutation]
  rw [BasedChart.exchange_monomial, comp_latticeMutation_single_row_self s k Finsupp.erase_same]

/-- The coordinate of the mutated seed at `row k` is the exchange element. -/
@[simp]
theorem mutation_chart_monomial_single_self (hE : IsUnit (s.exchangeElement k)) :
    (s.mutation k hE).chart.monomial (Finsupp.single (row k) 1) = hE.unit := by
  dsimp only [mutation]
  rw [BasedChart.exchange_monomial_single_self]

/-- Mutation keeps every monomial in the coordinates other than `row k`. -/
@[simp]
theorem mutation_chart_monomial_of_apply_eq_zero (hE : IsUnit (s.exchangeElement k))
    {a : I →₀ ℤ} (ha : a (row k) = 0) :
    (s.mutation k hE).chart.monomial a = s.chart.monomial a := by
  dsimp only [mutation]
  rw [BasedChart.exchange_monomial_of_apply_eq_zero (ha := ha)]

/-- The constructed seed is a mutation of `s` in direction `k`. -/
theorem isMutation_mutation (hE : IsUnit (s.exchangeElement k)) :
    s.IsMutation k (s.mutation k hE) where
  state_eq := (rfl)
  formMatrix_eq := formMatrix_mutation s k hE
  coordinate_eq := by simp
  coordinate_eq_of_ne i hi := by simp [Finsupp.single_eq_of_ne hi.symm]

/-- **Seed mutation**: if the exchange element in direction `k` is a unit, then exactly one
seed is a mutation of `s` in direction `k`. The faithfulness of its chart is part of the
conclusion, not an assumption. -/
theorem existsUnique_isMutation (hE : IsUnit (s.exchangeElement k)) : ∃! t, s.IsMutation k t :=
  ⟨s.mutation k hE, s.isMutation_mutation k hE, fun _ ht ↦ ht.eq (s.isMutation_mutation k hE)⟩

end Mutation

/-- The exchange element of the mutated seed in the same direction is the old coordinate, so
the reverse exchange is defined. -/
@[simp]
theorem exchangeElement_mutation (s : Seed c row u B) (k : K)
    (hE : IsUnit (s.exchangeElement k)) :
    (s.mutation k hE).exchangeElement k = s.chart.monomial (Finsupp.single (row k) 1) :=
  (s.isMutation_mutation k hE).exchangeElement_eq_coordinate

/-- The reverse exchange of a mutation is defined. -/
theorem isUnit_exchangeElement_mutation (s : Seed c row u B) (k : K)
    (hE : IsUnit (s.exchangeElement k)) : IsUnit ((s.mutation k hE).exchangeElement k) :=
  (s.isMutation_mutation k hE).symm.isUnit_exchangeElement

/-- Mutating twice in the same direction recovers the seed. -/
@[simp]
theorem mutation_mutation (s : Seed c row u B) (k : K) (hE : IsUnit (s.exchangeElement k))
    (hE' : IsUnit ((s.mutation k hE).exchangeElement k)) :
    (s.mutation k hE).mutation k hE' = s :=
  ((s.isMutation_mutation k hE).symm.eq ((s.mutation k hE).isMutation_mutation k hE')).symm

/-- A seed has a mutation in direction `k` exactly when its exchange element is a unit. -/
theorem exists_isMutation_iff (s : Seed c row u B) (k : K) :
    (∃ t, s.IsMutation k t) ↔ IsUnit (s.exchangeElement k) :=
  ⟨fun ⟨_, h⟩ ↦ h.isUnit_exchangeElement, fun hE ↦ ⟨_, s.isMutation_mutation k hE⟩⟩

/-- Every mutation of `s` in direction `k` is the constructed one. -/
theorem IsMutation.eq_mutation (h : s.IsMutation k t) :
    t = s.mutation k h.isUnit_exchangeElement :=
  h.eq (s.isMutation_mutation k _)

end TauCeti.Seed
