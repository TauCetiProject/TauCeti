/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.YSeed.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Mutation of semifield-valued cluster coordinates

A Y-seed over a coefficient semifield `P` acts on coordinate tuples in another coefficient
semifield `Q`, given a multiplicative coefficient map `φ : P →* Q`. The exchange uses the
auxiliary addition of `Q` in its numerator and that of `P` in its normalizer. The coefficient
map need not preserve addition. Mutation is a bijection between the coordinate copies at the
original and mutated Y-seeds, with inverse given by the reverse exchange.

These coordinate changes commute with relabelling and with addition-preserving maps of the
coordinate semifield. A compatible addition-preserving specialization of the coefficient
semifield also commutes with them. They can therefore be evaluated along finite mutation
words before or after specialization.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Definition 2.4,
  equation (2.4), for normalized exchange and its coefficient conventions.
-/

public section

namespace TauCeti.YSeed

variable {K K' P P' Q Q' : Type*}
  [CoefficientSemifield P] [CoefficientSemifield P']
  [CoefficientSemifield Q] [CoefficientSemifield Q']
  [Fintype K]

/-- The normalized exchange numerator in a coordinate semifield. Its denominator is the image
of the auxiliary sum in the coefficient semifield, formed before applying `φ`. -/
def pointExchange (s : YSeed K P) (φ : P →* Q) (x : K → Q) (k : K) : Q :=
  (φ (s.coefficient k) * ∏ i, x i ^ (s.exchangeMatrix.matrix i k)⁺ +
    ∏ i, x i ^ (-s.exchangeMatrix.matrix i k)⁺) / φ (s.coefficient k + 1)

/-- The two exchange monomials with their coefficient-semifield normalizer. -/
theorem pointExchange_def (s : YSeed K P) (φ : P →* Q) (x : K → Q) (k : K) :
    s.pointExchange φ x k =
      (φ (s.coefficient k) * ∏ i, x i ^ (s.exchangeMatrix.matrix i k)⁺ +
        ∏ i, x i ^ (-s.exchangeMatrix.matrix i k)⁺) / φ (s.coefficient k + 1) :=
  (rfl)

/-- The exchange numerator does not depend on the coordinate being mutated. -/
theorem pointExchange_congr (s : YSeed K P) (φ : P →* Q) {x z : K → Q} (k : K)
    (h : ∀ i, i ≠ k → x i = z i) : s.pointExchange φ x k = s.pointExchange φ z k := by
  have hd : s.exchangeMatrix.matrix k k = 0 := s.exchangeMatrix.matrix_row_self k
  have hp (ε : ℤ) :
      (∏ i, x i ^ (ε * s.exchangeMatrix.matrix i k)⁺) =
        ∏ i, z i ^ (ε * s.exchangeMatrix.matrix i k)⁺ := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = k
    · subst i
      simp [hd]
    · rw [h i hi]
  simp only [pointExchange]
  have hpos := hp 1
  have hneg := hp (-1)
  simp only [one_mul, neg_one_mul] at hpos hneg
  rw [hpos, hneg]

variable [DecidableEq K]

/-- Mutation preserves the normalized exchange numerator when the coordinates are unchanged.
The negated exchange column exchanges the two monomials. -/
@[simp]
theorem pointExchange_mutation (s : YSeed K P) (φ : P →* Q) (x : K → Q) (k : K) :
    (s.mutation k).pointExchange φ x k = s.pointExchange φ x k := by
  have hn : (s.coefficient k)⁻¹ + 1 = (s.coefficient k + 1) / s.coefficient k := by
    simpa using CoefficientSemifield.inv_add_inv (s.coefficient k) 1
  simp only [pointExchange, mutation_coefficient_self, mutation_exchangeMatrix,
    ExchangeMatrix.mutation_matrix, matrixMutation_apply_col, neg_neg, hn, map_div, map_inv]
  simp [div_eq_mul_inv, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, add_comm]

/-- Change the coordinate in direction `k` by normalized exchange, fixing all others. -/
def pointMutation (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) : K → Q :=
  Function.update x k (s.pointExchange φ x k / x k)

/-- The coordinate in the mutated direction is the normalized exchange divided by its old
value. -/
@[simp]
theorem pointMutation_self (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) :
    s.pointMutation φ k x k = s.pointExchange φ x k / x k := by
  simp [pointMutation]

/-- Coordinates outside the mutation direction are unchanged. -/
@[simp]
theorem pointMutation_of_ne (s : YSeed K P) (φ : P →* Q) {i k : K} (h : i ≠ k)
    (x : K → Q) : s.pointMutation φ k x i = x i := by
  simp [pointMutation, h]

/-- The exchange relation in the coordinate semifield. Both additions are auxiliary additions
in their respective semifields. -/
theorem pointMutation_mul (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) :
    s.pointMutation φ k x k * x k * φ (s.coefficient k + 1) =
      φ (s.coefficient k) * ∏ i, x i ^ (s.exchangeMatrix.matrix i k)⁺ +
        ∏ i, x i ^ (-s.exchangeMatrix.matrix i k)⁺ := by
  simp [pointExchange]

/-- The numerator is unchanged when the mutated coordinate replaces the old one. -/
@[simp]
theorem pointExchange_pointMutation (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) :
    s.pointExchange φ (s.pointMutation φ k x) k = s.pointExchange φ x k :=
  s.pointExchange_congr φ k fun _ hi ↦ s.pointMutation_of_ne φ hi x

/-- Mutating coordinates again at the mutated Y-seed is the inverse exchange. No preservation
of auxiliary addition is required of the coefficient map. -/
@[simp]
theorem pointMutation_pointMutation (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) :
    (s.mutation k).pointMutation φ k (s.pointMutation φ k x) = x := by
  funext i
  by_cases hi : i = k
  · subst i
    simp
  · simp [pointMutation_of_ne _ _ hi]

/-- The coordinate change between the copies of `Q^K` at adjacent Y-seeds. -/
def pointMutationEquiv (s : YSeed K P) (φ : P →* Q) (k : K) : (K → Q) ≃ (K → Q) where
  toFun := s.pointMutation φ k
  invFun := (s.mutation k).pointMutation φ k
  left_inv := s.pointMutation_pointMutation φ k
  right_inv x := by simpa using (s.mutation k).pointMutation_pointMutation φ k x

@[simp]
theorem pointMutationEquiv_apply (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) :
    s.pointMutationEquiv φ k x = s.pointMutation φ k x :=
  (rfl)

@[simp]
theorem pointMutationEquiv_symm_apply (s : YSeed K P) (φ : P →* Q) (k : K) (x : K → Q) :
    (s.pointMutationEquiv φ k).symm x = (s.mutation k).pointMutation φ k x :=
  (rfl)

/-- Reversing an edge gives the inverse coordinate equivalence. -/
@[simp]
theorem pointMutationEquiv_mutation (s : YSeed K P) (φ : P →* Q) (k : K) :
    (s.mutation k).pointMutationEquiv φ k = (s.pointMutationEquiv φ k).symm := by
  ext x i
  rfl

/-! ### Naturality -/

omit [DecidableEq K] in
/-- An addition-preserving map of coordinate semifields commutes with exchange numerators. -/
@[simp]
theorem map_pointExchange (s : YSeed K P) (φ : P →* Q)
    (f : CoefficientSemifieldHom Q Q') (x : K → Q) (k : K) :
    f (s.pointExchange φ x k) =
      s.pointExchange (f.toMonoidHom.comp φ) (f ∘ x) k := by
  simp [pointExchange, map_prod]

/-- Coordinate specialization commutes with a normalized exchange. -/
@[simp]
theorem map_pointMutation (s : YSeed K P) (φ : P →* Q)
    (f : CoefficientSemifieldHom Q Q') (k : K) (x : K → Q) :
    f ∘ s.pointMutation φ k x =
      s.pointMutation (f.toMonoidHom.comp φ) k (f ∘ x) := by
  funext i
  by_cases hi : i = k
  · subst i
    simp
  · simp [hi]

omit [DecidableEq K] in
/-- An addition-preserving coefficient specialization commutes with exchange numerators. -/
@[simp]
theorem pointExchange_map (s : YSeed K P) (f : CoefficientSemifieldHom P P')
    (φ : P' →* Q) (x : K → Q) (k : K) :
    (s.map f).pointExchange φ x k =
      s.pointExchange (φ.comp f.toMonoidHom) x k := by
  simp [pointExchange]

/-- Coefficient specialization commutes with coordinate mutation when the realization maps
are related by composition. -/
@[simp]
theorem pointMutation_map (s : YSeed K P) (f : CoefficientSemifieldHom P P')
    (φ : P' →* Q) (k : K) (x : K → Q) :
    (s.map f).pointMutation φ k x =
      s.pointMutation (φ.comp f.toMonoidHom) k x := by
  funext i
  by_cases hi : i = k
  · subst i
    simp
  · simp [hi]

/-! ### Relabelling -/

section Reindex

variable [Fintype K'] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in
/-- Relabelling coefficients, matrix and coordinates preserves the exchange numerator. -/
@[simp]
theorem pointExchange_reindex (e : K ≃ K') (s : YSeed K P) (φ : P →* Q)
    (x : K → Q) (k : K) :
    (reindex e s).pointExchange φ (x ∘ e.symm) (e k) = s.pointExchange φ x k := by
  simp only [pointExchange, reindex_coefficient, Equiv.symm_apply_apply,
    reindex_exchangeMatrix, ExchangeMatrix.reindex_matrix, Matrix.submatrix_apply,
    Function.comp_apply]
  rw [e.symm.prod_comp (fun i ↦ x i ^ (s.exchangeMatrix.matrix i k)⁺),
    e.symm.prod_comp (fun i ↦ x i ^ (-s.exchangeMatrix.matrix i k)⁺)]

/-- Coordinate mutation is equivariant under simultaneous relabelling. -/
theorem pointMutation_reindex (e : K ≃ K') (s : YSeed K P) (φ : P →* Q)
    (k : K) (x : K → Q) :
    (reindex e s).pointMutation φ (e k) (x ∘ e.symm) = s.pointMutation φ k x ∘ e.symm := by
  funext i
  by_cases hi : i = e k
  · subst i
    simp
  · have h : e.symm i ≠ k := by simpa [Equiv.symm_apply_eq] using hi
    simp [hi, h]

end Reindex

/-! ### Finite words -/

/-- Transport coordinates along a finite mutation word in reading order. Each successive
exchange uses the Y-seed produced by the preceding ones. -/
def pointMutationWordEquiv (s : YSeed K P) (φ : P →* Q) : List K → (K → Q) ≃ (K → Q)
  | [] => Equiv.refl _
  | k :: w => (s.pointMutationEquiv φ k).trans ((s.mutation k).pointMutationWordEquiv φ w)

@[simp]
theorem pointMutationWordEquiv_nil (s : YSeed K P) (φ : P →* Q) :
    s.pointMutationWordEquiv φ [] = Equiv.refl _ :=
  (rfl)

/-- Transport along a nonempty word begins with its first exchange. -/
@[simp]
theorem pointMutationWordEquiv_cons (s : YSeed K P) (φ : P →* Q) (k : K) (w : List K) :
    s.pointMutationWordEquiv φ (k :: w) =
      (s.pointMutationEquiv φ k).trans ((s.mutation k).pointMutationWordEquiv φ w) :=
  (rfl)

/-- Concatenation composes the coordinate equivalences, re-rooting the second word at the
Y-seed reached by the first. -/
theorem pointMutationWordEquiv_append (s : YSeed K P) (φ : P →* Q) (v w : List K) :
    s.pointMutationWordEquiv φ (v ++ w) =
      (s.pointMutationWordEquiv φ v).trans
        ((v.foldl mutation s).pointMutationWordEquiv φ w) := by
  induction v generalizing s with
  | nil => rfl
  | cons k v ih =>
    simp only [List.cons_append, pointMutationWordEquiv_cons, List.foldl_cons, ih]
    rfl

/-- Reversing a word, based at its endpoint Y-seed, inverts coordinate transport. -/
theorem pointMutationWordEquiv_reverse (s : YSeed K P) (φ : P →* Q) (w : List K) :
    (w.foldl mutation s).pointMutationWordEquiv φ w.reverse =
      (s.pointMutationWordEquiv φ w).symm := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w k ih =>
    simp [pointMutationWordEquiv_append, List.foldl_append, ih]

/-- Coordinate specialization commutes with transport along every finite word. -/
@[simp]
theorem map_pointMutationWordEquiv (s : YSeed K P) (φ : P →* Q)
    (f : CoefficientSemifieldHom Q Q') (w : List K) (x : K → Q) :
    f ∘ s.pointMutationWordEquiv φ w x =
      s.pointMutationWordEquiv (f.toMonoidHom.comp φ) w (f ∘ x) := by
  induction w generalizing s x with
  | nil => rfl
  | cons k w ih =>
    simpa only [pointMutationWordEquiv_cons, Equiv.trans_apply, pointMutationEquiv_apply,
      map_pointMutation] using ih (s.mutation k) (s.pointMutation φ k x)

/-- Specializing the coefficient semifield commutes with every coordinate word. -/
@[simp]
theorem pointMutationWordEquiv_map (s : YSeed K P) (f : CoefficientSemifieldHom P P')
    (φ : P' →* Q) (w : List K) :
    (s.map f).pointMutationWordEquiv φ w =
      s.pointMutationWordEquiv (φ.comp f.toMonoidHom) w := by
  induction w generalizing s with
  | nil => rfl
  | cons k w ih =>
    ext x i
    simp [← map_mutation, ih]

/-- Relabelling the mutation word and both coordinate copies commutes with transport. -/
theorem pointMutationWordEquiv_reindex [Fintype K'] [DecidableEq K']
    (e : K ≃ K') (s : YSeed K P) (φ : P →* Q) (w : List K) (x : K → Q) :
    (reindex e s).pointMutationWordEquiv φ (w.map e) (x ∘ e.symm) =
      s.pointMutationWordEquiv φ w x ∘ e.symm := by
  induction w generalizing s x with
  | nil => rfl
  | cons k w ih =>
    simpa only [List.map_cons, pointMutationWordEquiv_cons, Equiv.trans_apply,
      pointMutationEquiv_apply, mutation_reindex, pointMutation_reindex]
      using ih (s.mutation k) (s.pointMutation φ k x)

/-! ### Realization by units -/

/-- A multiplicative realization of the coordinate semifield by units, preserving auxiliary
addition in the ambient semiring, carries the exchange to an ordinary semiring identity.
This applies in particular to the inclusion of an addition-closed subgroup of units. -/
theorem pointMutation_mul_realization {A : Type*} [CommSemiring A]
    (s : YSeed K P) (φ : P →* Q) (j : Q →* Aˣ)
    (hj : ∀ a b, (j (a + b) : A) = (j a : A) + (j b : A)) (k : K) (x : K → Q) :
    (j (s.pointMutation φ k x k) : A) * (j (x k) : A) * (j (φ (s.coefficient k + 1)) : A) =
      (j (φ (s.coefficient k)) : A) *
        ∏ i, (j (x i) ^ (s.exchangeMatrix.matrix i k)⁺ : Aˣ) +
      ∏ i, (j (x i) ^ (-s.exchangeMatrix.matrix i k)⁺ : Aˣ) := by
  have h := congrArg (fun a ↦ (j a : A)) (s.pointMutation_mul φ k x)
  simpa only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, hj] using h

end TauCeti.YSeed
