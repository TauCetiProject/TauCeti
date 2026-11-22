/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Y-seeds and coefficient mutation

A Y-seed consists of coefficients in a coefficient semifield and a square exchange matrix.
Its mutation uses the auxiliary addition of the semifield, rather than addition in an ambient
field. This coefficient part of normalized seed mutation makes sense without a Laurent chart.

Mutation is involutive, commutes with coefficient-semifield homomorphisms, and is equivariant
under simultaneous relabelling of coefficients and matrix indices. In particular coefficient
specialization can be performed before or after a mutation.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  Definition 2.3 and equation (2.3).
-/

public section

namespace TauCeti

/-- A Y-seed over a coefficient semifield: a family of coefficients and a square exchange
matrix with its positive symmetrizer. No choice of ambient field or cluster is involved. -/
@[ext]
structure YSeed (K P : Type*) [CoefficientSemifield P] where
  /-- The coefficients of the seed. -/
  coefficient : K → P
  /-- The exchange matrix, with a chosen positive symmetrizer. -/
  exchangeMatrix : ExchangeMatrix (Function.Embedding.refl K)

namespace YSeed

variable {K K' K'' P Q R : Type*}
  [CoefficientSemifield P] [CoefficientSemifield Q] [CoefficientSemifield R]

section Mutation

variable [DecidableEq K]

/-- Normalized coefficient mutation, together with matrix mutation, in direction `k`.
The addition in the normalizer `s.coefficient k + 1` is the auxiliary semifield addition. -/
def mutation (s : YSeed K P) (k : K) : YSeed K P where
  coefficient j := if j = k then (s.coefficient k)⁻¹ else
    s.coefficient j * s.coefficient k ^ (s.exchangeMatrix.matrix k j)⁺ *
      (s.coefficient k + 1) ^ (-s.exchangeMatrix.matrix k j)
  exchangeMatrix := s.exchangeMatrix.mutation k

@[simp]
theorem mutation_exchangeMatrix (s : YSeed K P) (k : K) :
    (s.mutation k).exchangeMatrix = s.exchangeMatrix.mutation k :=
  (rfl)

/-- The coefficient in the mutated direction is inverted. -/
@[simp]
theorem mutation_coefficient_self (s : YSeed K P) (k : K) :
    (s.mutation k).coefficient k = (s.coefficient k)⁻¹ := by
  simp [mutation]

/-- The coefficient mutation formula away from the mutated direction. -/
theorem mutation_coefficient_of_ne (s : YSeed K P) {j k : K} (h : j ≠ k) :
    (s.mutation k).coefficient j =
      s.coefficient j * s.coefficient k ^ (s.exchangeMatrix.matrix k j)⁺ *
        (s.coefficient k + 1) ^ (-s.exchangeMatrix.matrix k j) := by
  simp [mutation, h]

/-- The coefficient correction for an entry and for its negation cancel after inversion
of the coefficient in the mutation direction. -/
private theorem correction_mul_correction (a : P) (b : ℤ) :
    a ^ b⁺ * (a + 1) ^ (-b) * (a⁻¹) ^ (-b)⁺ * (a⁻¹ + 1) ^ b = 1 := by
  have hn : a⁻¹ + 1 = (a + 1) / a := by
    simpa using CoefficientSemifield.inv_add_inv a 1
  rw [hn, div_zpow, inv_zpow, posPart_neg]
  have hp : a ^ b⁺ = a ^ b⁻ * a ^ b := by
    rw [← zpow_add]
    congr 1
    have := posPart_sub_negPart b
    omega
  rw [hp]
  simp [zpow_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Mutating a Y-seed twice in the same direction recovers the original seed. -/
@[simp]
theorem mutation_mutation (s : YSeed K P) (k : K) : (s.mutation k).mutation k = s := by
  ext : 1
  · funext j
    by_cases h : j = k
    · subst j
      simp
    · simp only [mutation_coefficient_of_ne _ h, mutation_coefficient_self,
        mutation_exchangeMatrix, ExchangeMatrix.mutation_matrix, matrixMutation_refl_apply_row,
        neg_neg]
      have hc := correction_mul_correction (s.coefficient k) (s.exchangeMatrix.matrix k j)
      calc
        _ = s.coefficient j *
            (s.coefficient k ^ (s.exchangeMatrix.matrix k j)⁺ *
              (s.coefficient k + 1) ^ (-s.exchangeMatrix.matrix k j) *
              (s.coefficient k)⁻¹ ^ (-s.exchangeMatrix.matrix k j)⁺ *
              ((s.coefficient k)⁻¹ + 1) ^ s.exchangeMatrix.matrix k j) := by ac_rfl
        _ = s.coefficient j := by rw [hc, mul_one]
  · simp

/-- Mutation in a fixed direction is an involution on Y-seeds. -/
theorem mutation_involutive (k : K) : Function.Involutive (fun s : YSeed K P ↦ s.mutation k) :=
  fun s ↦ s.mutation_mutation k

end Mutation

/-! ### Coefficient specialization -/

/-- Apply a homomorphism of coefficient semifields, retaining the exchange matrix. -/
def map (s : YSeed K P) (f : CoefficientSemifieldHom P Q) : YSeed K Q where
  coefficient := f ∘ s.coefficient
  exchangeMatrix := s.exchangeMatrix

@[simp]
theorem map_coefficient (s : YSeed K P) (f : CoefficientSemifieldHom P Q) (j : K) :
    (s.map f).coefficient j = f (s.coefficient j) :=
  (rfl)

@[simp]
theorem map_exchangeMatrix (s : YSeed K P) (f : CoefficientSemifieldHom P Q) :
    (s.map f).exchangeMatrix = s.exchangeMatrix :=
  (rfl)

@[simp]
theorem map_id (s : YSeed K P) : s.map (CoefficientSemifieldHom.id P) = s := by
  ext : 1
  · funext j
    simp
  · rfl

@[simp]
theorem map_map (s : YSeed K P) (f : CoefficientSemifieldHom P Q)
    (g : CoefficientSemifieldHom Q R) : (s.map f).map g = s.map (g.comp f) := by
  ext : 1
  · funext j
    simp
  · rfl

/-- Coefficient specialization commutes with Y-seed mutation. Preservation of auxiliary
addition, in addition to the group operations, is essential here. -/
@[simp]
theorem map_mutation [DecidableEq K] (s : YSeed K P) (f : CoefficientSemifieldHom P Q)
    (k : K) : (s.mutation k).map f = (s.map f).mutation k := by
  ext : 1
  · funext j
    by_cases h : j = k
    · subst j
      simp
    · simp [mutation_coefficient_of_ne _ h]
  · simp

/-! ### Relabelling -/

/-- Relabel a Y-seed along a bijection of its mutable indices. Coefficients and the two matrix
indices are relabelled simultaneously, together with the chosen symmetrizer. -/
def reindex (e : K ≃ K') : YSeed K P ≃ YSeed K' P where
  toFun s :=
    { coefficient := s.coefficient ∘ e.symm
      exchangeMatrix := ExchangeMatrix.reindex (row := Function.Embedding.refl K)
        (row' := Function.Embedding.refl K') e e
          (fun _ ↦ by simp only [Function.Embedding.refl_apply]) s.exchangeMatrix }
  invFun s :=
    { coefficient := s.coefficient ∘ e
      exchangeMatrix := ExchangeMatrix.reindex (row := Function.Embedding.refl K')
        (row' := Function.Embedding.refl K) e.symm e.symm
          (fun _ ↦ by simp only [Function.Embedding.refl_apply]) s.exchangeMatrix }
  left_inv s := by
    ext : 1
    · funext j
      simp
    · ext i j <;> simp
  right_inv s := by
    ext : 1
    · funext j
      simp
    · ext i j <;> simp

@[simp]
theorem reindex_coefficient (e : K ≃ K') (s : YSeed K P) (j : K') :
    (reindex e s).coefficient j = s.coefficient (e.symm j) :=
  (rfl)

@[simp]
theorem reindex_exchangeMatrix (e : K ≃ K') (s : YSeed K P) :
    (reindex e s).exchangeMatrix =
      ExchangeMatrix.reindex (row := Function.Embedding.refl K)
        (row' := Function.Embedding.refl K') e e
          (fun _ ↦ by simp only [Function.Embedding.refl_apply]) s.exchangeMatrix :=
  (rfl)

@[simp]
theorem reindex_refl : reindex (P := P) (Equiv.refl K) = Equiv.refl (YSeed K P) := by
  ext s : 2
  · funext j
    simp
  · simp only [reindex_exchangeMatrix, ExchangeMatrix.reindex_refl, Equiv.refl_apply]

/-- Relabelling twice is relabelling by the composite bijection. -/
@[simp]
theorem reindex_trans (e : K ≃ K') (e' : K' ≃ K'') :
    (reindex (P := P) e).trans (reindex e') = reindex (e.trans e') := by
  ext s : 2
  · funext j
    simp
  · simp only [reindex_exchangeMatrix]
    exact congrArg (fun e ↦ e s.exchangeMatrix) (ExchangeMatrix.reindex_trans
      (row := Function.Embedding.refl K) (row' := Function.Embedding.refl K')
      (row'' := Function.Embedding.refl K'') e e
      (fun _ ↦ by simp only [Function.Embedding.refl_apply]) e' e'
      (fun _ ↦ by simp only [Function.Embedding.refl_apply]))

/-- Nested mutable relabellings collapse to the composite index equivalence. -/
@[simp]
theorem reindex_reindex (e : K ≃ K') (e' : K' ≃ K'') (s : YSeed K P) :
    reindex e' (reindex e s) = reindex (e.trans e') s := by
  simpa only [Equiv.trans_apply] using
    congrArg (fun f : YSeed K P ≃ YSeed K'' P ↦ f s) (reindex_trans e e')

@[simp]
theorem reindex_symm (e : K ≃ K') :
    (reindex (P := P) e).symm = reindex e.symm :=
  (rfl)

/-- Relabelling carries mutation in direction `k` to mutation in direction `e k`. -/
theorem mutation_reindex [DecidableEq K] [DecidableEq K'] (e : K ≃ K')
    (s : YSeed K P) (k : K) : (reindex e s).mutation (e k) = reindex e (s.mutation k) := by
  ext : 1
  · funext j
    by_cases h : j = e k
    · subst j
      simp
    · have h' : e.symm j ≠ k := by simpa [Equiv.symm_apply_eq] using h
      simp [mutation_coefficient_of_ne _ h, mutation_coefficient_of_ne _ h',
        ExchangeMatrix.reindex_matrix]
  · simp only [mutation_exchangeMatrix, reindex_exchangeMatrix]
    exact s.exchangeMatrix.mutation_reindex e e
      (fun _ ↦ by simp only [Function.Embedding.refl_apply]) k

/-- Coefficient specialization and relabelling commute. -/
@[simp]
theorem map_reindex (e : K ≃ K') (s : YSeed K P) (f : CoefficientSemifieldHom P Q) :
    (reindex e s).map f = reindex e (s.map f) := by
  ext : 1 <;> rfl

/-! ### A skew-symmetrizable rank-two example -/

/-- Both mutation directions for the matrix with rows `(0, 1)` and `(-2, 0)`.
The exponent two in the second formula checks the nonsymmetric row convention. -/
example (p q : P) :
    let s : YSeed (Fin 2) P :=
      { coefficient := ![p, q]
        exchangeMatrix :=
          { matrix := !![0, 1; -2, 0]
            symmetrizer := ![2, 1]
            isSkewSymmetrizer := ⟨by decide, by decide⟩ } }
    (s.mutation 0).coefficient = ![p⁻¹, q * p / (p + 1)] ∧
      (s.mutation 1).coefficient = ![p * (q + 1) ^ 2, q⁻¹] := by
  dsimp only
  constructor <;> funext j <;> fin_cases j <;>
    simp [mutation_coefficient_of_ne, div_eq_mul_inv]

end YSeed

end TauCeti
