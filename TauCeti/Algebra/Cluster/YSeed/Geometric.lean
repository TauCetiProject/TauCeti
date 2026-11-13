/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Tropical
public import TauCeti.Algebra.Cluster.YSeed.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.FrozenSupport

import TauCeti.Algebra.Order.Ring.PosPart.Mul

import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Tactic.Linarith

/-!
# Tropical coefficients and finite-support extended exchange matrices

A tropical coefficient is a finitely supported integer exponent vector. Reading these
vectors as frozen columns identifies Y-seeds over `Trop J` with extended exchange matrices
on `K ⊕ J` whose frozen columns have finite support. The principal matrix and its chosen
symmetrizer are retained. The mutable and frozen index types can both be infinite.

The correspondence intertwines coefficient mutation with extended exchange-matrix mutation.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, §2, the tropical coefficient
  and extended exchange-matrix presentations of geometric type.
-/

public section

namespace TauCeti

variable {K K' J J' : Type*}

namespace ExchangeMatrix

/-- Recover a tropical Y-seed from a finite-support extended matrix, retaining the chosen
principal symmetrizer. -/
noncomputable def toTropicalYSeed
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : YSeed K (Trop J) where
  coefficient k := Multiplicative.ofAdd (B.frozenColumn h k)
  exchangeMatrix := B.principal

@[simp]
theorem toTropicalYSeed_coefficient
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) :
    (B.toTropicalYSeed h).coefficient k = Multiplicative.ofAdd (B.frozenColumn h k) :=
  (rfl)

theorem toAdd_toTropicalYSeed_coefficient
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) (j : J) :
    ((B.toTropicalYSeed h).coefficient k).toAdd j = B.matrix (Sum.inr j) k :=
  B.frozenColumn_apply h k j

@[simp]
theorem toTropicalYSeed_exchangeMatrix
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : (B.toTropicalYSeed h).exchangeMatrix = B.principal :=
  (rfl)

/-- A matrix's tropical coefficient is the finite product of frozen generators to the
entries of its frozen exponent column. -/
theorem toTropicalYSeed_coefficient_eq_prod_generator
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) :
    (B.toTropicalYSeed h).coefficient k =
      (B.frozenColumn h k).prod (fun j n ↦ Trop.generator j ^ n) :=
  Trop.eq_prod_generator _

end ExchangeMatrix

namespace YSeed

/-- Adjoin the tropical coefficient exponents as frozen rows of the principal matrix. -/
noncomputable def toExtendedMatrix (s : YSeed K (Trop J)) :
    ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) where
  matrix := Sum.elim s.exchangeMatrix.matrix (fun j k ↦ (s.coefficient k).toAdd j)
  symmetrizer := s.exchangeMatrix.symmetrizer
  isSkewSymmetrizer := s.exchangeMatrix.isSkewSymmetrizer

@[simp]
theorem toExtendedMatrix_mutable (s : YSeed K (Trop J)) (i k : K) :
    s.toExtendedMatrix.matrix (Sum.inl i) k = s.exchangeMatrix.matrix i k :=
  (rfl)

@[simp]
theorem toExtendedMatrix_frozen (s : YSeed K (Trop J)) (j : J) (k : K) :
    s.toExtendedMatrix.matrix (Sum.inr j) k = (s.coefficient k).toAdd j :=
  (rfl)

@[simp]
theorem toExtendedMatrix_symmetrizer (s : YSeed K (Trop J)) :
    s.toExtendedMatrix.symmetrizer = s.exchangeMatrix.symmetrizer :=
  (rfl)

/-- The matrix presentation of a tropical Y-seed has finitely supported frozen columns. -/
@[simp]
theorem hasFiniteFrozenSupport_toExtendedMatrix (s : YSeed K (Trop J)) :
    s.toExtendedMatrix.HasFiniteFrozenSupport := by
  rw [ExchangeMatrix.hasFiniteFrozenSupport_iff]
  exact fun k ↦ (s.coefficient k).toAdd.hasFiniteSupport

@[simp]
theorem frozenColumn_toExtendedMatrix (s : YSeed K (Trop J))
    (h : s.toExtendedMatrix.HasFiniteFrozenSupport) (k : K) :
    s.toExtendedMatrix.frozenColumn h k = (s.coefficient k).toAdd := by
  ext j
  simp

@[simp]
theorem principal_toExtendedMatrix (s : YSeed K (Trop J)) :
    s.toExtendedMatrix.principal = s.exchangeMatrix := by
  ext : 1
  · ext i k
    simp
  · simp

@[simp]
theorem toTropicalYSeed_toExtendedMatrix (s : YSeed K (Trop J))
    (h : s.toExtendedMatrix.HasFiniteFrozenSupport) :
    s.toExtendedMatrix.toTropicalYSeed h = s := by
  ext : 1
  · funext k
    apply Multiplicative.toAdd.injective
    ext j
    simp
  · exact s.principal_toExtendedMatrix

/-- Reading tropical exponents intertwines coefficient mutation with the actual extended
matrix mutation. -/
theorem toExtendedMatrix_mutation [DecidableEq K] [DecidableEq J]
    (s : YSeed K (Trop J)) (k : K) :
    (s.mutation k).toExtendedMatrix = s.toExtendedMatrix.mutation k := by
  ext : 1
  · ext i l
    cases i with
    | inl i =>
      simp only [toExtendedMatrix_mutable, mutation_exchangeMatrix,
        ExchangeMatrix.mutation_matrix, matrixMutation_apply,
        toExtendedMatrix_mutable, Function.Embedding.refl_apply, Function.Embedding.inl_apply]
      simp
    | inr j =>
      by_cases hl : l = k
      · subst l
        simp [ExchangeMatrix.mutation_matrix]
      · rw [toExtendedMatrix_frozen, mutation_coefficient_of_ne _ hl]
        simp only [toAdd_mul, toAdd_zpow, Trop.toAdd_add,
          toAdd_one, Finsupp.add_apply, Finsupp.smul_apply,
          Finsupp.inf_apply, Finsupp.zero_apply, smul_eq_mul]
        rw [ExchangeMatrix.mutation_matrix, matrixMutation_apply_of_ne (by simp) hl]
        simp only [toExtendedMatrix_frozen, toExtendedMatrix_mutable,
          Function.Embedding.inl_apply]
        have h := posPart_mul_add_neg_mul_inf_zero (s.exchangeMatrix.matrix k l)
          ((s.coefficient k).toAdd j)
        simp only [mul_comm] at h ⊢
        linarith
  · simp [toExtendedMatrix_symmetrizer]

/-- Mutable reindexing commutes with the extended-matrix presentation. -/
@[simp]
theorem toExtendedMatrix_reindex (eK : K ≃ K') (s : YSeed K (Trop J)) :
    (reindex eK s).toExtendedMatrix =
      ExchangeMatrix.reindex (row' := Function.Embedding.inl)
        (Equiv.sumCongr eK (Equiv.refl J)) eK (fun _ ↦ by simp) s.toExtendedMatrix := by
  ext : 1
  · ext i k
    cases i <;> simp
  · simp

/-- Relabelling frozen generators relabels precisely the frozen rows, retaining the
principal matrix and its chosen symmetrizer. -/
@[simp]
theorem toExtendedMatrix_reindex_frozen (eJ : J ≃ J') (s : YSeed K (Trop J)) :
    (s.map (Trop.reindex eJ).toCoefficientSemifieldHom).toExtendedMatrix =
      ExchangeMatrix.reindex (row' := Function.Embedding.inl)
        (Equiv.sumCongr (Equiv.refl K) eJ) (Equiv.refl K) (fun _ ↦ by simp)
        s.toExtendedMatrix := by
  ext : 1
  · ext i k
    cases i <;> simp
  · simp

end YSeed

namespace ExchangeMatrix

@[simp]
theorem toExtendedMatrix_toTropicalYSeed
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : (B.toTropicalYSeed h).toExtendedMatrix = B := by
  ext : 1
  · ext i k
    cases i <;>
      simp [YSeed.toExtendedMatrix, toTropicalYSeed, principal_matrix, Sum.elim,
        Matrix.submatrix_apply]
  · simp [YSeed.toExtendedMatrix, toTropicalYSeed]

/-- Tropical Y-seeds are exactly extended exchange matrices with finite frozen columns.
Both sides retain the same chosen principal symmetrizer. -/
noncomputable def tropicalYSeedEquiv :
    YSeed K (Trop J) ≃
      {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) // B.HasFiniteFrozenSupport} where
  toFun s := ⟨s.toExtendedMatrix, s.hasFiniteFrozenSupport_toExtendedMatrix⟩
  invFun B := B.1.toTropicalYSeed B.2
  left_inv s := s.toTropicalYSeed_toExtendedMatrix _
  right_inv B := Subtype.ext (B.1.toExtendedMatrix_toTropicalYSeed B.2)

@[simp]
theorem tropicalYSeedEquiv_apply_val (s : YSeed K (Trop J)) :
    (tropicalYSeedEquiv s).val = s.toExtendedMatrix :=
  (rfl)

@[simp]
theorem tropicalYSeedEquiv_symm_apply
    (B : {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
      B.HasFiniteFrozenSupport}) :
    tropicalYSeedEquiv.symm B = B.val.toTropicalYSeed B.property :=
  (rfl)

@[simp]
theorem tropicalYSeedEquiv_toTropicalYSeed
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : tropicalYSeedEquiv (B.toTropicalYSeed h) = ⟨B, h⟩ := by
  apply Subtype.ext
  exact B.toExtendedMatrix_toTropicalYSeed h

/-- With finite frozen index type `J`, tropical Y-seeds are equivalent to all extended
exchange matrices on `K ⊕ J` with mutable rows `K`. -/
noncomputable def tropicalYSeedEquivOfFinite [Finite J] :
    YSeed K (Trop J) ≃ ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) where
  toFun := YSeed.toExtendedMatrix
  invFun B := B.toTropicalYSeed B.hasFiniteFrozenSupport_of_finite
  left_inv s := s.toTropicalYSeed_toExtendedMatrix _
  right_inv B := B.toExtendedMatrix_toTropicalYSeed _

@[simp]
theorem tropicalYSeedEquivOfFinite_apply [Finite J] (s : YSeed K (Trop J)) :
    tropicalYSeedEquivOfFinite s = s.toExtendedMatrix :=
  (rfl)

@[simp]
theorem tropicalYSeedEquivOfFinite_symm_apply [Finite J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    tropicalYSeedEquivOfFinite.symm B = B.toTropicalYSeed B.hasFiniteFrozenSupport_of_finite :=
  (rfl)

/-- Converting a matrix mutation back to a tropical Y-seed gives its coefficient mutation. -/
theorem toTropicalYSeed_mutation [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (k : K) (h : (B.mutation k).HasFiniteFrozenSupport) :
    (B.mutation k).toTropicalYSeed h =
      (B.toTropicalYSeed ((B.hasFiniteFrozenSupport_mutation_iff k).mp h)).mutation k := by
  apply (tropicalYSeedEquiv (K := K) (J := J)).injective
  apply Subtype.ext
  simp only [tropicalYSeedEquiv_apply_val]
  rw [toExtendedMatrix_toTropicalYSeed, YSeed.toExtendedMatrix_mutation,
    toExtendedMatrix_toTropicalYSeed]

/-- Inverting the correspondence commutes with simultaneous mutable relabelling and
coefficient specialization along the frozen generator isomorphism. -/
@[simp]
theorem toTropicalYSeed_reindex (eK : K ≃ K') (eJ : J ≃ J')
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h' : (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by simp) B).HasFiniteFrozenSupport) :
    (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by simp) B).toTropicalYSeed h' =
      YSeed.reindex eK
        ((B.toTropicalYSeed ((B.hasFiniteFrozenSupport_reindex_iff eK eJ).mp h')).map
          (Trop.reindex eJ).toCoefficientSemifieldHom) := by
  ext : 1
  · funext k
    apply Multiplicative.toAdd.injective
    ext j
    simp
  · simp

end ExchangeMatrix

end TauCeti
