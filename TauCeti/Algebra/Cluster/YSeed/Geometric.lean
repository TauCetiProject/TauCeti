/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Tropical
public import TauCeti.Algebra.Cluster.YSeed.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.FrozenSupport

import TauCeti.Algebra.Order.Ring.PosPartMul

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
theorem toTropicalYSeed_coefficient_toAdd
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) (j : J) :
    ((B.toTropicalYSeed h).coefficient k).toAdd j = B.matrix (Sum.inr j) k :=
  B.frozenColumn_apply h k j

@[simp]
theorem toTropicalYSeed_exchangeMatrix
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : (B.toTropicalYSeed h).exchangeMatrix = B.principal :=
  (rfl)

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
theorem toExtendedMatrix_hasFiniteFrozenSupport (s : YSeed K (Trop J)) :
    s.toExtendedMatrix.HasFiniteFrozenSupport := by
  rw [ExchangeMatrix.hasFiniteFrozenSupport_iff]
  exact fun k ↦ (s.coefficient k).toAdd.hasFiniteSupport

@[simp]
theorem toExtendedMatrix_principal (s : YSeed K (Trop J)) :
    s.toExtendedMatrix.principal = s.exchangeMatrix := by
  ext : 1
  · ext i k
    simp
  · simp

@[simp]
theorem toTropicalYSeed_toExtendedMatrix (s : YSeed K (Trop J)) :
    s.toExtendedMatrix.toTropicalYSeed s.toExtendedMatrix_hasFiniteFrozenSupport = s := by
  ext : 1
  · funext k
    apply Multiplicative.toAdd.injective
    ext j
    simp
  · exact s.toExtendedMatrix_principal

/-- The tropical coefficient is the finite product of the generators raised to the frozen
column entries. -/
theorem coefficient_eq_prod_generator (s : YSeed K (Trop J)) (k : K) :
    s.coefficient k = (s.coefficient k).toAdd.prod (fun j n ↦ Trop.generator j ^ n) := by
  have hid : freeAbelianCharEquiv.symm (Trop.generator (J := J)) = MonoidHom.id (Trop J) := by
    apply freeAbelianCharEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    funext j
    apply Multiplicative.toAdd.injective
    simp [freeAbelianCharEquiv_apply, Trop.toAdd_generator]
  simpa only [hid, MonoidHom.id_apply, ofAdd_toAdd] using
    freeAbelianCharEquiv_symm_apply_ofAdd (M := Trop J) Trop.generator (s.coefficient k).toAdd

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
        linarith [Int.posPart_mul_add_neg_mul_min_zero ((s.coefficient k).toAdd j)
          (s.exchangeMatrix.matrix k l)]
  · simp [toExtendedMatrix_symmetrizer]

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
  toFun s := ⟨s.toExtendedMatrix, s.toExtendedMatrix_hasFiniteFrozenSupport⟩
  invFun B := B.1.toTropicalYSeed B.2
  left_inv := YSeed.toTropicalYSeed_toExtendedMatrix
  right_inv B := Subtype.ext (B.1.toExtendedMatrix_toTropicalYSeed B.2)

@[simp]
theorem tropicalYSeedEquiv_apply_val (s : YSeed K (Trop J)) :
    (tropicalYSeedEquiv s).val = s.toExtendedMatrix :=
  (rfl)

theorem tropicalYSeedEquiv_symm_apply
    (B : {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
      B.HasFiniteFrozenSupport}) :
    tropicalYSeedEquiv.symm B = B.val.toTropicalYSeed B.property :=
  (rfl)

/-- With finitely many frozen indices, every extended matrix has finite frozen columns. -/
noncomputable def tropicalYSeedEquivOfFinite [Finite J] :
    YSeed K (Trop J) ≃ ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) where
  toFun := YSeed.toExtendedMatrix
  invFun B := B.toTropicalYSeed B.hasFiniteFrozenSupport_of_finite
  left_inv := YSeed.toTropicalYSeed_toExtendedMatrix
  right_inv B := B.toExtendedMatrix_toTropicalYSeed _

@[simp]
theorem tropicalYSeedEquivOfFinite_apply [Finite J] (s : YSeed K (Trop J)) :
    tropicalYSeedEquivOfFinite s = s.toExtendedMatrix :=
  (rfl)

theorem tropicalYSeedEquivOfFinite_symm_apply [Finite J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    tropicalYSeedEquivOfFinite.symm B = B.toTropicalYSeed B.hasFiniteFrozenSupport_of_finite :=
  (rfl)

/-- Converting a matrix mutation back to a tropical Y-seed gives its coefficient mutation. -/
theorem toTropicalYSeed_mutation [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) :
    (B.mutation k).toTropicalYSeed (h.mutation k) = (B.toTropicalYSeed h).mutation k := by
  apply (tropicalYSeedEquiv (K := K) (J := J)).injective
  apply Subtype.ext
  simp only [tropicalYSeedEquiv_apply_val]
  rw [toExtendedMatrix_toTropicalYSeed, YSeed.toExtendedMatrix_mutation,
    toExtendedMatrix_toTropicalYSeed]

/-- Relabelling equivalence on finite-support extended matrices. It restricts the existing
exchange-matrix reindexing equivalence, without changing its action. -/
noncomputable def reindexFiniteFrozen (eK : K ≃ K') (eJ : J ≃ J') :
    {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) // B.HasFiniteFrozenSupport} ≃
      {B : ExchangeMatrix (Function.Embedding.inl : K' ↪ K' ⊕ J') //
        B.HasFiniteFrozenSupport} :=
  (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
    (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl])).subtypeEquiv
    fun B ↦ (B.hasFiniteFrozenSupport_reindex_iff eK eJ).symm

@[simp]
theorem reindexFiniteFrozen_val (eK : K ≃ K') (eJ : J ≃ J')
    (B : {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
      B.HasFiniteFrozenSupport}) :
    (reindexFiniteFrozen eK eJ B).val =
      reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
        (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl]) B.val :=
  (rfl)

/-- Under the tropical correspondence, frozen relabelling is precisely relabelling the
coefficient generators, while mutable relabelling changes the coefficient's column. -/
@[simp]
theorem tropicalYSeedEquiv_symm_reindex_coefficient (eK : K ≃ K') (eJ : J ≃ J')
    (B : {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
      B.HasFiniteFrozenSupport}) (k : K') :
    (tropicalYSeedEquiv.symm (reindexFiniteFrozen eK eJ B)).coefficient k =
      Trop.reindex eJ ((tropicalYSeedEquiv.symm B).coefficient (eK.symm k)) := by
  apply Multiplicative.toAdd.injective
  ext j
  simp [tropicalYSeedEquiv, Trop.toAdd_reindex]

/-- The principal part of simultaneous relabelling is the existing mutable Y-seed
relabelling, with the same chosen symmetrizer. -/
@[simp]
theorem tropicalYSeedEquiv_symm_reindex_exchangeMatrix (eK : K ≃ K') (eJ : J ≃ J')
    (B : {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
      B.HasFiniteFrozenSupport}) :
    (tropicalYSeedEquiv.symm (reindexFiniteFrozen eK eJ B)).exchangeMatrix =
      (YSeed.reindex eK (tropicalYSeedEquiv.symm B)).exchangeMatrix := by
  ext : 1
  · ext i k
    simp [tropicalYSeedEquiv, principal_matrix]
  · simp [tropicalYSeedEquiv]

end ExchangeMatrix

end TauCeti
