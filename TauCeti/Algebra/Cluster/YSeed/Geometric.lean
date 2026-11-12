/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Tropical
public import TauCeti.Algebra.Cluster.YSeed.Basic

import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Tropical coefficients and finite-support extended exchange matrices

A tropical coefficient is a finitely supported integer exponent vector. Reading these
vectors as frozen columns identifies Y-seeds over `Trop J` with extended exchange matrices
on `K ⊕ J` whose frozen columns have finite support. The principal matrix and its chosen
symmetrizer are retained. The mutable and frozen index types can both be infinite.

The correspondence intertwines the existing coefficient mutation with the existing matrix
mutation. Matrix mutation is not defined by transporting coefficient mutation. Its direct
entry formula also proves preservation of finite frozen support.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, §2, the tropical coefficient
  and extended exchange-matrix presentations of geometric type.
-/

public section

namespace TauCeti

variable {K K' J J' : Type*}

namespace ExchangeMatrix

/-- Each frozen column has finite support. There is no global finite frozen index set
when the mutable index type is infinite. -/
def HasFiniteFrozenSupport (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) : Prop :=
  ∀ k, (Function.support fun j ↦ B.matrix (Sum.inr j) k).Finite

/-- A finite frozen index type makes every frozen column finitely supported. -/
theorem hasFiniteFrozenSupport_of_finite [Finite J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    B.HasFiniteFrozenSupport :=
  fun _ ↦ Set.toFinite _

/-- Read a frozen column as a finitely supported exponent vector. -/
noncomputable def frozenColumn (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) : J →₀ ℤ :=
  Finsupp.ofSupportFinite (fun j ↦ B.matrix (Sum.inr j) k) (h k)

@[simp]
theorem frozenColumn_apply (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) (j : J) :
    B.frozenColumn h k j = B.matrix (Sum.inr j) k :=
  (rfl)

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
  (rfl)

@[simp]
theorem toTropicalYSeed_exchangeMatrix
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : (B.toTropicalYSeed h).exchangeMatrix = B.principal :=
  (rfl)

/-- Every entry in a mutated frozen column is supported on the union of that column's
old support and the mutation column's old support. -/
theorem support_mutation_frozen_subset [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (k l : K) :
    (Function.support fun j ↦ (B.mutation k).matrix (Sum.inr j) l) ⊆
      (Function.support fun j ↦ B.matrix (Sum.inr j) l) ∪
        Function.support fun j ↦ B.matrix (Sum.inr j) k := by
  intro j hj
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hj (by simp [mutation_matrix, matrixMutation_apply, h.1, h.2])

/-- Matrix mutation preserves finite support of every frozen column, directly from its
entry formula. -/
theorem HasFiniteFrozenSupport.mutation [DecidableEq K] [DecidableEq J]
    {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)}
    (h : B.HasFiniteFrozenSupport) (k : K) : (B.mutation k).HasFiniteFrozenSupport :=
  fun l ↦ ((h l).union (h k)).subset (B.support_mutation_frozen_subset k l)

/-- An initially zero frozen row is fixed by mutation. -/
theorem mutation_frozen_row_eq_zero [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) {j : J}
    (h : ∀ l, B.matrix (Sum.inr j) l = 0) (k l : K) :
    (B.mutation k).matrix (Sum.inr j) l = 0 := by
  simp [mutation_matrix, matrixMutation_apply, h]

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
    s.toExtendedMatrix.HasFiniteFrozenSupport :=
  fun k ↦ (s.coefficient k).toAdd.hasFiniteSupport

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
    rfl
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

/-- Tropical auxiliary addition produces the correction in rectangular matrix mutation. -/
private theorem tropical_mutation_correction (c b : ℤ) :
    b⁺ * c + (-b) * min c 0 = c⁺ * b⁺ - c⁻ * b⁻ := by
  by_cases hc : 0 ≤ c
  · simp only [posPart_def, negPart_def, max_eq_left hc,
      max_eq_right (neg_nonpos.mpr hc), min_eq_right hc, mul_zero]
    ring
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have hb := posPart_sub_negPart b
    simp only [posPart_def, negPart_def] at hb
    simp only [posPart_def, negPart_def, max_eq_right hc',
      max_eq_left (neg_nonneg.mpr hc'), min_eq_left hc', zero_mul, zero_sub]
    nlinarith

/-- Reading tropical exponents intertwines coefficient mutation with the actual extended
matrix mutation. This equality is proved entrywise from the two mutation formulas. -/
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
        linarith [tropical_mutation_correction ((s.coefficient k).toAdd j)
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
  change ((B.mutation k).toTropicalYSeed (h.mutation k)).toExtendedMatrix =
    ((B.toTropicalYSeed h).mutation k).toExtendedMatrix
  rw [toExtendedMatrix_toTropicalYSeed, YSeed.toExtendedMatrix_mutation,
    toExtendedMatrix_toTropicalYSeed]

/-- Simultaneous mutable and frozen relabelling preserves finite frozen support. -/
theorem hasFiniteFrozenSupport_reindex_iff (eK : K ≃ K') (eJ : J ≃ J')
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl])
      B).HasFiniteFrozenSupport ↔ B.HasFiniteFrozenSupport := by
  constructor
  · intro h k
    have hf := (h (eK k)).preimage eJ.injective.injOn
    simpa only [Function.support, Set.preimage_ofPred_eq, reindex_matrix,
      Matrix.submatrix_apply, Equiv.sumCongr_symm,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply] using hf
  · intro h k
    simpa only [Function.support, Set.preimage_ofPred_eq, reindex_matrix,
      Matrix.submatrix_apply, Equiv.sumCongr_symm,
      Equiv.sumCongr_apply, Sum.map_inr] using
      (h (eK.symm k)).preimage eJ.symm.injective.injOn

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

/-- A specified initially zero frozen row stays zero after any finite sequence of actual
matrix mutations. This requires no finiteness of either index type. -/
theorem foldl_mutation_frozen_row_eq_zero [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) {j : J}
    (h : ∀ l, B.matrix (Sum.inr j) l = 0) (w : List K) (l : K) :
    (w.foldl (fun C k ↦ C.mutation k) B).matrix (Sum.inr j) l = 0 := by
  induction w generalizing B with
  | nil => exact h l
  | cons k _w ih => exact ih (B.mutation k) (B.mutation_frozen_row_eq_zero h k)

/-- For finitely many mutable directions, one finite set of initially active frozen rows
contains every active frozen row after any finite sequence of mutations. This is a support
invariant of the existing matrix action, not a new word-action API. -/
theorem exists_finset_frozen_support_foldl [Finite K] [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) :
    ∃ S : Finset J, ∀ w : List K, ∀ j ∉ S, ∀ l,
      (w.foldl (fun C k ↦ C.mutation k) B).matrix (Sum.inr j) l = 0 := by
  classical
  have hf : (⋃ k, Function.support fun j ↦ B.matrix (Sum.inr j) k).Finite :=
    Set.finite_iUnion h
  refine ⟨hf.toFinset, fun w j hj l ↦ ?_⟩
  apply B.foldl_mutation_frozen_row_eq_zero _ w l
  have hnot : j ∉ ⋃ k, Function.support fun j ↦ B.matrix (Sum.inr j) k := by
    simpa using hj
  simpa only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] using hnot

end ExchangeMatrix

end TauCeti
