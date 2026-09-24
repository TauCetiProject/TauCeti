/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.IntegralMatrix
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Conjugation

/-!
# The rank-two spin carrier is the rank-two symplectic carrier

The diagrams `B₂` and `C₂` are the same, and the spin representation of `Spin₅` is the standard
representation of `Sp₄`. This file makes the corresponding statement about the two explicit
carriers Tau Ceti builds for that diagram: the full-weight type-`B` spin carrier
`TauCeti.TypeBSpinCarrier.groupScheme 1`, built on the exterior algebra of a rank-two isotropic
space, and the full-weight type-`C` standard carrier `TauCeti.SpStd.groupScheme 1`, built on the
four-dimensional symplectic module. A signed permutation of the two four-element lattice bases
conjugates the numbered simple root subgroups of the first onto those of the second and the weight
torus of the first onto the weight torus of the second, so conjugation by it identifies the two
carriers' points over every commutative ring.

Both carriers use the Bourbaki numbering of their own diagram, which disagree: node `0` of `B₂` is
the long simple root `ε₀ - ε₁` and node `1` the short one `ε₁`, while node `0` of `C₂` is the short
root and node `1` the long one. The identification therefore exchanges the two nodes, both on the
root subgroups and on the coordinates of the weight torus. In the exterior basis indexed by subsets
of `{0, 1}` and the symplectic basis `e₀, e₁, f₀, f₁`, the change of basis is

```text
{0, 1} ↦ e₀,    {0} ↦ e₁,    {1} ↦ f₁,    ∅ ↦ -f₀,
```

which carries each spin weight to the corresponding symplectic weight with its two coordinates
exchanged. The spin lattice basis is enumerated by `Fin (dimension 1)`, which is `Fin 4` only after
computing `dimension 1`, so the identification first reindexes along
`TauCeti.TypeBSpinCarrier.dimension_one` and then conjugates.

Nothing here asserts that either carrier is the pinned simply connected group scheme of its
diagram.

## Main definitions

* `TauCeti.TypeBSpinCarrier.rankTwoRootMatrix` and
  `TauCeti.TypeBSpinCarrier.rankTwoRootIntMatrix`: the integral matrices of the four numbered
  simple root generators on the rank-two exterior basis and on the enumerated lattice basis.
* `TauCeti.TypeBSpinCarrier.symplecticNode` and `TauCeti.TypeBSpinCarrier.symplecticRootIndex`: the
  exchange of the two nodes, from the `B₂` numbering of the spin carrier to the `C₂` numbering of
  the symplectic carrier.
* `TauCeti.TypeBSpinCarrier.symplecticBasisChange` and
  `TauCeti.TypeBSpinCarrier.symplecticChangeOfBasis`: the signed permutation matrix above, on the
  unenumerated and on the enumerated coordinates.
* `TauCeti.TypeBSpinCarrier.pointsMulEquivSymplecticPoints`: the resulting identification of the
  rank-two spin carrier points with the rank-two symplectic carrier points.

## Main results

* `TauCeti.TypeBSpinCarrier.rep_rootGenerator_exteriorBasis_rankTwo`: the action of the numbered
  simple root generators on the rank-two exterior basis.
* `TauCeti.TypeBSpinCarrier.coe_rootSubgroupPoints_eq_one_add_smul_rankTwo`: each root subgroup
  point of the rank-two spin carrier is `1 + u X` for the integral generator matrix `X`.
* `TauCeti.TypeBSpinCarrier.coe_pointsMulEquivSymplecticPoints_apply`: the identification is
  conjugation by the change of basis, after reindexing the four spin coordinates.
* `TauCeti.TypeBSpinCarrier.pointsMulEquivSymplecticPoints_rootSubgroupPoints` and
  `TauCeti.TypeBSpinCarrier.pointsMulEquivSymplecticPoints_weightTorusPoints`: the identification
  carries the numbered root subgroups and the weight torus of the spin carrier to those of the
  symplectic carrier, exchanging the two nodes.
* `TauCeti.TypeBSpinCarrier.pointsMulEquivSymplecticPoints_frobenius`: the identification commutes
  with the Frobenius maps of the two carriers.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III.
* R. W. Carter, *Simple Groups of Lie Type*, §§11.3 and 13.4.
-/

public section

open Matrix

namespace TauCeti.TypeBSpinCarrier

universe v

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-! ## The generators on the rank-two exterior basis -/

/-- **The integral matrices of the numbered simple root generators on the rank-two exterior
basis**, with rows and columns indexed by subsets of `{0, 1}`. The long raising generator moves
`{1}` to `{0}`, the short raising generator moves `∅` to `{1}` and `{0}` to `{0, 1}`, and the
lowering generators reverse these moves. -/
def rankTwoRootMatrix :
    Fin (1 + 1) ⊕ Fin (1 + 1) → Matrix (Finset (Fin (1 + 1))) (Finset (Fin (1 + 1))) ℤ
  | .inl 0 => single {0} {1} 1
  | .inl 1 => single {1} ∅ 1 + single {0, 1} {0} 1
  | .inr 0 => single {1} {0} 1
  | .inr 1 => single ∅ {1} 1 + single {0} {0, 1} 1

private theorem finset_fin_two_cases (S : Finset (Fin (1 + 1))) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
  revert S
  decide

private theorem finset_fin_two_ne : ({1} : Finset (Fin (1 + 1))) ≠ {0, 1} ∧
    (∅ : Finset (Fin (1 + 1))) ≠ {0, 1} ∧ ({0} : Finset (Fin (1 + 1))) ≠ {0, 1} ∧
      ({0, 1} : Finset (Fin (1 + 1))) ≠ {0} := by
  decide

section ExteriorBasis

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  (b : Module.Basis (Fin (1 + 1)) R W)

/-- The three relations among the exterior basis vectors of a rank-two free module that the
generator computations use. -/
private theorem rankTwo_exteriorBasis :
    b.ExteriorAlgebra ∅ = 1 ∧
      b.ExteriorAlgebra {0, 1} = ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 1) ∧
      ExteriorAlgebra.ι R (b 1) * ExteriorAlgebra.ι R (b 0) =
        -(ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 1)) := by
  refine ⟨by rw [ExteriorAlgebra.basis_apply]; simp,
    TauCeti.ExteriorAlgebra.basis_pair b (by decide), ?_⟩
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

private theorem ι_mul_contractLeft_one_exteriorBasis (S : Finset (Fin (1 + 1))) :
    ExteriorAlgebra.ι R (b 0) * CliffordAlgebra.contractLeft (b.coord 1) (b.ExteriorAlgebra S) =
      ∑ T, (rankTwoRootMatrix (.inl 0) T S : R) • b.ExteriorAlgebra T := by
  obtain ⟨hempty, h01, -⟩ := rankTwo_exteriorBasis b
  have hι : CliffordAlgebra.ι (0 : QuadraticForm R W) = ExteriorAlgebra.ι R := rfl
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl <;>
    simp [rankTwoRootMatrix, single_apply, finset_fin_two_ne, hempty, h01, hι,
      CliffordAlgebra.contractLeft_ι_mul]

private theorem ι_mul_involute_exteriorBasis (S : Finset (Fin (1 + 1))) :
    ExteriorAlgebra.ι R (b 1) * CliffordAlgebra.involute (b.ExteriorAlgebra S) =
      ∑ T, (rankTwoRootMatrix (.inl 1) T S : R) • b.ExteriorAlgebra T := by
  obtain ⟨hempty, h01, hanti⟩ := rankTwo_exteriorBasis b
  have hι : CliffordAlgebra.ι (0 : QuadraticForm R W) = ExteriorAlgebra.ι R := rfl
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl <;>
    simp [rankTwoRootMatrix, single_apply, finset_fin_two_ne, hempty, h01, hι, ← mul_assoc,
      hanti]
  -- The pair `{0, 1}` is left as `ι b₀ ι b₁ ι b₁`, which vanishes after reassociation.
  simp [mul_assoc]

private theorem ι_mul_contractLeft_zero_exteriorBasis (S : Finset (Fin (1 + 1))) :
    ExteriorAlgebra.ι R (b 1) * CliffordAlgebra.contractLeft (b.coord 0) (b.ExteriorAlgebra S) =
      ∑ T, (rankTwoRootMatrix (.inr 0) T S : R) • b.ExteriorAlgebra T := by
  obtain ⟨hempty, h01, -⟩ := rankTwo_exteriorBasis b
  have hι : CliffordAlgebra.ι (0 : QuadraticForm R W) = ExteriorAlgebra.ι R := rfl
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl <;>
    simp [rankTwoRootMatrix, single_apply, finset_fin_two_ne, hempty, h01, hι,
      CliffordAlgebra.contractLeft_ι_mul]

private theorem involute_contractLeft_one_exteriorBasis (S : Finset (Fin (1 + 1))) :
    CliffordAlgebra.involute (CliffordAlgebra.contractLeft (b.coord 1) (b.ExteriorAlgebra S)) =
      ∑ T, (rankTwoRootMatrix (.inr 1) T S : R) • b.ExteriorAlgebra T := by
  obtain ⟨hempty, h01, -⟩ := rankTwo_exteriorBasis b
  have hι : CliffordAlgebra.ι (0 : QuadraticForm R W) = ExteriorAlgebra.ι R := rfl
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl <;>
    simp [rankTwoRootMatrix, single_apply, finset_fin_two_ne, hempty, h01, hι,
      CliffordAlgebra.contractLeft_ι_mul]

end ExteriorBasis

/-- **The numbered simple root generators on the rank-two exterior basis.** Each acts on the basis
vector indexed by `S` through the column `S` of `TauCeti.TypeBSpinCarrier.rankTwoRootMatrix`. -/
theorem rep_rootGenerator_exteriorBasis_rankTwo (k : Fin (1 + 1) ⊕ Fin (1 + 1))
    (S : Finset (Fin (1 + 1))) :
    rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily k))
        ((polarizationBasis 1).ExteriorAlgebra S) =
      ∑ T, (rankTwoRootMatrix k T S : ℚ) • (polarizationBasis 1).ExteriorAlgebra T := by
  rcases k with k | k <;> fin_cases k
  · exact (rep_rootGenerator_inl_castSucc 1 0 _).trans
      (ι_mul_contractLeft_one_exteriorBasis _ S)
  · exact (rep_rootGenerator_inl_last 1 _).trans (ι_mul_involute_exteriorBasis _ S)
  · exact (rep_rootGenerator_inr_castSucc 1 0 _).trans
      (ι_mul_contractLeft_zero_exteriorBasis _ S)
  · exact (rep_rootGenerator_inr_last 1 _).trans (involute_contractLeft_one_exteriorBasis _ S)


/-! ## The generators in the lattice basis -/

/-- The integral matrix of a numbered simple root generator of the rank-two spin carrier in the
enumerated lattice basis `TauCeti.TypeBSpinCarrier.latticeBasis 1`. -/
noncomputable def rankTwoRootIntMatrix (k : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    Matrix (Fin (dimension 1)) (Fin (dimension 1)) ℤ :=
  (rankTwoRootMatrix k).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm

/-- A numbered simple root generator acts on an enumerated lattice basis vector by the
corresponding column of `TauCeti.TypeBSpinCarrier.rankTwoRootIntMatrix`. -/
theorem rep_rootGenerator_latticeBasis_eq_sum_rankTwo (k : Fin (1 + 1) ⊕ Fin (1 + 1))
    (s : Fin (dimension 1)) :
    rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily k))
        ((latticeBasis 1 s : (lattice 1).toAddSubgroup) : ExteriorAlgebra ℚ (polarization 1).W) =
      ∑ r, rankTwoRootIntMatrix k r s •
        ((latticeBasis 1 r : (lattice 1).toAddSubgroup) :
          ExteriorAlgebra ℚ (polarization 1).W) := by
  rw [coe_latticeBasis, rep_rootGenerator_exteriorBasis_rankTwo,
    ← (Fintype.equivFin (Finset (Fin (1 + 1)))).symm.sum_comp]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [coe_latticeBasis, rankTwoRootIntMatrix, submatrix_apply, Int.cast_smul_eq_zsmul]

/-- **Each numbered root subgroup point of the rank-two spin carrier is `1 + u X`** for `X` the
integral matrix of the corresponding generator. -/
theorem coe_rootSubgroupPoints_eq_one_add_smul_rankTwo (k : Fin (1 + 1) ⊕ Fin (1 + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints 1 k A u : GL (Fin (dimension 1)) A) :
        Matrix (Fin (dimension 1)) (Fin (dimension 1)) A) =
      1 + Multiplicative.toAdd u • (rankTwoRootIntMatrix k).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply] using
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul
      _ _ (rep 1) (lattice 1).toAddSubgroup (rep_kostantForm_mem_lattice 1) k
      (isNilpotent_rep_rootGenerator 1 k) (latticeBasis 1) (rankTwoRootIntMatrix k)
      (nilpotencyClass_rep_rootGenerator_le_two 1 k)
      (rep_rootGenerator_latticeBasis_eq_sum_rankTwo k)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)

/-! ## The change of basis to the symplectic carrier -/

/-- **The node exchange between the two rank-two numberings.** Node `0` of `B₂`, the long simple
root of the spin carrier, is node `1` of `C₂`, the long simple root of the symplectic carrier, and
the short nodes correspond likewise. -/
def symplecticNode : Equiv.Perm (Fin (1 + 1)) :=
  Equiv.swap 0 1

/-- The numbered root generator of the symplectic carrier corresponding to a numbered root
generator of the spin carrier: raising goes to raising and lowering to lowering, at the exchanged
node. -/
def symplecticRootIndex (k : Fin (1 + 1) ⊕ Fin (1 + 1)) : Fin (1 + 1) ⊕ Fin (1 + 1) :=
  Sum.map symplecticNode symplecticNode k

@[simp]
theorem symplecticNode_zero : symplecticNode 0 = 1 :=
  Equiv.swap_apply_left 0 1

@[simp]
theorem symplecticNode_one : symplecticNode 1 = 0 :=
  Equiv.swap_apply_right 0 1

@[simp]
theorem symplecticRootIndex_inl (i : Fin (1 + 1)) :
    symplecticRootIndex (.inl i) = .inl (symplecticNode i) :=
  (rfl)

@[simp]
theorem symplecticRootIndex_inr (i : Fin (1 + 1)) :
    symplecticRootIndex (.inr i) = .inr (symplecticNode i) :=
  (rfl)

/-- The node exchange is an involution on the numbered root generators. -/
@[simp]
theorem symplecticRootIndex_symplecticRootIndex (k : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    symplecticRootIndex (symplecticRootIndex k) = k := by
  rcases k with k | k <;> simp [symplecticRootIndex, symplecticNode]

/-- **The change of basis from the rank-two exterior basis to the symplectic coordinates**, with
rows indexed by the symplectic coordinates `e₀, e₁, f₀, f₁` and columns by subsets of `{0, 1}`:
`{0, 1} ↦ e₀`, `{0} ↦ e₁`, `{1} ↦ f₁` and `∅ ↦ -f₀`. -/
def symplecticBasisChange : Matrix (Fin (1 + 1) ⊕ Fin (1 + 1)) (Finset (Fin (1 + 1))) ℤ :=
  single (.inl 0) {0, 1} 1 + single (.inl 1) {0} 1 + single (.inr 1) {1} 1 -
    single (.inr 0) ∅ 1

/-- The integral matrices of the numbered root generators of the rank-two symplectic carrier, in
its unenumerated coordinates. -/
private def symplecticRootTable :
    Fin (1 + 1) ⊕ Fin (1 + 1) → Matrix (Fin (1 + 1) ⊕ Fin (1 + 1)) (Fin (1 + 1) ⊕ Fin (1 + 1)) ℤ
  | .inl 0 => single (.inl 0) (.inl 1) 1 - single (.inr 1) (.inr 0) 1
  | .inl 1 => single (.inl 1) (.inr 1) 1
  | .inr 0 => single (.inl 1) (.inl 0) 1 - single (.inr 0) (.inr 1) 1
  | .inr 1 => single (.inr 1) (.inl 1) 1

private theorem symplecticBasisChange_mul_rankTwoRootMatrix (k : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    symplecticBasisChange * rankTwoRootMatrix k =
      symplecticRootTable (symplecticRootIndex k) * symplecticBasisChange := by
  revert k
  decide

private theorem symplecticBasisChange_mul_transpose :
    symplecticBasisChange * symplecticBasisChangeᵀ = 1 := by
  decide

private theorem transpose_mul_symplecticBasisChange :
    symplecticBasisChangeᵀ * symplecticBasisChange = 1 := by
  decide

private theorem next_zero : SpStd.next 1 0 (by decide) = 1 :=
  Fin.ext (by rw [SpStd.val_next]; rfl)

private theorem rootIntMatrix_eq_submatrix :
    ∀ k : Fin (1 + 1) ⊕ Fin (1 + 1), SpStd.rootIntMatrix 1 k =
      (symplecticRootTable k).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  | .inl 0 => by
    rw [SpStd.rootIntMatrix_inl_of_ne_last 1 0 (by decide), next_zero]
    simp [symplecticRootTable, submatrix_sub]
  | .inl 1 => (SpStd.rootIntMatrix_inl_last 1).trans (by simp [symplecticRootTable])
  | .inr 0 => by
    rw [SpStd.rootIntMatrix_inr_of_ne_last 1 0 (by decide), next_zero]
    simp [symplecticRootTable, submatrix_sub]
  | .inr 1 => (SpStd.rootIntMatrix_inr_last 1).trans (by simp [symplecticRootTable])

/-! ## The identification with the symplectic carrier -/

/-- The rank-two spin module and the rank-two symplectic module both have four basis vectors. -/
theorem dimension_one : dimension 1 = 1 + 1 + (1 + 1) :=
  rfl

/-- The symplectic lattice coordinates, read as subsets of `{0, 1}` through the enumeration of the
spin lattice basis. -/
private noncomputable def spinIndex : Fin (1 + 1 + (1 + 1)) ≃ Finset (Fin (1 + 1)) :=
  (finCongr dimension_one).symm.trans (Fintype.equivFin _).symm

/-- **The change of basis from the spin lattice basis to the symplectic lattice basis**, as an
invertible integral matrix on the symplectic coordinates: the spin lattice basis is reindexed along
`TauCeti.TypeBSpinCarrier.dimension_one` and then carried to the symplectic basis by
`TauCeti.TypeBSpinCarrier.symplecticBasisChange`. It is a signed permutation matrix, inverted by
its transpose. -/
noncomputable def symplecticChangeOfBasis : GL (Fin (1 + 1 + (1 + 1))) ℤ where
  val := symplecticBasisChange.submatrix finSumFinEquiv.symm spinIndex
  inv := symplecticBasisChangeᵀ.submatrix spinIndex finSumFinEquiv.symm
  val_inv := by
    rw [submatrix_mul_equiv, symplecticBasisChange_mul_transpose, submatrix_one_equiv]
  inv_val := by
    rw [submatrix_mul_equiv, transpose_mul_symplecticBasisChange, submatrix_one_equiv]

/-- The reindexed integral matrix of a numbered spin generator, on the symplectic coordinates. -/
private theorem reindex_rankTwoRootIntMatrix (k : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    (rankTwoRootIntMatrix k).submatrix (finCongr dimension_one).symm
        (finCongr dimension_one).symm =
      (rankTwoRootMatrix k).submatrix spinIndex spinIndex := by
  rw [rankTwoRootIntMatrix, submatrix_submatrix]
  -- `spinIndex` is by definition the composite of the two reindexing equivalences.
  rfl

/-- The change of basis intertwines the reindexed integral matrix of each numbered spin generator
with the integral matrix of the symplectic generator at the exchanged node. -/
private theorem symplecticChangeOfBasis_mul_rankTwoRootIntMatrix
    (k : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    (symplecticChangeOfBasis : Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) ℤ) *
        (rankTwoRootIntMatrix k).submatrix (finCongr dimension_one).symm
          (finCongr dimension_one).symm *
        (symplecticChangeOfBasis⁻¹ : GL (Fin (1 + 1 + (1 + 1))) ℤ) =
      SpStd.rootIntMatrix 1 (symplecticRootIndex k) := by
  rw [reindex_rankTwoRootIntMatrix, rootIntMatrix_eq_submatrix]
  -- Expose the defining submatrices of the change of basis and of its inverse.
  change symplecticBasisChange.submatrix _ _ * (rankTwoRootMatrix k).submatrix _ _ *
    symplecticBasisChangeᵀ.submatrix _ _ = _
  rw [submatrix_mul_equiv, submatrix_mul_equiv, symplecticBasisChange_mul_rankTwoRootMatrix,
    Matrix.mul_assoc, symplecticBasisChange_mul_transpose, Matrix.mul_one]

/-- The change of basis carries each numbered spin root subgroup to the symplectic root subgroup at
the exchanged node. -/
private theorem symplecticChangeOfBasis_conj_rootSubgroupPoints (k : Fin (1 + 1) ⊕ Fin (1 + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis *
        (finCongr dimension_one).reindexGL A (rootSubgroupPoints 1 k A u) *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis)⁻¹ =
      SpStd.rootSubgroupPoints 1 (symplecticRootIndex k) A u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, Equiv.coe_reindexGL,
    coe_rootSubgroupPoints_eq_one_add_smul_rankTwo, SpStd.coe_rootSubgroupPoints_eq_one_add_smul,
    ← symplecticChangeOfBasis_mul_rankTwoRootIntMatrix]
  have hmap (M N : Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) ℤ) :
      (M * N).map (Int.cast : ℤ → A) = M.map Int.cast * N.map Int.cast :=
    Matrix.map_mul (f := Int.castRingHom A)
  have hinv :
      (symplecticChangeOfBasis : Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) ℤ) *
        (symplecticChangeOfBasis⁻¹ : GL (Fin (1 + 1 + (1 + 1))) ℤ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- The image of an integral matrix in `GL` over `A` is its entrywise image.
  have hcoe (g : GL (Fin (1 + 1 + (1 + 1))) ℤ) :
      ((Matrix.GeneralLinearGroup.map (Int.castRingHom A) g : GL (Fin (1 + 1 + (1 + 1))) A) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) A) =
        (g : Matrix _ _ ℤ).map Int.cast :=
    rfl
  have hsub :
      (1 + Multiplicative.toAdd u • (rankTwoRootIntMatrix k).map (Int.cast : ℤ → A)).submatrix
          (finCongr dimension_one).symm (finCongr dimension_one).symm =
        1 + Multiplicative.toAdd u • ((rankTwoRootIntMatrix k).submatrix
          (finCongr dimension_one).symm (finCongr dimension_one).symm).map Int.cast := by
    ext i j
    simp [Matrix.one_apply]
  rw [algebraMap_int_eq, hcoe, hcoe, hsub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, ← hmap, ← hmap, ← hmap, hinv,
    Matrix.map_one Int.cast Int.cast_zero Int.cast_one]

private theorem symplecticBasisChange_ne_zero :
    ∀ (a : Fin (1 + 1) ⊕ Fin (1 + 1)) (S : Finset (Fin (1 + 1))),
      symplecticBasisChange a S ≠ 0 →
        (a = .inl 0 ∧ S = {0, 1}) ∨ (a = .inl 1 ∧ S = {0}) ∨ (a = .inr 1 ∧ S = {1}) ∨
          (a = .inr 0 ∧ S = ∅) := by
  intro a S
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl <;> revert a <;> decide

/-- The change of basis matches weights: each spin weight is the weight of the corresponding
symplectic coordinate with its two coordinates exchanged. -/
private theorem typeBSpinWeight_eq_weight_comp_symplecticNode {a : Fin (1 + 1) ⊕ Fin (1 + 1)}
    {S : Finset (Fin (1 + 1))} (h : symplecticBasisChange a S ≠ 0) :
    DynkinType.typeBSpinWeight S = SpStd.weight 1 a ∘ symplecticNode := by
  have hsucc : Order.succ (0 : Fin (1 + 1)) = 1 := rfl
  rcases symplecticBasisChange_ne_zero a S h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    funext j <;> fin_cases j <;>
    simp [DynkinType.TypeC.weight_apply, symplecticNode, hsucc]

/-- The change of basis carries the spin weight torus to the symplectic weight torus, with the two
torus coordinates exchanged. -/
private theorem symplecticChangeOfBasis_conj_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin (1 + 1) → Aˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis *
        (finCongr dimension_one).reindexGL A (weightTorusPoints 1 A s) *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis)⁻¹ =
      SpStd.weightTorusPoints 1 A (s ∘ symplecticNode) := by
  -- The symplectic torus parameter is the spin one relabelled along the node exchange.
  have hs : s ∘ symplecticNode =
      MulEquiv.arrowCongr symplecticNode (MulEquiv.refl Aˣ) s := by
    funext j
    simp [symplecticNode, Equiv.symm_swap]
  set Q := Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis
  -- Conjugating a diagonal matrix: it suffices that `Q D₁ = D₂ Q`.
  suffices hcomm : (Q : Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) A) *
      (((finCongr dimension_one).reindexGL A (weightTorusPoints 1 A s) :
        GL (Fin (1 + 1 + (1 + 1))) A) : Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) A) =
      ((SpStd.weightTorusPoints 1 A (s ∘ symplecticNode) : GL (Fin (1 + 1 + (1 + 1))) A) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) A) * Q by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]
  rw [Equiv.coe_reindexGL, coe_weightTorusPoints, SpStd.coe_weightTorusPoints,
    TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe, diagGL_coe,
    submatrix_diagonal_equiv]
  ext a j
  rw [mul_diagonal, diagonal_mul]
  by_cases h : symplecticBasisChange (finSumFinEquiv.symm a) (spinIndex j) = 0
  · have hQ : (Q : Matrix _ _ A) a j = 0 := by
      -- An entry of the image of the integral change of basis is the image of its entry.
      change algebraMap ℤ A (symplecticBasisChange (finSumFinEquiv.symm a) (spinIndex j)) = 0
      rw [h, map_zero]
    rw [hQ, zero_mul, mul_zero]
  · rw [mul_comm]
    congr 3
    rw [SpStd.basisWeight_apply, hs, torusCharacter_mulEquivArrowCongr,
      ← typeBSpinWeight_eq_weight_comp_symplecticNode h]
    -- The weight of the reindexed spin basis vector is by definition the spin weight of its sign
    -- set, which is `spinIndex j`.
    rfl

/-- The rank-two spin carrier points, presented as the points of the Kostant toral closure. -/
private theorem points_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    points 1 A = TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
      (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep 1) (lattice 1).toAddSubgroup
      (rep_kostantForm_mem_lattice 1) (isNilpotent_rep_rootGenerator 1)
      (latticeBasis 1) (basisWeight 1) A := by
  rw [points_def, TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def,
    definingIdeal_def]

/-- The rank-two symplectic carrier points, presented as the points of the Kostant toral
closure. -/
private theorem symplecticPoints_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    SpStd.points 1 A = TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
      (SpStd.rootGenerator 1) (SpStd.cartanGenerator 1) (SpStd.rep 1)
      (SpStd.lattice 1).toAddSubgroup
      (fun _ hu _ hv => SpStd.rep_kostantForm_mem_lattice 1 hu hv)
      (SpStd.isNilpotent_rep_rootGenerator 1) (SpStd.latticeBasis 1) (SpStd.basisWeight 1) A := by
  rw [SpStd.points_def, TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def,
    SpStd.definingIdeal_def]

private theorem symplecticChangeOfBasis_inv_conj (A : Type v) [CommRing A]
    (g : GL (Fin (dimension 1)) A) (x : GL (Fin (1 + 1 + (1 + 1))) A)
    (hx : Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis *
        (finCongr dimension_one).reindexGL A g *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis)⁻¹ = x) :
    (finCongr dimension_one).symm.reindexGL A
        ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis)⁻¹ * x *
          Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis) = g := by
  rw [← hx]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [Equiv.reindexGL_symm, MulEquiv.symm_apply_apply]

/-- **The rank-two spin carrier is the rank-two symplectic carrier.** Over every commutative ring
`A`, reindexing the spin lattice basis to the symplectic coordinates and conjugating by
`TauCeti.TypeBSpinCarrier.symplecticChangeOfBasis` identifies the points of
`TauCeti.TypeBSpinCarrier.groupScheme 1` with the points of `TauCeti.SpStd.groupScheme 1`. -/
noncomputable def pointsMulEquivSymplecticPoints (A : Type v) [CommRing A] :
    points 1 A ≃* SpStd.points 1 A :=
  (MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup A)).trans <|
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsReindexConjMulEquiv
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ dimension_one _ _ symplecticChangeOfBasis
      (fun B _ k q => by
        rw [← (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B)).symm_apply_apply q,
          ← coe_rootSubgroupPoints, symplecticChangeOfBasis_conj_rootSubgroupPoints,
          ← symplecticPoints_eq_kostantToralPointsSubgroup]
        exact SetLike.coe_mem _)
      (fun B _ s => by
        rw [← coe_weightTorusPoints, symplecticChangeOfBasis_conj_weightTorusPoints,
          ← symplecticPoints_eq_kostantToralPointsSubgroup]
        exact SetLike.coe_mem _)
      (fun B _ k q => by
        rw [← (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B)).symm_apply_apply q,
          ← SpStd.coe_rootSubgroupPoints, ← symplecticRootIndex_symplecticRootIndex k,
          symplecticChangeOfBasis_inv_conj B _ _
            (symplecticChangeOfBasis_conj_rootSubgroupPoints _ B _),
          ← points_eq_kostantToralPointsSubgroup]
        exact SetLike.coe_mem _)
      (fun B _ s => by
        have hs : s = (s ∘ symplecticNode) ∘ symplecticNode := by
          funext j
          simp [symplecticNode]
        rw [← SpStd.coe_weightTorusPoints, hs,
          symplecticChangeOfBasis_inv_conj B _ _
            (symplecticChangeOfBasis_conj_weightTorusPoints B _),
          ← points_eq_kostantToralPointsSubgroup]
        exact SetLike.coe_mem _) A).trans
    (MulEquiv.subgroupCongr (symplecticPoints_eq_kostantToralPointsSubgroup A).symm)

/-- The identification of the rank-two carriers reindexes and conjugates by
`TauCeti.TypeBSpinCarrier.symplecticChangeOfBasis`. -/
theorem coe_pointsMulEquivSymplecticPoints_apply (A : Type v) [CommRing A] (g : points 1 A) :
    (pointsMulEquivSymplecticPoints A g : GL (Fin (1 + 1 + (1 + 1))) A) =
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis *
        (finCongr dimension_one).reindexGL A g *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis)⁻¹ := by
  rw [pointsMulEquivSymplecticPoints, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply,
    TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralPointsReindexConjMulEquiv_apply,
    MulEquiv.subgroupCongr_apply]

/-- **The identification carries each numbered spin root subgroup to the symplectic root subgroup
at the exchanged node**, with the same parameter. -/
@[simp]
theorem pointsMulEquivSymplecticPoints_rootSubgroupPoints (k : Fin (1 + 1) ⊕ Fin (1 + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    pointsMulEquivSymplecticPoints A (rootSubgroupPoints 1 k A u) =
      SpStd.rootSubgroupPoints 1 (symplecticRootIndex k) A u := by
  apply Subtype.ext
  rw [coe_pointsMulEquivSymplecticPoints_apply, symplecticChangeOfBasis_conj_rootSubgroupPoints]

/-- **The identification carries the spin weight torus to the symplectic weight torus**, with the
two torus coordinates exchanged. -/
@[simp]
theorem pointsMulEquivSymplecticPoints_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin (1 + 1) → Aˣ) :
    pointsMulEquivSymplecticPoints A (weightTorusPoints 1 A s) =
      SpStd.weightTorusPoints 1 A (s ∘ symplecticNode) := by
  apply Subtype.ext
  rw [coe_pointsMulEquivSymplecticPoints_apply, symplecticChangeOfBasis_conj_weightTorusPoints]

/-- **The identification commutes with the `p ^ k`-power Frobenius maps of the two carriers**,
since the change of basis is integral. -/
@[simp]
theorem pointsMulEquivSymplecticPoints_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : points 1 A) :
    pointsMulEquivSymplecticPoints A (frobenius 1 p k A g) =
      SpStd.frobenius 1 p k A (pointsMulEquivSymplecticPoints A g) := by
  apply Subtype.ext
  rw [SpStd.coe_frobenius, coe_pointsMulEquivSymplecticPoints_apply,
    coe_pointsMulEquivSymplecticPoints_apply,
    coe_frobenius, map_mul, map_mul, map_inv]
  -- Frobenius fixes the integral change of basis and commutes with reindexing.
  have hQ : Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis) =
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) symplecticChangeOfBasis := by
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
      RingHom.ext_int ((iterateFrobenius A p k).comp (algebraMap ℤ A)) (algebraMap ℤ A)]
  have hreindex : Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)
      ((finCongr dimension_one).reindexGL A (g : GL (Fin (dimension 1)) A)) =
      (finCongr dimension_one).reindexGL A
        (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)
          (g : GL (Fin (dimension 1)) A)) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  rw [hQ, hreindex]

end TauCeti.TypeBSpinCarrier
