/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Positive.BorelCandidate
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic

/-!
# The highest line of the positive short-root F₄ subgroup

Over every field of characteristic two, every nonzero subcomodule of the positive subgroup's
standard twenty-six-dimensional representation contains the highest-weight line. In particular,
that line is its unique simple subcomodule and its unique invariant line. This is the first
invariant flag step for testing maximality of the positive subgroup among connected solvable
subgroups. No Borel maximality or identification with an independently pinned group is asserted.

The calculation uses the common fixed vectors of the four positive root points at parameter one.
Their differences from the identity are strictly upper triangular, so every nonzero invariant
subspace meets their common kernel. That kernel is precisely the highest line, even over 𝔽₂.
The divided-square terms of the short-root points are retained throughout.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§17 and 21.

The scalar-extension and root-point interfaces follow
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.F4ShortRoot.PrimeField.Positive

universe u

noncomputable section

variable (k : Type u) [CommRing k] [Algebra (ZMod 2) k]

/-- The standard coordinate morphism of the positive subgroup after scalar extension. -/
def standardCoordinateMap : GeneralLinear.coordinateHopfAlgebra k 26 ⟶
    CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv ≫
    CommHopfAlgCat.baseChangeMap (CommHopfAlgCat.mkQuotient _ definingIdeal)

/-- The standard coordinate morphism is the scalar extension of the ambient quotient map. -/
theorem standardCoordinateMap_def :
    standardCoordinateMap k =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv ≫
        CommHopfAlgCat.baseChangeMap (CommHopfAlgCat.mkQuotient _ definingIdeal) := (rfl)

/-- The standard coordinate morphism is surjective. -/
theorem standardCoordinateMap_surjective : Function.Surjective (standardCoordinateMap k).hom := by
  simpa only [standardCoordinateMap_def, Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
    _root_.CommHopfAlgCat.baseChangeMap_surjective_of_iso
      (CommHopfAlgCat.mkQuotient _ definingIdeal) (CommHopfAlgCat.mkQuotient_surjective _ _)
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).symm (Iso.refl _)

/-- The standard representation of the scalar-extended positive subgroup. -/
@[instance_reducible]
def standardComodule : Comodule k
    (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k) :=
  GeneralLinear.corestrictStandardComodule k 26 (standardCoordinateMap k).hom

attribute [local instance] standardComodule

/-- Its coefficient matrix is the ambient generic matrix restricted to the positive subgroup. -/
theorem coefficientMatrix_basisFun :
    Comodule.coefficientMatrix
        (C := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra)
        (Pi.basisFun k (Fin 26)) =
      (GeneralLinear.genericMatrix k 26).map (standardCoordinateMap k).hom := by
  let _ := GeneralLinear.standardComodule k 26
  rw [← GeneralLinear.coefficientMatrix_basisFun]
  exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k (Fin 26))
    (standardCoordinateMap k).hom.toCoalgHom

/-- The standard representation is faithful as a group-scheme representation. -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := k)
      (H := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (V := Fin 26 → k) :=
  GeneralLinear.isFaithful_corestrictStandardComodule k 26 (standardCoordinateMap k).hom
    (standardCoordinateMap_surjective k)

/-- Every positive subcomodule is stable under every numbered positive root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k))
    (i : Fin 4) (u : Multiplicative k) {v : Fin 26 → k} (hv : v ∈ N) :
    ((PrimeField.rootSubgroupPoints (.inl i) k u : Matrix.GeneralLinearGroup (Fin 26) k) :
      Matrix (Fin 26) (Fin 26) k) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := ZMod 2) (A := k)).symm u
  let p := toConv (q.ofConv.comp
    (CommHopfAlgCat.commonKernelLift generator (.inl i)).hom.toAlgHom)
  let p' := (AlgHom.baseChangePointsMulEquiv (k := ZMod 2) (K := k)
    (A := coordinateHopfAlgebra) (R := k)) p
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem k 26
    (standardCoordinateMap k).hom N p' hv
  simp only [BialgHom.mapDomain_apply, standardCoordinateMap] at h
  rw [GeneralLinear.pointToGeneralLinear_baseChangeMap, MulEquiv.symm_apply_apply] at h
  have hcomp : p.ofConv.comp (CommHopfAlgCat.mkQuotient _ definingIdeal).hom.toAlgHom =
      q.ofConv.comp (PrimeField.generator (.inl (.inl i))).hom.toAlgHom := by
    simpa only [p, ofConv_toConv, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
      AlgHom.comp_assoc, generator_inl] using
      congrArg (fun f ↦ q.ofConv.comp f.hom.toAlgHom)
        (CommHopfAlgCat.mkQuotient_comp_commonKernelLift generator (.inl i))
  rw [hcomp] at h
  have hmatrix := PrimeField.coe_rootSubgroupPoints_gaPointsMulEquiv (.inl i) k q
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, GeneralLinear.pointsMulEquiv_apply,
    MulEquiv.apply_symm_apply] at hmatrix
  rwa [← hmatrix] at h

/-- The ordered weight basis triangularizes the positive subgroup's standard representation. -/
theorem coefficientMatrix_isUpperTriangular :
    (Comodule.coefficientMatrix
      (C := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra)
      (Pi.basisFun k (Fin 26))).IsUpperTriangular := by
  rw [coefficientMatrix_basisFun]
  intro a b hba
  have hz : (CommHopfAlgCat.mkQuotient _ definingIdeal).hom
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv (ZMod 2) 26
        (GeneralLinear.coordinateRingMap (ZMod 2) 26 (MvPolynomial.X (a, b)))) = 0 := by
    apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ definingIdeal _).mpr
    apply upperTriangular_le_definingIdeal
    rw [← HopfIdeal.mem_toIdeal, GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal]
    exact Ideal.subset_span
      ((GeneralLinear.UpperTriangular.mem_definingRelationSet_iff _ _ _).mpr
        ⟨a, b, hba, rfl⟩)
  simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, standardCoordinateMap,
    CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_inv_X,
    CommHopfAlgCat.baseChangeMap_apply_tmul]
  simp only [hz, TensorProduct.tmul_zero]

/-- The highest-weight line as a subcomodule of the positive subgroup. -/
def highestLine :
    Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k) :=
  Comodule.flagSubcomodule (Pi.basisFun k (Fin 26)) (coefficientMatrix_isUpperTriangular k) 1

/-- The highest line is spanned by the first weight vector. -/
-- Normalize the projections in the indexed comodule type before registering simp rules:
-- callers' expressions undergo this normalization before the simplifier matches them.
@[simp]
theorem highestLine_toSubmodule :
    (dsimp% only ((highestLine k).toSubmodule)) = k ∙ Pi.single 0 1 := by
  rw [highestLine, Comodule.flagSubcomodule_toSubmodule, Module.Basis.flag]
  congr 1
  ext v
  simp [Fin.lt_one_iff]

/-- Membership in the highest line means being a scalar multiple of the first weight vector. -/
@[simp]
theorem mem_highestLine (v : Fin 26 → k) :
    (dsimp% only (v ∈ highestLine k)) ↔ ∃ c : k, c • Pi.single 0 1 = v := by
  rw [← Subcomodule.mem_toSubmodule, highestLine_toSubmodule, Submodule.mem_span_singleton]

/-- A root and row reading each coordinate after the highest one. At the two zero weights,
the divided-square term also reads the coordinate opposite to the corresponding simple root. -/
private def raisingReadout : Fin 25 → Fin 4 × Fin 26 := ![
  (3, 0), (2, 1), (1, 2), (0, 3), (2, 3), (0, 5), (3, 5), (1, 6), (0, 7),
  (2, 8), (1, 9), (3, 10), (2, 11), (2, 12), (3, 13), (1, 14), (2, 15),
  (0, 16), (1, 17), (0, 19), (2, 19), (0, 21), (1, 22), (2, 23), (3, 24)]

private theorem raisingReadout_apply (v : Fin 26 → k) (b : Fin 25) :
    ((raisingMatrix (raisingReadout b).1 + raisingDividedSquareMatrix (raisingReadout b).1).map
        (Int.cast : ℤ → k) *ᵥ v) (raisingReadout b).2 =
      v b.succ + (if b.succ = 12 then v 15 else if b.succ = 13 then v 14 else 0) := by
  have htwo : (2 : k) = 0 := by
    rw [← map_ofNat (algebraMap (ZMod 2) k) 2]
    have hzero : (2 : ZMod 2) = 0 := by decide
    rw [hzero, map_zero]
  fin_cases b <;>
    simp [raisingReadout, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      raisingMatrix_apply, raisingDividedSquareMatrix_apply, raisingTarget, raisingCoeff,
      raisingDividedSquareTarget, raisingDividedSquareCoeff, htwo]

private theorem unitRootDifference_eq (i : Fin 4) :
    (((PrimeField.rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) - 1) =
      (raisingMatrix i + raisingDividedSquareMatrix i).map (Int.cast : ℤ → k) := by
  rw [PrimeField.coe_rootSubgroupPoints, F4ShortRoot.coe_rootSubgroupPoints_inl]
  simp [Matrix.map_add, add_comm, add_left_comm]

/-- A vector is fixed by all four positive root points at parameter one exactly when it belongs
to the highest line. This tests actual root points, including their divided-square terms. -/
theorem forall_rootSubgroupPoints_one_mulVec_eq_self_iff (v : Fin 26 → k) :
    (∀ i : Fin 4,
      ((PrimeField.rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
          Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ v = v) ↔
      v ∈ highestLine k := by
  have hkernel :
      (∀ i : Fin 4, (raisingMatrix i + raisingDividedSquareMatrix i).map
        (Int.cast : ℤ → k) *ᵥ v = 0) ↔ v = v 0 • Pi.single 0 1 := by
    constructor
    · intro h
      have hread (b : Fin 25) :
          v b.succ + (if b.succ = 12 then v 15 else if b.succ = 13 then v 14 else 0) = 0 := by
        rw [← raisingReadout_apply]
        exact congrFun (h (raisingReadout b).1) (raisingReadout b).2
      have h14 : v 14 = 0 := by simpa using hread 13
      have h15 : v 15 = 0 := by simpa using hread 14
      have hcoordinates (b : Fin 25) : v b.succ = 0 := by
        simpa only [h14, h15, ite_self, add_zero] using hread b
      ext a
      refine Fin.cases ?_ (fun b ↦ ?_) a
      · simp
      · simp only [Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero b), smul_zero,
          hcoordinates b]
    · intro hv i
      rw [hv, Matrix.mulVec_smul, Matrix.mulVec_single_one]
      have hcolumn : Matrix.col
          ((raisingMatrix i + raisingDividedSquareMatrix i).map (Int.cast : ℤ → k)) 0 = 0 := by
        ext a
        fin_cases i <;>
          simp [raisingMatrix_apply, raisingDividedSquareMatrix_apply, raisingTarget,
            raisingCoeff, raisingDividedSquareTarget, raisingDividedSquareCoeff]
      rw [hcolumn, smul_zero]
  have hfixed :
      (∀ i : Fin 4,
        ((PrimeField.rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
            Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ v = v) ↔
      ∀ i : Fin 4, (raisingMatrix i + raisingDividedSquareMatrix i).map
        (Int.cast : ℤ → k) *ᵥ v = 0 := by
    simp only [← unitRootDifference_eq, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [hfixed, hkernel, mem_highestLine]
  constructor
  · intro hv
    exact ⟨v 0, hv.symm⟩
  · rintro ⟨c, rfl⟩
    simp

/-- The highest line is nonzero over every nontrivial coefficient ring. -/
theorem highestLine_ne_bot [Nontrivial k] : highestLine k ≠ ⊥ := by
  intro h
  have he : Pi.single 0 (1 : k) ∈ highestLine k := (mem_highestLine k _).mpr ⟨1, one_smul _ _⟩
  rw [h] at he
  have hz : (Pi.single (0 : Fin 26) (1 : k) : Fin 26 → k) = 0 := by
    simpa only [Subcomodule.mem_bot] using he
  have hcoord : (1 : k) = 0 := by
    simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun hz 0
  exact one_ne_zero hcoord

private theorem unitRootDifference_apply_diag (i : Fin 4) (a : Fin 26) :
    ((((PrimeField.rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) - 1)) a a = 0 := by
  rw [unitRootDifference_eq]
  fin_cases i <;> fin_cases a <;>
    simp [raisingMatrix_apply, raisingDividedSquareMatrix_apply, raisingTarget, raisingCoeff,
      raisingDividedSquareTarget, raisingDividedSquareCoeff]

end

section Field

variable (k : Type u) [Field k] [Algebra (ZMod 2) k]

attribute [local instance] standardComodule

/-- Every nonzero invariant subspace contains the highest-weight line, over any field of
characteristic two, including the prime field itself. -/
theorem highestLine_le_of_ne_bot
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k))
    (hN : N ≠ ⊥) : highestLine k ≤ N := by
  let A : Fin 4 → Matrix (Fin 26) (Fin 26) k := fun i ↦
    ((PrimeField.rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
      Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) - 1
  have htri (i : Fin 4) : (A i).IsUpperTriangular :=
    (PrimeField.isUpperTriangular_rootSubgroupPoints_inl i k _).sub Matrix.blockTriangular_one
  have hsub : N.toSubmodule ≠ ⊥ := (not_congr Subcomodule.toSubmodule_eq_bot).mpr hN
  have hstable (i : Fin 4) (v : Fin 26 → k) (hv : v ∈ N.toSubmodule) :
      A i *ᵥ v ∈ N.toSubmodule := by
    dsimp only [A]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact N.toSubmodule.sub_mem (rootSubgroupPoints_mulVec_mem k N i _ hv) hv
  obtain ⟨v, hv, hv0, hfixed⟩ :=
    Matrix.exists_ne_zero_forall_mulVec_eq_zero_of_invariant_submodule A htri
      (unitRootDifference_apply_diag k) N.toSubmodule hsub hstable
  have hfix : ∀ i : Fin 4,
      ((PrimeField.rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ v = v := by
    simpa only [A, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hfixed
  obtain ⟨c, hc⟩ := (mem_highestLine k v).mp
    ((forall_rootSubgroupPoints_one_mulVec_eq_self_iff k v).mp hfix)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (hc.symm.trans (zero_smul k _))
  have he0 : Pi.single 0 (1 : k) ∈ N.toSubmodule := by
    have hcv : c • Pi.single 0 (1 : k) ∈ N.toSubmodule := hc.symm ▸ hv
    simpa only [inv_smul_smul₀ hc0] using N.toSubmodule.smul_mem c⁻¹ hcv
  rw [← Subcomodule.toSubmodule_le_toSubmodule, highestLine_toSubmodule,
    Submodule.span_singleton_le_iff_mem]
  exact he0

/-- The highest line has dimension one. -/
@[simp]
theorem finrank_highestLine :
    (dsimp% only (Module.finrank k (highestLine k).toSubmodule)) = 1 := by
  rw [highestLine_toSubmodule]
  exact finrank_span_singleton (by simp)

/-- The highest-weight line is the only one-dimensional invariant subspace. -/
@[simp]
theorem finrank_eq_one_iff_eq_highestLine
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k)) :
    (dsimp% only (Module.finrank k N.toSubmodule = 1 ↔ N = highestLine k)) := by
  constructor
  · intro hdim
    have hN' : N.toSubmodule ≠ ⊥ :=
      (not_congr Submodule.finrank_eq_zero).mp (hdim.trans_ne Nat.one_ne_zero)
    have hN : N ≠ ⊥ := (not_congr Subcomodule.toSubmodule_eq_bot).mp hN'
    have hle := highestLine_le_of_ne_bot k N hN
    have hdim' : Module.finrank k (highestLine k).toSubmodule =
        Module.finrank k N.toSubmodule := (finrank_highestLine k).trans hdim.symm
    have heq := Submodule.eq_of_le_of_finrank_eq
      (Subcomodule.toSubmodule_le_toSubmodule.mpr hle) hdim'
    exact le_antisymm (Subcomodule.toSubmodule_le_toSubmodule.mp heq.ge) hle
  · rintro rfl
    exact finrank_highestLine k

/-- An invariant subspace contains the highest line exactly when it is nonzero. -/
@[simp]
theorem highestLine_le_iff_ne_bot
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k)) :
    (dsimp% only (highestLine k ≤ N ↔ N ≠ ⊥)) := by
  constructor
  · rintro h rfl
    exact highestLine_ne_bot k (le_bot_iff.mp h)
  · exact highestLine_le_of_ne_bot k N

/-- The highest line is the unique simple subcomodule of the positive standard representation. -/
@[simp]
theorem isAtom_iff_eq_highestLine
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 26 → k)) :
    (dsimp% only (IsAtom N ↔ N = highestLine k)) := by
  have hatom : IsAtom (highestLine k) := isAtom_iff_le_of_ge.mpr
    ⟨highestLine_ne_bot k, fun M hM _ ↦ highestLine_le_of_ne_bot k M hM⟩
  constructor
  · intro hN
    exact ((hN.le_iff_eq (highestLine_ne_bot k)).mp
      (highestLine_le_of_ne_bot k N hN.ne_bot)).symm
  · rintro rfl
    exact hatom

end Field

end TauCeti.F4ShortRoot.PrimeField.Positive
