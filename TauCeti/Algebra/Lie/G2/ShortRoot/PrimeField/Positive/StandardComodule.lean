/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.BorelCandidate
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import Mathlib.Order.Preorder.Finite

/-!
# Invariant subspaces of the positive short-root G₂ subgroup

Over every field of characteristic three, the subcomodules of the positive subgroup's standard
seven-dimensional representation are exactly the initial spans of the ordered weight basis.
The torus separates its seven weight lines, and the two raising root subgroups connect every
coordinate vector to its predecessor. Thus the standard flag is the only invariant full flag.
This rigidity supplies the flag comparison needed when testing maximality of the positive
subgroup among connected solvable subgroups. No Borel maximality or identification with an
independently pinned group is asserted here.

## Main declarations

* `standardComodule`: the standard representation after arbitrary scalar extension from 𝔽₃.
* `exists_flag_eq_toSubmodule`: every invariant subspace is an initial coordinate span.
* `flagOrderIso`: the complete lattice of subcomodules, identified with `Fin 8` in its usual order.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§17 and 21.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The weight extraction and root-point action follow
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.StandardComodule`.
The flag construction uses `TauCeti.Comodule.flagSubcomodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix TensorProduct

namespace TauCeti.G2ShortRoot.PrimeField.Positive

universe u

noncomputable section

variable (k : Type u) [CommRing k] [Algebra (ZMod 3) k]

/-- The standard coordinate morphism of the positive subgroup after scalar extension to `k`. -/
def standardCoordinateMap : GeneralLinear.coordinateHopfAlgebra k 7 ⟶
    CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 3) k 7).inv ≫
    CommHopfAlgCat.baseChangeMap (CommHopfAlgCat.mkQuotient _ definingIdeal)

/-- The standard coordinate morphism is the scalar extension of the positive subgroup's
ambient quotient map, transported through the general-linear coordinate identification. -/
theorem standardCoordinateMap_def :
    standardCoordinateMap k =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 3) k 7).inv ≫
        CommHopfAlgCat.baseChangeMap (CommHopfAlgCat.mkQuotient _ definingIdeal) := by
  rw [standardCoordinateMap]

/-- The positive subgroup's standard coordinate morphism is surjective. -/
theorem standardCoordinateMap_surjective :
    Function.Surjective (standardCoordinateMap k).hom := by
  simpa only [standardCoordinateMap_def, Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
    _root_.CommHopfAlgCat.baseChangeMap_surjective_of_iso
      (CommHopfAlgCat.mkQuotient _ definingIdeal) (CommHopfAlgCat.mkQuotient_surjective _ _)
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 3) k 7).symm (Iso.refl _)

/-- Restriction of positive-subgroup coordinates to its weight torus after scalar extension. -/
def weightTorusCoordinateMap : CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra ⟶
    (DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup (Fin 2))).obj :=
  CommHopfAlgCat.baseChangeMap (CommHopfAlgCat.commonKernelLift generator (.inr ())) ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso (ZMod 3) k
      (SplitTorus.characterGroup (Fin 2))).hom

/-- Restricting the standard matrix coordinates to the torus gives the seven short-root weights. -/
@[reassoc]
theorem standardCoordinateMap_comp_weightTorusCoordinateMap :
    standardCoordinateMap k ≫ weightTorusCoordinateMap k =
      GeneralLinear.weightTorusBaseChangeCoordinateMap (ZMod 3) k weight := by
  have htorus : CommHopfAlgCat.mkQuotient _ definingIdeal ≫
      CommHopfAlgCat.commonKernelLift generator (.inr ()) =
        GeneralLinear.weightTorusCoordinateMap (R := ZMod 3) weight := by
    simp only [CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr,
      PrimeField.generator_inr, GeneralLinear.weightTorusBaseChangeCoordinateMap_eq]
  simp only [standardCoordinateMap, weightTorusCoordinateMap,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_def, Category.assoc,
    ← (CommHopfAlgCat.baseChangeFunctor (K := k)).map_comp_assoc, htorus]

/-- The positive subgroup's standard representation on `k⁷`, including finite coefficient fields. -/
@[instance_reducible]
def standardComodule : Comodule k
    (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k) :=
  GeneralLinear.corestrictStandardComodule k 7 (standardCoordinateMap k).hom

/-- The positive standard comodule is the corestriction along its standard coordinate map. -/
theorem standardComodule_def :
    standardComodule k =
      GeneralLinear.corestrictStandardComodule k 7 (standardCoordinateMap k).hom := (rfl)

attribute [local instance] standardComodule

/-- On the weight torus, the standard representation is the direct sum of its seven weight lines. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (weightTorusCoordinateMap k).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun k (Fin 7))
        (fun a ↦ SplitTorus.weightCharacter (weight a)) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (standardCoordinateMap k).hom (weightTorusCoordinateMap k).hom weight
  rw [← CommHopfAlgCat.hom_comp, standardCoordinateMap_comp_weightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- A positive subcomodule is stable under every numbered raising-root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k))
    (i : Fin 2) (u : Multiplicative k) {v : Fin 7 → k} (hv : v ∈ N) :
    ((PrimeField.rootSubgroupPoints (.inl i) k u : Matrix.GeneralLinearGroup (Fin 7) k) :
      Matrix (Fin 7) (Fin 7) k) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) (A := k)).symm u
  let p := toConv (q.ofConv.comp
    (CommHopfAlgCat.commonKernelLift generator (.inl i)).hom.toAlgHom)
  let p' := (AlgHom.baseChangePointsMulEquiv (k := ZMod 3) (K := k)
    (A := coordinateHopfAlgebra) (R := k)) p
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem k 7
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
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply, GeneralLinear.pointsMulEquiv_apply,
    MulEquiv.apply_symm_apply] at hmatrix
  rwa [← hmatrix] at h

/-- The ordered weight basis triangularizes the standard comodule after every scalar extension. -/
theorem coefficientMatrix_isUpperTriangular :
    (Comodule.coefficientMatrix
      (C := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra)
      (Pi.basisFun k (Fin 7))).IsUpperTriangular := by
  have hmatrix : Comodule.coefficientMatrix
      (C := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra)
      (Pi.basisFun k (Fin 7)) =
        (GeneralLinear.genericMatrix k 7).map (standardCoordinateMap k).hom := by
    let _ := GeneralLinear.standardComodule k 7
    rw [← GeneralLinear.coefficientMatrix_basisFun]
    exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k (Fin 7))
      (standardCoordinateMap k).hom.toCoalgHom
  rw [hmatrix]
  intro a b hba
  have hz : (CommHopfAlgCat.mkQuotient _ definingIdeal).hom
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv (ZMod 3) 7
        (GeneralLinear.coordinateRingMap (ZMod 3) 7 (MvPolynomial.X (a, b)))) = 0 := by
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

end

section Field

variable (k : Type u) [Field k] [Algebra (ZMod 3) k]

attribute [local instance] standardComodule

private theorem weightCharacter_injective :
    Function.Injective fun a : Fin 7 ↦ SplitTorus.weightCharacter (weight a) := by
  intro a b h
  apply weight_injective
  funext i
  simpa only [SplitTorus.toAdd_weightCharacter] using
    congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) ↦ Multiplicative.toAdd χ i) h

private theorem single_mem_of_apply_ne_zero
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k))
    {v : Fin 7 → k} (hv : v ∈ N) {a : Fin 7} (ha : v a ≠ 0) : Pi.single a (1 : k) ∈ N := by
  have h := Subcomodule.single_smul_mem_of_corestrict_eq_ofWeights
    (weightTorusCoordinateMap k).hom.toCoalgHom _ weightCharacter_injective
    (torusCorestrict_eq_ofWeights k) N hv a
  rw [← Subcomodule.mem_toSubmodule]
  simpa only [inv_smul_smul₀ ha] using N.toSubmodule.smul_mem (v a)⁻¹ h

private theorem single_predecessor_mem
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k))
    (a : Fin 6) (ha : Pi.single a.succ (1 : k) ∈ N) : Pi.single a.castSucc (1 : k) ∈ N := by
  have htwo : (2 : k) ≠ 0 := by
    have h : IsUnit ((algebraMap (ZMod 3) k) 2) :=
      ((ZMod.isUnit_iff_coprime 2 3).mpr (by decide)).map
        (algebraMap (ZMod 3) k).toMonoidHom
    simpa only [map_ofNat] using h.ne_zero
  refine single_mem_of_apply_ne_zero k N
    (rootSubgroupPoints_mulVec_mem k N (if a.val = 1 ∨ a.val = 4 then 1 else 0)
      (Multiplicative.ofAdd 1) ha) ?_
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  split_ifs with h
  · rw [PrimeField.coe_rootSubgroupPoints_inl_one]
    revert h
    fin_cases a <;> norm_num [raisingMatrix]
  · rw [PrimeField.coe_rootSubgroupPoints_inl_zero]
    revert h
    fin_cases a <;> norm_num [raisingMatrix, Matrix.single]
    exact htwo

private theorem single_mem_of_le
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k))
    {a b : Fin 7} (hab : a ≤ b) (hb : Pi.single b (1 : k) ∈ N) : Pi.single a (1 : k) ∈ N := by
  induction b using Fin.induction with
  | zero => simpa only [Fin.le_zero_iff.mp hab] using hb
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hab
    · exact hb
    · exact ih (by
        simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hab ⊢
        omega)
        (single_predecessor_mem k N b hb)

/-- Every invariant subspace of the positive subgroup is the span of an initial segment of the
ordered weight basis. This is a scheme-representation assertion, also over the finite field 𝔽₃. -/
theorem exists_flag_eq_toSubmodule
    (N : Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k)) :
    ∃ r : Fin 8, N.toSubmodule = (Pi.basisFun k (Fin 7)).flag r := by
  classical
  let S : Finset (Fin 7) := Finset.univ.filter fun a ↦ Pi.single a (1 : k) ∈ N
  have hspan := Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (weightTorusCoordinateMap k).hom.toCoalgHom _ weightCharacter_injective
    (torusCorestrict_eq_ofWeights k) N
  by_cases hS : S.Nonempty
  · let b := S.max' hS
    refine ⟨b.succ, ?_⟩
    rw [hspan, Module.Basis.flag]
    apply congrArg (Submodule.span k)
    apply congrArg (fun s : Set (Fin 7) ↦ (Pi.basisFun k (Fin 7)) '' s)
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ha
      have hb : a ≤ b := Finset.le_max' S a (by simp [S, ha])
      simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] using Nat.lt_succ_of_le hb
    · intro ha
      have hb : Pi.single b (1 : k) ∈ N := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
      exact single_mem_of_le k N (by
        simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at ha ⊢
        omega) hb
  · refine ⟨0, ?_⟩
    rw [hspan, Module.Basis.flag_zero]
    have hempty : {a : Fin 7 | Pi.single a (1 : k) ∈ N} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro ha
      exact hS ⟨a, by simp [S, ha]⟩
    simp [hempty]

/-- The eight initial spans of the ordered weight basis are precisely the subcomodules of the
positive subgroup's standard representation, with inclusion corresponding to the usual order. -/
noncomputable def flagOrderIso : Fin 8 ≃o
    Subcomodule k (CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) (Fin 7 → k) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono
      (Comodule.flagSubcomodule (Pi.basisFun k (Fin 7)) (coefficientMatrix_isUpperTriangular k))
      (Comodule.flagSubcomodule_strictMono _ _))
    (fun N ↦ by
      obtain ⟨r, hr⟩ := exists_flag_eq_toSubmodule k N
      refine ⟨r, ?_⟩
      ext v
      simp only [OrderEmbedding.coe_ofStrictMono, ← Subcomodule.mem_toSubmodule,
        Comodule.flagSubcomodule_toSubmodule, hr])

/-- The invariant subspace at index `r` is the span of the first `r` weight vectors. -/
-- Normalize the structure projections in the indexed comodule type before registering the rule:
-- `simp` performs that normalization on a caller's expression before matching simp lemmas.
@[simp]
theorem flagOrderIso_apply_toSubmodule (r : Fin 8) :
    (dsimp% only ((flagOrderIso k r).toSubmodule)) = (Pi.basisFun k (Fin 7)).flag r :=
  Comodule.flagSubcomodule_toSubmodule _ _ r

/-- Every basis triangularizing the positive subgroup defines the same full flag as the ordered
weight basis. In particular, a Lie--Kolchin flag for a solvable overgroup must be this flag. -/
theorem flag_eq_of_coefficientMatrix_isUpperTriangular (b : Module.Basis (Fin 7) k (Fin 7 → k))
    (hb : (Comodule.coefficientMatrix
      (C := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) b).IsUpperTriangular)
    (r : Fin 8) : b.flag r = (Pi.basisFun k (Fin 7)).flag r := by
  have hmono : StrictMono (fun s ↦ (flagOrderIso k).symm (Comodule.flagSubcomodule b hb s)) :=
    (flagOrderIso k).symm.strictMono.comp (Comodule.flagSubcomodule_strictMono b hb)
  have heq := congrArg (flagOrderIso k) (congrFun hmono.eq_id r)
  rw [OrderIso.apply_symm_apply] at heq
  exact (Comodule.flagSubcomodule_toSubmodule b hb r).symm.trans
    ((congrArg Subcomodule.toSubmodule heq).trans (flagOrderIso_apply_toSubmodule k r))

end Field

end TauCeti.G2ShortRoot.PrimeField.Positive
