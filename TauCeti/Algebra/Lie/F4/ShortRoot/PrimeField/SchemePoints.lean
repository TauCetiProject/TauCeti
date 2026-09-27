/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor

/-!
# Scheme-valued points of the prime-field F4 carrier

The quotient-coordinate presentation identifies scheme-valued points of the carrier with its
matrix-valued points. The numbered root subgroups and weight torus agree under this equivalence.
These identifications transfer equations between quotient-coordinate, matrix-valued, and
scheme-valued points, so the carrier's matrix-point laws yield scheme-level statements.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.F4ShortRoot.PrimeField

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator
local notation "Q" => CommHopfAlgCat.quotient H₂₆ J

/-- A scheme-valued F4 carrier point is a quotient-coordinate Hopf-algebra point. -/
noncomputable def groupSchemePointMulEquiv (A : Type) [CommRing A] [Algebra 𝔽₂ A] :
    HopfAlgebra.points (H := Q) (CommAlgCat.of 𝔽₂ A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶ groupScheme.X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation Q A (GeneralLinear.generatedGroupScheme_def 26 generator)

private theorem groupScheme_X_left : groupScheme.X.left = Spec (CommRingCat.of Q) := by
  rw [groupScheme_def, definingIdeal_def]
  exact hopfSpec_obj_X_left 𝔽₂ _

private theorem groupSchemePointMulEquiv_apply_left (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := Q) (CommAlgCat.of 𝔽₂ A)) :
    (groupSchemePointMulEquiv A q).left = Spec.map (CommRingCat.ofHom (q.ofConv : Q →+* A)) ≫
        eqToHom groupScheme_X_left.symm := by
  exact CommHopfAlgCat.mapMulEquivOfPresentation_apply_left Q A
    (GeneralLinear.generatedGroupScheme_def 26 generator) groupScheme_X_left q

/-- Scheme-valued points of the F4 carrier are its named matrix-valued points. -/
noncomputable def schemePointsMulEquiv (A : Type) [CommRing A] [Algebra 𝔽₂ A] :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶ groupScheme.X) ≃* points A :=
  (groupSchemePointMulEquiv A).symm.trans (coordinatePointsEquiv A)

/-- The scheme point represented by a quotient-coordinate point maps to its corresponding
matrix point under the scheme-point equivalence. -/
@[simp] theorem schemePointsMulEquiv_groupSchemePointMulEquiv (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := Q) (CommAlgCat.of 𝔽₂ A)) :
    schemePointsMulEquiv A (groupSchemePointMulEquiv A q) = coordinatePointsEquiv A q := by
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- The inverse comparison presents a matrix point as a quotient-coordinate scheme point. -/
@[simp] theorem schemePointsMulEquiv_symm_apply (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (g : points A) :
    (schemePointsMulEquiv A).symm g =
      groupSchemePointMulEquiv A ((coordinatePointsEquiv A).symm g) := by
  rfl

/-- The scheme-point comparison commutes with change of coefficient algebra. -/
theorem schemePointsMulEquiv_mapValue {A B : Type} [CommRing A] [CommRing B]
    [Algebra 𝔽₂ A] [Algebra 𝔽₂ B] (φ : A →ₐ[𝔽₂] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶ groupScheme.X) :
    schemePointsMulEquiv B
        ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
          (Spec (CommRingCat.of 𝔽₂)) ≫ p) =
      pointsMap φ (schemePointsMulEquiv A p) := by
  let q : HopfAlgebra.points (H := Q) (CommAlgCat.of 𝔽₂ A) :=
    (groupSchemePointMulEquiv A).symm p
  have hpre :
      (groupSchemePointMulEquiv B).symm
          ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
            (Spec (CommRingCat.of 𝔽₂)) ≫ p) =
        HopfAlgebra.mapPoints (H := Q) (CommAlgCat.ofHom φ) q := by
    simpa only [q, groupSchemePointMulEquiv] using
      CommHopfAlgCat.mapMulEquivOfPresentation_mapValue Q φ
        (GeneralLinear.generatedGroupScheme_def 26 generator) p
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply]
  rw [hpre, HopfAlgebra.mapPoints_apply]
  exact coordinatePointsEquiv_mapPoints φ q

/-- A coordinate endomorphism acts on scheme-valued points by precomposition. -/
theorem groupSchemePointMulEquiv_comp_coordinateMap
    (A : Type) [CommRing A] [Algebra 𝔽₂ A] (phi : Q ⟶ Q)
    (q : HopfAlgebra.points (H := Q) (CommAlgCat.of 𝔽₂ A)) :
    groupSchemePointMulEquiv A q ≫ (eqToHom (GeneralLinear.generatedGroupScheme_def 26 generator) ≫
          (hopfSpec (CommRingCat.of 𝔽₂)).map phi.op ≫
            eqToHom (GeneralLinear.generatedGroupScheme_def 26 generator).symm).hom.hom =
      groupSchemePointMulEquiv A (AlgHom.mapDomain phi.hom q) := by
  have h := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := 𝔽₂) A (GeneralLinear.generatedGroupScheme_def 26 generator)
      (GeneralLinear.generatedGroupScheme_def 26 generator)
      (groupSchemePointMulEquiv A) (groupSchemePointMulEquiv A)
      (groupSchemePointMulEquiv_apply_left A)
      (groupSchemePointMulEquiv_apply_left A) phi q
  have heval : ((CommHopfAlgCat.mapPointsFunctor phi).app (CommAlgCat.of 𝔽₂ A)) q =
        AlgHom.mapDomain phi.hom q := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, AlgHom.mapDomain_apply]
  rw [heval] at h
  exact h

private theorem groupSchemePointMulEquiv_comp_rootSubgroup (k : Fin 4 ⊕ Fin 4)
    (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra 𝔽₂) (CommAlgCat.of 𝔽₂ A)) :
    AdditiveGroup.groupSchemePointMulEquiv A q ≫ (rootSubgroup k).hom.hom =
      groupSchemePointMulEquiv A
        ((CommHopfAlgCat.mapPointsFunctor (CommHopfAlgCat.commonKernelLift generator (.inl k))).app
            (CommAlgCat.of 𝔽₂ A) q) := by
  rw [rootSubgroup_def, GeneralLinear.generatorToGeneratedGroupScheme_def]
  simpa only [Category.assoc, eqToHom_trans] using
    CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
      (R := 𝔽₂) A (GeneralLinear.generatedGroupScheme_def 26 generator)
      (AdditiveGroup.groupScheme_def 𝔽₂)
      (groupSchemePointMulEquiv A) (AdditiveGroup.groupSchemePointMulEquiv A)
      (groupSchemePointMulEquiv_apply_left A)
      (AdditiveGroup.groupSchemePointMulEquiv_apply_left A)
      (CommHopfAlgCat.commonKernelLift generator (.inl k)) q

private theorem groupSchemePointMulEquiv_comp_weightTorus (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := (DiagonalizableGroup.coordinateRing 𝔽₂
        (SplitTorus.characterGroup (Fin 4))).obj) (CommAlgCat.of 𝔽₂ A)) :
    (DiagonalizableGroup.groupSchemePointsMulEquiv
      (R := 𝔽₂) (A := A) (SplitTorus.characterGroup (Fin 4))).symm q ≫ weightTorus.hom.hom =
      groupSchemePointMulEquiv A ((CommHopfAlgCat.mapPointsFunctor
          (CommHopfAlgCat.commonKernelLift generator (.inr ()))).app (CommAlgCat.of 𝔽₂ A) q) := by
  rw [weightTorus_def, GeneralLinear.generatorToGeneratedGroupScheme_def]
  simpa only [Category.assoc, eqToHom_trans] using
    CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
      (R := 𝔽₂) A (GeneralLinear.generatedGroupScheme_def 26 generator)
      (DiagonalizableGroup.groupScheme_def 𝔽₂ (SplitTorus.characterGroup (Fin 4)))
      (groupSchemePointMulEquiv A)
      (DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := 𝔽₂) (A := A) (SplitTorus.characterGroup (Fin 4))).symm
      (groupSchemePointMulEquiv_apply_left A)
      (DiagonalizableGroup.groupSchemePointsMulEquiv_symm_apply_left
        (R := 𝔽₂) (A := A) (SplitTorus.characterGroup (Fin 4)))
      (CommHopfAlgCat.commonKernelLift generator (.inr ())) q

private theorem coe_coordinatePointsEquiv_commonKernelLift
    (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := generatorCodomain j) (CommAlgCat.of 𝔽₂ A)) :
    (coordinatePointsEquiv A ((CommHopfAlgCat.mapPointsFunctor
        (CommHopfAlgCat.commonKernelLift generator j)).app (CommAlgCat.of 𝔽₂ A) q) :
        GL (Fin 26) A) =
      GeneralLinear.pointsMulEquiv 26
        ((CommHopfAlgCat.mapPointsFunctor (generator j)).app (CommAlgCat.of 𝔽₂ A) q) := by
  calc
    _ = GeneralLinear.pointsMulEquiv 26
        (CommHopfAlgCat.quotientPointsHom H₂₆ J (CommAlgCat.of 𝔽₂ A)
          ((CommHopfAlgCat.mapPointsFunctor
            (CommHopfAlgCat.commonKernelLift generator j)).app (CommAlgCat.of 𝔽₂ A) q)) := by
      exact (coe_coordinatePointsEquiv A _).trans (congrArg (GeneralLinear.pointsMulEquiv 26)
          (CommHopfAlgCat.quotientPointsHom_apply H₂₆ J (CommAlgCat.of 𝔽₂ A) _).symm)
    _ = _ := congrArg _ (CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
        J (CommHopfAlgCat.commonKernelLift generator j) (generator j)
        (CommHopfAlgCat.mkQuotient_comp_commonKernelLift generator j)
        (CommAlgCat.of 𝔽₂ A) q).symm

/-- The public root-subgroup scheme morphism induces the named root points. -/
@[simp] theorem schemePointsMulEquiv_comp_rootSubgroup (k : Fin 4 ⊕ Fin 4)
    (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶
      (AdditiveGroup.groupScheme 𝔽₂).X) :
    schemePointsMulEquiv A (p ≫ (rootSubgroup k).hom.hom) =
      rootSubgroupPoints k A (AdditiveGroup.schemePointsMulEquiv A p) := by
  obtain ⟨q, rfl⟩ := (AdditiveGroup.groupSchemePointMulEquiv A).surjective p
  rw [groupSchemePointMulEquiv_comp_rootSubgroup]
  calc _ = coordinatePointsEquiv A
        ((CommHopfAlgCat.mapPointsFunctor (CommHopfAlgCat.commonKernelLift generator (.inl k))).app
            (CommAlgCat.of 𝔽₂ A) q) :=
      schemePointsMulEquiv_groupSchemePointMulEquiv A _
    _ = rootSubgroupPoints k A (AdditiveGroup.gaPointsMulEquiv q) := by
      apply Subtype.ext
      calc _ = GeneralLinear.pointsMulEquiv 26
            ((CommHopfAlgCat.mapPointsFunctor (generator (.inl k))).app (CommAlgCat.of 𝔽₂ A) q) :=
          coe_coordinatePointsEquiv_commonKernelLift (.inl k) A q
        _ = _ := (coe_rootSubgroupPoints_gaPointsMulEquiv k A q).symm
    _ = _ := congrArg (rootSubgroupPoints k A)
      (AdditiveGroup.schemePointsMulEquiv_groupSchemePointMulEquiv A q).symm

/-- The public weight-torus scheme morphism induces the named torus points. -/
@[simp] theorem schemePointsMulEquiv_comp_weightTorus (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶
      (SplitTorus.groupScheme 𝔽₂ (Fin 4)).X) :
    schemePointsMulEquiv A (p ≫ weightTorus.hom.hom) =
      weightTorusPoints A (SplitTorus.schemePointsMulEquiv p) := by
  obtain ⟨q, rfl⟩ := (DiagonalizableGroup.groupSchemePointsMulEquiv
    (R := 𝔽₂) (A := A) (SplitTorus.characterGroup (Fin 4))).symm.surjective p
  rw [groupSchemePointMulEquiv_comp_weightTorus]
  calc _ = coordinatePointsEquiv A
        ((CommHopfAlgCat.mapPointsFunctor (CommHopfAlgCat.commonKernelLift generator (.inr ()))).app
            (CommAlgCat.of 𝔽₂ A) q) :=
      schemePointsMulEquiv_groupSchemePointMulEquiv A _
    _ = weightTorusPoints A (SplitTorus.pointsMulEquiv q) := by
      apply Subtype.ext
      calc _ = GeneralLinear.pointsMulEquiv 26
            ((CommHopfAlgCat.mapPointsFunctor (generator (.inr ()))).app (CommAlgCat.of 𝔽₂ A) q) :=
          coe_coordinatePointsEquiv_commonKernelLift (.inr ()) A q
        _ = _ := (coe_weightTorusPoints_pointsMulEquiv A q).symm
    _ = _ := by
      congr 1
      rw [SplitTorus.schemePointsMulEquiv_eq_freeAbelianCharEquiv,
        DiagonalizableGroup.schemePointsMulEquiv_eq_pointsMulEquiv_groupSchemePointsMulEquiv,
        MulEquiv.apply_symm_apply]
      exact SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv q

/-- Conjugation by the weight torus rescales every numbered root subgroup by its root
character, on scheme-valued points. -/
theorem weightTorus_conj_rootSubgroup (k : Fin 4 ⊕ Fin 4)
    (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶
      (SplitTorus.groupScheme 𝔽₂ (Fin 4)).X) (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm (Multiplicative.ofAdd u) ≫
          (rootSubgroup k).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv s)
                (DynkinType.F4.rootGeneratorWeight DynkinType.valid_F4 k) : A) * u)) ≫
        (rootSubgroup k).hom.hom := by
  apply (schemePointsMulEquiv A).injective
  simpa only [map_mul, map_inv, schemePointsMulEquiv_comp_weightTorus,
    schemePointsMulEquiv_comp_rootSubgroup, MulEquiv.apply_symm_apply,
    toAdd_ofAdd] using
    weightTorusPoints_conj_rootSubgroupPoints k A
      (SplitTorus.schemePointsMulEquiv s) (Multiplicative.ofAdd u)

end

end TauCeti.F4ShortRoot.PrimeField
