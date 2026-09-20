/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors

/-!
# The special isogeny of the short-root type-G2 carrier

The matrix `Matrix.g2SpecialIsogeny` of signed two-by-two minors is multiplicative on matrices
preserving the type-`G₂` cross product and its invariant dual form.  The universal point of the
short-root carrier over `𝔽₃` preserves both tensors, so the formula determines an endomorphism of
the carrier.  Its action exchanges the two numbered simple roots, cubes the parameter at the
short root, and sends a torus point `(s₀, s₁)` to `(s₁, s₀³)`.

The square is the prime-field Frobenius.  This is proved first on the coordinate Hopf algebra:
the two coordinate maps agree after every root-subgroup and torus generator, hence agree by the
common-kernel presentation.  Evaluation gives the corresponding square relation on points.

The carrier is not identified here with the pinned simply connected group scheme of type `G₂`;
the construction transfers to that group scheme only along such an identification.

## Main definitions

* `TauCeti.G2ShortRoot.PrimeField.specialIsogenyCoordinateMap`: the endomorphism of the carrier's
  coordinate Hopf algebra.
* `TauCeti.G2ShortRoot.PrimeField.specialIsogenyHom`: the resulting carrier endomorphism.
* `TauCeti.G2ShortRoot.PrimeField.specialIsogeny`: its action on matrix-valued points.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` and
  `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_weightTorusPoints`: the pinning equations.
* `TauCeti.G2ShortRoot.PrimeField.schemePointsMulEquiv_comp_specialIsogenyHom` and its Frobenius
  counterpart: compatibility between the scheme endomorphisms and their named point maps.
* `TauCeti.G2ShortRoot.PrimeField.schemePointsMulEquiv_comp_rootSubgroup_comp_specialIsogenyHom`
  and its torus counterpart: the pinning equations for scheme-valued points.
* `TauCeti.G2ShortRoot.PrimeField.map_carrierGenericMatrix_specialIsogenyCoordinateMap` and
  `TauCeti.G2ShortRoot.PrimeField.map_carrierGenericMatrix_frobeniusCoordinateMap`: the defining
  equations of the two coordinate maps on the universal point.
* `TauCeti.G2ShortRoot.PrimeField.specialIsogenyCoordinateMap_comp_self` and
  `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_comp_specialIsogeny`: the Frobenius square
  relations.
* `TauCeti.G2ShortRoot.PrimeField.pointsMap_specialIsogeny`: naturality in the value algebra.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6.

The coordinate-algebra proof is adapted from the earlier closed
[Tau Ceti PR #6786](https://github.com/TauCetiProject/TauCeti/pull/6786), updated to use the
current generated-subgroup endomorphism and multiplicative-matrix APIs.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix WithConv
open scoped TensorProduct
open scoped CategoryTheory.MonObj

namespace TauCeti.G2ShortRoot.PrimeField

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

universe v w

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

private theorem comul_g2SpecialIsogeny_carrierGenericMatrix :
    (g2SpecialIsogeny carrierGenericMatrix).map
        (Bialgebra.comulAlgHom (ZMod 3) carrierAlgebra) =
      (g2SpecialIsogeny carrierGenericMatrix).map
          (Algebra.TensorProduct.includeLeft (R := ZMod 3) (S := ZMod 3)) *
        (g2SpecialIsogeny carrierGenericMatrix).map
          (Algebra.TensorProduct.includeRight (R := ZMod 3)) := by
  let _ : CharP (carrierAlgebra ⊗[ZMod 3] carrierAlgebra) 3 :=
    charP_of_injective_algebraMap (R := ZMod 3) (fun x y h => by
      have h' := congrArg (Bialgebra.counitAlgHom (ZMod 3)
        (carrierAlgebra ⊗[ZMod 3] carrierAlgebra)) h
      simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using h') 3
  have hX : carrierGenericMatrix.map (Bialgebra.comulAlgHom (ZMod 3) carrierAlgebra) =
      carrierGenericMatrix.map
          (Algebra.TensorProduct.includeLeft (R := ZMod 3) (S := ZMod 3)) *
        carrierGenericMatrix.map (Algebra.TensorProduct.includeRight (R := ZMod 3)) := by
    simpa only [carrierGenericMatrix_def, BialgHom.coe_toAlgHom, Matrix.map_map] using
      TauCeti.GeneralLinear.map_comul_map_genericMatrix carrierQuotient.hom
  set iL : carrierAlgebra →ₐ[ZMod 3] carrierAlgebra ⊗[ZMod 3] carrierAlgebra :=
    Algebra.TensorProduct.includeLeft with hiL
  set iR : carrierAlgebra →ₐ[ZMod 3] carrierAlgebra ⊗[ZMod 3] carrierAlgebra :=
    Algebra.TensorProduct.includeRight with hiR
  have hmul := g2SpecialIsogeny_mul
    (preservesG2Cross_map iL preservesG2Cross_carrierGenericMatrix)
    (preservesDualForm_map iL preservesDualForm_carrierGenericMatrix)
    (preservesG2Cross_map iR preservesG2Cross_carrierGenericMatrix)
  rw [← g2SpecialIsogeny_map (Bialgebra.comulAlgHom (ZMod 3) carrierAlgebra), hX, hmul,
    g2SpecialIsogeny_map iL, g2SpecialIsogeny_map iR]

private theorem counit_g2SpecialIsogeny_carrierGenericMatrix :
    (g2SpecialIsogeny carrierGenericMatrix).map
      (Bialgebra.counitAlgHom (ZMod 3) carrierAlgebra) = 1 := by
  have hX : carrierGenericMatrix.map (Bialgebra.counitAlgHom (ZMod 3) carrierAlgebra) = 1 := by
    simpa only [carrierGenericMatrix_def, BialgHom.coe_toAlgHom, Matrix.map_map] using
      TauCeti.GeneralLinear.map_counit_map_genericMatrix carrierQuotient.hom
  rw [← g2SpecialIsogeny_map (Bialgebra.counitAlgHom (ZMod 3) carrierAlgebra), hX,
    g2SpecialIsogeny_one]

private noncomputable def ambientCoordinateMap :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ carrierAlgebra :=
  CommHopfAlgCat.ofHom (TauCeti.GeneralLinear.coordinateBialgHomOfMultiplicative (ZMod 3) 7
    (g2SpecialIsogeny carrierGenericMatrix) comul_g2SpecialIsogeny_carrierGenericMatrix
    counit_g2SpecialIsogeny_carrierGenericMatrix)

private theorem map_genericMatrix_ambientCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        ambientCoordinateMap.hom.toAlgHom = g2SpecialIsogeny carrierGenericMatrix := by
  rw [ambientCoordinateMap]
  simpa only [CommHopfAlgCat.hom_ofHom, BialgHom.coe_toAlgHom] using
    TauCeti.GeneralLinear.map_genericMatrix_coordinateBialgHomOfMultiplicative (ZMod 3) 7
      (g2SpecialIsogeny carrierGenericMatrix) comul_g2SpecialIsogeny_carrierGenericMatrix
      counit_g2SpecialIsogeny_carrierGenericMatrix

/-! ### Equations on the generators -/

/-- The special isogeny's length-exchanging permutation on positive and negative numbered simple
root subgroups. -/
def specialIsogenyRootIndex : Equiv.Perm (Fin 2 ⊕ Fin 2) :=
  Equiv.Perm.sumCongr (Equiv.swap 0 1) (Equiv.swap 0 1)

/-- The parameter exponent of the special isogeny: three at either short root and one at either
long root. -/
def specialIsogenyExponent : Fin 2 ⊕ Fin 2 → ℕ
  | .inl i | .inr i => if i = 0 then 3 else 1

/-- The special isogeny swaps the two positive numbered simple roots. -/
@[simp]
theorem specialIsogenyRootIndex_inl (i : Fin 2) :
    specialIsogenyRootIndex (.inl i) = .inl (Equiv.swap 0 1 i) := by
  rw [specialIsogenyRootIndex, Equiv.Perm.sumCongr_apply, Sum.map_inl]

/-- The special isogeny swaps the two negative numbered simple roots. -/
@[simp]
theorem specialIsogenyRootIndex_inr (i : Fin 2) :
    specialIsogenyRootIndex (.inr i) = .inr (Equiv.swap 0 1 i) := by
  rw [specialIsogenyRootIndex, Equiv.Perm.sumCongr_apply, Sum.map_inr]

/-- Exchanging the lengths of a numbered simple root twice returns the original root. -/
@[simp]
theorem specialIsogenyRootIndex_specialIsogenyRootIndex (k : Fin 2 ⊕ Fin 2) :
    specialIsogenyRootIndex (specialIsogenyRootIndex k) = k := by
  rcases k with i | i <;> fin_cases i <;>
    simp [specialIsogenyRootIndex]

/-- On a positive numbered root, the parameter is cubed at the short node and unchanged at the
long node. -/
@[simp]
theorem specialIsogenyExponent_inl (i : Fin 2) :
    specialIsogenyExponent (.inl i) = if i = 0 then 3 else 1 := by
  rw [specialIsogenyExponent]

/-- On a negative numbered root, the parameter is cubed at the short node and unchanged at the
long node. -/
@[simp]
theorem specialIsogenyExponent_inr (i : Fin 2) :
    specialIsogenyExponent (.inr i) = if i = 0 then 3 else 1 := by
  rw [specialIsogenyExponent]

private theorem g2SpecialIsogeny_coe_rootSubgroupPoints
    (k : Fin 2 ⊕ Fin 2) (t : A) :
    g2SpecialIsogeny ((rootSubgroupPoints k A (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      ((rootSubgroupPoints (specialIsogenyRootIndex k) A
          (Multiplicative.ofAdd (t ^ specialIsogenyExponent k)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rcases k with i | i
  · fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, specialIsogenyRootIndex_inl,
        specialIsogenyExponent_inl, ↓reduceIte]
      simp only [Equiv.swap_apply_def, ↓reduceIte]
      rw [coe_rootSubgroupPoints_inl_zero, coe_rootSubgroupPoints_inl_one,
        g2SpecialIsogeny_one_add_smul_raisingMatrix_zero]
    · simp only [Fin.isValue, Fin.mk_one, specialIsogenyRootIndex_inl,
        specialIsogenyExponent_inl, one_ne_zero, ↓reduceIte, pow_one]
      simp only [Equiv.swap_apply_def, one_ne_zero, ↓reduceIte]
      rw [coe_rootSubgroupPoints_inl_one, coe_rootSubgroupPoints_inl_zero,
        g2SpecialIsogeny_one_add_smul_raisingMatrix_one]
  · fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, specialIsogenyRootIndex_inr,
        specialIsogenyExponent_inr, ↓reduceIte]
      simp only [Equiv.swap_apply_def, ↓reduceIte]
      rw [coe_rootSubgroupPoints_inr_zero, coe_rootSubgroupPoints_inr_one,
        g2SpecialIsogeny_one_add_smul_loweringMatrix_zero]
    · simp only [Fin.isValue, Fin.mk_one, specialIsogenyRootIndex_inr,
        specialIsogenyExponent_inr, one_ne_zero, ↓reduceIte, pow_one]
      simp only [Equiv.swap_apply_def, one_ne_zero, ↓reduceIte]
      rw [coe_rootSubgroupPoints_inr_one, coe_rootSubgroupPoints_inr_zero,
        g2SpecialIsogeny_one_add_smul_loweringMatrix_one]

/-- The map induced by the special isogeny on the weight torus, `(s₀, s₁) ↦ (s₁, s₀³)`. -/
def specialIsogenyTorusMap (s : Fin 2 → Aˣ) : Fin 2 → Aˣ := ![s 1, s 0 ^ 3]

private theorem g2SpecialIsogeny_coe_weightTorusPoints (s : Fin 2 → Aˣ) :
    g2SpecialIsogeny ((weightTorusPoints A s :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      ((weightTorusPoints A (specialIsogenyTorusMap s) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rw [coe_weightTorusPoints, coe_weightTorusPoints,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    specialIsogenyTorusMap, g2SpecialIsogeny_diagonal_torusCharacter]

private theorem map_genericMatrix_comp {K L : CommHopfAlgCat (ZMod 3)}
    (chi : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ K) (chi' : K ⟶ L) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map (chi ≫ chi').hom.toAlgHom =
      ((TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi.hom.toAlgHom).map
        chi'.hom.toAlgHom := by
  rw [Matrix.map_map]
  exact congrArg _ (funext fun x => CommHopfAlgCat.comp_apply chi chi' x)

private theorem map_genericMatrix_ambientCoordinateMap_comp_commonKernelLift
    (j : (Fin 2 ⊕ Fin 2) ⊕ Unit) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        (ambientCoordinateMap ≫ CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom =
      g2SpecialIsogeny ((TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        (generator j).hom.toAlgHom) := by
  have hgen : (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
      (generator j).hom.toAlgHom =
      carrierGenericMatrix.map
        (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom := by
    rw [carrierGenericMatrix_def, ← map_genericMatrix_comp]
    exact (congrArg
      (fun f => (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map f.hom.toAlgHom)
      (CommHopfAlgCat.mkQuotient_comp_commonKernelLift generator j)).symm
  rw [map_genericMatrix_comp, map_genericMatrix_ambientCoordinateMap, hgen,
    g2SpecialIsogeny_map]

private theorem toIdeal_le_ker_of_map_genericMatrix_eq {K : CommHopfAlgCat (ZMod 3)}
    (chi : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ K) (g : points K)
    (h : (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi.hom.toAlgHom =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) :
    (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker chi.hom.toAlgHom.toRingHom := by
  rw [← definingIdeal_def]
  rw [← TauCeti.GeneralLinear.pointToGeneralLinear_mem_hopfIdealPointsSubgroup_iff_toIdeal_le_ker]
  have hg : TauCeti.GeneralLinear.pointToGeneralLinear 7 (toConv chi.hom.toAlgHom) =
      (g : _root_.Matrix.GeneralLinearGroup (Fin 7) K) := by
    apply Units.ext
    rw [← TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear, h]
  rw [hg]
  exact (points_eq_hopfIdealPointsSubgroup K).le g.2

private theorem commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap :
    (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker ambientCoordinateMap.hom.toAlgHom.toRingHom := by
  refine CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker_of_comp_commonKernelLift generator
    ambientCoordinateMap fun j => ?_
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
    obtain ⟨t, rfl⟩ : ∃ t, Multiplicative.ofAdd t = u := ⟨Multiplicative.toAdd u, rfl⟩
    refine toIdeal_le_ker_of_map_genericMatrix_eq _
      (rootSubgroupPoints (specialIsogenyRootIndex k)
        (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
        (Multiplicative.ofAdd (t ^ specialIsogenyExponent k))) ?_
    rw [map_genericMatrix_ambientCoordinateMap_comp_commonKernelLift, hu]
    exact g2SpecialIsogeny_coe_rootSubgroupPoints k t
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    refine toIdeal_le_ker_of_map_genericMatrix_eq _
      (weightTorusPoints ((DiagonalizableGroup.coordinateRing (ZMod 3)
        (SplitTorus.characterGroup (Fin 2))).obj) (specialIsogenyTorusMap s)) ?_
    rw [map_genericMatrix_ambientCoordinateMap_comp_commonKernelLift, hs]
    exact g2SpecialIsogeny_coe_weightTorusPoints s

/-- The special isogeny's endomorphism of the carrier coordinate Hopf algebra. -/
noncomputable def specialIsogenyCoordinateMap : carrierAlgebra ⟶ carrierAlgebra :=
  CommHopfAlgCat.liftQuotient (CommHopfAlgCat.commonKernelHopfIdeal generator)
    ambientCoordinateMap commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap

/-- The carrier is represented by the quotient of the ambient coordinate Hopf algebra by the
common kernel of its generators. -/
theorem groupScheme_eq_commonKernelSpec :
    groupScheme = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
      (CommHopfAlgCat.commonKernelHopfIdeal generator) := by
  simpa only [definingIdeal_def] using groupScheme_def

/-- The special isogeny as an endomorphism of the short-root type-`G₂` carrier over `𝔽₃`. -/
noncomputable def specialIsogenyHom : groupScheme ⟶ groupScheme :=
  eqToHom groupScheme_eq_commonKernelSpec ≫
    CommHopfAlgCat.commonKernelSpecRestrict ambientCoordinateMap
      commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap ≫
    eqToHom groupScheme_eq_commonKernelSpec.symm

/-- The comorphism of the carrier special isogeny is `specialIsogenyCoordinateMap`. -/
theorem specialIsogenyHom_eq_map_specialIsogenyCoordinateMap :
    specialIsogenyHom =
      eqToHom groupScheme_eq_commonKernelSpec ≫
        (hopfSpec (CommRingCat.of (ZMod 3))).map specialIsogenyCoordinateMap.op ≫
          eqToHom groupScheme_eq_commonKernelSpec.symm := by
  rw [specialIsogenyHom, CommHopfAlgCat.commonKernelSpecRestrict_def]
  rfl

/-! ### The endomorphism on points -/

private theorem map_ofConv_genericMatrix (h : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm h).ofConv =
      (h : Matrix (Fin 7) (Fin 7) A) := by
  rw [TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    ← TauCeti.GeneralLinear.pointsMulEquiv_apply, WithConv.toConv_ofConv,
    MulEquiv.apply_symm_apply]

private noncomputable def carrierAlgebraPointsMulEquiv (A : CommAlgCat.{v} (ZMod 3)) :
    HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra) A ≃* points A :=
  (TauCeti.GeneralLinear.hopfIdealPointsSubgroupMulEquiv 7
      (CommHopfAlgCat.commonKernelHopfIdeal generator) A).trans
    (MulEquiv.subgroupCongr (by
      simpa only [definingIdeal_def] using points_eq_hopfIdealPointsSubgroup A)).symm

private noncomputable def carrierGroupSchemePointMulEquiv (A : Type) [CommRing A]
    [Algebra (ZMod 3) A] :
    WithConv (carrierAlgebra →ₐ[ZMod 3] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶ groupScheme.X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation carrierAlgebra A groupScheme_eq_commonKernelSpec

private theorem groupScheme_X_left :
    groupScheme.X.left = Spec (CommRingCat.of carrierAlgebra) := by
  rw [groupScheme_eq_commonKernelSpec]
  exact hopfSpec_obj_X_left (ZMod 3) _

private theorem carrierGroupSchemePointMulEquiv_apply_left
    (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (q : WithConv (carrierAlgebra →ₐ[ZMod 3] B)) :
    (carrierGroupSchemePointMulEquiv B q).left =
      Spec.map (CommRingCat.ofHom q.ofConv) ≫
        eqToHom groupScheme_X_left.symm := by
  simpa only [carrierGroupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left carrierAlgebra B
      groupScheme_eq_commonKernelSpec groupScheme_X_left q

private theorem carrierGroupSchemePointMulEquiv_comp_carrierι
    (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    carrierGroupSchemePointMulEquiv B q ≫ carrierι.hom.hom =
      TauCeti.GeneralLinear.groupSchemePointMulEquiv 7 B
        (CommHopfAlgCat.quotientPointsHom
          (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
          (CommHopfAlgCat.commonKernelHopfIdeal generator)
          (CommAlgCat.of (ZMod 3) B) q) := by
  have hpoint := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
      (R := ZMod 3) B (TauCeti.GeneralLinear.groupScheme_def (ZMod 3) 7)
      groupScheme_eq_commonKernelSpec
      (TauCeti.GeneralLinear.groupSchemePointMulEquiv 7 B)
      (carrierGroupSchemePointMulEquiv B)
      (TauCeti.GeneralLinear.groupSchemePointMulEquiv_apply_left 7 B)
      (carrierGroupSchemePointMulEquiv_apply_left B)
      carrierQuotient q
  have hpresentation :
      groupScheme_eq_generatedGroupScheme.trans
        (TauCeti.GeneralLinear.generatedGroupScheme_def 7 generator) =
          groupScheme_eq_commonKernelSpec := Subsingleton.elim _ _
  have hι : carrierι =
      eqToHom groupScheme_eq_commonKernelSpec ≫
        (hopfSpec (CommRingCat.of (ZMod 3))).map carrierQuotient.op ≫
          eqToHom (TauCeti.GeneralLinear.groupScheme_def (ZMod 3) 7).symm := by
    rw [carrierι_def, TauCeti.GeneralLinear.generatedGroupSchemeι_def,
      CommHopfAlgCat.quotientSpecι_def]
    rw [← Category.assoc, eqToHom_trans, hpresentation]
  rw [CommHopfAlgCat.quotientPointsHom, hι]
  exact hpoint

private theorem schemePointsMulEquiv_carrierGroupSchemePointMulEquiv
    {B : Type} [CommRing B] [Algebra (ZMod 3) B]
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    schemePointsMulEquiv B (carrierGroupSchemePointMulEquiv B q) =
      carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B) q := by
  apply Subtype.ext
  rw [← schemePointsMulEquiv_comp_carrierι B,
    carrierGroupSchemePointMulEquiv_comp_carrierι,
    TauCeti.GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv]
  simpa only [carrierAlgebraPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_symm_apply] using
      (TauCeti.GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply 7
        (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 3) B) q).symm

private theorem coe_carrierAlgebraPointsMulEquiv
    {B : Type v} [CommRing B] [Algebra (ZMod 3) B]
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    (carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B) q :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) =
      TauCeti.GeneralLinear.pointsMulEquiv 7
        (CommHopfAlgCat.quotientPointsHom
          (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
          (CommHopfAlgCat.commonKernelHopfIdeal generator)
          (CommAlgCat.of (ZMod 3) B) q) := by
  simp only [carrierAlgebraPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_symm_apply]
  exact TauCeti.GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply 7
    (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 3) B) q

private theorem coe_carrierAlgebraPointsMulEquiv_eq_map_carrierGenericMatrix
    {B : Type v} [CommRing B] [Algebra (ZMod 3) B]
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    ((carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B) q :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B) =
      carrierGenericMatrix.map q.ofConv := by
  rw [coe_carrierAlgebraPointsMulEquiv]
  let q' := CommHopfAlgCat.quotientPointsHom
    (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)
    (CommAlgCat.of (ZMod 3) B) q
  rw [← map_ofConv_genericMatrix
    (TauCeti.GeneralLinear.pointsMulEquiv 7 q')]
  simp only [MulEquiv.symm_apply_apply]
  ext i j
  rw [carrierGenericMatrix_def, Matrix.map_map, Matrix.map_apply, Matrix.map_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply]
  rfl

private theorem carrierGroupSchemePointMulEquiv_comp_coordinateMap
    {B : Type} [CommRing B] [Algebra (ZMod 3) B]
    (phi : carrierAlgebra ⟶ carrierAlgebra)
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    carrierGroupSchemePointMulEquiv B q ≫
        (eqToHom groupScheme_eq_commonKernelSpec ≫
          (hopfSpec (CommRingCat.of (ZMod 3))).map phi.op ≫
            eqToHom groupScheme_eq_commonKernelSpec.symm).hom.hom =
      carrierGroupSchemePointMulEquiv B
        (AlgHom.mapDomain phi.hom q) := by
  have h := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := ZMod 3) B groupScheme_eq_commonKernelSpec groupScheme_eq_commonKernelSpec
    (carrierGroupSchemePointMulEquiv B) (carrierGroupSchemePointMulEquiv B)
    (carrierGroupSchemePointMulEquiv_apply_left B)
    (carrierGroupSchemePointMulEquiv_apply_left B) phi q
  have heval :
      ((CommHopfAlgCat.mapPointsFunctor phi).app (CommAlgCat.of (ZMod 3) B)) q =
        AlgHom.mapDomain phi.hom q := rfl
  rw [heval] at h
  exact h

private theorem coe_generatedPointsEndomorphism
    (g : TauCeti.GeneralLinear.generatedPointsSubgroup 7 generator A) :
    ((TauCeti.GeneralLinear.generatedPointsEndomorphism 7 ambientCoordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap A g :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) := by
  ext a b
  have hxy : (CommHopfAlgCat.mkQuotient (TauCeti.GeneralLinear.coordinateHopfAlgebra
        (ZMod 3) 7) (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom
        (g2SpecialIsogeny (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7) a b) =
      ambientCoordinateMap.hom (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7 a b) := by
    have hl := congrFun (congrFun (g2SpecialIsogeny_map carrierQuotient.hom.toAlgHom
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7)) a) b
    have hr := congrFun (congrFun map_genericMatrix_ambientCoordinateMap a) b
    simp only [Matrix.map_apply, BialgHom.coe_toAlgHom] at hl hr ⊢
    rw [hr, carrierGenericMatrix_def, ← hl]
    simp only [BialgHom.coe_toAlgHom]
  have key := TauCeti.GeneralLinear.ofConv_pointsMulEquiv_symm_generatedPointsEndomorphism 7
    ambientCoordinateMap commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap A g
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7 a b)
    (g2SpecialIsogeny (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7) a b) hxy
  have hL : ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm
        (TauCeti.GeneralLinear.generatedPointsEndomorphism 7 ambientCoordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap A g :
          _root_.Matrix.GeneralLinearGroup (Fin 7) A)).ofConv
        (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7 a b) =
      ((TauCeti.GeneralLinear.generatedPointsEndomorphism 7 ambientCoordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap A g :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) a b := by
    rw [← map_ofConv_genericMatrix, Matrix.map_apply]
  have hR : ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm
        (g : _root_.Matrix.GeneralLinearGroup (Fin 7) A)).ofConv
        (g2SpecialIsogeny (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7) a b) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) a b := by
    rw [← map_ofConv_genericMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 7) A),
      g2SpecialIsogeny_map, Matrix.map_apply]
  rw [hL, hR] at key
  exact key

/-- The special isogeny on matrix-valued points of the carrier, functorially over every
`𝔽₃`-algebra. -/
noncomputable def specialIsogeny (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A →* points A :=
  (MulEquiv.subgroupCongr (points_def A).symm).toMonoidHom.comp
    ((TauCeti.GeneralLinear.generatedPointsEndomorphism 7 ambientCoordinateMap
      commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap A).comp
        (MulEquiv.subgroupCongr (points_def A)).toMonoidHom)

/-- The special isogeny is the signed-minor formula on the underlying matrix. -/
@[simp]
theorem coe_specialIsogeny (g : points A) :
    ((specialIsogeny A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) := by
  rw [specialIsogeny, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_apply] using
    coe_generatedPointsEndomorphism
      (MulEquiv.subgroupCongr (points_def A) g)

/-- The pinning equation on all four numbered simple root subgroups. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (t : A) :
    specialIsogeny A (rootSubgroupPoints k A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints (specialIsogenyRootIndex k) A
        (Multiplicative.ofAdd (t ^ specialIsogenyExponent k)) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny]
  exact g2SpecialIsogeny_coe_rootSubgroupPoints k t

/-- The special isogeny sends a torus point `(s₀, s₁)` to `(s₁, s₀³)`. -/
@[simp]
theorem specialIsogeny_weightTorusPoints (s : Fin 2 → Aˣ) :
    specialIsogeny A (weightTorusPoints A s) =
      weightTorusPoints A (specialIsogenyTorusMap s) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny]
  exact g2SpecialIsogeny_coe_weightTorusPoints s

/-- The special isogeny commutes with extension of the value algebra. -/
theorem pointsMap_specialIsogeny {B : Type w} [CommRing B] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (g : points A) :
    pointsMap f (specialIsogeny A g) = specialIsogeny B (pointsMap f g) := by
  apply Subtype.ext
  apply Units.ext
  have hmap (x : points A) :
      (((pointsMap f x : points B) : _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
          Matrix (Fin 7) (Fin 7) B) =
        (((x : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A).map f) := by
    ext i j
    rw [coe_pointsMap, _root_.Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
    rfl
  rw [hmap, coe_specialIsogeny, coe_specialIsogeny (A := B), hmap,
    g2SpecialIsogeny_map]

/-! ### The Frobenius square relation -/

private theorem map_pow_map {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 3) S] [Algebra (ZMod 3) T] (f : S →ₐ[ZMod 3] T)
    (g : Matrix (Fin 7) (Fin 7) S) :
    (g.map (fun x => x ^ 3)).map f = (g.map f).map (fun y => y ^ 3) := by
  ext a b
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, map_pow]

private theorem specialIsogenyTorusMap_specialIsogenyTorusMap {B : Type*} [CommRing B]
    (s : Fin 2 → Bˣ) :
    specialIsogenyTorusMap (specialIsogenyTorusMap s) = s ^ 3 := by
  funext i
  fin_cases i <;>
    simp only [specialIsogenyTorusMap, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.pow_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one]

private theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_map_pow
    {B : Type*} [CommRing B] [Algebra (ZMod 3) B]
    (k : Fin 2 ⊕ Fin 2) (u : Multiplicative B) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((rootSubgroupPoints k B u : _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
          Matrix (Fin 7) (Fin 7) B)) =
      ((rootSubgroupPoints k B u : _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
        Matrix (Fin 7) (Fin 7) B).map (fun x => x ^ 3) := by
  obtain ⟨t, rfl⟩ : ∃ t : B, Multiplicative.ofAdd t = u := ⟨Multiplicative.toAdd u, rfl⟩
  have hsq : g2SpecialIsogeny (g2SpecialIsogeny
      ((rootSubgroupPoints k B (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B)) =
      ((frobenius 1 B (rootSubgroupPoints k B (Multiplicative.ofAdd t)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B) := by
    rw [g2SpecialIsogeny_coe_rootSubgroupPoints,
      g2SpecialIsogeny_coe_rootSubgroupPoints, frobenius_rootSubgroupPoints]
    rcases k with i | i <;> fin_cases i <;>
      simp [specialIsogenyRootIndex, specialIsogenyExponent, pow_one]
  rw [hsq]
  ext a b
  rw [Matrix.map_apply, coe_frobenius_apply]
  norm_num

private theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_weightTorusPoints_eq_map_pow
    {B : Type*} [CommRing B] [Algebra (ZMod 3) B] (s : Fin 2 → Bˣ) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((weightTorusPoints B s : _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
          Matrix (Fin 7) (Fin 7) B)) =
      ((weightTorusPoints B s : _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
        Matrix (Fin 7) (Fin 7) B).map (fun x => x ^ 3) := by
  rw [g2SpecialIsogeny_coe_weightTorusPoints, g2SpecialIsogeny_coe_weightTorusPoints,
    specialIsogenyTorusMap_specialIsogenyTorusMap]
  have hfrob := frobenius_weightTorusPoints 1 B s
  rw [pow_one] at hfrob
  rw [← hfrob]
  ext a b
  rw [Matrix.map_apply, coe_frobenius_apply]
  norm_num

private theorem coordinate_hom_ext {K : CommHopfAlgCat (ZMod 3)}
    (chi chi' : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ K)
    (h : (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi.hom.toAlgHom =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi'.hom.toAlgHom) : chi = chi' := by
  refine CommHopfAlgCat.hom_ext ?_
  refine TauCeti.GeneralLinear.coordinateHopfAlgebra_bialgHom_ext (R := ZMod 3) (n := 7) ?_
  intro a b
  have hab := congrFun (congrFun h a) b
  rw [Matrix.map_apply, Matrix.map_apply, TauCeti.GeneralLinear.genericMatrix_apply] at hab
  simpa only [BialgHom.coe_toAlgHom] using hab

private noncomputable def ambientFrobeniusCoordinateMap :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ carrierAlgebra :=
  CommHopfAlgCat.ofHom
      (TauCeti.frobeniusBialgHom (ZMod 3)
        (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)) ≫
    carrierQuotient

/-- The special isogeny's coordinate map sends the universal point of the carrier to its
signed-minor image: this is the defining equation of `specialIsogenyCoordinateMap`. -/
theorem map_carrierGenericMatrix_specialIsogenyCoordinateMap :
    carrierGenericMatrix.map specialIsogenyCoordinateMap.hom.toAlgHom =
      g2SpecialIsogeny carrierGenericMatrix := by
  -- Expand only the named universal matrix on the left, so that the composition lemma can see
  -- the two successive coordinate maps.
  conv_lhs => rw [carrierGenericMatrix_def]
  rw [← map_genericMatrix_comp, specialIsogenyCoordinateMap,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient, map_genericMatrix_ambientCoordinateMap]

private theorem carrierAlgebraPointsMulEquiv_map_specialIsogenyCoordinateMap
    {B : Type} [CommRing B] [Algebra (ZMod 3) B]
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B)
        (AlgHom.mapDomain specialIsogenyCoordinateMap.hom q) =
      specialIsogeny B (carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B) q) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_carrierAlgebraPointsMulEquiv_eq_map_carrierGenericMatrix,
    coe_specialIsogeny, coe_carrierAlgebraPointsMulEquiv_eq_map_carrierGenericMatrix]
  have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) carrierAlgebra => M.map q.ofConv)
    map_carrierGenericMatrix_specialIsogenyCoordinateMap
  have hmap :
      (((AlgHom.mapDomain specialIsogenyCoordinateMap.hom q).ofConv :
          carrierAlgebra →ₐ[ZMod 3] B) : carrierAlgebra → B) =
        q.ofConv ∘ specialIsogenyCoordinateMap.hom := by
    funext x
    rfl
  rw [hmap]
  simpa only [Matrix.map_map, Function.comp_apply, BialgHom.coe_toAlgHom,
    g2SpecialIsogeny_map] using h

/-- The action induced by `specialIsogenyHom` on scheme-valued carrier points is the named
matrix-valued special isogeny. -/
@[simp]
theorem schemePointsMulEquiv_comp_specialIsogenyHom
    (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (p : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶ groupScheme.X) :
    schemePointsMulEquiv B (p ≫ specialIsogenyHom.hom.hom) =
      specialIsogeny B (schemePointsMulEquiv B p) := by
  obtain ⟨q, rfl⟩ := (carrierGroupSchemePointMulEquiv B).surjective p
  rw [specialIsogenyHom_eq_map_specialIsogenyCoordinateMap,
    carrierGroupSchemePointMulEquiv_comp_coordinateMap,
    schemePointsMulEquiv_carrierGroupSchemePointMulEquiv,
    schemePointsMulEquiv_carrierGroupSchemePointMulEquiv]
  exact carrierAlgebraPointsMulEquiv_map_specialIsogenyCoordinateMap q

private theorem map_genericMatrix_ambientCoordinateMap_comp_specialIsogenyCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        (ambientCoordinateMap ≫ specialIsogenyCoordinateMap).hom.toAlgHom =
      g2SpecialIsogeny (g2SpecialIsogeny carrierGenericMatrix) := by
  rw [map_genericMatrix_comp, map_genericMatrix_ambientCoordinateMap,
    ← g2SpecialIsogeny_map, map_carrierGenericMatrix_specialIsogenyCoordinateMap]

private theorem map_genericMatrix_ambientFrobeniusCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        ambientFrobeniusCoordinateMap.hom.toAlgHom =
      carrierGenericMatrix.map (fun x => x ^ 3) := by
  rw [ambientFrobeniusCoordinateMap, map_genericMatrix_comp, carrierGenericMatrix_def,
    Matrix.map_map, Matrix.map_map]
  refine congrArg _ (funext fun x => ?_)
  simp only [Function.comp_apply, CommHopfAlgCat.hom_ofHom, BialgHom.coe_toAlgHom,
    TauCeti.frobeniusBialgHom_apply, ZMod.card, map_pow]

private theorem ambientCoordinateMap_comp_specialIsogenyCoordinateMap :
    ambientCoordinateMap ≫ specialIsogenyCoordinateMap = ambientFrobeniusCoordinateMap := by
  refine CommHopfAlgCat.commonKernelLift_hom_ext generator _ _ fun j => ?_
  refine coordinate_hom_ext _ _ ?_
  have hXj : carrierGenericMatrix.map
        (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map (generator j).hom.toAlgHom := by
    rw [carrierGenericMatrix_def, ← map_genericMatrix_comp,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  rw [map_genericMatrix_comp (ambientCoordinateMap ≫ specialIsogenyCoordinateMap)
      (CommHopfAlgCat.commonKernelLift generator j),
    map_genericMatrix_ambientCoordinateMap_comp_specialIsogenyCoordinateMap,
    map_genericMatrix_comp ambientFrobeniusCoordinateMap
      (CommHopfAlgCat.commonKernelLift generator j),
    map_genericMatrix_ambientFrobeniusCoordinateMap, ← g2SpecialIsogeny_map,
    ← g2SpecialIsogeny_map, map_pow_map, hXj]
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
    rw [hu]
    exact g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_map_pow k u
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    rw [hs]
    exact g2SpecialIsogeny_g2SpecialIsogeny_coe_weightTorusPoints_eq_map_pow s

private theorem commonKernelHopfIdeal_toIdeal_le_ker_ambientFrobeniusCoordinateMap :
    (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker ambientFrobeniusCoordinateMap.hom.toAlgHom.toRingHom := by
  rw [← ambientCoordinateMap_comp_specialIsogenyCoordinateMap]
  intro x hx
  rw [RingHom.mem_ker]
  have hzero := commonKernelHopfIdeal_toIdeal_le_ker_ambientCoordinateMap hx
  rw [RingHom.mem_ker] at hzero
  simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hzero
  -- Composition in `CommHopfAlgCat` evaluates in this order; spelling out the application avoids
  -- relying on simplification through the bundled morphism and ring-hom coercions.
  change specialIsogenyCoordinateMap.hom (ambientCoordinateMap.hom x) = 0
  rw [hzero, map_zero]

/-- The Frobenius endomorphism of the carrier coordinate Hopf algebra. -/
noncomputable def frobeniusCoordinateMap : carrierAlgebra ⟶ carrierAlgebra :=
  CommHopfAlgCat.liftQuotient (CommHopfAlgCat.commonKernelHopfIdeal generator)
    ambientFrobeniusCoordinateMap
    commonKernelHopfIdeal_toIdeal_le_ker_ambientFrobeniusCoordinateMap

/-- The Frobenius coordinate map cubes the universal point of the carrier: this is the
defining equation of `frobeniusCoordinateMap`. -/
theorem map_carrierGenericMatrix_frobeniusCoordinateMap :
    carrierGenericMatrix.map frobeniusCoordinateMap.hom.toAlgHom =
      carrierGenericMatrix.map (fun x => x ^ 3) := by
  -- As for the special-isogeny coordinate map above, expand only the named universal matrix on
  -- the left, so the quotient factorization is visible to its explicit rewrite lemma.
  conv_lhs => rw [carrierGenericMatrix_def]
  rw [← map_genericMatrix_comp, frobeniusCoordinateMap,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient,
    map_genericMatrix_ambientFrobeniusCoordinateMap]

private theorem carrierQuotient_comp_specialIsogenyCoordinateMap :
    carrierQuotient ≫ specialIsogenyCoordinateMap = ambientCoordinateMap := by
  rw [specialIsogenyCoordinateMap, CommHopfAlgCat.mkQuotient_comp_liftQuotient]

private theorem carrierQuotient_comp_frobeniusCoordinateMap :
    carrierQuotient ≫ frobeniusCoordinateMap = ambientFrobeniusCoordinateMap := by
  rw [frobeniusCoordinateMap, CommHopfAlgCat.mkQuotient_comp_liftQuotient]

/-- The special isogeny squared is the prime-field Frobenius on the carrier coordinate ring. -/
theorem specialIsogenyCoordinateMap_comp_self :
    specialIsogenyCoordinateMap ≫ specialIsogenyCoordinateMap = frobeniusCoordinateMap := by
  let _ : Epi carrierQuotient := ConcreteCategory.epi_of_surjective carrierQuotient
    (CommHopfAlgCat.mkQuotient_surjective
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
      (CommHopfAlgCat.commonKernelHopfIdeal generator))
  apply (cancel_epi carrierQuotient).1
  rw [← Category.assoc, carrierQuotient_comp_specialIsogenyCoordinateMap,
    ambientCoordinateMap_comp_specialIsogenyCoordinateMap,
    carrierQuotient_comp_frobeniusCoordinateMap]

/-- The cubic Frobenius as an endomorphism of the short-root type-`G₂` carrier. -/
noncomputable def frobeniusHom : groupScheme ⟶ groupScheme :=
  eqToHom groupScheme_eq_commonKernelSpec ≫
    CommHopfAlgCat.commonKernelSpecRestrict ambientFrobeniusCoordinateMap
      commonKernelHopfIdeal_toIdeal_le_ker_ambientFrobeniusCoordinateMap ≫
    eqToHom groupScheme_eq_commonKernelSpec.symm

/-- The comorphism of the carrier Frobenius is `frobeniusCoordinateMap`. -/
theorem frobeniusHom_eq_map_frobeniusCoordinateMap :
    frobeniusHom =
      eqToHom groupScheme_eq_commonKernelSpec ≫
        (hopfSpec (CommRingCat.of (ZMod 3))).map frobeniusCoordinateMap.op ≫
          eqToHom groupScheme_eq_commonKernelSpec.symm := by
  rw [frobeniusHom, CommHopfAlgCat.commonKernelSpecRestrict_def]
  rfl

private theorem carrierAlgebraPointsMulEquiv_map_frobeniusCoordinateMap
    {B : Type} [CommRing B] [Algebra (ZMod 3) B]
    (q : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra)
      (CommAlgCat.of (ZMod 3) B)) :
    carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B)
        (AlgHom.mapDomain frobeniusCoordinateMap.hom q) =
      frobenius 1 B (carrierAlgebraPointsMulEquiv (CommAlgCat.of (ZMod 3) B) q) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_carrierAlgebraPointsMulEquiv_eq_map_carrierGenericMatrix]
  ext i j
  rw [coe_frobenius_apply,
    coe_carrierAlgebraPointsMulEquiv_eq_map_carrierGenericMatrix, Matrix.map_apply]
  have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) carrierAlgebra => M.map q.ofConv)
    map_carrierGenericMatrix_frobeniusCoordinateMap
  have hmap :
      (((AlgHom.mapDomain frobeniusCoordinateMap.hom q).ofConv :
          carrierAlgebra →ₐ[ZMod 3] B) : carrierAlgebra → B) =
        q.ofConv ∘ frobeniusCoordinateMap.hom := by
    funext x
    rfl
  have hij := congrFun (congrFun h i) j
  rw [hmap]
  simpa only [Matrix.map_map, Matrix.map_apply, Function.comp_apply, BialgHom.coe_toAlgHom,
    map_pow, pow_one] using hij

/-- The action induced by `frobeniusHom` on scheme-valued carrier points is the named cubic
Frobenius. -/
@[simp]
theorem schemePointsMulEquiv_comp_frobeniusHom
    (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (p : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶ groupScheme.X) :
    schemePointsMulEquiv B (p ≫ frobeniusHom.hom.hom) =
      frobenius 1 B (schemePointsMulEquiv B p) := by
  obtain ⟨q, rfl⟩ := (carrierGroupSchemePointMulEquiv B).surjective p
  rw [frobeniusHom_eq_map_frobeniusCoordinateMap,
    carrierGroupSchemePointMulEquiv_comp_coordinateMap,
    schemePointsMulEquiv_carrierGroupSchemePointMulEquiv,
    schemePointsMulEquiv_carrierGroupSchemePointMulEquiv]
  exact carrierAlgebraPointsMulEquiv_map_frobeniusCoordinateMap q

/-- On scheme-valued points, composing a numbered root subgroup with the carrier special
isogeny exchanges the root lengths and applies the prescribed parameter exponent. -/
@[simp]
theorem schemePointsMulEquiv_comp_rootSubgroup_comp_specialIsogenyHom
    (k : Fin 2 ⊕ Fin 2) (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (p : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶
      (AdditiveGroup.groupScheme (ZMod 3)).X) :
    schemePointsMulEquiv B
        (p ≫ (rootSubgroup k).hom.hom ≫ specialIsogenyHom.hom.hom) =
      rootSubgroupPoints (specialIsogenyRootIndex k) B
        (Multiplicative.ofAdd
          (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv B p) ^
            specialIsogenyExponent k)) := by
  rw [← Category.assoc, schemePointsMulEquiv_comp_specialIsogenyHom,
    schemePointsMulEquiv_comp_rootSubgroup]
  obtain ⟨t, ht⟩ : ∃ t : B, Multiplicative.ofAdd t =
      AdditiveGroup.schemePointsMulEquiv B p :=
    ⟨Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv B p), rfl⟩
  rw [← ht, specialIsogeny_rootSubgroupPoints]
  simp only [toAdd_ofAdd]

/-- On scheme-valued points, composing the weight torus with the carrier special isogeny sends
`(s₀, s₁)` to `(s₁, s₀³)`. -/
@[simp]
theorem schemePointsMulEquiv_comp_weightTorus_comp_specialIsogenyHom
    (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (p : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶
      (SplitTorus.groupScheme (ZMod 3) (Fin 2)).X) :
    schemePointsMulEquiv B
        (p ≫ weightTorus.hom.hom ≫ specialIsogenyHom.hom.hom) =
      weightTorusPoints B (specialIsogenyTorusMap (SplitTorus.schemePointsMulEquiv p)) := by
  rw [← Category.assoc, schemePointsMulEquiv_comp_specialIsogenyHom,
    schemePointsMulEquiv_comp_weightTorus, specialIsogeny_weightTorusPoints]

/-- On scheme-valued points, composing a numbered root subgroup with carrier Frobenius cubes its
parameter. -/
@[simp]
theorem schemePointsMulEquiv_comp_rootSubgroup_comp_frobeniusHom
    (k : Fin 2 ⊕ Fin 2) (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (p : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶
      (AdditiveGroup.groupScheme (ZMod 3)).X) :
    schemePointsMulEquiv B (p ≫ (rootSubgroup k).hom.hom ≫ frobeniusHom.hom.hom) =
      rootSubgroupPoints k B
        (Multiplicative.ofAdd
          (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv B p) ^ 3)) := by
  rw [← Category.assoc, schemePointsMulEquiv_comp_frobeniusHom,
    schemePointsMulEquiv_comp_rootSubgroup, frobenius_rootSubgroupPoints]
  norm_num

/-- On scheme-valued points, composing the weight torus with carrier Frobenius cubes every torus
coordinate. -/
@[simp]
theorem schemePointsMulEquiv_comp_weightTorus_comp_frobeniusHom
    (B : Type) [CommRing B] [Algebra (ZMod 3) B]
    (p : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶
      (SplitTorus.groupScheme (ZMod 3) (Fin 2)).X) :
    schemePointsMulEquiv B (p ≫ weightTorus.hom.hom ≫ frobeniusHom.hom.hom) =
      weightTorusPoints B (SplitTorus.schemePointsMulEquiv p ^ 3) := by
  rw [← Category.assoc, schemePointsMulEquiv_comp_frobeniusHom,
    schemePointsMulEquiv_comp_weightTorus, frobenius_weightTorusPoints]
  norm_num

/-- The special isogeny squared is the cubic Frobenius as a carrier morphism. -/
theorem specialIsogenyHom_comp_self :
    specialIsogenyHom ≫ specialIsogenyHom = frobeniusHom := by
  rw [specialIsogenyHom, frobeniusHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [CommHopfAlgCat.commonKernelSpecRestrict_def]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← op_comp]
  have h := specialIsogenyCoordinateMap_comp_self
  simp only [specialIsogenyCoordinateMap, frobeniusCoordinateMap] at h
  rw [h]

private theorem g2SpecialIsogeny_g2SpecialIsogeny_carrierGenericMatrix :
    g2SpecialIsogeny (g2SpecialIsogeny carrierGenericMatrix) =
      carrierGenericMatrix.map (fun x => x ^ 3) := by
  rw [← map_genericMatrix_ambientCoordinateMap_comp_specialIsogenyCoordinateMap,
    ambientCoordinateMap_comp_specialIsogenyCoordinateMap,
    map_genericMatrix_ambientFrobeniusCoordinateMap]

private theorem g2SpecialIsogeny_g2SpecialIsogeny_of_mem_points
    {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A} (hg : g ∈ points A) :
    g2SpecialIsogeny (g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A)) =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A).map (fun x => x ^ 3) := by
  have hker : ∀ h : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7,
      h ∈ CommHopfAlgCat.commonKernelHopfIdeal generator →
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g).ofConv h = 0 := by
    have hmem := le_of_eq (points_def A) hg
    rw [TauCeti.GeneralLinear.mem_generatedPointsSubgroup_iff] at hmem
    exact hmem
  set q := CommHopfAlgCat.liftQuotientPoint
    (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
    (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 3) A)
    ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g) hker with hq
  have hcomp : (q.ofConv : carrierAlgebra → A) ∘
        (carrierQuotient.hom.toAlgHom :
          TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 → carrierAlgebra) =
      (((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g).ofConv :
        TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 → A) := by
    funext x
    rw [Function.comp_apply, hq, BialgHom.coe_toAlgHom, CommHopfAlgCat.mkQuotient_apply]
    exact CommHopfAlgCat.liftQuotientPoint_mk
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
      (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 3) A)
      ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g) hker x
  have hphi : carrierGenericMatrix.map q.ofConv =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
    rw [carrierGenericMatrix_def, Matrix.map_map, hcomp, map_ofConv_genericMatrix]
  rw [← hphi, g2SpecialIsogeny_map, g2SpecialIsogeny_map,
    g2SpecialIsogeny_g2SpecialIsogeny_carrierGenericMatrix, Matrix.map_map, Matrix.map_map]
  exact congrArg _ (funext fun x => map_pow q.ofConv x 3)

/-- The special isogeny of the carrier squares pointwise to the cubic Frobenius. -/
@[simp]
theorem specialIsogeny_specialIsogeny (g : points A) :
    specialIsogeny A (specialIsogeny A g) = frobenius 1 A g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny, coe_specialIsogeny,
    g2SpecialIsogeny_g2SpecialIsogeny_of_mem_points g.2]
  ext a b
  rw [Matrix.map_apply, coe_frobenius_apply]
  norm_num

/-- The special isogeny squared is the cubic Frobenius on matrix-valued points. -/
theorem specialIsogeny_comp_specialIsogeny :
    (specialIsogeny A).comp (specialIsogeny A) = frobenius 1 A :=
  MonoidHom.ext fun g => specialIsogeny_specialIsogeny g

end TauCeti.G2ShortRoot.PrimeField
