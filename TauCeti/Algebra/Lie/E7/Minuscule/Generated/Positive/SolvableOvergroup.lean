/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.BorelCandidate
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight.Positive
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.Lie.E7.Minuscule.WeightAction

/-!
# Equations for solvable overgroups of the positive E7 subgroup

A reduced connected solvable overgroup of the positive minuscule subgroup satisfies every
matrix-entry equation forced by the positive root cone. These are equations in its coordinate
algebra, and therefore hold over arbitrary value algebras. Its actual adjoint torus representation
has no nonzero negative-cone weight space, in every characteristic.

The same conclusions apply to Borel candidates containing the positive subgroup in the carrier
generated over the field. The quotient isomorphism identifies their specified weight tori and
adjoint weight spaces. No maximality or integral specialization comparison is assumed.

## References

The stable flag is supplied by
`Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable`.
`HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus` identifies adjoint weight spaces with
the vanishing of tangent-matrix entries outside the specified character.
-/

public section

open CategoryTheory WithConv
open TauCeti.DynkinType
open scoped Matrix TensorProduct

namespace TauCeti.E7Minuscule.Generated.Positive

universe u

noncomputable section

variable {k : Type u} [Field k]

local notation "μ" => e7MinusculeWeight
local notation "C₊" => posRootCone e7SimplyConnectedRootDatum e7SimplyConnectedBase

private theorem liftQuotient_generator_comp_mkQuotient
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    (g : (Fin 7 ⊕ Fin 7) ⊕ Unit)
    (hg : J.toIdeal ≤ RingHom.ker (generatorCoordinateMap k g).hom.toAlgHom.toRingHom) :
    (CommHopfAlgCat.liftQuotient J (generatorCoordinateMap k g) hg).hom.comp
        (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      (generatorCoordinateMap k g).hom := by
  simpa only [_root_.CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_mkQuotient] using
    congrArg _root_.CommHopfAlgCat.Hom.hom
      (CommHopfAlgCat.mkQuotient_comp_liftQuotient J (generatorCoordinateMap k g) hg)

private theorem quotient_rootSubgroup_point
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    (hJ : J ≤ definingIdeal k) (i : Fin 7) (t : k) :
    let f := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap k (.inl (.inl i)))
      (((le_definingIdeal_iff k J).mp hJ).1 i)
    let q := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
      (Multiplicative.ofAdd t)
    GeneralLinear.pointToGeneralLinear 56
        ((CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra k 56) J).mapPointsFunctor.app
          (CommAlgCat.of k k) (f.mapPointsFunctor.app (CommAlgCat.of k k) q)) =
      (rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 56) k) := by
  let f := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap k (.inl (.inl i)))
    (((le_definingIdeal_iff k J).mp hJ).1 i)
  let q := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
    (Multiplicative.ofAdd t)
  dsimp only
  -- The exposed point-functor application packages coordinate precomposition.
  -- Folding this wrapper does not unfold the underlying point-map implementation.
  have h : GeneralLinear.pointToGeneralLinear 56
      ((coordinateMap k).mapPointsFunctor.app (CommAlgCat.of k k)
        (toConv (q.ofConv.comp
          (rootSubgroupToBaseChangeCoordinateMap k (.inl i)).hom.toAlgHom))) =
      (rootSubgroupPoints (.inl i) k (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 56) k) :=
    pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
      k (.inl i) (CommAlgCat.of k k) q
  have hcomp' : f.hom.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      (rootSubgroupToBaseChangeCoordinateMap k (.inl i)).hom.comp (coordinateMap k).hom := by
    calc
      _ = (generatorCoordinateMap k (.inl (.inl i))).hom :=
        liftQuotient_generator_comp_mkQuotient J (.inl (.inl i))
          (((le_definingIdeal_iff k J).mp hJ).1 i)
      _ = _ := by
        rw [generatorCoordinateMap_inl,
          ← coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap,
          _root_.CommHopfAlgCat.hom_comp]
  have hcompAlg := congrArg BialgHom.toAlgHom hcomp'
  simp only [BialgHom.comp_toAlgHom] at hcompAlg
  -- Explicit evaluation crosses the categorical object and hom coercions.
  erw [_root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at h
  erw [_root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    _root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  simpa only [CommHopfAlgCat.hom_mkQuotient, ofConv_toConv, AlgHom.comp_assoc,
    ← hcompAlg, f, q, MulEquiv.apply_symm_apply] using h

private theorem single_mem_of_raising_step
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    (hJ : J ≤ definingIdeal k) :
    let _ := GeneralLinear.corestrictStandardComodule k 56
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
    ∀ (N : Subcomodule k (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal)
        (Fin 56 → k)) {a b : Fin 56}, E7MinusculeRaisingStep a b →
      Pi.single a (1 : k) ∈ N → Pi.single b (1 : k) ∈ N := by
  let _ := GeneralLinear.corestrictStandardComodule k 56
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
  dsimp only
  intro N a b hab ha
  obtain ⟨i, hi, rfl⟩ := (e7MinusculeRaisingStep_iff _ _).mp hab
  let f := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap k (.inl (.inl i)))
    (((le_definingIdeal_iff k J).mp hJ).1 i)
  let q := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
    (Multiplicative.ofAdd (1 : k))
  -- The quotient's point-functor application folds the same exposed wrapper, so
  -- the subcomodule action is expressed in the form of quotient_rootSubgroup_point.
  have hmem :
      (GeneralLinear.pointToGeneralLinear 56
        ((CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra k 56) J).mapPointsFunctor.app
          (CommAlgCat.of k k) (f.mapPointsFunctor.app (CommAlgCat.of k k) q)) :
        Matrix (Fin 56) (Fin 56) k) *ᵥ Pi.single a (1 : k) ∈ N :=
    GeneralLinear.corestrictStandardComodule_mulVec_mem k 56
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) N
      (f.mapPointsFunctor.app (CommAlgCat.of k k) q) ha
  rw [quotient_rootSubgroup_point J hJ i (1 : k)] at hmem
  rw [← Subcomodule.mem_toSubmodule] at hmem ha ⊢
  simpa only [positiveRoot_mulVec_single_sub k i a hi] using
    N.toSubmodule.sub_mem hmem ha

private theorem single_mem_of_raising_path
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    (hJ : J ≤ definingIdeal k) :
    let _ := GeneralLinear.corestrictStandardComodule k 56
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
    ∀ (N : Subcomodule k (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal)
        (Fin 56 → k)) {a b : Fin 56},
      Relation.ReflTransGen E7MinusculeRaisingStep a b →
      Pi.single a (1 : k) ∈ N → Pi.single b (1 : k) ∈ N := by
  let _ := GeneralLinear.corestrictStandardComodule k 56
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
  dsimp only
  intro N a b h
  induction h with
  | refl => exact id
  | tail h hstep ih => exact fun ha ↦ single_mem_of_raising_step J hJ N hstep (ih ha)

-- Relabelling the integral characters lets the categorical adjoint criterion use the
-- field universe without restricting the original torus or its characters.
private def liftedCharacterEquiv : Multiplicative (Fin 7 →₀ ℤ) ≃*
    Multiplicative (ULift.{u} (Fin 7) →₀ ℤ) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)

private abbrev liftedCharacterAlgebraEquiv (k : Type u) [Field k] :
    MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)) ≃ₐc[k]
      MonoidAlgebra k (Multiplicative (ULift.{u} (Fin 7) →₀ ℤ)) :=
  MonoidAlgebra.domCongrBialgEquiv k k liftedCharacterEquiv

private theorem liftedCharacterAlgebraEquiv_single
    (α : Multiplicative (Fin 7 →₀ ℤ)) :
    liftedCharacterAlgebraEquiv k (MonoidAlgebra.single α 1) =
      MonoidAlgebra.single (liftedCharacterEquiv α) 1 := by
  simp only [liftedCharacterAlgebraEquiv, MonoidAlgebra.domCongrBialgEquiv,
    BialgEquiv.ofAlgEquiv_apply]
  exact MonoidAlgebra.domCongr_single (R := k) (A := k) liftedCharacterEquiv α 1

private theorem liftedCharacterEquiv_weightCharacter (w : Fin 7 → ℤ) :
    liftedCharacterEquiv (SplitTorus.weightCharacter w) =
      SplitTorus.weightCharacter (fun i : ULift.{u} (Fin 7) ↦ w i.down) := by
  apply Multiplicative.toAdd.injective
  ext i
  simp [liftedCharacterEquiv, Finsupp.domCongr]

private theorem lifted_weightTorusCoordinateMap :
    (liftedCharacterAlgebraEquiv k).toBialgHom.comp
        (GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ) =
      (GeneralLinear.weightTorusCoordinateMap
        (fun a (i : ULift.{u} (Fin 7)) ↦ μ a i.down)).hom := by
  apply GeneralLinear.coordinateHopfAlgebra_bialgHom_ext k 56
  intro a b
  rw [BialgHom.comp_apply, GeneralLinear.weightTorusCoordinateBialgHom_X,
    GeneralLinear.weightTorusCoordinateMap_X]
  split_ifs with hab
  · -- The direct torus map uses the finitely supported representative of its character;
    -- the bialgebra equivalence acts through the same underlying function.
    change liftedCharacterAlgebraEquiv k (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (μ a))) 1) = _
    rw [liftedCharacterAlgebraEquiv_single]
    congr 1
    rw [← SplitTorus.weightCharacter_coe, ← SplitTorus.weightCharacter_coe,
      Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_equivFunOnFinite_symm]
    exact liftedCharacterEquiv_weightCharacter (μ a)
  · exact map_zero _

private theorem mem_adjointWeightSpace_iff_directWeightTorus
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    [Module.Finite k (Bialgebra.CotangentSpace k
      (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal))]
    [Module.Projective k (Bialgebra.CotangentSpace k
      (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal))]
    (π : (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ)
    (α : Multiplicative (Fin 7 →₀ ℤ))
    (x : Module.Dual k (Bialgebra.CotangentSpace k
      (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal))) :
    x ∈ Derivation.adjointWeightSpace π α ↔
      ∀ a b, SplitTorus.weightCharacter (μ a - μ b) ≠ α →
        GeneralLinear.tangentMatrix 56
          (HopfIdeal.quotientLieHom J (Derivation.cotangentLinearEquiv (B := k) x)) a b = 0 := by
  let π' := (liftedCharacterAlgebraEquiv k).toBialgHom.comp π
  have hπ' : π'.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap
        (fun a (i : ULift.{u} (Fin 7)) ↦ μ a i.down)).hom := by
    rw [BialgHom.comp_assoc, hπ, lifted_weightTorusCoordinateMap]
  rw [← Derivation.adjointWeightSpace_domCongr liftedCharacterEquiv π α]
  rw [HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus J _ π' hπ']
  have hchar (a b : Fin 56) :
      SplitTorus.weightCharacter
          ((fun i : ULift.{u} (Fin 7) ↦ μ a i.down) - fun i ↦ μ b i.down) =
        liftedCharacterEquiv (SplitTorus.weightCharacter (μ a - μ b)) :=
    (liftedCharacterEquiv_weightCharacter (μ a - μ b)).symm
  simp only [hchar, ne_eq, liftedCharacterEquiv.injective.eq_iff]

variable [IsAlgClosed k]

/-- Every nonzero positive-cone difference forces a universal matrix-entry equation in a
reduced geometrically connected solvable overgroup of the positive minuscule subgroup. -/
theorem quotient_genericMatrix_eq_zero_of_posRootCone
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    (hJ : J ≤ definingIdeal k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56) J))
    {a b : Fin 56} (hcone : μ b - μ a ∈ C₊) (hne : μ b - μ a ≠ 0) :
    Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
      (GeneralLinear.genericMatrix k 56 a b) = 0 := by
  classical
  let H := GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
  let _ := GeneralLinear.corestrictStandardComodule k 56 q
  let π := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap k (.inr ()))
    (((le_definingIdeal_iff k J).mp hJ).2)
  have hπ : π.hom.comp q = GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ := by
    calc
      π.hom.comp q = (generatorCoordinateMap k (.inr ())).hom :=
        liftQuotient_generator_comp_mkQuotient J (.inr ())
          (((le_definingIdeal_iff k J).mp hJ).2)
      _ = GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ := by
        rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hweights := GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights q π.hom μ hπ
  obtain ⟨n, bas, htri, _⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (M := Fin 56 → k) hconn hsolv
  let F := Comodule.flagSubcomodule bas htri
  have hcoord (r : Fin (n + 1)) :
      (F r).toSubmodule = Submodule.span k ((Pi.basisFun k (Fin 56)) ''
        {a | Pi.single a (1 : k) ∈ F r}) :=
    Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights π.hom.toCoalgHom
      (fun a ↦ SplitTorus.weightCharacter (μ a)) minusculeCharacter_injective hweights (F r)
  have hbas (r : Fin (n + 1)) : bas.flag r = Submodule.span k
      ((Pi.basisFun k (Fin 56)) '' {a | Pi.single a (1 : k) ∈ bas.flag r}) := by
    simpa only [F, Comodule.flagSubcomodule_toSubmodule,
      ← Subcomodule.mem_toSubmodule] using hcoord r
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hne (sub_self _)
  have hpath := (e7Minuscule_raisingPath_iff_mem_posRootCone a b).mpr hcone
  have hzero : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 56)) a b = 0 := by
    apply Comodule.coefficient_eq_zero_of_coordinate_flag (Pi.basisFun k (Fin 56)) bas htri
    · simpa only [Pi.basisFun_apply] using hbas
    · exact hab
    · intro N
      simpa only [Pi.basisFun_apply] using single_mem_of_raising_path J hJ N hpath
  have hcoeff : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 56)) =
      (GeneralLinear.genericMatrix k 56).map q := by
    let _ := GeneralLinear.standardComodule k 56
    rw [← GeneralLinear.coefficientMatrix_basisFun]
    exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k (Fin 56)) q.toCoalgHom
  simpa only [hcoeff, Matrix.map_apply] using hzero

/-- Every nonzero negative-cone character has zero actual adjoint weight space in a reduced
geometrically connected solvable overgroup. The character is integral, in every characteristic. -/
theorem adjointWeightSpace_neg_eq_bot_of_posRootCone
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 56))
    (hJ : J ≤ definingIdeal k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56) J))
    (π : (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ)
    {δ : Fin 7 → ℤ} (hδ : δ ∈ C₊) (hne : δ ≠ 0) :
    Derivation.adjointWeightSpace π (SplitTorus.weightCharacter (-δ)) = ⊥ := by
  classical
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hentry := (mem_adjointWeightSpace_iff_directWeightTorus J π hπ
    (SplitTorus.weightCharacter (-δ)) x).mp hx
  apply (Derivation.cotangentLinearEquiv (B := k)).injective
  apply (HopfIdeal.quotientLieHom_injective J)
  apply (GeneralLinear.tangentLinearEquivMatrix 56).injective
  simp only [GeneralLinear.tangentLinearEquivMatrix_apply]
  ext a b
  simp only [map_zero, Matrix.zero_apply]
  by_cases hab : SplitTorus.weightCharacter (μ a - μ b) =
      SplitTorus.weightCharacter (-δ)
  · have hchars : μ a - μ b = -δ := by
      funext i
      have h := congrArg (fun χ : Multiplicative (Fin 7 →₀ ℤ) ↦ Multiplicative.toAdd χ i) hab
      simpa only [SplitTorus.toAdd_weightCharacter] using h
    have hdiff : μ b - μ a = δ := by
      apply neg_injective
      simpa only [neg_sub] using hchars
    have hzero := quotient_genericMatrix_eq_zero_of_posRootCone J hJ hconn hsolv
      (a := a) (b := b) (by simpa only [hdiff] using hδ) (by simpa only [hdiff] using hne)
    rw [GeneralLinear.genericMatrix_apply] at hzero
    have hqzero : Ideal.Quotient.mkₐ k J.toIdeal
        ((GeneralLinear.coordinateHopfAlgebraAlgEquiv k 56)
          ((GeneralLinear.coordinateRingMap k 56) (MvPolynomial.X (a, b)))) = 0 := by
      simpa only [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk] using hzero
    simp only [GeneralLinear.tangentMatrix_apply, HopfIdeal.quotientLieHom_apply_apply,
      hqzero, map_zero]
    -- Align the exported counit-algebra synonym before using its zero-preserving map.
    change (Bialgebra.CounitAlgebra.algEquivSelf k
      (GeneralLinear.coordinateHopfAlgebra k 56) k)
        (0 : Bialgebra.CounitAlgebra k (GeneralLinear.coordinateHopfAlgebra k 56) k) = 0
    exact map_zero _
  · exact hentry a b hab

omit [IsAlgClosed k] in
private abbrev carrierQuotientIso (I : HopfIdeal k (generatedCoordinateHopfAlgebra k)) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56)
        (I.comapOfSurjective (generatedCoordinateMap k).hom
          (generatedCoordinateMap_surjective k)) ≅
      CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I :=
  (open _root_.TauCeti.CommHopfAlgCat _root_.CommHopfAlgCat.Hom in
    quotientIsoOfSurjective (generatedCoordinateMap k)
      (generatedCoordinateMap_surjective k) I)

omit [IsAlgClosed k] in
private theorem carrier_comap_properties
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I)) :
    let J := I.comapOfSurjective (generatedCoordinateMap k).hom
      (generatedCoordinateMap_surjective k)
    IsReduced (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal) ∧
      geometricallyConnectedCommHopfAlgProperty k
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56) J) ∧
      geometricallySolvablePointsCommHopfAlgProperty k
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 56) J) := by
  let e := carrierQuotientIso I
  exact ⟨isReduced_of_injective (_root_.CommHopfAlgCat.ofIso e).toAlgEquiv.toRingHom
      (_root_.CommHopfAlgCat.ofIso e).injective,
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm hconn,
    (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm hsolv⟩

omit [IsAlgClosed k] in
private theorem carrierQuotientIso_hom_comp_mkQuotient
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k)) :
    (carrierQuotientIso I).hom.hom.comp
        (Bialgebra.Quotient.mkBialgHom (R := k)
          (I.comapOfSurjective (generatedCoordinateMap k).hom
            (generatedCoordinateMap_surjective k)).toIdeal) =
      (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal).comp (generatedCoordinateMap k).hom := by
  simpa only [_root_.CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_mkQuotient] using
    congrArg _root_.CommHopfAlgCat.Hom.hom
      (open _root_.TauCeti.CommHopfAlgCat _root_.CommHopfAlgCat.Hom in
        mkQuotient_comp_quotientIsoOfSurjective_hom
          (generatedCoordinateMap k) (generatedCoordinateMap_surjective k) I)

omit [IsAlgClosed k] in
private theorem carrier_comap_le_definingIdeal
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k) :
    I.comapOfSurjective (generatedCoordinateMap k).hom
      (generatedCoordinateMap_surjective k) ≤ definingIdeal k := by
  intro z hz
  have hzero := (mem_carrierDefiningIdeal k _).mp
    (hI (HopfIdeal.mem_comapOfSurjective.mp hz))
  have hcomp := congrArg _root_.CommHopfAlgCat.Hom.hom
    (generatedCoordinateMap_comp_restriction k)
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ z).mp
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using
    (BialgHom.congr_fun hcomp z).symm.trans hzero

/-- The positive-cone equations hold in every reduced connected solvable overgroup inside
E7's field-generated carrier, in its actual quotient coordinate algebra. -/
theorem carrierQuotient_genericMatrix_eq_zero_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    {a b : Fin 56} (hcone : μ b - μ a ∈ C₊) (hne : μ b - μ a ≠ 0) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap k).hom (GeneralLinear.genericMatrix k 56 a b)) = 0 := by
  let J := I.comapOfSurjective (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)
  let e := carrierQuotientIso I
  obtain ⟨hred, hconn', hsolv'⟩ := carrier_comap_properties I hconn hsolv
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal) := hred
  have hzero := quotient_genericMatrix_eq_zero_of_posRootCone J
    (carrier_comap_le_definingIdeal I hI)
    hconn' hsolv' hcone hne
  have hcomm := carrierQuotientIso_hom_comp_mkQuotient I
  have hz := BialgHom.congr_fun hcomm (GeneralLinear.genericMatrix k 56 a b)
  simp only [BialgHom.comp_apply] at hz
  exact hz.symm.trans ((congrArg e.hom.hom hzero).trans (map_zero _))

/-- The actual carrier quotient has no negative-cone adjoint characters. The torus factor
is the one induced by the carrier's stored weight-torus generator. -/
theorem carrierQuotient_adjointWeightSpace_neg_eq_bot_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (π : (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift k (.inr ())).hom)
    {δ : Fin 7 → ℤ} (hδ : δ ∈ C₊) (hne : δ ≠ 0) :
    Derivation.adjointWeightSpace π (SplitTorus.weightCharacter (-δ)) = ⊥ := by
  let J := I.comapOfSurjective (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)
  let e := carrierQuotientIso I
  obtain ⟨hred, hconn', hsolv'⟩ := carrier_comap_properties I hconn hsolv
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k 56 ⧸ J.toIdeal) := hred
  have hcomm := carrierQuotientIso_hom_comp_mkQuotient I
  have htorus : (π.comp e.hom.hom).comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ := by
    rw [BialgHom.comp_assoc, hcomm, ← BialgHom.comp_assoc, hπ]
    have hgen := congrArg _root_.CommHopfAlgCat.Hom.hom
      (generatedCoordinateMap_comp_generatedCoordinateLift k (.inr ()))
    simpa only [_root_.CommHopfAlgCat.hom_comp, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap] using hgen
  have hzero := adjointWeightSpace_neg_eq_bot_of_posRootCone J
    (carrier_comap_le_definingIdeal I hI)
    hconn' hsolv'
    (π.comp e.hom.hom) htorus hδ hne
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hmem := (Derivation.dualCotangentMap_mem_adjointWeightSpace_iff_of_characterEquiv
    liftedCharacterEquiv (_root_.CommHopfAlgCat.ofIso e).toBialgHom
    (_root_.CommHopfAlgCat.ofIso e).surjective π (SplitTorus.weightCharacter (-δ)) x).mpr hx
  rw [BialgEquiv.toBialgHom_eq_coe, CommHopfAlgCat.coe_ofIso] at hmem
  have hxzero : Derivation.dualCotangentMap e.hom.hom x = 0 := by
    exact (Submodule.mem_bot k).mp (hzero ▸ hmem)
  have hmap : Derivation.dualCotangentEquiv (_root_.CommHopfAlgCat.ofIso e) x =
      Derivation.dualCotangentMap e.hom.hom x := by
    rw [Derivation.dualCotangentEquiv_apply]
    exact congrArg (fun f ↦ Derivation.dualCotangentMap f x) (CommHopfAlgCat.coe_ofIso e)
  apply (Derivation.dualCotangentEquiv (_root_.CommHopfAlgCat.ofIso e)).injective
  exact hmap.trans (hxzero.trans (map_zero _).symm)

/-- In particular every Borel candidate containing the generated positive subgroup satisfies
its positive-cone matrix-entry equations. -/
theorem borelCandidate_genericMatrix_eq_zero_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    (hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k)) I)
    {a b : Fin 56} (hcone : μ b - μ a ∈ C₊) (hne : μ b - μ a ≠ 0) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap k).hom (GeneralLinear.genericMatrix k 56 a b)) = 0 := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact carrierQuotient_genericMatrix_eq_zero_of_posRootCone I hI
    hB.geometricallyConnected hB.geometricallySolvable hcone hne

/-- Every Borel candidate containing the positive subgroup has zero adjoint weight space for
each nonzero negative-cone character of the stored weight torus. -/
theorem borelCandidate_adjointWeightSpace_neg_eq_bot_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    (hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k)) I)
    (π : (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift k (.inr ())).hom)
    {δ : Fin 7 → ℤ} (hδ : δ ∈ C₊) (hne : δ ≠ 0) :
    Derivation.adjointWeightSpace π (SplitTorus.weightCharacter (-δ)) = ⊥ := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact carrierQuotient_adjointWeightSpace_neg_eq_bot_of_posRootCone I hI
    hB.geometricallyConnected hB.geometricallySolvable π hπ hδ hne

end

end TauCeti.E7Minuscule.Generated.Positive
