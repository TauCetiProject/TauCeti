/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.BorelCandidate
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Basis
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.StandardComodule

/-!
# Solvable overgroups of the positive type-D spin subgroup

Over an algebraically closed field, every reduced connected solvable overgroup of the positive
spin subgroup satisfies the matrix-entry equations opposite every simple raising step. Its
adjoint weight spaces at the negative numbered simple roots vanish, in every characteristic.
The equations hold in the quotient coordinate algebra, not just at ground-field points.

The conclusions also apply inside the field-generated spin carrier, with its stored weight
torus, and in particular to every Borel candidate containing the positive subgroup. These are
constraints on possible solvable overgroups; maximality of the positive subgroup is not asserted.
No identification with the pinned simply connected group scheme is used or proved.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* The flag argument follows
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.SolvableOvergroup`.
  Spin root moves use `exists_rootSubgroupPoints_inl_mulVec_single_sub`, and adjoint vanishing
  uses `HopfIdeal.adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.TypeDSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) {k : Type u} [Field k]

private theorem single_mem_of_raising_step
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n hn k) :
    let _ := GeneralLinear.corestrictStandardComodule k (dimension n)
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
    ∀ (N : Subcomodule k (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)
        (Fin (dimension n) → k)) (i : Fin n) (a : Fin (dimension n)),
      basisWeight n a i = -1 → Pi.single a (1 : k) ∈ N →
        Pi.single (basisReflection n i a) (1 : k) ∈ N := by
  let _ := GeneralLinear.corestrictStandardComodule k (dimension n)
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
  dsimp only
  intro N i a ha hv
  let f := CommHopfAlgCat.quotientMapOfLe
    (GeneralLinear.coordinateHopfAlgebra k (dimension n)) hJ
  have hcomodule : Comodule.Corestrict f.hom.toCoalgHom = standardComodule n hn k := by
    let _ := GeneralLinear.standardComodule k (dimension n)
    apply Comodule.ext
    rw [standardComodule_coact, Comodule.corestrict_coact,
      ← Comodule.corestrictCoact_comp (M := Fin (dimension n) → k)
        (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom f.hom.toCoalgHom]
    have hcomp : f.hom.toCoalgHom.comp
        (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom =
        (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn k)).hom.toCoalgHom :=
      congrArg (fun g : _root_.CommHopfAlgCat.Hom _ _ ↦ g.hom.toCoalgHom)
        (CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe
          (GeneralLinear.coordinateHopfAlgebra k (dimension n)) hJ)
    rw [hcomp]
  have hraise : let _ := Comodule.Corestrict (M := Fin (dimension n) → k) f.hom.toCoalgHom
      ∀ W : Subcomodule k (coordinateHopfAlgebra n hn k) (Fin (dimension n) → k),
        Pi.single a (1 : k) ∈ W → Pi.single (basisReflection n i a) (1 : k) ∈ W := by
    rw [hcomodule]
    exact fun W ↦ single_basisReflection_mem n hn k W i a ha
  exact (Subcomodule.mem_corestrict f.hom.toCoalgHom N _).mp
    (hraise (N.corestrict f.hom.toCoalgHom)
      ((Subcomodule.mem_corestrict f.hom.toCoalgHom N _).mpr hv))

variable [IsAlgClosed k]

/-- In a reduced connected solvable overgroup of the positive spin subgroup, each matrix entry
opposite a simple raising step is zero in the coordinate algebra. -/
theorem quotient_genericMatrix_eq_zero_of_raising_step
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n hn k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (i : Fin n) (a : Fin (dimension n)) (ha : basisWeight n a i = -1) :
    Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
      (GeneralLinear.genericMatrix k (dimension n) a (basisReflection n i a)) = 0 := by
  classical
  let H := GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
  let _ := GeneralLinear.corestrictStandardComodule k (dimension n) q
  -- Restrict the overgroup's standard representation to its separated torus weight lines.
  let π := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap n hn k (.inr ()))
    (((le_definingIdeal_iff n hn k J).mp hJ).2)
  have hπ : π.hom.comp q = GeneralLinear.weightTorusCoordinateBialgHom (S := k)
      (basisWeight n) := by
    calc
      π.hom.comp q = (generatorCoordinateMap n hn k (.inr ())).hom :=
        Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom J.toIdeal _
          (((le_definingIdeal_iff n hn k J).mp hJ).2)
      _ = GeneralLinear.weightTorusCoordinateBialgHom (S := k) (basisWeight n) := by
        rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hweights := GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    q π.hom (basisWeight n) hπ
  obtain ⟨m, bas, htri, _⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (M := Fin (dimension n) → k) hconn hsolv
  let F := Comodule.flagSubcomodule bas htri
  have hcoord (r : Fin (m + 1)) :
      (F r).toSubmodule = Submodule.span k ((Pi.basisFun k (Fin (dimension n))) ''
        {a | Pi.single a (1 : k) ∈ F r}) :=
    Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights π.hom.toCoalgHom
      (basisCharacter n) (basisCharacter_injective n) hweights (F r)
  have hbas (r : Fin (m + 1)) : bas.flag r = Submodule.span k
      ((Pi.basisFun k (Fin (dimension n))) ''
        {a | Pi.single a (1 : k) ∈ bas.flag r}) := by
    simpa only [F, Comodule.flagSubcomodule_toSubmodule,
      ← Subcomodule.mem_toSubmodule] using hcoord r
  -- Lie–Kolchin's flag is coordinatewise; a raising edge must point forward in that flag.
  have hne : a ≠ basisReflection n i a := by
    intro h
    have hzero := (basisReflection_eq_self_iff n i a).mp h.symm
    omega
  have hzero : Comodule.coefficientMatrix (C := H)
      (Pi.basisFun k (Fin (dimension n))) a (basisReflection n i a) = 0 := by
    apply Comodule.coefficient_eq_zero_of_coordinate_flag
      (Pi.basisFun k (Fin (dimension n))) bas htri
    · simpa only [Pi.basisFun_apply] using hbas
    · exact hne
    · intro N
      simpa only [Pi.basisFun_apply] using single_mem_of_raising_step n hn J hJ N i a ha
  have hcoeff : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin (dimension n))) =
      (GeneralLinear.genericMatrix k (dimension n)).map q := by
    let _ := GeneralLinear.standardComodule k (dimension n)
    rw [← GeneralLinear.coefficientMatrix_basisFun]
    exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k (Fin (dimension n))) q.toCoalgHom
  simpa only [hcoeff, Matrix.map_apply] using hzero

/-- Every negative numbered simple-root character has zero actual adjoint weight space in a
reduced connected solvable overgroup. This uses integral torus characters in every characteristic.
-/
theorem adjointWeightSpace_neg_simpleRoot_eq_bot
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n hn k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (π : (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin n →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) (basisWeight n)) (i : Fin n) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (-TypeDStd.rootGeneratorWeight n (.inl i))) = ⊥ := by
  refine HopfIdeal.adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom J
    (basisWeight n) π hπ _ fun a b hab ↦ ?_
  have hchars : basisWeight n a - basisWeight n b =
      -TypeDStd.rootGeneratorWeight n (.inl i) := by
    funext j
    simpa only [SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin n →₀ ℤ) ↦ Multiplicative.toAdd χ j) hab
  have hdiff : basisWeight n b - basisWeight n a =
      TypeDStd.rootGeneratorWeight n (.inl i) := by
    rw [← neg_sub, hchars, neg_neg]
  obtain ⟨ha, rfl⟩ := (basisWeight_sub_eq_rootGeneratorWeight_iff n hn i a b).mp hdiff
  exact quotient_genericMatrix_eq_zero_of_raising_step n hn J hJ hconn hsolv i a ha

omit [IsAlgClosed k] in
private theorem carrier_comap_le_definingIdeal
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n hn k))
    (hI : I ≤ carrierDefiningIdeal n hn k) :
    I.comapOfSurjective (generatedCoordinateMap n hn k).hom
      (generatedCoordinateMap_surjective n hn k) ≤ definingIdeal n hn k := by
  intro z hz
  have hzero := (mem_carrierDefiningIdeal n hn k _).mp
    (hI (HopfIdeal.mem_comapOfSurjective.mp hz))
  have hcomp := congrArg _root_.CommHopfAlgCat.Hom.hom
    (generatedCoordinateMap_comp_restriction n hn k)
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ z).mp
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using
    (BialgHom.congr_fun hcomp z).symm.trans hzero

/-- Inside the field-generated spin carrier, each reduced connected solvable overgroup of the
positive subgroup has zero adjoint weight space at every negative numbered simple root. -/
theorem carrierQuotient_adjointWeightSpace_neg_simpleRoot_eq_bot
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n hn k))
    (hI : I ≤ carrierDefiningIdeal n hn k)
    [IsReduced (generatedCoordinateHopfAlgebra n hn k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra n hn k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra n hn k) I))
    (π : (generatedCoordinateHopfAlgebra n hn k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin n →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift n hn k (.inr ())).hom) (i : Fin n) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (-TypeDStd.rootGeneratorWeight n (.inl i))) = ⊥ := by
  let J := I.comapOfSurjective (generatedCoordinateMap n hn k).hom
    (generatedCoordinateMap_surjective n hn k)
  let e := (generatedCoordinateMap n hn k).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective n hn k) I
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal) :=
    (_root_.CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff _ _ I).mpr inferInstance
  have htorus : (π.comp e.hom.hom).comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) (basisWeight n) := by
    rw [BialgHom.comp_assoc,
      _root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom,
      ← BialgHom.comp_assoc, hπ]
    have hgen := congrArg _root_.CommHopfAlgCat.Hom.hom
      (generatedCoordinateMap_comp_generatedCoordinateLift n hn k (.inr ()))
    simpa only [_root_.CommHopfAlgCat.hom_comp, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap] using hgen
  have hzero := adjointWeightSpace_neg_simpleRoot_eq_bot n hn J
    (carrier_comap_le_definingIdeal n hn I hI)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hconn)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hsolv) (π.comp e.hom.hom) htorus i
  rw [← CommHopfAlgCat.coe_ofIso e] at hzero
  exact (Derivation.adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv
    MulEquiv.ulift.symm (_root_.CommHopfAlgCat.ofIso e) π _).mp hzero

/-- In particular, every Borel candidate containing the positive spin subgroup has zero adjoint
weight space at each negative numbered simple root of its stored weight torus. -/
theorem borelCandidate_adjointWeightSpace_neg_simpleRoot_eq_bot
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n hn k))
    (hI : I ≤ carrierDefiningIdeal n hn k)
    (hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n hn k)) I)
    (π : (generatedCoordinateHopfAlgebra n hn k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin n →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift n hn k (.inr ())).hom) (i : Fin n) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (-TypeDStd.rootGeneratorWeight n (.inl i))) = ⊥ := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra n hn k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra n hn k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact carrierQuotient_adjointWeightSpace_neg_simpleRoot_eq_bot n hn I hI
    hB.geometricallyConnected hB.geometricallySolvable π hπ i

end

end TauCeti.TypeDSpinCarrier.Generated.Positive
