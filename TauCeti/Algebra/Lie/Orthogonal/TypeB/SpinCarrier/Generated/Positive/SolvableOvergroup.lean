/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.BorelCandidate
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule.Quotient

/-!
# Negative simple weights in solvable overgroups of the positive spin subgroup

Over an algebraically closed field, every reduced connected solvable overgroup of the generated
positive type-B spin subgroup satisfies the matrix-entry equations opposite to simple raising
steps. Consequently its adjoint representation has zero weight space at each negative simple
root, for the specified spin weight torus. These are integral characters, not Lie weights reduced
modulo the characteristic; the conclusions include characteristic two.

The results apply both in the ambient general linear group and inside the field-generated spin
carrier, and in particular to Borel candidates containing its positive subgroup. They do not
assert Borel maximality, exclusion of all negative roots, or agreement of this carrier with an
independently pinned simply connected group scheme.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 26–28.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The coordinate-flag argument is adapted from
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.SolvableOvergroup`. The spin raising
coefficients are the units supplied by
`TypeBSpinCarrier.exists_rep_rootGenerator_inl_exteriorBasis`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.TypeBSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) {k : Type u} [Field k]

private theorem rootPoint_matrix (i : Fin (n + 1))
    (p : HopfAlgebra.points (R := k) (H := AdditiveGroup.coordinateHopfAlgebra k)
      (CommAlgCat.of k k)) :
    GeneralLinear.pointToGeneralLinear (dimension n)
        (toConv (p.ofConv.comp (generatorCoordinateMap n k (.inl (.inl i))).hom.toAlgHom)) =
      (rootSubgroupPoints n (.inl i) k (AdditiveGroup.gaPointsMulEquiv p) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) k) := by
  have h := pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    n k (.inl i) p
  rw [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc] at h
  have hcomp := congrArg _root_.CommHopfAlgCat.Hom.hom
    (generatedCoordinateMap_comp_generatedCoordinateLift n k (.inl (.inl i)))
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom] using hcomp ▸ h

private theorem single_mem_of_raising_step
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n k) :
    let _ := GeneralLinear.corestrictStandardComodule k (dimension n)
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
    ∀ (N : Subcomodule k (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)
        (Fin (dimension n) → k)) (i : Fin (n + 1)) (a : Fin (dimension n)),
      basisWeight n a i = -1 → Pi.single a (1 : k) ∈ N →
        Pi.single (basisReflection n i a) (1 : k) ∈ N := by
  let _ := GeneralLinear.corestrictStandardComodule k (dimension n)
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
  dsimp only
  intro N i a hi ha
  obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inl_exteriorBasis n i _ _ hi
    (signSet_basisReflection n i a).symm
  rw [← coe_latticeBasis, ← coe_latticeBasis] at hc
  apply single_mem_of_rep_rootGenerator_eq n k N.toSubmodule (.inl i) (c := c) _ hc ha
  intro w hw
  let p := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
    (Multiplicative.ofAdd (1 : k))
  have hmem := GeneralLinear.quotientStandardComodule_mulVec_mem k (dimension n) J
    (generatorCoordinateMap n k (.inl (.inl i)))
    (((le_definingIdeal_iff n k J).mp hJ).1 i) N p hw
  rwa [rootPoint_matrix, MulEquiv.apply_symm_apply] at hmem

private theorem basisReflection_eq_of_weight_sub
    (i : Fin (n + 1)) {a b : Fin (dimension n)}
    (hab : basisWeight n b - basisWeight n a = rootGeneratorWeight n (.inl i)) :
    basisWeight n a i = -1 ∧ basisReflection n i a = b := by
  have hi := congrFun hab i
  rw [Pi.sub_apply, rootGeneratorWeight_inl, CartanMatrix.B_diag] at hi
  have ha : basisWeight n a i = -1 ∨ basisWeight n a i = 0 ∨ basisWeight n a i = 1 :=
    DynkinType.typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n a) i
  have hb : basisWeight n b i = -1 ∨ basisWeight n b i = 0 ∨ basisWeight n b i = 1 :=
    DynkinType.typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n b) i
  have hneg : basisWeight n a i = -1 := by rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;> omega
  refine ⟨hneg, basisCharacter_injective n ?_⟩
  apply congrArg SplitTorus.weightCharacter
  funext j
  have hj := congrFun hab j
  rw [Pi.sub_apply, rootGeneratorWeight_inl] at hj
  simp only [basisWeight, signSet_basisReflection,
    DynkinType.typeBSpinWeight_typeBSpinReflection_apply]
  simp only [basisWeight] at hneg
  rw [hneg]
  linarith

variable [IsAlgClosed k]

/-- Opposite to each simple raising step, a reduced geometrically connected solvable overgroup
of the positive spin subgroup has a zero universal matrix entry. -/
theorem quotient_genericMatrix_eq_zero_of_simpleRoot
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (i : Fin (n + 1)) {a b : Fin (dimension n)}
    (hab : basisWeight n b - basisWeight n a = rootGeneratorWeight n (.inl i)) :
    Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
      (GeneralLinear.genericMatrix k (dimension n) a b) = 0 := by
  classical
  let H := GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
  let _ := GeneralLinear.corestrictStandardComodule k (dimension n) q
  let π := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap n k (.inr ()))
    (((le_definingIdeal_iff n k J).mp hJ).2)
  have hπ : π.hom.comp q = GeneralLinear.weightTorusCoordinateBialgHom (S := k)
      (basisWeight n) := by
    calc
      π.hom.comp q = (generatorCoordinateMap n k (.inr ())).hom :=
        Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom J.toIdeal _
          (((le_definingIdeal_iff n k J).mp hJ).2)
      _ = GeneralLinear.weightTorusCoordinateBialgHom (S := k) (basisWeight n) := by
        rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hweights := GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights q π.hom
    (basisWeight n) hπ
  -- Lie–Kolchin supplies a stable flag; the distinct torus characters make it coordinate.
  obtain ⟨d, bas, htri, _⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (M := Fin (dimension n) → k) hconn hsolv
  let F := Comodule.flagSubcomodule bas htri
  have hbas (r : Fin (d + 1)) : bas.flag r = Submodule.span k
      ((Pi.basisFun k (Fin (dimension n))) '' {a | Pi.single a (1 : k) ∈ bas.flag r}) := by
    have hcoord := Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights π.hom.toCoalgHom
      (basisCharacter n) (basisCharacter_injective n) hweights (F r)
    simpa only [F, Comodule.flagSubcomodule_toSubmodule,
      ← Subcomodule.mem_toSubmodule] using hcoord
  -- A unit raising coefficient propagates membership in each flag term, forcing the reverse
  -- matrix coefficient to vanish. No division by two is involved.
  obtain ⟨hneg, href⟩ := basisReflection_eq_of_weight_sub n i hab
  have hne : a ≠ b := by
    intro heq
    have := congrArg (fun z ↦ basisWeight n z i) heq
    have hi := congrFun hab i
    rw [Pi.sub_apply, rootGeneratorWeight_inl, CartanMatrix.B_diag] at hi
    omega
  have hzero : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin (dimension n))) a b =
      0 := by
    apply Comodule.coefficient_eq_zero_of_coordinate_flag (Pi.basisFun k _) bas htri
    · simpa only [Pi.basisFun_apply] using hbas
    · exact hne
    · intro N
      simpa only [Pi.basisFun_apply, href] using
        single_mem_of_raising_step n J hJ N i a hneg
  have hcoeff : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin (dimension n))) =
      (GeneralLinear.genericMatrix k (dimension n)).map q := by
    let _ := GeneralLinear.standardComodule k (dimension n)
    rw [← GeneralLinear.coefficientMatrix_basisFun]
    exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k _) q.toCoalgHom
  simpa only [hcoeff, Matrix.map_apply] using hzero

/-- The actual adjoint torus representation of a reduced connected solvable overgroup has no
negative simple-root weight, including in characteristic two. -/
theorem adjointWeightSpace_neg_simpleRoot_eq_bot
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (π : (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin (n + 1) →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) (basisWeight n))
    (i : Fin (n + 1)) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (-rootGeneratorWeight n (.inl i))) = ⊥ := by
  refine HopfIdeal.adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom J
    (basisWeight n) π hπ _ fun a b hab ↦ ?_
  apply quotient_genericMatrix_eq_zero_of_simpleRoot n J hJ hconn hsolv i
  have hchars : basisWeight n a - basisWeight n b = -rootGeneratorWeight n (.inl i) := by
    funext j
    simpa only [SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin (n + 1) →₀ ℤ) ↦ Multiplicative.toAdd χ j) hab
  rw [← neg_sub, hchars, neg_neg]

omit [IsAlgClosed k] in
private theorem carrier_comap_le_definingIdeal
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n k))
    (hI : I ≤ carrierDefiningIdeal n k) :
    I.comapOfSurjective (generatedCoordinateMap n k).hom
      (generatedCoordinateMap_surjective n k) ≤ definingIdeal n k := by
  intro z hz
  have hzero := (mem_carrierDefiningIdeal n k _).mp
    (hI (HopfIdeal.mem_comapOfSurjective.mp hz))
  have hcomp := congrArg _root_.CommHopfAlgCat.Hom.hom
    (generatedCoordinateMap_comp_restriction n k)
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ z).mp
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using
    (BialgHom.congr_fun hcomp z).symm.trans hzero

/-- Inside the field-generated spin carrier, every reduced connected solvable overgroup of the
positive subgroup has zero adjoint weight space at each negative simple-root character of the
stored weight torus. -/
theorem carrierQuotient_adjointWeightSpace_neg_simpleRoot_eq_bot
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n k))
    (hI : I ≤ carrierDefiningIdeal n k)
    [IsReduced (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra n k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra n k) I))
    (π : (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin (n + 1) →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift n k (.inr ())).hom)
    (i : Fin (n + 1)) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (-rootGeneratorWeight n (.inl i))) = ⊥ := by
  let J := I.comapOfSurjective (generatedCoordinateMap n k).hom
    (generatedCoordinateMap_surjective n k)
  let e := (generatedCoordinateMap n k).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective n k) I
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal) :=
    (_root_.CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff _ _ I).mpr inferInstance
  have htorus : (π.comp e.hom.hom).comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) (basisWeight n) := by
    rw [BialgHom.comp_assoc,
      _root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom,
      ← BialgHom.comp_assoc, hπ]
    have hgen := congrArg _root_.CommHopfAlgCat.Hom.hom
      (generatedCoordinateMap_comp_generatedCoordinateLift n k (.inr ()))
    simpa only [_root_.CommHopfAlgCat.hom_comp, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap] using hgen
  have hzero := adjointWeightSpace_neg_simpleRoot_eq_bot n J
    (carrier_comap_le_definingIdeal n I hI)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hconn)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hsolv) (π.comp e.hom.hom) htorus i
  rw [← CommHopfAlgCat.coe_ofIso e] at hzero
  exact (Derivation.adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv
    MulEquiv.ulift.symm (_root_.CommHopfAlgCat.ofIso e) π _).mp hzero

/-- In particular, a Borel candidate containing the positive spin subgroup has no negative
simple-root adjoint weight for the specified weight torus. -/
theorem borelCandidate_adjointWeightSpace_neg_simpleRoot_eq_bot
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n k))
    (hI : I ≤ carrierDefiningIdeal n k)
    (hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n k)) I)
    (π : (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin (n + 1) →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift n k (.inr ())).hom)
    (i : Fin (n + 1)) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (-rootGeneratorWeight n (.inl i))) = ⊥ := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact carrierQuotient_adjointWeightSpace_neg_simpleRoot_eq_bot n I hI
    hB.geometricallyConnected hB.geometricallySolvable π hπ i

end

end TauCeti.TypeBSpinCarrier.Generated.Positive
