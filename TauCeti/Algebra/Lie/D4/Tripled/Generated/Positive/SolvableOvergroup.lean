/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.BorelCandidate
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Raising

/-!
# Solvable overgroups of the positive tripled D₄ subgroup

In a reduced connected solvable overgroup of the positive tripled subgroup, matrix entries
opposite a simple raising edge vanish in the coordinate algebra. Consequently its adjoint
representation has no negative simple-root weight. These are universal coordinate equations,
not just equations on field-valued points; the characters are integral, including in
characteristic two.

The argument restricts a Lie–Kolchin flag to the weight torus. Its twenty-four distinct
characters force each flag member to be a coordinate span, and the positive simple-root
subgroups force these spans to be closed under raising. This supplies restrictions on solvable
overgroups needed to recognize the positive subgroup as a Borel. Neither Borel maximality nor
agreement with the specialization of the integral carrier is asserted.

## Main results

* `quotient_genericMatrix_reflection_eq_zero`: universal vanishing opposite a raising edge.
* `quotient_adjointWeightSpace_neg_simple_eq_bot`: negative simple-root weight exclusion
  for reduced connected solvable overgroups.
* `borelCandidate_adjointWeightSpace_neg_simple_eq_bot`: the Borel-candidate specialization.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The flag argument follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.SolvableOvergroup`, using the tripled
minuscule weight table and the existing generated-carrier root-point comparison.
-/

public section

open CategoryTheory WithConv
open TauCeti.DynkinType
open scoped Matrix

namespace TauCeti.D4Tripled.Generated.Positive

universe u

noncomputable section

variable {k : Type u} [Field k]

private theorem tripledCharacter_injective :
    Function.Injective (fun a ↦ SplitTorus.weightCharacter (d4TripledWeight a)) := by
  intro a b h
  apply d4TripledWeight_injective
  funext i
  simpa only [SplitTorus.toAdd_weightCharacter] using
    congrArg (fun c : Multiplicative (Fin 4 →₀ ℤ) ↦ Multiplicative.toAdd c i) h

private theorem single_reflection_mem
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k)) (hI : I ≤ definingIdeal k) :
    let q := (CommHopfAlgCat.mkQuotient _ I).hom.comp (generatedCoordinateMap k).hom
    let _ := GeneralLinear.corestrictStandardComodule k 24 q
    ∀ (N : Subcomodule k (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) (Fin 24 → k))
      (i : Fin 4) (a : Fin 24), d4TripledWeight a i = -1 →
      Pi.single a (1 : k) ∈ N → Pi.single (d4TripledReflection i a) (1 : k) ∈ N := by
  let q := (CommHopfAlgCat.mkQuotient _ I).hom.comp (generatedCoordinateMap k).hom
  let _ := GeneralLinear.corestrictStandardComodule k 24 q
  dsimp only
  intro N i a ha hv
  let l := CommHopfAlgCat.liftQuotient I (generatedCoordinateLift k (.inl (.inl i)))
    (((le_definingIdeal_iff k I).mp hI).1 i)
  let p := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
    (Multiplicative.ofAdd (1 : k))
  have hl : l.hom.comp (CommHopfAlgCat.mkQuotient _ I).hom =
      (generatedCoordinateLift k (.inl (.inl i))).hom :=
    congrArg _root_.CommHopfAlgCat.Hom.hom
      (CommHopfAlgCat.mkQuotient_comp_liftQuotient I _ _)
  have hp : BialgHom.mapDomain q
      (toConv (p.ofConv.comp l.hom.toAlgHom)) =
      BialgHom.mapDomain (generatedCoordinateMap k).hom
        (toConv (p.ofConv.comp (generatedCoordinateLift k (.inl (.inl i))).hom.toAlgHom)) := by
    apply WithConv.ext
    ext z
    simpa only [BialgHom.mapDomain_apply_apply, ofConv_toConv, AlgHom.comp_apply,
      q, BialgHom.comp_apply, BialgHom.coe_toAlgHom] using
      congrArg (fun f ↦ p.ofConv (f ((generatedCoordinateMap k).hom z))) hl
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem k 24 q N
    (toConv (p.ofConv.comp l.hom.toAlgHom)) hv
  rw [hp, pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    k (.inl i) (CommAlgCat.of k k) p,
    MulEquiv.apply_symm_apply, coe_rootSubgroupPoints_inl, toAdd_ofAdd, one_smul,
    raisingMatrix_def] at h
  simpa only [weightTable_reflection, Subcomodule.mem_toSubmodule] using
    weightTable.single_reflection_mem_of_mulVec_mem N.toSubmodule i a
      (by simpa only [weightTable_weight] using ha) hv h

variable [IsAlgClosed k]

/-- In a reduced connected solvable overgroup of the positive subgroup, every matrix entry
opposite a simple raising edge vanishes universally. -/
theorem quotient_genericMatrix_reflection_eq_zero
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k)) (hI : I ≤ definingIdeal k)
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (i : Fin 4) (a : Fin 24) (ha : d4TripledWeight a i = -1) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap k).hom
        (GeneralLinear.genericMatrix k 24 a (d4TripledReflection i a))) = 0 := by
  classical
  -- Factor the stored torus through the overgroup and recover its distinct character lines.
  let H := generatedCoordinateHopfAlgebra k ⧸ I.toIdeal
  let q := (CommHopfAlgCat.mkQuotient _ I).hom.comp (generatedCoordinateMap k).hom
  let _ := GeneralLinear.corestrictStandardComodule k 24 q
  let π := CommHopfAlgCat.liftQuotient I (generatedCoordinateLift k (.inr ()))
    (((le_definingIdeal_iff k I).mp hI).2)
  have hπ : π.hom.comp q = GeneralLinear.weightTorusCoordinateBialgHom (S := k)
      d4TripledWeight := by
    rw [← BialgHom.comp_assoc]
    have hl : π.hom.comp (CommHopfAlgCat.mkQuotient _ I).hom =
        (generatedCoordinateLift k (.inr ())).hom :=
      congrArg _root_.CommHopfAlgCat.Hom.hom
        (CommHopfAlgCat.mkQuotient_comp_liftQuotient I
          (generatedCoordinateLift k (.inr ())) (((le_definingIdeal_iff k I).mp hI).2))
    rw [hl, ← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hweights := GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    q π.hom d4TripledWeight hπ
  -- Lie–Kolchin gives a full flag; torus restriction makes its members coordinate spans.
  obtain ⟨n, bas, htri, _⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (M := Fin 24 → k) hconn hsolv
  let F := Comodule.flagSubcomodule bas htri
  have hcoord (r : Fin (n + 1)) :=
    Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights π.hom.toCoalgHom
      (fun a ↦ SplitTorus.weightCharacter (d4TripledWeight a))
      tripledCharacter_injective hweights (F r)
  have hbas (r : Fin (n + 1)) : bas.flag r = Submodule.span k
      ((Pi.basisFun k (Fin 24)) '' {a | Pi.single a (1 : k) ∈ bas.flag r}) := by
    simpa only [F, Comodule.flagSubcomodule_toSubmodule, Pi.basisFun_apply,
      ← Subcomodule.mem_toSubmodule] using hcoord r
  have hne : a ≠ d4TripledReflection i a := by
    intro h
    have heq := congrArg (fun b ↦ d4TripledWeight b i) h
    rw [d4TripledWeight_reflection, ha] at heq
    norm_num [CartanMatrix.D_diag, ha] at heq
  -- Raising stability orders each edge in the flag, killing the opposite matrix coefficient.
  have hz : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 24))
      a (d4TripledReflection i a) = 0 := by
    apply Comodule.coefficient_eq_zero_of_coordinate_flag (Pi.basisFun k (Fin 24)) bas htri
    · simpa only [Pi.basisFun_apply] using hbas
    · exact hne
    · intro N
      simpa only [Pi.basisFun_apply] using single_reflection_mem I hI N i a ha
  have hcoeff : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 24)) =
      (GeneralLinear.genericMatrix k 24).map q := by
    let _ := GeneralLinear.standardComodule k 24
    rw [Comodule.coefficientMatrix_corestrict, GeneralLinear.coefficientMatrix_basisFun]
    ext a b
    simp only [Matrix.map_apply, BialgHom.toCoalgHom_apply]
  simpa only [hcoeff, Matrix.map_apply, q, BialgHom.comp_apply,
    CommHopfAlgCat.hom_mkQuotient] using hz

/-- A reduced connected solvable overgroup of the positive tripled subgroup has no negative
simple-root adjoint weight. The torus is the one induced by the stored generator. -/
theorem quotient_adjointWeightSpace_neg_simple_eq_bot
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k)) (hI : I ≤ definingIdeal k)
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (π : (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 4 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift k (.inr ())).hom) (i : Fin 4) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 (.inr i))) = ⊥ := by
  -- Present the overgroup as a quotient of GL₂₄ to use the tangent-matrix weight criterion.
  let J := I.comapOfSurjective (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)
  let e := (generatedCoordinateMap k).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective k) I
  have htorus : (π.comp e.hom.hom).comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) d4TripledWeight := by
    rw [BialgHom.comp_assoc,
      _root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom,
      ← BialgHom.comp_assoc, hπ, ← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hzero : Derivation.adjointWeightSpace (π.comp e.hom.hom)
      (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 (.inr i))) = ⊥ := by
    apply HopfIdeal.adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom
      J d4TripledWeight (π.comp e.hom.hom) htorus
    intro a b hab
    -- A difference equal to a negative simple root is the reverse of a raising edge.
    have hdiff : d4TripledWeight a - d4TripledWeight b =
        TypeDStd.rootGeneratorWeight 4 (.inr i) := by
      funext j
      simpa only [SplitTorus.toAdd_weightCharacter] using
        congrArg (fun c : Multiplicative (Fin 4 →₀ ℤ) ↦ Multiplicative.toAdd c j) hab
    have ha : d4TripledWeight a i = -1 := by
      have hd := congrFun hdiff i
      have hwa := d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i
      have hwb := d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i
      simp only [Pi.sub_apply, TypeDStd.rootGeneratorWeight_inr, CartanMatrix.D_diag] at hd
      omega
    have hb : b = d4TripledReflection i a := by
      apply d4TripledWeight_injective
      rw [d4TripledWeight_reflection, ha]
      ext j
      have hd := congrFun hdiff j
      simp only [Pi.sub_apply, TypeDStd.rootGeneratorWeight_inr] at hd
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      omega
    have hz := quotient_genericMatrix_reflection_eq_zero I hI hconn hsolv i a ha
    rw [← hb] at hz
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    have he := BialgHom.congr_fun
      (_root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom
        (generatedCoordinateMap k) (generatedCoordinateMap_surjective k) I)
      (GeneralLinear.genericMatrix k 24 a b)
    simpa only [BialgHom.comp_apply, map_zero] using he.trans hz
  -- Return from the ambient quotient presentation to the actual overgroup's adjoint comodule.
  rw [← CommHopfAlgCat.coe_ofIso e] at hzero
  exact (Derivation.adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv
    MulEquiv.ulift.symm (_root_.CommHopfAlgCat.ofIso e) π _).mp hzero

/-- Every Borel candidate containing the positive tripled subgroup has zero adjoint weight
space at each negative simple root, with respect to its induced weight torus. -/
theorem borelCandidate_adjointWeightSpace_neg_simple_eq_bot
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k)) (hI : I ≤ definingIdeal k)
    (hB : HopfIdeal.IsBorelCandidate k (generatedFiniteTypeCoordinateHopfAlgebra k) I)
    (π : (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 4 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift k (.inr ())).hom) (i : Fin 4) :
    Derivation.adjointWeightSpace π
      (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 (.inr i))) = ⊥ := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact quotient_adjointWeightSpace_neg_simple_eq_bot I hI
    hB.geometricallyConnected hB.geometricallySolvable π hπ i

end

end TauCeti.D4Tripled.Generated.Positive
