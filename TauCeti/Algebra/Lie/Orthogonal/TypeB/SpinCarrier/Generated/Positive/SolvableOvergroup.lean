/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.BorelCandidate
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SolvableOvergroup
import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule.Quotient

/-!
# Negative simple weights in solvable overgroups of the positive spin subgroup

Over an algebraically closed field, every reduced connected solvable overgroup of the generated
positive type-B spin subgroup satisfies the matrix-entry equations opposite to nontrivial chains
of simple raising steps. Consequently its adjoint representation has zero weight space at each
negative simple root, for the specified spin weight torus. These are integral characters, not Lie
weights reduced modulo the characteristic; the conclusions include characteristic two.

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
  apply single_basisReflection_mem_of_rootSubgroupPoints n k N.toSubmodule i a _ hi ha
  intro w hw
  let p := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
    (Multiplicative.ofAdd (1 : k))
  have hmem := GeneralLinear.quotientStandardComodule_mulVec_mem k (dimension n) J
    (generatorCoordinateMap n k (.inl (.inl i)))
    (((le_definingIdeal_iff n k J).mp hJ).1 i) N p hw
  rw [← generator_inl] at hmem
  rwa [rootPoint_matrix, MulEquiv.apply_symm_apply] at hmem

variable [IsAlgClosed k]

/-- Opposite to every nontrivial chain of simple raising steps, a reduced geometrically
connected solvable overgroup of the positive spin subgroup has a zero universal matrix entry. -/
theorem quotient_genericMatrix_eq_zero_of_raisingPath
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (dimension n)))
    (hJ : J ≤ definingIdeal n k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (dimension n)) J))
    {a b : Fin (dimension n)}
    (hpath : Relation.ReflTransGen (fun a b ↦ ∃ i : Fin (n + 1),
      basisWeight n b - basisWeight n a = rootGeneratorWeight n (.inl i)) a b)
    (hne : a ≠ b) :
    Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
      (GeneralLinear.genericMatrix k (dimension n) a b) = 0 := by
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
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
  exact GeneralLinear.quotient_genericMatrix_eq_zero_of_single_mem J hconn hsolv
    (basisWeight n) π.hom hπ (basisCharacter_injective n) hne fun N ↦ by
      clear hne
      induction hpath with
      | refl => exact id
      | @tail b c hpath hstep ih =>
        obtain ⟨i, hi⟩ := hstep
        obtain ⟨hneg, href⟩ := basisReflection_eq_of_weight_sub n i hi
        exact fun ha ↦ by
          simpa only [href] using single_mem_of_raising_step n J hJ N i b hneg (ih ha)

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
  have hchars : basisWeight n a - basisWeight n b = -rootGeneratorWeight n (.inl i) := by
    funext j
    simpa only [SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin (n + 1) →₀ ℤ) ↦ Multiplicative.toAdd χ j) hab
  have hdiff : basisWeight n b - basisWeight n a = rootGeneratorWeight n (.inl i) := by
    rw [← neg_sub, hchars, neg_neg]
  apply quotient_genericMatrix_eq_zero_of_raisingPath n J hJ hconn hsolv
    (Relation.ReflTransGen.single ⟨i, hdiff⟩)
  intro heq
  have hi := congrFun hdiff i
  simp only [heq, sub_self, Pi.zero_apply, rootGeneratorWeight_inl,
    CartanMatrix.B_diag] at hi
  omega

/-- The raising-path equations hold in the actual quotient coordinate algebra of a
reduced connected solvable overgroup inside the field-generated spin carrier. -/
theorem carrierQuotient_genericMatrix_eq_zero_of_raisingPath
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n k))
    (hI : I ≤ carrierDefiningIdeal n k)
    [IsReduced (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra n k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra n k) I))
    {a b : Fin (dimension n)}
    (hpath : Relation.ReflTransGen (fun a b ↦ ∃ i : Fin (n + 1),
      basisWeight n b - basisWeight n a = rootGeneratorWeight n (.inl i)) a b)
    (hne : a ≠ b) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap n k).hom
        (GeneralLinear.genericMatrix k (dimension n) a b)) = 0 := by
  let J := I.comapOfSurjective (generatedCoordinateMap n k).hom
    (generatedCoordinateMap_surjective n k)
  let e := (generatedCoordinateMap n k).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective n k) I
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k (dimension n) ⧸ J.toIdeal) :=
    (_root_.CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff _ _ I).mpr inferInstance
  have hzero := quotient_genericMatrix_eq_zero_of_raisingPath n J
    (carrier_comap_le_definingIdeal n k I hI)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hconn)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hsolv) hpath hne
  have hz := BialgHom.congr_fun
    (_root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom
      (generatedCoordinateMap n k) (generatedCoordinateMap_surjective n k) I)
    (GeneralLinear.genericMatrix k (dimension n) a b)
  simp only [BialgHom.comp_apply] at hz
  exact hz.symm.trans ((congrArg _ hzero).trans (map_zero _))

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
    (carrier_comap_le_definingIdeal n k I hI)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hconn)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hsolv) (π.comp e.hom.hom) htorus i
  rw [← CommHopfAlgCat.coe_ofIso e] at hzero
  exact (Derivation.adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv
    MulEquiv.ulift.symm (_root_.CommHopfAlgCat.ofIso e) π _).mp hzero

/-- A Borel candidate containing the positive spin subgroup satisfies the universal matrix-entry
equations opposite every nontrivial chain of simple raising edges. -/
theorem borelCandidate_genericMatrix_eq_zero_of_raisingPath
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra n k))
    (hI : I ≤ carrierDefiningIdeal n k)
    (hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n k)) I)
    {a b : Fin (dimension n)}
    (hpath : Relation.ReflTransGen (fun a b ↦ ∃ i : Fin (n + 1),
      basisWeight n b - basisWeight n a = rootGeneratorWeight n (.inl i)) a b)
    (hne : a ≠ b) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap n k).hom
        (GeneralLinear.genericMatrix k (dimension n) a b)) = 0 := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra n k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact carrierQuotient_genericMatrix_eq_zero_of_raisingPath n I hI
    hB.geometricallyConnected hB.geometricallySolvable hpath hne

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
