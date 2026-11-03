/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Positive.BorelCandidate
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight.Positive
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule.Quotient
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# Solvable overgroups of the positive doubled E₆ subgroup

Over an algebraically closed field, a reduced connected solvable closed subgroup of the
generated doubled minuscule carrier containing the positive subgroup satisfies universal
matrix-entry equations: entry `(a,b)`
vanishes whenever the difference of weights `μ b - μ a` is nonzero and in the positive root
cone. Consequently its adjoint weight spaces vanish at every nonzero negative-cone character,
including in characteristics two and three.

Lie--Kolchin supplies an invariant full flag. The weight torus makes each flag member a
coordinate span. Positive root elements propagate its coordinate lines along raising paths
in the first minuscule block and along reversed paths in the dual block, whose root coefficients
are negative. Entries between the two blocks already vanish in the full generated carrier.
The equations are in the coordinate algebra, not just equations on ground-field points.

These constraints apply in particular to every Borel candidate containing the positive subgroup.
They do not assert Borel maximality, equality with the specialized integral carrier, or an
identification with the pinned simply connected E₆ group.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§17 and 21.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The flag and adjoint-weight argument follows
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.SolvableOvergroup`, with reversed
raising paths and negative root coefficients on the contragredient summand.
-/

public section

open CategoryTheory WithConv
open TauCeti.DynkinType
open scoped Matrix TensorProduct

namespace TauCeti.E6DoubledMinuscule.Generated.Positive

universe u

noncomputable section

variable {k : Type u} [Field k]

local notation "μ" => matrixWeight
local notation "C₊" => posRootCone e6SimplyConnectedRootDatum e6SimplyConnectedBase

private theorem single_mem_of_raising_step
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 54))
    (hJ : J ≤ definingIdeal k) :
    let _ := GeneralLinear.corestrictStandardComodule k 54
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
    ∀ (N : Subcomodule k (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal)
        (Fin 54 → k)) (a : Fin 27 ⊕ Fin 27) (i : Fin 6),
      e6DoubledMinusculeWeight a i = -1 → Pi.single (matrixIndexEquiv a) (1 : k) ∈ N →
        Pi.single (matrixIndexEquiv (reflection i a)) (1 : k) ∈ N := by
  let _ := GeneralLinear.corestrictStandardComodule k 54
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
  dsimp only
  intro N a i hw ha
  let p := (AdditiveGroup.gaPointsMulEquiv (R := k) (A := k)).symm
    (Multiplicative.ofAdd (1 : k))
  have hmem := GeneralLinear.quotientStandardComodule_mulVec_mem k 54 J
    (generator k (.inl i))
    (by simpa only [generator_inl] using ((le_definingIdeal_iff k J).mp hJ).1 i) N p ha
  have hpoint : GeneralLinear.pointToGeneralLinear 54
      (toConv (p.ofConv.comp (generator k (.inl i)).hom.toAlgHom)) =
        (rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
          Matrix.GeneralLinearGroup (Fin 54) k) := by
    rw [generator_inl, ← generatedCoordinateMap_comp_generatedCoordinateLift]
    simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.mapDomain_apply,
      BialgHom.comp_toAlgHom, ofConv_toConv, AlgHom.comp_assoc, p,
      MulEquiv.apply_symm_apply] using
      pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
        k (.inl i) (CommAlgCat.of k k) p
  rw [hpoint] at hmem
  have hsub := N.toSubmodule.sub_mem hmem ha
  have hcalc :
      (((rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
          Matrix.GeneralLinearGroup (Fin 54) k) : Matrix (Fin 54) (Fin 54) k) *ᵥ
          Pi.single (matrixIndexEquiv a) 1) - Pi.single (matrixIndexEquiv a) 1 =
        (summandSign a : k) • Pi.single (matrixIndexEquiv (reflection i a)) 1 := by
    rw [coe_rootSubgroupPoints_eq_one_add_smul, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec]
    simp only [toAdd_ofAdd, one_smul, add_sub_cancel_left, Matrix.mulVec_single_one]
    ext b
    simp [Matrix.map_apply, rootIntMatrix_apply, matrixWeight_apply, hw, Pi.single_apply]
  rw [hcalc] at hsub
  cases a <;> simpa using hsub

private theorem single_mem_of_posRootCone
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 54))
    (hJ : J ≤ definingIdeal k) :
    let _ := GeneralLinear.corestrictStandardComodule k 54
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
    ∀ (N : Subcomodule k (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal)
        (Fin 54 → k)) {a b : Fin 54}, matrixSummand a = matrixSummand b →
      μ b - μ a ∈ C₊ → Pi.single a (1 : k) ∈ N → Pi.single b (1 : k) ∈ N := by
  let _ := GeneralLinear.corestrictStandardComodule k 54
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
  dsimp only
  intro N a b hblock hcone ha
  obtain ⟨a, rfl⟩ := matrixIndexEquiv.surjective a
  obtain ⟨b, rfl⟩ := matrixIndexEquiv.surjective b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hpath := (e6Minuscule_raisingPath_iff_mem_posRootCone a b).mpr
        (by simpa only [matrixWeight_apply, Equiv.symm_apply_apply,
          e6DoubledMinusculeWeight_inl] using hcone)
      have hforward : ∀ {a b : Fin 27}, Relation.ReflTransGen E6MinusculeRaisingStep a b →
          Pi.single (matrixIndexEquiv (.inl a)) (1 : k) ∈ N →
            Pi.single (matrixIndexEquiv (.inl b)) (1 : k) ∈ N := by
        intro a b h
        induction h with
        | refl => exact id
        | tail h hstep ih =>
          obtain ⟨i, hi, rfl⟩ := (e6MinusculeRaisingStep_iff _ _).mp hstep
          intro ha
          simpa only [reflection_inl] using single_mem_of_raising_step J hJ N (.inl _) i
            (by simpa only [e6DoubledMinusculeWeight_inl] using hi) (ih ha)
      exact hforward hpath ha
    | inr b => simp only [matrixSummand_inl, matrixSummand_inr, zero_ne_one] at hblock
  | inr a =>
    cases b with
    | inl b => simp only [matrixSummand_inl, matrixSummand_inr, one_ne_zero] at hblock
    | inr b =>
      have hpath := (e6Minuscule_raisingPath_iff_mem_posRootCone b a).mpr
        (by simpa only [matrixWeight_apply, Equiv.symm_apply_apply,
          e6DoubledMinusculeWeight_inr, neg_sub_neg] using hcone)
      -- A raising path on the dual is a reversed raising path on the original module.
      have hreverse : ∀ {b a : Fin 27}, Relation.ReflTransGen E6MinusculeRaisingStep b a →
          Pi.single (matrixIndexEquiv (.inr a)) (1 : k) ∈ N →
            Pi.single (matrixIndexEquiv (.inr b)) (1 : k) ∈ N := by
        intro b a h
        induction h with
        | refl => exact id
        | @tail c d h hstep ih =>
          obtain ⟨i, hi, rfl⟩ := (e6MinusculeRaisingStep_iff _ _).mp hstep
          intro hd
          apply ih
          have hw : e6DoubledMinusculeWeight (.inr (e6MinusculeReflection i c)) i = -1 := by
            simp [TauCeti.E6Minuscule.e6MinusculeWeight_reflection_apply_self, hi]
          simpa only [reflection_inr, e6MinusculeReflection_apply_apply] using
            single_mem_of_raising_step J hJ N (.inr (e6MinusculeReflection i c)) i hw hd
      exact hreverse hpath ha

variable [IsAlgClosed k]

/-- Every nonzero positive-cone difference forces a universal matrix-entry equation in a
reduced connected solvable overgroup of the positive subgroup inside the generated carrier,
here expressed as a closed subgroup of `GL₅₄`. -/
theorem quotient_genericMatrix_eq_zero_of_posRootCone
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 54))
    (hfull : generatedDefiningIdeal k ≤ J) (hJ : J ≤ definingIdeal k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 54) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 54) J))
    {a b : Fin 54} (hcone : μ b - μ a ∈ C₊) (hne : μ b - μ a ≠ 0) :
    Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
      (GeneralLinear.genericMatrix k 54 a b) = 0 := by
  classical
  -- Inside a block, Lie--Kolchin and raising paths force the entry to vanish.
  by_cases hblock : matrixSummand a = matrixSummand b
  · let H := GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal
    let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
    let _ := GeneralLinear.corestrictStandardComodule k 54 q
    let π := CommHopfAlgCat.liftQuotient J (generatorCoordinateMap k (.inr ()))
      (((le_definingIdeal_iff k J).mp hJ).2)
    have hπ : π.hom.comp q = GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ := by
      calc
        π.hom.comp q = (generatorCoordinateMap k (.inr ())).hom :=
          Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom J.toIdeal _
            (((le_definingIdeal_iff k J).mp hJ).2)
        _ = GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ := by
          rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    have hweights := GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights q π.hom μ hπ
    have hinj : Function.Injective (fun a ↦ SplitTorus.weightCharacter (μ a)) := by
      intro a b hab
      apply matrixIndexEquiv.symm.injective
      apply e6DoubledMinusculeWeight_injective
      funext i
      simpa only [SplitTorus.toAdd_weightCharacter, matrixWeight_apply] using
        congrArg (fun χ : Multiplicative (Fin 6 →₀ ℤ) ↦ Multiplicative.toAdd χ i) hab
    obtain ⟨n, bas, htri, _⟩ :=
      Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
        (M := Fin 54 → k) hconn hsolv
    let F := Comodule.flagSubcomodule bas htri
    have hbas (r : Fin (n + 1)) : bas.flag r = Submodule.span k
        ((Pi.basisFun k (Fin 54)) '' {a | Pi.single a (1 : k) ∈ bas.flag r}) := by
      simpa only [F, Comodule.flagSubcomodule_toSubmodule, ← Subcomodule.mem_toSubmodule] using
        Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights π.hom.toCoalgHom
          (fun a ↦ SplitTorus.weightCharacter (μ a)) hinj hweights (F r)
    have hab : a ≠ b := by
      rintro rfl
      exact hne (sub_self _)
    have hzero : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 54)) a b = 0 := by
      apply Comodule.coefficient_eq_zero_of_coordinate_flag (Pi.basisFun k (Fin 54)) bas htri
      · simpa only [Pi.basisFun_apply] using hbas
      · exact hab
      · intro N
        simpa only [Pi.basisFun_apply] using single_mem_of_posRootCone J hJ N hblock hcone
    have hcoeff : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 54)) =
        (GeneralLinear.genericMatrix k 54).map q := by
      let _ := GeneralLinear.standardComodule k 54
      rw [← GeneralLinear.coefficientMatrix_basisFun]
      exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k (Fin 54)) q.toCoalgHom
    simpa only [hcoeff, Matrix.map_apply] using hzero
  -- Between blocks, the equation is inherited from the full generated carrier.
  · apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr
    rw [GeneralLinear.genericMatrix_apply]
    apply hfull
    apply baseChangeDefiningIdeal_le_generatedDefiningIdeal k
    have hz := RingHom.mem_ker.mpr (coordinateMap_X_eq_zero k hblock)
    rwa [coordinateMap_ker] at hz

/-- Every nonzero negative-cone character has zero adjoint weight space in a reduced connected
solvable overgroup of the positive subgroup inside the generated doubled carrier. -/
theorem adjointWeightSpace_neg_eq_bot_of_posRootCone
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 54))
    (hfull : generatedDefiningIdeal k ≤ J) (hJ : J ≤ definingIdeal k)
    [IsReduced (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 54) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 54) J))
    (π : (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 6 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ)
    {δ : Fin 6 → ℤ} (hδ : δ ∈ C₊) (hne : δ ≠ 0) :
    Derivation.adjointWeightSpace π (SplitTorus.weightCharacter (-δ)) = ⊥ := by
  refine HopfIdeal.adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom J μ π hπ _
    fun a b hab ↦ ?_
  have hchars : μ a - μ b = -δ := by
    funext i
    simpa only [SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin 6 →₀ ℤ) ↦ Multiplicative.toAdd χ i) hab
  have hdiff : μ b - μ a = δ := by rw [← neg_sub, hchars, neg_neg]
  exact quotient_genericMatrix_eq_zero_of_posRootCone J hfull hJ hconn hsolv
    (hdiff ▸ hδ) (hdiff ▸ hne)

omit [IsAlgClosed k] in
private theorem carrier_comap_bounds
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k) :
    let J := I.comapOfSurjective (generatedCoordinateMap k).hom
      (generatedCoordinateMap_surjective k)
    generatedDefiningIdeal k ≤ J ∧ J ≤ definingIdeal k := by
  constructor
  · intro x hx
    apply HopfIdeal.mem_comapOfSurjective.mpr
    have hz : (generatedCoordinateMap k).hom x = 0 := RingHom.mem_ker.mp (by
      rw [generatedCoordinateMap_ker]
      exact hx)
    rw [hz]
    exact I.toIdeal.zero_mem
  · intro z hz
    have hzero := (mem_carrierDefiningIdeal k _).mp
      (hI (HopfIdeal.mem_comapOfSurjective.mp hz))
    have hcomp := congrArg _root_.CommHopfAlgCat.Hom.hom
      (generatedCoordinateMap_comp_restriction k)
    apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ z).mp
    simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using
      (BialgHom.congr_fun hcomp z).symm.trans hzero

/-- The positive-cone equations in the actual quotient coordinate algebra of a reduced
connected solvable overgroup inside the generated doubled E₆ carrier. -/
theorem carrierQuotient_genericMatrix_eq_zero_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    {a b : Fin 54} (hcone : μ b - μ a ∈ C₊) (hne : μ b - μ a ≠ 0) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap k).hom (GeneralLinear.genericMatrix k 54 a b)) = 0 := by
  let J := I.comapOfSurjective (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)
  let e := (generatedCoordinateMap k).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective k) I
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal) :=
    (_root_.CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff _ _ I).mpr inferInstance
  have hbounds := carrier_comap_bounds I hI
  have hzero := quotient_genericMatrix_eq_zero_of_posRootCone J hbounds.1 hbounds.2
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hconn)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hsolv) hcone hne
  have hz := BialgHom.congr_fun
    (_root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom
      (generatedCoordinateMap k) (generatedCoordinateMap_surjective k) I)
    (GeneralLinear.genericMatrix k 54 a b)
  simp only [BialgHom.comp_apply] at hz
  exact hz.symm.trans ((congrArg _ hzero).trans (map_zero _))

/-- Every nonzero negative-cone character of the stored weight torus has zero adjoint weight
space in a reduced connected solvable overgroup inside the generated doubled E₆ carrier. -/
theorem carrierQuotient_adjointWeightSpace_neg_eq_bot_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    [IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (π : (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (Fin 6 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift k (.inr ())).hom)
    {δ : Fin 6 → ℤ} (hδ : δ ∈ C₊) (hne : δ ≠ 0) :
    Derivation.adjointWeightSpace π (SplitTorus.weightCharacter (-δ)) = ⊥ := by
  let J := I.comapOfSurjective (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)
  let e := (generatedCoordinateMap k).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective k) I
  have : IsReduced (GeneralLinear.coordinateHopfAlgebra k 54 ⧸ J.toIdeal) :=
    (_root_.CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff _ _ I).mpr inferInstance
  have htorus : (π.comp e.hom.hom).comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := k) μ := by
    rw [BialgHom.comp_assoc,
      _root_.CommHopfAlgCat.Hom.hom_quotientIsoOfSurjective_hom_comp_mkBialgHom,
      ← BialgHom.comp_assoc, hπ]
    have hgen := congrArg _root_.CommHopfAlgCat.Hom.hom
      (generatedCoordinateMap_comp_generatedCoordinateLift k (.inr ()))
    simpa only [_root_.CommHopfAlgCat.hom_comp, generatorCoordinateMap_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap] using hgen
  have hbounds := carrier_comap_bounds I hI
  have hzero := adjointWeightSpace_neg_eq_bot_of_posRootCone J hbounds.1 hbounds.2
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hconn)
    ((ObjectProperty.prop_iff_of_iso _ e).mpr hsolv)
    (π.comp e.hom.hom) htorus hδ hne
  rw [← CommHopfAlgCat.coe_ofIso e] at hzero
  exact (Derivation.adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv
    MulEquiv.ulift.symm (_root_.CommHopfAlgCat.ofIso e) π _).mp hzero

/-- Every Borel candidate containing the generated positive subgroup satisfies the
positive-cone matrix-entry equations. -/
theorem borelCandidate_genericMatrix_eq_zero_of_posRootCone
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : I ≤ carrierDefiningIdeal k)
    (hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k)) I)
    {a b : Fin 54} (hcone : μ b - μ a ∈ C₊) (hne : μ b - μ a ≠ 0) :
    Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
      ((generatedCoordinateMap k).hom (GeneralLinear.genericMatrix k 54 a b)) = 0 := by
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
      MonoidAlgebra k (Multiplicative (Fin 6 →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) =
      (generatedCoordinateLift k (.inr ())).hom)
    {δ : Fin 6 → ℤ} (hδ : δ ∈ C₊) (hne : δ ≠ 0) :
    Derivation.adjointWeightSpace π (SplitTorus.weightCharacter (-δ)) = ⊥ := by
  let : Algebra.Smooth k (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hB.smooth
  let : IsReduced (generatedCoordinateHopfAlgebra k ⧸ I.toIdeal) := isReduced_of_smooth k _
  exact carrierQuotient_adjointWeightSpace_neg_eq_bot_of_posRootCone I hI
    hB.geometricallyConnected hB.geometricallySolvable π hπ hδ hne

end

end TauCeti.E6DoubledMinuscule.Generated.Positive
