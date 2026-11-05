/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.StandardComodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Raising
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.StandardComodule

/-!
# Invariant subspaces of the positive tripled D₄ subgroup

The subcomodules of the positive generated subgroup's 24-dimensional representation over a
field are exactly the coordinate spans closed under its four raising operators. The integral
torus characters distinguish all twenty-four lines, including lines in different summands.
This describes the subspaces that can occur in flags invariant under the positive subgroup.

The coordinate-span criterion holds over every nontrivial commutative ring. Exhaustion of
subcomodules by coordinate spans requires a field, but neither algebraic closedness nor a
restriction on the characteristic. Invariance here is scheme-theoretic, not just invariance
under the points over the ground field. The generated subgroup is not identified with a
specialization of the integral toral closure or with the pinned simply connected group.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.

The argument adapts `TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.StandardComodule`,
using the tripled carrier's generated-root comparison and distinct torus characters.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.D4Tripled.Generated.Positive

open DynkinType

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the positive subgroup generated over the ground ring. -/
@[instance_reducible]
def standardComodule : Comodule R (coordinateHopfAlgebra R) (Fin 24 → R) :=
  GeneralLinear.corestrictStandardComodule R 24
    (generatedCoordinateMap R ≫ CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom

attribute [local instance] standardComodule

/-- The standard coefficients are the ambient matrix coordinates restricted to the positive
subgroup through the full generated carrier. -/
theorem coefficientMatrix_basisFun :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra R) (Pi.basisFun R (Fin 24)) =
      (GeneralLinear.genericMatrix R 24).map
        (generatedCoordinateMap R ≫ CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom := by
  let _ := GeneralLinear.standardComodule R 24
  rw [Comodule.coefficientMatrix_corestrict, GeneralLinear.coefficientMatrix_basisFun]
  ext a b
  simp only [Matrix.map_apply, BialgHom.toCoalgHom_apply]

/-- Restriction to the positive subgroup's weight torus gives its twenty-four character lines. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 24)) tripledCharacter := by
  have hchar : (fun a ↦ SplitTorus.weightCharacter (d4TripledWeight a)) = tripledCharacter := by
    funext a
    apply Multiplicative.toAdd.injective
    ext j
    simp [tripledCharacter]
  rw [← hchar]
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap R ≫ CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom
    (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom d4TripledWeight
  rw [← _root_.CommHopfAlgCat.hom_comp, Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr,
    generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inr,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- Every positive subcomodule is stable under each positive numbered root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R))
    (i : Fin 4) (t : Multiplicative R) {v : Fin 24 → R} (hv : v ∈ N) :
    ((rootSubgroupPoints (.inl i) R t : Matrix.GeneralLinearGroup (Fin 24) R) :
      Matrix (Fin 24) (Fin 24) R) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  let f := CommHopfAlgCat.commonKernelLift (generator R) (.inl i)
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 24
    (generatedCoordinateMap R ≫ CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom N
    (toConv (q.ofConv.comp f.hom.toAlgHom)) hv
  have hp : BialgHom.mapDomain
      (generatedCoordinateMap R ≫ CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom
      (toConv (q.ofConv.comp f.hom.toAlgHom)) =
      BialgHom.mapDomain (generatedCoordinateMap R).hom
        (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl (.inl i))).hom.toAlgHom)) := by
    have hcomp : (generatedCoordinateMap R ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal R)) ≫ f =
        generatedCoordinateMap R ≫ generatedCoordinateLift R (.inl (.inl i)) := by
      rw [Category.assoc, CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inl]
    apply WithConv.ext
    ext x
    simp only [BialgHom.mapDomain_apply_apply, AlgHom.comp_apply]
    exact congrArg (fun g ↦ q.ofConv (g.hom x)) hcomp
  rw [hp, pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    R (.inl i) (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- A subcomodule containing a coordinate vector also contains its next raising-step vector. -/
theorem single_reflection_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R))
    (i : Fin 4) (a : Fin 24) (ha : d4TripledWeight a i = -1)
    (hv : Pi.single a (1 : R) ∈ N) :
    Pi.single (d4TripledReflection i a) (1 : R) ∈ N := by
  have h := rootSubgroupPoints_mulVec_mem R N i (Multiplicative.ofAdd 1) hv
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, one_smul, raisingMatrix_def] at h
  simpa only [weightTable_reflection, Subcomodule.mem_toSubmodule] using
    weightTable.single_reflection_mem_of_mulVec_mem N.toSubmodule i a
      (by simpa only [weightTable_weight] using ha) hv h

variable {R}

private theorem stable_of_raising_closed (s : Set (Fin 24))
    (hs : ∀ i a, a ∈ s → d4TripledWeight a i = -1 → d4TripledReflection i a ∈ s) :
    (Pi.basisFun R (Fin 24)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s := by
  classical
  let w : Fin 24 → ℤ := fun a ↦ if a ∈ s then 1 else 0
  have hI : GeneralLinear.weightParabolicDefiningHopfIdeal R w ≤
      (definingIdeal R).comapOfSurjective (generatedCoordinateMap R).hom
        (generatedCoordinateMap_surjective R) := by
    rw [CommHopfAlgCat.comapOfSurjective_commonKernelHopfIdeal,
      CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
    rintro (i | ⟨⟩)
    · rw [generator_inl, generatedCoordinateMap_comp_generatedCoordinateLift]
      apply GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker
      intro a b hab
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have ha : a ∉ s := by
        intro ha
        by_cases hb : b ∈ s <;> simp [w, ha, hb] at hab
      have hb : b ∈ s := by
        by_contra hb
        simp [w, ha, hb] at hab
      let A := CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)
      let q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A :=
        toConv (AlgHom.id R _)
      have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 24) A ↦
        (g : Matrix (Fin 24) (Fin 24) A) a b)
        (pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
          R (.inl i) A q)
      rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear] at hm
      simp only [BialgHom.mapDomain_apply, ofConv_toConv, Matrix.map_apply,
        GeneralLinear.genericMatrix_apply, q, AlgHom.id_comp] at hm
      rw [← BialgHom.comp_toAlgHom, ← _root_.CommHopfAlgCat.hom_comp,
        generatedCoordinateMap_comp_generatedCoordinateLift] at hm
      rw [hm, coe_rootSubgroupPoints_inl, raisingMatrix_def]
      have hab' : a ≠ b := fun h ↦ ha (h ▸ hb)
      have hedge : ¬(d4TripledWeight b i = -1 ∧ a = d4TripledReflection i b) := by
        rintro ⟨hbi, rfl⟩
        exact ha (hs i b hb hbi)
      simp [Matrix.add_apply, hab', Matrix.smul_apply, Matrix.map_apply,
        weightTable_weight, weightTable_reflection, hedge]
    · rw [generator_inr, generatedCoordinateMap_comp_generatedCoordinateLift,
        generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
      exact
        GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker_weightTorusCoordinateBialgHom
          w d4TripledWeight
  rw [Module.Basis.coordinateSpanIsStable_iff]
  intro a ha b hb
  rw [coefficientMatrix_basisFun, Matrix.map_apply, GeneralLinear.genericMatrix_apply,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    CommHopfAlgCat.mkQuotient_eq_zero_iff]
  apply HopfIdeal.mem_comapOfSurjective.mp
  apply hI
  rw [← HopfIdeal.mem_toIdeal, GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal]
  exact Ideal.subset_span (GeneralLinear.X_mem_weightParabolicRelationSet R w (by simp [w, ha, hb]))

/-- A coordinate span is a subcomodule exactly when its indices are closed under raising steps.
This is a criterion for the universal coaction, including over finite coefficient rings. -/
theorem coordinateSpanIsStable_iff [Nontrivial R] (s : Set (Fin 24)) :
    (Pi.basisFun R (Fin 24)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s ↔
      ∀ i a, a ∈ s → d4TripledWeight a i = -1 → d4TripledReflection i a ∈ s := by
  classical
  refine ⟨fun h i a ha hia ↦ ?_, stable_of_raising_closed s⟩
  let N := (Pi.basisFun R (Fin 24)).coordinateSpanSubcomodule s h
  have hv : Pi.single a (1 : R) ∈ N := by
    rw [Module.Basis.mem_coordinateSpanSubcomodule]
    exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin 24) a⟩
  have hr := single_reflection_mem R N i a hia hv
  rw [Module.Basis.mem_coordinateSpanSubcomodule] at hr
  exact (Pi.basisFun R (Fin 24)).mem_span_image.mp hr (by simp)

variable (k : Type u) [Field k]

/-- Every positive invariant subspace is spanned by the coordinate lines it contains. -/
theorem toSubmodule_eq_span
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 24 → k)) :
    N.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin 24)) ''
      {a | Pi.single a (1 : k) ∈ N}) := by
  apply Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (CommHopfAlgCat.commonKernelLift (generator k) (.inr ())).hom.toCoalgHom
    tripledCharacter tripledCharacter_injective (torusCorestrict_eq_ofWeights k) N

/-- **Invariant-subspace classification for the positive tripled D₄ subgroup.** Subcomodules
are precisely the coordinate spans closed under all four positive simple-root operators. -/
theorem exists_subcomodule_iff (W : Submodule k (Fin 24 → k)) :
    (∃ N : Subcomodule k (coordinateHopfAlgebra k) (Fin 24 → k), N.toSubmodule = W) ↔
      ∃ s : Set (Fin 24),
        (∀ i a, a ∈ s → d4TripledWeight a i = -1 → d4TripledReflection i a ∈ s) ∧
        W = Submodule.span k ((Pi.basisFun k (Fin 24)) '' s) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨{a | Pi.single a (1 : k) ∈ N}, ?_, ?_⟩
    · intro i a ha hia
      exact single_reflection_mem k N i a hia ha
    · exact hN.symm.trans (toSubmodule_eq_span k N)
  · rintro ⟨s, hs, rfl⟩
    exact (Module.Basis.exists_subcomodule_toSubmodule_eq_span_iff_coordinateSpanIsStable
      (Pi.basisFun k (Fin 24)) s).mpr ((coordinateSpanIsStable_iff s).mpr hs)

end

end TauCeti.D4Tripled.Generated.Positive
