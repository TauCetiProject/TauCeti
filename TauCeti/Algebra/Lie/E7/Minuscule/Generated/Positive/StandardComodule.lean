/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E7.Minuscule.WeightAction
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule.Quotient
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.StandardComodule
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# Invariant subspaces of the positive E₇ minuscule subgroup

The subcomodules of the generated positive subgroup's 56-dimensional representation over a
field are precisely the coordinate spans closed under the seven raising operators. Restriction
to the weight torus separates the coordinate lines, and the positive simple-root points move
these lines along the directed minuscule weight diagram. This characterizes the subspaces
that can occur in invariant flags containing the action of the positive subgroup.

The coordinate-span criterion works over every nontrivial commutative ring. The assertion
that every invariant subspace is a coordinate span uses a field, but needs neither algebraic
closure nor a restriction on the characteristic. No maximal-solvability or identification
with a pinned simply connected group scheme is asserted.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.

The construction follows
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.StandardComodule`, using the E₇ weight
and root matrices. Weight extraction uses
`Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.E7Minuscule.Generated.Positive

open DynkinType

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The standard representation of the positive subgroup generated over `R`. -/
@[instance_reducible]
def standardComodule : Comodule R (coordinateHopfAlgebra R) (Fin 56 → R) :=
  GeneralLinear.corestrictStandardComodule R 56
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom

attribute [local instance] standardComodule

/-- The coefficient matrix is the ambient generic matrix modulo the positive subgroup's ideal. -/
theorem coefficientMatrix_basisFun :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra R) (Pi.basisFun R (Fin 56)) =
      (GeneralLinear.genericMatrix R 56).map
        (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom := by
  let _ := GeneralLinear.standardComodule R 56
  rw [Comodule.coefficientMatrix_corestrict, GeneralLinear.coefficientMatrix_basisFun]
  ext a b
  simp only [Matrix.map_apply, BialgHom.toCoalgHom_apply]

/-- Restriction to the weight torus splits the standard representation into its minuscule lines. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 56)) minusculeCharacter := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom
    (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom e7MinusculeWeight
  rw [← CommHopfAlgCat.hom_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
    generator_inr, generatorCoordinateMap_inr,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- The ambient point of a positive root generator is its concrete minuscule root matrix. -/
theorem pointToGeneralLinear_comp_generator_inl_eq_rootSubgroupPoints
    (i : Fin 7) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    GeneralLinear.pointToGeneralLinear 56
        (toConv (q.ofConv.comp (generator R (.inl i)).hom.toAlgHom)) =
      (rootSubgroupPoints (.inl i) A (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 56) A) := by
  rw [generator_inl, generatorCoordinateMap_inl,
    ← coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap]
  have h :=
    pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
      R (.inl i) A q
  rw [BialgHom.mapDomain_apply, ofConv_toConv] at h
  simpa only [CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom, AlgHom.comp_assoc] using h

/-- Every positive subcomodule is stable under each raising-root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 56 → R))
    (i : Fin 7) (t : Multiplicative R) {v : Fin 56 → R} (hv : v ∈ N) :
    ((rootSubgroupPoints (.inl i) R t : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.quotientStandardComodule_mulVec_mem R 56
    (definingIdeal R) (generator R (.inl i))
    (by simpa only [generator_inl] using
      ((le_definingIdeal_iff R (definingIdeal R)).mp le_rfl).1 i) N q hv
  simpa only [
    pointToGeneralLinear_comp_generator_inl_eq_rootSubgroupPoints R i (CommAlgCat.of R R) q, q,
    MulEquiv.apply_symm_apply] using h

/-- A subcomodule containing a weight vector contains its reflection along any raising edge. -/
theorem single_reflection_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 56 → R))
    (i : Fin 7) (a : Fin 56) (ha : e7MinusculeWeight a i = -1)
    (hv : Pi.single a (1 : R) ∈ N) :
    Pi.single (e7MinusculeReflection i a) (1 : R) ∈ N := by
  have h := rootSubgroupPoints_mulVec_mem R N i (Multiplicative.ofAdd 1) hv
  simpa only [positiveRoot_mulVec_single_sub R i a ha, Subcomodule.mem_toSubmodule] using
    N.toSubmodule.sub_mem h hv

variable {R}

private theorem stable_of_raising_closed (s : Set (Fin 56))
    (hs : ∀ i a, a ∈ s → e7MinusculeWeight a i = -1 → e7MinusculeReflection i a ∈ s) :
    (Pi.basisFun R (Fin 56)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s := by
  classical
  let w : Fin 56 → ℤ := fun a ↦ if a ∈ s then 1 else 0
  refine GeneralLinear.coordinateSpanIsStable_of_weightParabolicDefiningHopfIdeal_le (w := w) ?_
    fun a ha b hb ↦ by simp [w, ha, hb]
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker
    intro a b hab
    have ha : a ∉ s := by
      intro ha
      by_cases hb : b ∈ s <;> simp [w, ha, hb] at hab
    have hb : b ∈ s := by
      by_contra hb
      simp [w, ha, hb] at hab
    let A := CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)
    let q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A :=
      toConv (AlgHom.id R _)
    have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 56) A ↦
      (g : Matrix (Fin 56) (Fin 56) A) a b)
      (pointToGeneralLinear_comp_generator_inl_eq_rootSubgroupPoints R i A q)
    rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear] at hm
    simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, q,
      AlgHom.id_comp, generator_inl] at hm
    rw [hm, coe_rootSubgroupPoints_inl]
    have hab' : a ≠ b := fun h ↦ ha (h ▸ hb)
    have hedge : ¬(e7MinusculeWeight b i = -1 ∧ a = e7MinusculeReflection i b) := by
      rintro ⟨hbi, rfl⟩
      exact ha (hs i b hb hbi)
    simp [Matrix.add_apply, hab', Matrix.smul_apply, Matrix.map_apply, raisingMatrix_apply, hedge]
  · rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    exact
      GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker_weightTorusCoordinateBialgHom
        w e7MinusculeWeight

/-- A coordinate span is invariant exactly when its weight indices are closed under raising.
This criterion uses the universal coaction, not just the action of rational points. -/
theorem coordinateSpanIsStable_iff [Nontrivial R] (s : Set (Fin 56)) :
    (Pi.basisFun R (Fin 56)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s ↔
      ∀ i a, a ∈ s → e7MinusculeWeight a i = -1 → e7MinusculeReflection i a ∈ s := by
  classical
  refine ⟨fun h i a ha hia ↦ ?_, stable_of_raising_closed s⟩
  let N := (Pi.basisFun R (Fin 56)).coordinateSpanSubcomodule s h
  have hv : Pi.single a (1 : R) ∈ N := by
    rw [Module.Basis.mem_coordinateSpanSubcomodule]
    exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin 56) a⟩
  have hr := single_reflection_mem R N i a hia hv
  rw [Module.Basis.mem_coordinateSpanSubcomodule] at hr
  exact (Pi.basisFun R (Fin 56)).mem_span_image.mp hr (by simp)

variable (k : Type u) [Field k]

/-- Every invariant subspace is the span of exactly the minuscule coordinate lines it contains. -/
theorem toSubmodule_eq_span
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k)) :
    N.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin 56)) ''
      {a | Pi.single a (1 : k) ∈ N}) := by
  apply Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (CommHopfAlgCat.commonKernelLift (generator k) (.inr ())).hom.toCoalgHom
    minusculeCharacter minusculeCharacter_injective (torusCorestrict_eq_ofWeights k) N

/-- **Invariant-subspace classification for the positive E₇ minuscule subgroup.** A subspace
is a subcomodule precisely when it is a coordinate span closed under all seven raising operators. -/
theorem exists_subcomodule_iff (W : Submodule k (Fin 56 → k)) :
    (∃ N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k), N.toSubmodule = W) ↔
      ∃ s : Set (Fin 56),
        (∀ i a, a ∈ s → e7MinusculeWeight a i = -1 → e7MinusculeReflection i a ∈ s) ∧
        W = Submodule.span k ((Pi.basisFun k (Fin 56)) '' s) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨{a | Pi.single a (1 : k) ∈ N}, ?_, ?_⟩
    · intro i a ha hia
      exact single_reflection_mem k N i a hia ha
    · exact hN.symm.trans (toSubmodule_eq_span k N)
  · rintro ⟨s, hs, rfl⟩
    exact (Module.Basis.exists_subcomodule_toSubmodule_eq_span_iff_coordinateSpanIsStable
      (Pi.basisFun k (Fin 56)) s).mpr ((coordinateSpanIsStable_iff s).mpr hs)

end

end TauCeti.E7Minuscule.Generated.Positive
