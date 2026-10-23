/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.StandardComodule

/-!
# Invariant subspaces of the positive E₆ minuscule subgroup

The subcomodules of the positive subgroup's 27-dimensional representation over a field
are precisely the coordinate spans closed under the six raising operators. The weight torus
separates the coordinate lines, while a raising operator sends a weight vector at a negative
simple-root coordinate to its reflected weight vector. This classification is the flag
input for testing maximality of the positive subgroup among connected solvable subgroups.

The coordinate-span criterion works over every nontrivial commutative ring. The assertion
that every invariant subspace is a coordinate span uses a field. No algebraic closure or
restriction on the characteristic is needed.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.

Weight extraction uses `Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights`;
the standard-comodule and root-point constructions follow the full generated E₆ carrier.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.E6Minuscule.Generated.Positive

open DynkinType

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The standard representation of the positive subgroup generated over `R`. -/
@[instance_reducible]
def standardComodule : Comodule R (coordinateHopfAlgebra R) (Fin 27 → R) :=
  GeneralLinear.corestrictStandardComodule R 27
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom

attribute [local instance] standardComodule

/-- The coefficient matrix is the ambient generic matrix modulo the positive subgroup's ideal. -/
theorem coefficientMatrix_basisFun :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra R) (Pi.basisFun R (Fin 27)) =
      (GeneralLinear.genericMatrix R 27).map
        (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom := by
  let _ := GeneralLinear.standardComodule R 27
  rw [Comodule.coefficientMatrix_corestrict, GeneralLinear.coefficientMatrix_basisFun]
  ext a b
  simp only [Matrix.map_apply, BialgHom.toCoalgHom_apply]

/-- Restriction to the weight torus splits the standard representation into its minuscule lines. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 27)) minusculeCharacter := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom
    (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom e6MinusculeWeight
  rw [← CommHopfAlgCat.hom_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
    generator_inr, generatorCoordinateMap_inr,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap, weightTable_weight]

private theorem rootPoint_matrix (i : Fin 6) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    GeneralLinear.pointToGeneralLinear 27
        (toConv (q.ofConv.comp (generator R (.inl i)).hom.toAlgHom)) =
      (rootSubgroupPoints (.inl i) A (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 27) A) := by
  rw [generator_inl, generatorCoordinateMap_inl,
    ← coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap]
  simpa only [BialgHom.mapDomain_apply, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    AlgHom.comp_assoc] using
    pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
      R (.inl i) A q

/-- Every positive subcomodule is stable under each raising-root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 27 → R))
    (i : Fin 6) (t : Multiplicative R) {v : Fin 27 → R} (hv : v ∈ N) :
    ((rootSubgroupPoints (.inl i) R t : Matrix.GeneralLinearGroup (Fin 27) R) :
      Matrix (Fin 27) (Fin 27) R) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  let f := CommHopfAlgCat.commonKernelLift (generator R) (.inl i)
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 27
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom N
    (toConv (q.ofConv.comp f.hom.toAlgHom)) hv
  have hcomp : BialgHom.mapDomain (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom
      (toConv (q.ofConv.comp f.hom.toAlgHom)) =
      toConv (q.ofConv.comp (generator R (.inl i)).hom.toAlgHom) := by
    apply WithConv.ext
    ext x
    simp only [BialgHom.mapDomain_apply_apply, AlgHom.comp_apply]
    exact congrArg (fun g ↦ q.ofConv (g.hom x))
      (CommHopfAlgCat.mkQuotient_comp_commonKernelLift (generator R) (.inl i))
  rw [hcomp, rootPoint_matrix R i (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- A subcomodule containing a weight vector contains every vector obtained by one raising step. -/
theorem single_reflection_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 27 → R))
    (i : Fin 6) (a : Fin 27) (ha : e6MinusculeWeight a i = -1)
    (hv : Pi.single a (1 : R) ∈ N) :
    Pi.single (e6MinusculeReflection i a) (1 : R) ∈ N := by
  have h := rootSubgroupPoints_mulVec_mem R N i (Multiplicative.ofAdd 1) hv
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, one_smul, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_single_one, weightTable.raisingMatrix_map_col] at h
  rw [← Subcomodule.mem_toSubmodule]
  simpa only [weightTable_weight, weightTable_reflection, ha, ↓reduceIte,
    add_sub_cancel_left] using N.toSubmodule.sub_mem h hv

variable {R}

private theorem stable_of_raising_closed (s : Set (Fin 27))
    (hs : ∀ i a, a ∈ s → e6MinusculeWeight a i = -1 → e6MinusculeReflection i a ∈ s) :
    (Pi.basisFun R (Fin 27)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s := by
  classical
  let w : Fin 27 → ℤ := fun a ↦ if a ∈ s then 1 else 0
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
    have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 27) A ↦
      (g : Matrix (Fin 27) (Fin 27) A) a b) (rootPoint_matrix R i A q)
    rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear] at hm
    simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, q,
      AlgHom.id_comp, generator_inl] at hm
    rw [hm, coe_rootSubgroupPoints_inl]
    have hab' : a ≠ b := fun h ↦ ha (h ▸ hb)
    have hedge : ¬(e6MinusculeWeight b i = -1 ∧ a = e6MinusculeReflection i b) := by
      rintro ⟨hbi, rfl⟩
      exact ha (hs i b hb hbi)
    simp [Matrix.add_apply, hab', Matrix.smul_apply, Matrix.map_apply, hedge]
  · rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    exact
      GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker_weightTorusCoordinateBialgHom
        w weightTable.weight

/-- A coordinate span is invariant exactly when its weight indices are closed under raising.
This criterion uses the universal coaction, rather than just the action of rational points. -/
theorem coordinateSpanIsStable_iff [Nontrivial R] (s : Set (Fin 27)) :
    (Pi.basisFun R (Fin 27)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s ↔
      ∀ i a, a ∈ s → e6MinusculeWeight a i = -1 → e6MinusculeReflection i a ∈ s := by
  classical
  refine ⟨fun h i a ha hia ↦ ?_, stable_of_raising_closed s⟩
  let N := (Pi.basisFun R (Fin 27)).coordinateSpanSubcomodule s h
  have hv : Pi.single a (1 : R) ∈ N := by
    rw [Module.Basis.mem_coordinateSpanSubcomodule]
    exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin 27) a⟩
  have hr := single_reflection_mem R N i a hia hv
  rw [Module.Basis.mem_coordinateSpanSubcomodule] at hr
  exact (Pi.basisFun R (Fin 27)).mem_span_image.mp hr (by simp)

variable (k : Type u) [Field k]

/-- Every invariant subspace is the span of exactly those minuscule coordinate lines it contains. -/
theorem toSubmodule_eq_span
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 27 → k)) :
    N.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin 27)) ''
      {a | Pi.single a (1 : k) ∈ N}) := by
  apply Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (CommHopfAlgCat.commonKernelLift (generator k) (.inr ())).hom.toCoalgHom
    minusculeCharacter minusculeCharacter_injective (torusCorestrict_eq_ofWeights k) N

/-- **Invariant-subspace classification for the positive E₆ minuscule subgroup.** A subspace
is a subcomodule precisely when it is a coordinate span closed under all six raising operators. -/
theorem exists_subcomodule_iff (W : Submodule k (Fin 27 → k)) :
    (∃ N : Subcomodule k (coordinateHopfAlgebra k) (Fin 27 → k), N.toSubmodule = W) ↔
      ∃ s : Set (Fin 27),
        (∀ i a, a ∈ s → e6MinusculeWeight a i = -1 → e6MinusculeReflection i a ∈ s) ∧
        W = Submodule.span k ((Pi.basisFun k (Fin 27)) '' s) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨{a | Pi.single a (1 : k) ∈ N}, ?_, ?_⟩
    · intro i a ha hia
      exact single_reflection_mem k N i a hia ha
    · exact hN.symm.trans (toSubmodule_eq_span k N)
  · rintro ⟨s, hs, rfl⟩
    exact (Module.Basis.exists_subcomodule_toSubmodule_eq_span_iff_coordinateSpanIsStable
      (Pi.basisFun k (Fin 27)) s).mpr ((coordinateSpanIsStable_iff s).mpr hs)

end

end TauCeti.E6Minuscule.Generated.Positive
