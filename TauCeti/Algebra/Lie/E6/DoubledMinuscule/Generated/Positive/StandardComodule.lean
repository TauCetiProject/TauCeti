/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.StandardComodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule.Quotient
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.StandardComodule

/-!
# Invariant subspaces of the positive doubled E₆ subgroup

The subcomodules of the positive subgroup's representation on `V(ϖ₁) ⊕ V(ϖ₆)` over a field
are precisely the coordinate spans closed under the six raising operators. Its fifty-four
distinct torus characters separate the coordinate lines scheme-theoretically, even over finite
fields. On either summand, a raising operator moves a weight pairing to `-1` with its simple
coroot to its reflection; the coefficient on the dual summand is `-1`, still a unit in every
characteristic. This gives invariant flag data for testing maximality of the positive subgroup
among connected solvable subgroups.

The coordinate-span criterion works over every nontrivial commutative ring. Exhaustion of all
invariant subspaces by coordinate spans uses a field. No algebraic closure or characteristic
restriction is needed. Neither the generated carrier nor its positive subgroup is identified
here with the pinned simply connected group scheme of type E₆ or its Borel subgroup.

## Main declarations

* `TauCeti.E6DoubledMinuscule.Generated.Positive.standardComodule`: the positive subgroup's
  doubled minuscule representation.
* `TauCeti.E6DoubledMinuscule.Generated.Positive.coordinateSpanIsStable_iff`: invariance of a
  coordinate span is equivalent to closure under raising steps.
* `TauCeti.E6DoubledMinuscule.Generated.Positive.exists_subcomodule_iff`: the invariant-subspace
  classification over every field.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.

The construction follows
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.StandardComodule`, using the signed doubled
root matrices and the weight-extraction theorem
`Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule.Generated.Positive

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The standard representation of the positive doubled minuscule subgroup generated over `R`. -/
@[instance_reducible]
def standardComodule : Comodule R (coordinateHopfAlgebra R) (Fin 54 → R) :=
  GeneralLinear.corestrictStandardComodule R 54
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom

attribute [local instance] standardComodule

/-- Restriction to the weight torus splits the representation into its fifty-four weight lines. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 54)) minusculeCharacter := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)).hom
    (CommHopfAlgCat.commonKernelLift (generator R) (.inr ())).hom matrixWeight
  rw [← CommHopfAlgCat.hom_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
    generator_inr, generatorCoordinateMap_inr,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

private theorem rootPoint_matrix (i : Fin 6) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    GeneralLinear.pointToGeneralLinear 54
        (toConv (q.ofConv.comp (generator R (.inl i)).hom.toAlgHom)) =
      (rootSubgroupPoints (.inl i) A (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 54) A) := by
  have h := pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    R (.inl i) A q
  rw [generator_inl, ← generatedCoordinateMap_comp_generatedCoordinateLift]
  simpa only [BialgHom.mapDomain_apply, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    AlgHom.comp_assoc] using h

/-- Every positive subcomodule is stable under each raising-root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 54 → R))
    (i : Fin 6) (t : Multiplicative R) {v : Fin 54 → R} (hv : v ∈ N) :
    ((rootSubgroupPoints (.inl i) R t : Matrix.GeneralLinearGroup (Fin 54) R) :
      Matrix (Fin 54) (Fin 54) R) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.quotientStandardComodule_mulVec_mem R 54
    (definingIdeal R) (generator R (.inl i))
    (by simpa only [generator_inl] using
      ((le_definingIdeal_iff R (definingIdeal R)).mp le_rfl).1 i) N q hv
  simpa only [rootPoint_matrix R i (CommAlgCat.of R R) q, q,
    MulEquiv.apply_symm_apply] using h

/-- A subcomodule containing a coordinate vector contains its reflection whenever the weight
pairs to `-1` with the corresponding simple coroot. -/
theorem single_reflection_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 54 → R))
    (i : Fin 6) (a : Fin 54) (ha : matrixWeight a i = -1)
    (hv : Pi.single a (1 : R) ∈ N) :
    Pi.single (matrixIndexEquiv (reflection i (matrixIndexEquiv.symm a))) (1 : R) ∈ N := by
  have h := N.toSubmodule.sub_mem
    (rootSubgroupPoints_mulVec_mem R N i (Multiplicative.ofAdd 1) hv) hv
  rw [root_mulVec_single_sub R (.inl i) a ha] at h
  cases hblock : matrixIndexEquiv.symm a <;> simpa [hblock] using h

variable {R}

private theorem stable_of_raising_closed (s : Set (Fin 54))
    (hs : ∀ i a, a ∈ s → matrixWeight a i = -1 →
      matrixIndexEquiv (reflection i (matrixIndexEquiv.symm a)) ∈ s) :
    (Pi.basisFun R (Fin 54)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s := by
  classical
  let w : Fin 54 → ℤ := fun a ↦ if a ∈ s then 1 else 0
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
    have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 54) A ↦
      (g : Matrix (Fin 54) (Fin 54) A) a b) (rootPoint_matrix R i A q)
    rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear] at hm
    simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, q,
      AlgHom.id_comp, generator_inl] at hm
    have hab' : a ≠ b := fun h ↦ ha (h ▸ hb)
    have hedge : ¬(a = matrixIndexEquiv (reflection i (matrixIndexEquiv.symm b)) ∧
        matrixWeight b i = -1) := by
      rintro ⟨rfl, hbi⟩
      exact ha (hs i b hb hbi)
    rw [hm, coe_rootSubgroupPoints_eq_one_add_smul]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, rootIntMatrix_apply,
      Sum.elim_inl]
    split_ifs <;> simp_all
  · rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    exact
      GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker_weightTorusCoordinateBialgHom
        w matrixWeight

/-- A coordinate span is invariant exactly when its indices are closed under the six raising
steps. Invariance here is scheme-theoretic, not just stability under rational points. -/
theorem coordinateSpanIsStable_iff [Nontrivial R] (s : Set (Fin 54)) :
    (Pi.basisFun R (Fin 54)).coordinateSpanIsStable (C := coordinateHopfAlgebra R) s ↔
      ∀ i a, a ∈ s → matrixWeight a i = -1 →
        matrixIndexEquiv (reflection i (matrixIndexEquiv.symm a)) ∈ s := by
  classical
  refine ⟨fun h i a ha hia ↦ ?_, stable_of_raising_closed s⟩
  let N := (Pi.basisFun R (Fin 54)).coordinateSpanSubcomodule s h
  have hv : Pi.single a (1 : R) ∈ N := by
    rw [Module.Basis.mem_coordinateSpanSubcomodule]
    exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin 54) a⟩
  have hr := single_reflection_mem R N i a hia hv
  rw [Module.Basis.mem_coordinateSpanSubcomodule] at hr
  exact (Pi.basisFun R (Fin 54)).mem_span_image.mp hr (by simp)

variable (k : Type u) [Field k]

/-- Every invariant subspace is the span of exactly the doubled minuscule coordinate lines
it contains. -/
theorem toSubmodule_eq_span
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 54 → k)) :
    N.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin 54)) ''
      {a | Pi.single a (1 : k) ∈ N}) :=
  Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (CommHopfAlgCat.commonKernelLift (generator k) (.inr ())).hom.toCoalgHom
    minusculeCharacter minusculeCharacter_injective (torusCorestrict_eq_ofWeights k) N

/-- **Invariant-subspace classification for the positive doubled E₆ subgroup.** A subspace
is a subcomodule precisely when it is a coordinate span closed under all six raising operators. -/
theorem exists_subcomodule_iff (W : Submodule k (Fin 54 → k)) :
    (∃ N : Subcomodule k (coordinateHopfAlgebra k) (Fin 54 → k), N.toSubmodule = W) ↔
      ∃ s : Set (Fin 54),
        (∀ i a, a ∈ s → matrixWeight a i = -1 →
          matrixIndexEquiv (reflection i (matrixIndexEquiv.symm a)) ∈ s) ∧
        W = Submodule.span k ((Pi.basisFun k (Fin 54)) '' s) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨{a | Pi.single a (1 : k) ∈ N}, ?_, ?_⟩
    · intro i a ha hia
      exact single_reflection_mem k N i a hia ha
    · exact hN.symm.trans (toSubmodule_eq_span k N)
  · rintro ⟨s, hs, rfl⟩
    exact (Module.Basis.exists_subcomodule_toSubmodule_eq_span_iff_coordinateSpanIsStable
      (Pi.basisFun k (Fin 54)) s).mpr ((coordinateSpanIsStable_iff s).mpr hs)

end

end TauCeti.E6DoubledMinuscule.Generated.Positive
