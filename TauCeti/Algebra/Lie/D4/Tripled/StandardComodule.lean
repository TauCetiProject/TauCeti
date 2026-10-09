/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Lie.D4.Tripled.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.Lie.D4.Tripled.Levi
import TauCeti.Data.List.Involutive

/-!
# The standard representation of the tripled type-D4 carrier

The tripled type-`D₄` carrier is a closed subgroup of `GL₂₄`, constructed from the direct sum
of the vector and two half-spin eight-dimensional representations. After base change to a
commutative ring `R`, its standard representation is the corestriction of the standard
`O(GL₂₄)`-comodule along the quotient coordinate morphism.

This file proves that the resulting representation is faithful over every commutative ring. It
also identifies the action of an algebra-valued point with multiplication by its ambient
`24 × 24` matrix and deduces that subcomodules are stable under the concrete carrier points.

The tripled representation is designed to have three eight-dimensional constituents, and it is
not simple. Instead, every union of the summands `V(ϖ₁)`, `V(ϖ₃)` and `V(ϖ₄)` spans a subcomodule
over every commutative ring, because the carrier lies in the block-diagonal subgroup of the
summands. Over a field the representation is completely reducible. Restriction to the weight
torus separates the twenty-four distinct weight lines, so a subcomodule is spanned by the
coordinate vectors it contains. The positive and negative simple-root points move a coordinate
vector to that of each reflected weight, and the simple reflections act transitively on each
summand. Hence every subcomodule is the span of a union of summands, and the remaining summands
span a complement. The criterion
`TauCeti.D4Tripled.isCompletelyReducible_of_tripledWeights_of_rootSubgroupPoints` uses only the
torus weights, numbered root actions, and absence of coefficients between summands; it applies
also to the subgroup generated directly over the coefficient field.

## Main declarations

* `TauCeti.D4Tripled.standardComodule`: the standard comodule on `R²⁴`.
* `TauCeti.D4Tripled.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.D4Tripled.piScalarRight_comp_endOfPoint`: algebra-valued points act through their
  ambient matrices.
* `TauCeti.D4Tripled.points_mulVec_mem`: invariant submodules are stable under concrete carrier
  points.
* `TauCeti.D4Tripled.summandSubcomodule`: the subcomodule spanned by a union of summands.
* `TauCeti.D4Tripled.torusCorestrict_eq_ofWeights`: the weight decomposition under the weight
  torus, over every commutative ring.
* `TauCeti.D4Tripled.isCompletelyReducible_standardComodule`: complete reducibility over a field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.

The corestriction and point-action interface follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule`; the organization is adapted from
`TauCeti.Algebra.Lie.E7.Minuscule.StandardComodule`. The weight-line and reflection steps follow
the simplicity proof in `TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`, and the complement
construction follows `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.StandardComodule`.
-/

public section

open CategoryTheory Module WithConv
open TauCeti.DynkinType
open scoped Matrix TensorProduct

namespace TauCeti.D4Tripled

universe u

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized tripled type-`D₄` carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R) (Fin 24 → R) :=
  GeneralLinear.corestrictStandardComodule R 24 (coordinateMap R).hom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- **The standard comodule of the specialized tripled type-`D₄` carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R)
      (V := Fin 24 → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R 24
    (coordinateMap R).hom (coordinateMap_surjective R)

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under scalar extension, a carrier-valued point acts on the standard comodule by the matrix
obtained from its ambient `GL₂₄` point. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin 24)).toLinearMap.comp
        (Comodule.endOfPoint (Fin 24 → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
          (GeneralLinear.pointToGeneralLinear 24
            (CommHopfAlgCat.quotientPointsHom
              (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
              (CommAlgCat.of R A) g)) :
          (Fin 24 → A) →ₗ[A] Fin 24 → A).comp
        (TensorProduct.piScalarRight R A A (Fin 24)).toLinearMap := by
  rw [Comodule.endOfPoint_corestrict]
  have hpoint :
      g.ofConv.comp ((coordinateMap R).hom :
        GeneralLinear.coordinateHopfAlgebra R 24 →ₐ[R] coordinateHopfAlgebra R) =
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R A) g).ofConv := by
    exact congrArg WithConv.ofConv (mapPointsFunctor_coordinateMap_app R g)
  rw [hpoint]
  exact GeneralLinear.piScalarRight_comp_endOfPoint R 24 _

end PointAction

/-- A subcomodule of the standard carrier comodule is stable under every coordinate-algebra
point over the base ring. -/
theorem mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R))
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] R)) {w : Fin 24 → R} (hw : w ∈ N) :
    (GeneralLinear.pointToGeneralLinear 24
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g) : Matrix (Fin 24) (Fin 24) R) *ᵥ w ∈ N := by
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 24
    (coordinateMap R).hom N g hw
  have hpoint : AlgHom.mapDomain (coordinateMap R).hom g = _ :=
    mapPointsFunctor_coordinateMap_app R g
  rwa [hpoint] at h

/-- A subcomodule of the standard carrier comodule is stable under every concrete tripled
type-`D₄` carrier point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R))
    (g : points R) {w : Fin 24 → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin 24) R) : Matrix (Fin 24) (Fin 24) R) *ᵥ w ∈ N := by
  have h := mulVec_mem R N
    ((baseChangePointsMulEquiv R (CommAlgCat.of R R)).symm g) hw
  rw [quotientPointsHom_baseChangePointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-! ## The summand subcomodules -/

/-- **A union of summands spans a subcomodule of the standard carrier comodule**, over every
commutative ring: the carrier preserves each of `V(ϖ₁)`, `V(ϖ₃)` and `V(ϖ₄)`. -/
noncomputable def summandSubcomodule (s : Set (Fin 24))
    (hs : ∀ a b, d4TripledSummand a = d4TripledSummand b → b ∈ s → a ∈ s) :
    Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R) :=
  (Pi.basisFun R (Fin 24)).coordinateSpanSubcomodule s <|
    ((Pi.basisFun R (Fin 24)).coordinateSpanIsStable_iff
      (C := coordinateHopfAlgebra R) s).2 <| by
    intro a ha b hb
    have hab : d4TripledSummand a ≠ d4TripledSummand b := fun h ↦ ha (hs a b h hb)
    rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
      GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
      GeneralLinear.genericMatrix_apply]
    exact coordinateMap_X_eq_zero R hab

/-- A summand subcomodule is the span of the coordinate vectors of its summands. -/
@[simp]
theorem summandSubcomodule_toSubmodule (s : Set (Fin 24))
    (hs : ∀ a b, d4TripledSummand a = d4TripledSummand b → b ∈ s → a ∈ s) :
    (summandSubcomodule R s hs).toSubmodule = Submodule.span R ((Pi.basisFun R (Fin 24)) '' s) :=
  Module.Basis.coordinateSpanSubcomodule_toSubmodule _ _ _

/-- Membership in a summand subcomodule means vanishing outside the chosen summands. -/
@[simp]
theorem mem_summandSubcomodule (s : Set (Fin 24))
    (hs : ∀ a b, d4TripledSummand a = d4TripledSummand b → b ∈ s → a ∈ s) (v : Fin 24 → R) :
    v ∈ summandSubcomodule R s hs ↔ ∀ a ∉ s, v a = 0 := by
  classical
  rw [← Subcomodule.mem_toSubmodule, summandSubcomodule_toSubmodule,
    (Pi.basisFun R (Fin 24)).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr]
  exact forall_congr' fun a ↦ not_imp_comm

/-! ## The weight decomposition under the weight torus -/

/-- The character of the weight torus on the coordinate vector at a tripled weight index. -/
noncomputable abbrev tripledCharacter (a : Fin 24) : Multiplicative (Fin 4 →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (d4TripledWeight a))

/-- **Restricting the standard carrier comodule to the rank-four weight torus gives the direct sum
of the twenty-four distinct tripled weight comodules.** The coordinate vector at `a` spans the
weight line of the torus character `tripledCharacter a`, over every commutative ring. -/
theorem torusCorestrict_eq_ofWeights :
    let _ := standardComodule R
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 24)) tripledCharacter := by
  let _ := GeneralLinear.standardComodule R 24
  let _ := standardComodule R
  apply Comodule.ext
  rw [Comodule.corestrict_coact,
    ← Comodule.corestrictCoact_comp (coordinateMap R).hom.toCoalgHom
      (weightTorusToBaseChangeCoordinateMap R).hom.toCoalgHom]
  have hcomp :
      _root_.CoalgHom.comp ((weightTorusToBaseChangeCoordinateMap R).hom.toCoalgHom)
          ((coordinateMap R).hom.toCoalgHom) =
        (GeneralLinear.weightTorusCoordinateBialgHom (S := R) d4TripledWeight).toCoalgHom := by
    have hb :
        (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
          GeneralLinear.weightTorusCoordinateBialgHom (S := R) d4TripledWeight := by
      rw [← _root_.CommHopfAlgCat.hom_comp,
        coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
        GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    apply DFunLike.ext _ _
    intro x
    exact DFunLike.congr_fun hb x
  rw [hcomp]
  simpa only [Comodule.corestrict_coact] using
    congrArg (fun c : Comodule R _ (Fin 24 → R) ↦ c.coact)
      (GeneralLinear.corestrict_standardComodule_weightTorusCoordinateBialgHom_eq_ofWeights
        d4TripledWeight)

/-! ## Complete reducibility over a field -/

section RootInvariance

variable (k : Type u) [CommRing k]

private theorem tripledCharacter_injective : Function.Injective tripledCharacter := by
  intro a b h
  apply d4TripledWeight_injective
  apply Finsupp.equivFunOnFinite.symm.injective
  exact Multiplicative.ofAdd.injective h

private theorem positiveRoot_mulVec_single_sub (i : Fin 4) (a : Fin 24)
    (ha : d4TripledWeight a i = -1) :
    (((rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 24) k) : Matrix (Fin 24) (Fin 24) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (d4TripledReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [toAdd_ofAdd, one_smul]
  rw [Matrix.mulVec_single_one, raisingMatrix_def, weightTable.raisingMatrix_map_col]
  simp only [weightTable_weight, weightTable_reflection, ha, ite_true, add_sub_cancel_left]

private theorem negativeRoot_mulVec_single_sub (i : Fin 4) (a : Fin 24)
    (ha : d4TripledWeight a i = 1) :
    (((rootSubgroupPoints (.inr i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 24) k) : Matrix (Fin 24) (Fin 24) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (d4TripledReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inr, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [toAdd_ofAdd, one_smul]
  rw [Matrix.mulVec_single_one, loweringMatrix_def, weightTable.loweringMatrix_map_col]
  simp only [weightTable_weight, weightTable_reflection, ha, ite_true, add_sub_cancel_left]

/-- Invariance under the two simple-root points makes membership of coordinate vectors stable
under every simple reflection. -/
private theorem single_reflection_mem
    (N : Submodule k (Fin 24 → k))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 24) k) : Matrix (Fin 24) (Fin 24) k) *ᵥ v ∈ N)
    (a : Fin 24) (i : Fin 4) (ha : Pi.single a 1 ∈ N) :
    Pi.single (d4TripledReflection i a) 1 ∈ N := by
  rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with hneg | hzero | hpos
  · have hact := hroot (.inl i) _ ha
    have hsub := N.sub_mem hact ha
    rwa [positiveRoot_mulVec_single_sub k i a hneg] at hsub
  · have hfix : d4TripledReflection i a = a := by
      apply d4TripledWeight_injective
      rw [d4TripledWeight_reflection, hzero, zero_smul, sub_zero]
    rw [hfix]
    exact ha
  · have hact := hroot (.inr i) _ ha
    have hsub := N.sub_mem hact ha
    rwa [negativeRoot_mulVec_single_sub k i a hpos] at hsub

/-- A submodule stable under the numbered tripled root matrices containing one coordinate
vector contains every coordinate vector in the same eight-dimensional summand. -/
theorem single_mem_of_summand_eq_of_rootSubgroupPoints
    (N : Submodule k (Fin 24 → k))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 24) k) : Matrix (Fin 24) (Fin 24) k) *ᵥ v ∈ N)
    {a b : Fin 24} (hab : d4TripledSummand a = d4TripledSummand b)
    (hb : Pi.single b 1 ∈ N) : Pi.single a 1 ∈ N := by
  obtain ⟨l, hl⟩ := (exists_foldl_d4TripledReflection_eq_iff b a).2 hab.symm
  have h := (predicate_foldl_iff_of_involutive (fun c ↦ Pi.single c (1 : k) ∈ N)
    (fun i ↦ d4TripledReflection i) (fun i ↦ d4TripledReflection_apply_apply i)
    (single_reflection_mem k N hroot) l b).2 hb
  rwa [hl] at h

end RootInvariance

section CompletelyReducible

variable (k : Type u) [Field k]

/-- A comodule with the distinct tripled torus weights, the numbered root actions, and no
coefficients mixing the three summands is completely reducible. -/
theorem isCompletelyReducible_of_tripledWeights_of_rootSubgroupPoints
    {H : Type*} [AddCommGroup H] [Module k H] [Coalgebra k H]
    [Comodule k H (Fin 24 → k)]
    (τ : H →ₗc[k] (DiagonalizableGroup.coordinateRing k
      (SplitTorus.characterGroup (Fin 4))).obj)
    (hτ : Comodule.Corestrict τ = Comodule.ofWeights (Pi.basisFun k (Fin 24)) tripledCharacter)
    (hroot : ∀ (N : Subcomodule k H (Fin 24 → k)) j v, v ∈ N →
      ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 24) k) : Matrix (Fin 24) (Fin 24) k) *ᵥ v ∈ N)
    (hsummand : ∀ a b, d4TripledSummand a ≠ d4TripledSummand b →
      Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 24)) a b = 0) :
    Comodule.IsCompletelyReducible k H (Fin 24 → k) := by
  classical
  apply Comodule.IsCompletelyReducible.of_exists_isCompl
  intro N
  let s : Set (Fin 24) := {a | Pi.single a (1 : k) ∈ N}
  let M := (Pi.basisFun k (Fin 24)).coordinateSpanSubcomodule sᶜ <|
    ((Pi.basisFun k (Fin 24)).coordinateSpanIsStable_iff (C := H) sᶜ).2 <| by
      intro a ha b hb
      apply hsummand
      intro hab
      exact hb (single_mem_of_summand_eq_of_rootSubgroupPoints k N.toSubmodule
        (hroot N) hab.symm (Set.notMem_compl_iff.mp ha))
  refine ⟨M, ?_⟩
  rw [Module.Basis.coordinateSpanSubcomodule_toSubmodule,
    Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights τ tripledCharacter
      tripledCharacter_injective hτ N]
  exact (Pi.basisFun k (Fin 24)).linearIndependent.isCompl_span_image
    (Pi.basisFun k (Fin 24)).span_eq isCompl_compl

/-- **The standard comodule of the specialized tripled type-`D₄` carrier is completely reducible
over every field.** Every subcomodule is the span of a union of the three summands, and the
remaining summands span a complementary subcomodule. -/
theorem isCompletelyReducible_standardComodule :
    Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k) (Fin 24 → k) :=
  isCompletelyReducible_of_tripledWeights_of_rootSubgroupPoints k
    (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom
    (torusCorestrict_eq_ofWeights k)
    (fun N j _ hw ↦ points_mulVec_mem k N
      (rootSubgroupPoints j k (Multiplicative.ofAdd 1)) hw)
    (fun a b hab ↦ by
      rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
        GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
        GeneralLinear.genericMatrix_apply]
      exact coordinateMap_X_eq_zero k hab)

end CompletelyReducible

end TauCeti.D4Tripled
