/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.TensorInduction
import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Resolution
import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.CyclicFour

/-!
# The degree-one Evens norm for arbitrary finite index

For a compact open subgroup `U` of finite index `l` in a topological group `G`, tensor induction
of the homogeneous cocycle of a continuous `𝔽₂` character defines a class in `Hˡ(G, 𝔽₂)`.
Every degree-one class has a unique continuous character representative, so this construction
gives the function `evensNormH1 : H¹(U, 𝔽₂) → Hˡ(G, 𝔽₂)`.

The formula `evensNormH1_homClass` computes the norm with any transversal. Independence of the
transversal is supplied by the comparison of tensor-induced resolutions. At index two,
`evensNormH1_eq_evensNormIndexTwo` identifies this tensor construction with the graph norm.
The operation is a function, without an additivity assertion.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), Sections 2–5, for the tensor-induced construction.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer.
  Math. Soc. **91** (1984), 309–313, Lemma 2.4, for the graph normalization at index two.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]

private noncomputable local instance : Fintype (G ⧸ U.toSubgroup) :=
  U.toSubgroup.fintypeQuotientOfFiniteIndex

-- Use the direct-sum module action also when forming the tensor of total resolutions.
private noncomputable local instance : Module ℤ (trivialF2 U.toSubgroup).gradedResolutionModule :=
  @DirectSum.instModule ℤ _ ℕ
    (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V)
    (fun _ ↦ inferInstance) (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).hV2)

private noncomputable def characterNorm (s : U.toSubgroup.LeftTransversal)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    continuousCohomology U.toSubgroup.index (trivialF2 G) :=
  (eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 G))
    (by simp [Subgroup.index_eq_card, Nat.card_eq_fintype_card] :
      Fintype.card (G ⧸ U.toSubgroup) * 1 = U.toSubgroup.index))).hom
    (ContinuousCohomology.coeffMap
      (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' s).hom.hom
      (Fintype.card (G ⧸ U.toSubgroup) * 1)
      (smoothTensorInducedDiagonalClass U.toSubgroup U.isOpen' s
        ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
        (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
        (evensCharacterRepresentative U.toSubgroup α hα)
        (evensCharacterRepresentative_mem U.toSubgroup α hα)
        (evensCharacterRepresentative_invariant U.toSubgroup α hα)
        (evensCharacterRepresentative_d_eq_zero U.toSubgroup α hα)))

private theorem characterNorm_changeTransversal (s t : U.toSubgroup.LeftTransversal)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    characterNorm U s α hα = characterNorm U t α hα := by
  exact congrArg
    ((eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 G))
    (by simp [Subgroup.index_eq_card, Nat.card_eq_fintype_card] :
      Fintype.card (G ⧸ U.toSubgroup) * 1 = U.toSubgroup.index))).hom)
    (smoothTensorInducedDiagonalClass_trivialF2_changeTransversal G U.toSubgroup U.isOpen' t s
      (evensCharacterRepresentative U.toSubgroup α hα)
      (evensCharacterRepresentative_mem U.toSubgroup α hα)
      (evensCharacterRepresentative_invariant U.toSubgroup α hα)
      (evensCharacterRepresentative_d_eq_zero U.toSubgroup α hα))

/-- The Evens norm from degree one for a compact open subgroup of arbitrary finite index.
Tensor induction multiplies the degree by the index. The input class is represented by its
unique continuous `𝔽₂` character, and the tensor-induced coefficient object is identified with
`trivialF2 G` by multiplication of the factors. -/
noncomputable def evensNormH1 (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    continuousCohomology U.toSubgroup.index (trivialF2 G) :=
  characterNorm U default (homClass_surjective U.toSubgroup x).choose
    (homClass_surjective U.toSubgroup x).choose_spec.choose

/-- The degree-one Evens norm is the tensor-induced diagonal class of the homogeneous character
cocycle, computed with any transversal. This equation includes the transport from the number of
tensor factors to the subgroup index. -/
theorem evensNormH1_homClass (s : U.toSubgroup.LeftTransversal)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    letI : Fintype (G ⧸ U.toSubgroup) := U.toSubgroup.fintypeQuotientOfFiniteIndex
    evensNormH1 U (homClass U.toSubgroup α hα) =
      (eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 G))
        (by simp [Subgroup.index_eq_card, Nat.card_eq_fintype_card] :
          Fintype.card (G ⧸ U.toSubgroup) * 1 = U.toSubgroup.index))).hom
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' s).hom.hom
          (Fintype.card (G ⧸ U.toSubgroup) * 1)
          (smoothTensorInducedDiagonalClass U.toSubgroup U.isOpen' s
            ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
            (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
            (evensCharacterRepresentative U.toSubgroup α hα)
            (evensCharacterRepresentative_mem U.toSubgroup α hα)
            (evensCharacterRepresentative_invariant U.toSubgroup α hα)
            (evensCharacterRepresentative_d_eq_zero U.toSubgroup α hα))) := by
  dsimp only
  have hα' := (homClass_inj U.toSubgroup
    (homClass_surjective U.toSubgroup (homClass U.toSubgroup α hα)).choose_spec.choose hα).mp
      (homClass_surjective U.toSubgroup (homClass U.toSubgroup α hα)).choose_spec.choose_spec
  have hrep :
      (⟨(homClass_surjective U.toSubgroup (homClass U.toSubgroup α hα)).choose,
        (homClass_surjective U.toSubgroup (homClass U.toSubgroup α hα)).choose_spec.choose⟩ :
          {β : U.toSubgroup →* Multiplicative (ZMod 2) // Continuous β}) = ⟨α, hα⟩ :=
    Subtype.ext hα'
  exact (congrArg (fun a : {β : U.toSubgroup →* Multiplicative (ZMod 2) // Continuous β} ↦
    characterNorm U default a.val a.property) hrep).trans
      (characterNorm_changeTransversal U default s α hα)

/-- The Evens norm in degree one sends zero to zero. -/
@[simp]
theorem evensNormH1_zero : evensNormH1 U 0 = 0 := by
  rw [← homClass_one U.toSubgroup, evensNormH1_homClass U default]
  simp only [evensCharacterRepresentative_one]
  let : LinearOrder (G ⧸ U.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U.toSubgroup)).injective
  rw [smoothTensorInducedDiagonalClass_eq]
  have hz : PiTensorProduct.tprod ℤ
      (fun _ : G ⧸ U.toSubgroup ↦ (0 : (trivialF2 U.toSubgroup).gradedResolutionModule)) = 0 :=
    (PiTensorProduct.tprod ℤ).map_coord_zero (QuotientGroup.mk 1) rfl
  -- The smooth/discrete dictionary uses the same tensor carrier with opaque wrappers.
  -- Default transparency identifies that carrier before applying the zero-class equation.
  simp only [hz]
  erw [TopRep.ResolutionContraction.gradedCohomologyClass_zero, map_zero, map_zero]

/-- At index two, the tensor-induced degree-one Evens norm is the graph norm. -/
theorem evensNormH1_eq_evensNormIndexTwo [LocallyCompactSpace G]
    (hU : U.toSubgroup.index = 2) (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    evensNormH1 U x =
      (eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 G)) hU.symm)).hom
        (evensNormIndexTwo U hU x) := by
  obtain ⟨α, hα, rfl⟩ := homClass_surjective U.toSubgroup x
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hU
  let t : U.toSubgroup.LeftTransversal :=
    ⟨Set.range (U.toSubgroup.indexTwoTransversal s),
      Subgroup.isComplement_range_left (Subgroup.indexTwoTransversal_mk hU hs)⟩
  rw [evensNormH1_homClass U t, evensNormIndexTwo_homClass]
  rw [smoothTensorInducedDiagonalClass_eq_graphClass U hU s hs α hα
    (evensCharacterRepresentative U.toSubgroup α hα)
    (evensCharacterRepresentative_mem U.toSubgroup α hα)
    (evensCharacterRepresentative_invariant U.toSubgroup α hα)
    (evensCharacterRepresentative_d_eq_zero U.toSubgroup α hα)
    (evensCharacterRepresentative_def U.toSubgroup α hα)]
  rw [← ConcreteCategory.comp_apply, eqToHom_trans]

-- On the even subgroup of `C₄`, the nontrivial character has nonzero norm. This exercises
-- the public class-level operation through its tensor-to-graph comparison.
example : evensNormH1 cyclicFourEvenSubgroup
    (homClass cyclicFourEvenSubgroup.toSubgroup cyclicFourEvenCharacter
      continuous_of_discreteTopology) ≠ 0 := by
  rw [evensNormH1_eq_evensNormIndexTwo _ cyclicFourEvenSubgroup_index,
    evensNormIndexTwo_homClass]
  intro hzero
  apply graphClass_cyclicFour_ne_zero
  exact (ConcreteCategory.bijective_of_isIso
    (eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 (Multiplicative (ZMod 4))))
      cyclicFourEvenSubgroup_index.symm))).injective (hzero.trans (map_zero _).symm)

end TauCeti.ContCohomology
