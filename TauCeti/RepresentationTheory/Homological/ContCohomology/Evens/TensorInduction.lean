/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Representative
public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2
import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Explicit
import Mathlib.GroupTheory.IndexNormal

/-!
# The tensor-induced character class and the index-two graph cocycle

For an index-two compact open subgroup, the diagonal tensor of the homogeneous cocycle of a
continuous character has the class of the two-point graph cocycle. This identifies the
resolution-level multiplicative transfer on character representatives with the explicit
index-two Evens norm.

The calculation uses the transversal with representatives `1` and an element `s` outside the
subgroup, ordered with `1` first. The ordered tensor homotopy first sends `z ⊗ z` to `h z ⊗ z`.
The explicit cocycle of the contracted complex then has the two branches of the graph formula.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), Sections 2–5.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer.
  Math. Soc. **91** (1984), 309–313, Lemma 2.4, for the index-two graph normalization.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
  (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α)

private noncomputable abbrev characterCochain :=
  inhomogeneousCochain1 (fun x ↦ Multiplicative.toAdd (α x)) (continuous_toAdd.comp hα)

private noncomputable def twoTransversal : U.toSubgroup.LeftTransversal :=
  ⟨Set.range (U.toSubgroup.indexTwoTransversal s),
    Subgroup.isComplement_range_left (Subgroup.indexTwoTransversal_mk hU hs)⟩

omit [IsTopologicalGroup G] in
private theorem twoTransversal_rep :
    U.toSubgroup.leftTransversalRep (twoTransversal U hU s hs) =
      U.toSubgroup.indexTwoTransversal s :=
  Subgroup.leftTransversalRep_range _ _ (Subgroup.indexTwoTransversal_mk hU hs)

private noncomputable abbrev characterPrimitive :
    (trivialF2 U.toSubgroup).gradedResolutionModule :=
  (trivialF2 U.toSubgroup).gradedResolutionHomotopy (evensCharacterRepresentative U.toSubgroup α hα)

private theorem characterPrimitive_eq :
    characterPrimitive U α hα =
      DirectSum.lof ℤ ℕ (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V)
        0 ((characterCochain U α hα).val 1) := by
  rw [characterPrimitive, evensCharacterRepresentative_def]
  exact (trivialF2 U.toSubgroup).gradedResolutionHomotopy_lof_succ
    0 (characterCochain U α hα).val

-- The differential and homotopy use the direct-sum module action. Selecting it here keeps the
-- indexed tensor carrier identical to that of the tensor-induced resolution.
private noncomputable local instance : Module ℤ (trivialF2 U.toSubgroup).gradedResolutionModule :=
  @DirectSum.instModule ℤ _ ℕ
    (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V)
    (fun _ ↦ inferInstance) (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).hV2)

open scoped Classical in
private noncomputable def twoTensor
    (x y : (trivialF2 U.toSubgroup).gradedResolutionModule) :
    ⨂[ℤ] _ : G ⧸ U.toSubgroup, (trivialF2 U.toSubgroup).gradedResolutionModule :=
  PiTensorProduct.tprod ℤ fun i ↦ if i = QuotientGroup.mk 1 then x else y

private theorem twoTensor_zero_left
    (y : (trivialF2 U.toSubgroup).gradedResolutionModule) : twoTensor U 0 y = 0 := by
  classical
  exact (PiTensorProduct.tprod ℤ).map_coord_zero (QuotientGroup.mk 1) (by simp)

include s hs in
private theorem twoTensor_zero_right
    (x : (trivialF2 U.toSubgroup).gradedResolutionModule) : twoTensor U x 0 = 0 := by
  classical
  exact (PiTensorProduct.tprod ℤ).map_coord_zero (QuotientGroup.mk s)
    (by simp [mk_ne_mk_one_of_notMem hs])

private theorem twoTensor_self
    (x : (trivialF2 U.toSubgroup).gradedResolutionModule) :
    twoTensor U x x = PiTensorProduct.tprod ℤ (fun _ ↦ x) := by
  classical
  simp [twoTensor]

include hU hs in
private theorem twoTensor_slotHomotopy [Fintype (G ⧸ U.toSubgroup)]
    [LinearOrder (G ⧸ U.toSubgroup)]
    (hlt : (QuotientGroup.mk 1 : G ⧸ U.toSubgroup) < QuotientGroup.mk s)
    (x y : (trivialF2 U.toSubgroup).gradedResolutionModule) :
    PiTensorProduct.slotHomotopy (G ⧸ U.toSubgroup)
        ((trivialF2 U.toSubgroup).gradedResolutionAugmentation ∘ₗ
          (trivialF2 U.toSubgroup).gradedResolutionProjection)
        (trivialF2 U.toSubgroup).gradedResolutionHomotopy (twoTensor U x y) =
      twoTensor U ((trivialF2 U.toSubgroup).gradedResolutionHomotopy x) y +
        twoTensor U ((trivialF2 U.toSubgroup).gradedResolutionAugmentation
          ((trivialF2 U.toSubgroup).gradedResolutionProjection x))
          ((trivialF2 U.toSubgroup).gradedResolutionHomotopy y) := by
  classical
  rw [twoTensor, PiTensorProduct.slotHomotopy_tprod,
    sum_quotient_eq_add_of_index_two hU hs]
  congr 1
  · congr 1
    funext i
    rcases eq_mk_one_or_eq_mk_of_index_two hU hs i with rfl | rfl <;>
      simp [hlt.ne', not_lt_of_ge hlt.le]
  · congr 1
    funext i
    rcases eq_mk_one_or_eq_mk_of_index_two hU hs i with rfl | rfl <;>
      simp [hlt, hlt.ne, hlt.ne']

private theorem characterPrimitive_homotopy :
    (trivialF2 U.toSubgroup).gradedResolutionHomotopy (characterPrimitive U α hα) = 0 := by
  rw [characterPrimitive_eq]
  exact (trivialF2 U.toSubgroup).gradedResolutionHomotopy_lof_zero _

private theorem characterTotal_projection :
    (trivialF2 U.toSubgroup).gradedResolutionProjection
      (evensCharacterRepresentative U.toSubgroup α hα) = 0 := by
  rw [evensCharacterRepresentative_def]
  exact (trivialF2 U.toSubgroup).gradedResolutionProjection_lof_succ
    0 (characterCochain U α hα).val

include hU hs in
private theorem twoTensor_diagonal_homotopy [Fintype (G ⧸ U.toSubgroup)]
    [LinearOrder (G ⧸ U.toSubgroup)]
    (hlt : (QuotientGroup.mk 1 : G ⧸ U.toSubgroup) < QuotientGroup.mk s) :
    PiTensorProduct.slotHomotopy (G ⧸ U.toSubgroup)
        ((trivialF2 U.toSubgroup).gradedResolutionAugmentation ∘ₗ
          (trivialF2 U.toSubgroup).gradedResolutionProjection)
        (trivialF2 U.toSubgroup).gradedResolutionHomotopy
        (PiTensorProduct.tprod ℤ (fun _ ↦ evensCharacterRepresentative U.toSubgroup α hα)) =
      twoTensor U (characterPrimitive U α hα) (evensCharacterRepresentative U.toSubgroup α hα) := by
  rw [← twoTensor_self, twoTensor_slotHomotopy U hU s hs hlt,
    characterTotal_projection, map_zero, twoTensor_zero_left, add_zero]

open scoped Classical in
private theorem twoTensor_action (g : G)
    (x y : (trivialF2 U.toSubgroup).gradedResolutionModule) :
    U.toSubgroup.tensorInducedRepresentation (twoTransversal U hU s hs)
        (trivialF2 U.toSubgroup).gradedResolutionRepresentation g (twoTensor U x y) =
      if g ∈ U then
        twoTensor U
          ((trivialF2 U.toSubgroup).gradedResolutionRepresentation
            ((U.toSubgroup.monomialHom (twoTransversal U hU s hs) g).left
              (QuotientGroup.mk 1)) x)
          ((trivialF2 U.toSubgroup).gradedResolutionRepresentation
            ((U.toSubgroup.monomialHom (twoTransversal U hU s hs) g).left
              (QuotientGroup.mk s)) y)
      else
        twoTensor U
          ((trivialF2 U.toSubgroup).gradedResolutionRepresentation
            ((U.toSubgroup.monomialHom (twoTransversal U hU s hs) g).left
              (QuotientGroup.mk 1)) y)
          ((trivialF2 U.toSubgroup).gradedResolutionRepresentation
            ((U.toSubgroup.monomialHom (twoTransversal U hU s hs) g).left
              (QuotientGroup.mk s)) x) := by
  classical
  let := Subgroup.normal_of_index_eq_two hU
  rw [twoTensor, Subgroup.tensorInducedRepresentation_apply_tprod]
  by_cases hg : g ∈ U
  · rw [ite_eq_left hg, twoTensor]
    congr 1
    funext i
    rcases eq_mk_one_or_eq_mk_of_index_two hU hs i with rfl | rfl <;>
      simp only [smul_quotient_eq_self_of_mem (U.toSubgroup.inv_mem hg),
        mk_ne_mk_one_of_notMem hs, ↓reduceIte]
  · rw [ite_eq_right hg, twoTensor]
    congr 1
    funext i
    rcases eq_mk_one_or_eq_mk_of_index_two hU hs i with rfl | rfl <;>
      simp only [smul_mk_one_of_notMem_of_index_two hU hs (mt U.toSubgroup.inv_mem_iff.mp hg),
        smul_mk_of_notMem_of_index_two hU hs (mt U.toSubgroup.inv_mem_iff.mp hg),
        mk_ne_mk_one_of_notMem hs, ↓reduceIte]

private theorem characterPrimitive_homotopy_action (x : U.toSubgroup) :
    (trivialF2 U.toSubgroup).gradedResolutionHomotopy
        ((trivialF2 U.toSubgroup).gradedResolutionRepresentation x
          (characterPrimitive U α hα)) = 0 := by
  rw [characterPrimitive_eq]
  exact (congrArg (trivialF2 U.toSubgroup).gradedResolutionHomotopy
    ((trivialF2 U.toSubgroup).gradedResolutionRepresentation_lof 0 x _)).trans
      ((trivialF2 U.toSubgroup).gradedResolutionHomotopy_lof_zero _)

private theorem characterPrimitive_projection_action (x : U.toSubgroup) :
    (trivialF2 U.toSubgroup).gradedResolutionProjection
        ((trivialF2 U.toSubgroup).gradedResolutionRepresentation x
          (characterPrimitive U α hα)) =
      (trivialF2Equiv U.toSubgroup).symm (Multiplicative.toAdd (α x)) := by
  rw [characterPrimitive_eq]
  refine (congrArg (trivialF2 U.toSubgroup).gradedResolutionProjection
    ((trivialF2 U.toSubgroup).gradedResolutionRepresentation_lof 0 x _)).trans ?_
  refine ((trivialF2 U.toSubgroup).gradedResolutionProjection_lof_zero _).trans ?_
  refine ((trivialF2 U.toSubgroup).resolutionX_succ_ρ_apply_apply 0 x _ 1).trans ?_
  rw [trivialF2_ρ_apply_apply, mul_one]
  exact (inhomogeneousCochain1_apply
    (fun x ↦ Multiplicative.toAdd (α x)) (continuous_toAdd.comp hα) 1 x⁻¹).trans
      (congrArg (trivialF2Equiv U.toSubgroup).symm
        (by simp [map_inv, toAdd_inv, CharTwo.neg_eq]))

private noncomputable abbrev wordCoord (g : G) (i : G ⧸ U.toSubgroup) : U.toSubgroup :=
  (U.toSubgroup.monomialHom (twoTransversal U hU s hs) g).left i

private noncomputable abbrev wordValue (g : G) (i : G ⧸ U.toSubgroup) : ZMod 2 :=
  Multiplicative.toAdd (α (wordCoord U hU s hs g i))

omit [IsTopologicalGroup G] in
private theorem wordValue_def (g : G) (i : G ⧸ U.toSubgroup) :
    wordValue U hU s hs α g i =
      Multiplicative.toAdd (α ((U.toSubgroup.monomialHom (twoTransversal U hU s hs) g).left i)) :=
  (rfl)

omit [IsTopologicalGroup G] in
private theorem wordValue_one (g : G) :
    wordValue U hU s hs α g (QuotientGroup.mk 1) = evensB1 U.toSubgroup s α g := by
  rw [← evensExtend_lWord_mk_one hU hs,
    evensExtend_of_mem (lWord_mem _ _ (Subgroup.indexTwoTransversal_mk hU hs) _ _)]
  simp only [wordValue, wordCoord, Subgroup.monomialHom_left, twoTransversal_rep]

omit [IsTopologicalGroup G] in
private theorem wordValue_s (g : G) :
    wordValue U hU s hs α g (QuotientGroup.mk s) = evensBs U.toSubgroup s α g := by
  rw [← evensExtend_lWord_mk hU hs,
    evensExtend_of_mem (lWord_mem _ _ (Subgroup.indexTwoTransversal_mk hU hs) _ _)]
  simp only [wordValue, wordCoord, Subgroup.monomialHom_left, twoTransversal_rep]

omit [IsTopologicalGroup G] in
private theorem wordValue_inv (g : G) (i : G ⧸ U.toSubgroup) :
    wordValue U hU s hs α g⁻¹ i = wordValue U hU s hs α g (g • i) := by
  have hw : wordCoord U hU s hs g⁻¹ i = (wordCoord U hU s hs g (g • i))⁻¹ := by
    apply Subtype.ext
    simp only [wordCoord, Subgroup.monomialHom_left, Subgroup.coe_mk, Subgroup.coe_inv]
    exact lWord_inv U.toSubgroup _ i g
  exact (congrArg (fun x : U.toSubgroup ↦ Multiplicative.toAdd (α x)) hw).trans
    (by simp only [map_inv, toAdd_inv, CharTwo.neg_eq])

private noncomputable abbrev characterCoeff : SmoothDiscreteTopRep ℤ U.toSubgroup :=
  ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩

section TensorRead

variable [Fintype (G ⧸ U.toSubgroup)]

omit [Fintype (G ⧸ U.toSubgroup)] in
private local instance [Finite (G ⧸ U.toSubgroup)] : U.toSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

private noncomputable def tensorRead
    (z : ⨂[ℤ] _ : G ⧸ U.toSubgroup, (trivialF2 U.toSubgroup).gradedResolutionModule) : ZMod 2 :=
  trivialF2Equiv G ((smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
    (twoTransversal U hU s hs)).hom.hom.hom
      (smoothTensorInducedGradedResolutionProjection U.toSubgroup (characterCoeff U) z))

private theorem tensorRead_tprod
    (x : G ⧸ U.toSubgroup → (trivialF2 U.toSubgroup).gradedResolutionModule) :
    tensorRead U hU s hs (PiTensorProduct.tprod ℤ x) =
      ∏ i, trivialF2Equiv U.toSubgroup
        ((trivialF2 U.toSubgroup).gradedResolutionProjection (x i)) := by
  unfold tensorRead
  rw [smoothTensorInducedGradedResolutionProjection_tprod]
  refine (congrArg (fun z ↦ trivialF2Equiv G
    ((smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs)).hom.hom.hom z))
        (smoothTensorInducedTrivialF2Tprod_eq G U.toSubgroup U.isOpen'
          (twoTransversal U hU s hs)
          (fun i ↦ (trivialF2 U.toSubgroup).gradedResolutionProjection (x i)))).symm.trans
    ((smoothTensorInducedTrivialF2Iso_hom_apply_tprod G U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs)
      (fun i ↦ (trivialF2 U.toSubgroup).gradedResolutionProjection (x i))).trans ?_)
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

private theorem tensorRead_twoTensor
    (x y : (trivialF2 U.toSubgroup).gradedResolutionModule) :
    tensorRead U hU s hs (twoTensor U x y) =
      trivialF2Equiv U.toSubgroup ((trivialF2 U.toSubgroup).gradedResolutionProjection x) *
        trivialF2Equiv U.toSubgroup ((trivialF2 U.toSubgroup).gradedResolutionProjection y) := by
  classical
  rw [twoTensor, tensorRead_tprod]
  have hp := Fintype.prod_eq_mul
    (f := fun i : G ⧸ U.toSubgroup ↦ trivialF2Equiv U.toSubgroup
      ((trivialF2 U.toSubgroup).gradedResolutionProjection
        (if i = QuotientGroup.mk 1 then x else y)))
    (QuotientGroup.mk 1) (QuotientGroup.mk s) (mk_ne_mk_one_of_notMem hs).symm
    (fun i hi ↦ ((eq_mk_one_or_eq_mk_of_index_two hU hs i).elim hi.1 hi.2).elim)
  simpa only [mk_ne_mk_one_of_notMem hs, ↓reduceIte] using hp

omit [Fintype (G ⧸ U.toSubgroup)] in
private theorem characterTotal_action (x : U.toSubgroup) :
    (trivialF2 U.toSubgroup).gradedResolutionRepresentation x
        (evensCharacterRepresentative U.toSubgroup α hα) =
      evensCharacterRepresentative U.toSubgroup α hα :=
  ((trivialF2 U.toSubgroup).gradedResolutionTopRep_ρ_apply x _).symm.trans
    (evensCharacterRepresentative_invariant U.toSubgroup α hα x)

omit [Fintype (G ⧸ U.toSubgroup)] in
private theorem projection_action_augmentation (x : U.toSubgroup) (a : (trivialF2 U.toSubgroup).V) :
    (trivialF2 U.toSubgroup).gradedResolutionProjection
        ((trivialF2 U.toSubgroup).gradedResolutionRepresentation x
          ((trivialF2 U.toSubgroup).gradedResolutionAugmentation a)) = a := by
  rw [← TopRep.gradedResolutionAugmentation_equivariant, trivialF2_ρ_apply_apply,
    TopRep.gradedResolutionProjection_augmentation]

omit [Fintype (G ⧸ U.toSubgroup)] in
private theorem projection_action_primitive_action (x y : U.toSubgroup) :
    trivialF2Equiv U.toSubgroup ((trivialF2 U.toSubgroup).gradedResolutionProjection
      ((trivialF2 U.toSubgroup).gradedResolutionRepresentation x
        ((trivialF2 U.toSubgroup).gradedResolutionRepresentation y
          (characterPrimitive U α hα)))) =
      Multiplicative.toAdd (α x) + Multiplicative.toAdd (α y) := by
  rw [← Module.End.mul_apply, ← map_mul, characterPrimitive_projection_action,
    AddEquiv.apply_symm_apply, map_mul, toAdd_mul]

private noncomputable abbrev tensorHomotopy [LinearOrder (G ⧸ U.toSubgroup)] :=
  PiTensorProduct.slotHomotopy (G ⧸ U.toSubgroup)
    ((trivialF2 U.toSubgroup).gradedResolutionAugmentation ∘ₗ
      (trivialF2 U.toSubgroup).gradedResolutionProjection)
    (trivialF2 U.toSubgroup).gradedResolutionHomotopy

private noncomputable abbrev tensorAction :=
  U.toSubgroup.tensorInducedRepresentation (twoTransversal U hU s hs)
    (trivialF2 U.toSubgroup).gradedResolutionRepresentation

private theorem tensorRead_graph [LinearOrder (G ⧸ U.toSubgroup)]
    (hlt : (QuotientGroup.mk 1 : G ⧸ U.toSubgroup) < QuotientGroup.mk s) (g h : G) :
    tensorRead U hU s hs
      (tensorAction U hU s hs h⁻¹ (tensorHomotopy U
        (tensorAction U hU s hs g⁻¹ (tensorHomotopy U
          (PiTensorProduct.tprod ℤ fun _ ↦ evensCharacterRepresentative U.toSubgroup α hα))))) =
      evensGraphCochain U.toSubgroup s α (g, h) := by
  classical
  let := Subgroup.normal_of_index_eq_two hU
  rw [twoTensor_diagonal_homotopy U hU s hs α hα hlt,
    twoTensor_action U hU s hs]
  by_cases hg : g ∈ U
  -- If `g` preserves the cosets, the second homotopy leaves a constant in the first factor.
  · have hgi : g⁻¹ ∈ U := U.inv_mem hg
    rw [ite_eq_left hgi, characterTotal_action,
      twoTensor_slotHomotopy U hU s hs hlt, characterPrimitive_homotopy_action,
      twoTensor_zero_left, zero_add, characterPrimitive_projection_action,
      twoTensor_action U hU s hs]
    by_cases hh : h ∈ U
    · have hhi : h⁻¹ ∈ U := U.inv_mem hh
      rw [ite_eq_left hhi, tensorRead_twoTensor,
        projection_action_augmentation, characterPrimitive_projection_action,
        AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      simp only [← wordValue_def, wordValue_inv, smul_quotient_eq_self_of_mem hg,
        smul_quotient_eq_self_of_mem hh, wordValue_one, wordValue_s,
        evensGraphCochain_of_mem hg]
    · have hhi : h⁻¹ ∉ U := mt U.toSubgroup.inv_mem_iff.mp hh
      rw [ite_eq_right hhi, tensorRead_twoTensor,
        projection_action_augmentation, characterPrimitive_projection_action,
        AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      simp only [← wordValue_def, wordValue_inv, smul_quotient_eq_self_of_mem hg,
        smul_mk_one_of_notMem_of_index_two hU hs hh, wordValue_one, wordValue_s,
        evensGraphCochain_of_mem hg]
      exact mul_comm _ _
  -- If `g` exchanges the cosets, both remaining factors have degree zero. The action of `h`
  -- either preserves their order or exchanges it, giving the same graph branch.
  · have hgi : g⁻¹ ∉ U := mt U.toSubgroup.inv_mem_iff.mp hg
    rw [ite_eq_right hgi, characterTotal_action,
      twoTensor_slotHomotopy U hU s hs hlt, characterTotal_projection,
      map_zero, twoTensor_zero_left, add_zero, twoTensor_action U hU s hs]
    by_cases hh : h ∈ U
    · have hhi : h⁻¹ ∈ U := U.inv_mem hh
      rw [ite_eq_left hhi, tensorRead_twoTensor,
        characterPrimitive_projection_action, AddEquiv.apply_symm_apply,
        projection_action_primitive_action]
      simp only [← wordValue_def, wordValue_inv, smul_quotient_eq_self_of_mem hh,
        smul_mk_of_notMem_of_index_two hU hs hg, wordValue_one, wordValue_s,
        evensGraphCochain_of_notMem hg]
      ring
    · have hhi : h⁻¹ ∉ U := mt U.toSubgroup.inv_mem_iff.mp hh
      rw [ite_eq_right hhi, tensorRead_twoTensor,
        characterPrimitive_projection_action, AddEquiv.apply_symm_apply,
        projection_action_primitive_action]
      simp only [← wordValue_def, wordValue_inv,
        smul_mk_one_of_notMem_of_index_two hU hs hh,
        smul_mk_of_notMem_of_index_two hU hs hh,
        smul_mk_of_notMem_of_index_two hU hs hg, wordValue_one, wordValue_s,
        evensGraphCochain_of_notMem hg]
      ring

variable [CompactSpace U.toSubgroup]

-- These are the same native actions through the smooth/discrete dictionary, but typeclass
-- search does not unfold its carrier presentation before falling back to the integer action.
private noncomputable local instance : Module ℤ
    ((ofSmoothDiscrete ℤ U.toSubgroup).obj
      (smoothGradedResolutionFunctor.obj (characterCoeff U))).V :=
  ((ofSmoothDiscrete ℤ U.toSubgroup).obj
    (smoothGradedResolutionFunctor.obj (characterCoeff U))).module

private noncomputable local instance : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2

omit [Fintype (G ⧸ U.toSubgroup)] in
private theorem tensorAction_smooth [U.toSubgroup.FiniteIndex] (g : G)
    (z : ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs)).obj (characterCoeff U)).obj.V) :
    ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs)).obj (characterCoeff U)).obj.ρ g z =
      tensorAction U hU s hs g z := by
  have hρ : ((ofSmoothDiscrete ℤ U.toSubgroup).obj
      (smoothGradedResolutionFunctor.obj (characterCoeff U))).ρ =
        (trivialF2 U.toSubgroup).gradedResolutionRepresentation := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (ofSmoothDiscrete_obj_ρ_apply ℤ U.toSubgroup _ x y).trans
      ((smoothGradedResolutionFunctor_obj_obj_ρ_apply (characterCoeff U) x y).trans
        ((trivialF2 U.toSubgroup).gradedResolutionTopRep_ρ_apply x y))
  exact (smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply
    U.toSubgroup U.isOpen' (twoTransversal U hU s hs) (characterCoeff U) g z).trans
      (congrArg (fun ρ ↦ U.toSubgroup.tensorInducedRepresentation
        (twoTransversal U hU s hs) ρ g z) hρ)

private noncomputable abbrev tensorContraction [LinearOrder (G ⧸ U.toSubgroup)] :=
  smoothTensorInducedGradedResolutionContraction U.toSubgroup U.isOpen'
    (twoTransversal U hU s hs) (characterCoeff U)
    (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)

attribute [local instance] TopRep.distribMulAction

private theorem tensorContraction_class_graph [LocallyCompactSpace G]
    [LinearOrder (G ⧸ U.toSubgroup)]
    (hlt : (QuotientGroup.mk 1 : G ⧸ U.toSubgroup) < QuotientGroup.mk s)
    {n : ℕ} (hn : n = 2)
    (hz : PiTensorProduct.tprod ℤ
        (fun _ : G ⧸ U.toSubgroup ↦ evensCharacterRepresentative U.toSubgroup α hα) ∈
      smoothTensorInducedGradedResolutionPiece U.toSubgroup U.isOpen'
        (twoTransversal U hU s hs) (characterCoeff U) n)
    (hinv : ∀ g, ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs)).obj (characterCoeff U)).obj.ρ g
        (PiTensorProduct.tprod ℤ fun _ ↦ evensCharacterRepresentative U.toSubgroup α hα) =
          PiTensorProduct.tprod ℤ (fun _ ↦ evensCharacterRepresentative U.toSubgroup α hα))
    (hdz : (smoothTensorInducedGradedResolutionDifferential U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs) (characterCoeff U)).hom.hom
        (PiTensorProduct.tprod ℤ fun _ ↦ evensCharacterRepresentative U.toSubgroup α hα) = 0) :
    ContinuousCohomology.coeffMap
      (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
        (twoTransversal U hU s hs)).hom.hom n
      ((tensorContraction U hU s hs).gradedCohomologyClass _ hz hinv hdz) =
        (eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 G)) hn.symm)).hom
          (graphClass U hU α hα) := by
  subst n
  let B := (toSmoothDiscrete ℤ G).obj
    (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' (twoTransversal U hU s hs)
      ((ofSmoothDiscrete ℤ U.toSubgroup).obj (characterCoeff U)))
  let : ContinuousSMul G B.obj.V := B.property.continuousSMul
  let : ContinuousSMul G (trivialF2 G).V := (isSmoothDiscrete_trivialF2 G).continuousSMul
  let F : B.obj ⟶ trivialF2 G :=
    (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
      (twoTransversal U hU s hs)).hom.hom
  let : Module ℤ B.obj.V := B.obj.hV2
  let f := F.hom.toContinuousLinearMap.toLinearMap.toAddMonoidHom
  have hf (g : G) (a : B.obj.V) :
      f ((ContinuousMonoidHom.id G) g • a) = g • f a :=
    TopRep.hom_comm_apply F g a
  have hF (g : G) (a : B.obj.V) : f (B.obj.ρ g a) = f a :=
    (TopRep.hom_comm_apply F g a).trans (trivialF2_ρ_apply_apply G g _)
  let c := tensorContraction U hU s hs
  refine (congrArg (fun x ↦ ContinuousCohomology.coeffMap F 2 x)
    (c.gradedCohomologyClass_def _ hz hinv hdz)).trans ?_
  rw [← c.explicitH2AddEquivContinuousCohomologyOfDiscrete_explicitCocycle2]
  rw [ContinuousCohomology.coeffMap_def]
  rw [B.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete_map
    (trivialF2 G) (ContinuousMonoidHom.id G) F f (fun _ ↦ rfl) hf]
  rw [explicitMap2_mk]
  simp only [eqToHom_refl, CategoryTheory.id_apply]
  rw [← evensGraphCocycle_class_eq_graphClass U hU s hs α hα]
  apply congrArg (trivialF2 G).explicitH2AddEquivContinuousCohomologyOfDiscrete
  apply congrArg (fun z : Z2 G (trivialF2 G).V ↦ (z : H2 G (trivialF2 G).V))
  apply Subtype.ext
  funext p
  apply (trivialF2Equiv G).injective
  rw [cocyclesMap2_apply, c.explicitCocycle2_apply]
  -- The invariant tensor is carried through the smooth/discrete functor object. Default
  -- transparency recognizes that carrier when applying the public equivariance equation.
  erw [hF]
  simp only [c, tensorContraction, smoothTensorInducedGradedResolutionContraction_proj_apply,
    smoothTensorInducedGradedResolutionContraction_hom_apply,
    TopRep.gradedCochainComplex_ρ_apply, smoothTensorInducedGradedResolutionHomotopy_def,
    coe_evensGraphCocycle, AddEquiv.apply_symm_apply, ContinuousMonoidHom.coe_id, id_eq]
  -- The smooth/discrete functor-object carrier is definitionally the tensor-product carrier
  -- used by `tensorAction_smooth`; default transparency exposes it for both action rewrites.
  erw [TopRep.gradedCochainComplexInvariant_val, tensorAction_smooth, tensorAction_smooth]
  exact tensorRead_graph U hU s hs α hα hlt p.1 p.2

/-- The tensor-induced class of the homogeneous degree-one cocycle of a continuous character is
the index-two graph class. The transversal has representatives `1` and `s`, and the coefficient
identification multiplies the two tensor factors. The equality includes only the transport of
degrees from `2` to `card (G ⧸ U) * 1`.

The quotient `Fintype` is a caller parameter: the diagonal class and its graded contraction use
that enumeration. The input `z` and its cocycle data are exactly the inputs of
`smoothTensorInducedDiagonalClass`; `hzα` identifies their explicit homogeneous representative.
The theorem compares the classes associated to this explicit homogeneous representative. The
statement installs local compactness from the compact open subgroup because the existing
`graphClass` requires it. -/
theorem smoothTensorInducedDiagonalClass_eq_graphClass
    (z : (trivialF2 U.toSubgroup).gradedResolutionModule)
    (hz : z ∈ (trivialF2 U.toSubgroup).gradedResolutionPiece 1)
    (hinv : ∀ x, (trivialF2 U.toSubgroup).gradedResolutionTopRep.ρ x z = z)
    (hdz : (trivialF2 U.toSubgroup).gradedResolutionDifferential z = 0)
    (hzα : z = DirectSum.lof ℤ ℕ
      (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V) 1
        (inhomogeneousCochain1 (fun x ↦ Multiplicative.toAdd (α x))
          (continuous_toAdd.comp hα)).val) :
    letI : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    letI : LocallyCompactSpace G :=
      (isCompact_iff_compactSpace.2
        ‹CompactSpace U.toSubgroup›).locallyCompactSpace_of_mem_nhds_of_group
        (U.isOpen'.mem_nhds U.one_mem)
    let t : U.toSubgroup.LeftTransversal :=
      ⟨Set.range (U.toSubgroup.indexTwoTransversal s),
        Subgroup.isComplement_range_left (Subgroup.indexTwoTransversal_mk hU hs)⟩
    let A : SmoothDiscreteTopRep ℤ U.toSubgroup :=
      ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
    ContinuousCohomology.coeffMap
      (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' t).hom.hom
        (Fintype.card (G ⧸ U.toSubgroup) * 1)
      (smoothTensorInducedDiagonalClass U.toSubgroup U.isOpen' t A
        (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
        z hz hinv hdz) =
      (eqToHom (congrArg (fun n ↦ continuousCohomology n (trivialF2 G))
        (by simpa only [Subgroup.index_eq_card, Nat.card_eq_fintype_card, mul_one]
          using hU.symm : 2 = Fintype.card (G ⧸ U.toSubgroup) * 1))).hom
        (graphClass U hU α hα) := by
  classical
  let : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2
      ‹CompactSpace U.toSubgroup›).locallyCompactSpace_of_mem_nhds_of_group
      (U.isOpen'.mem_nhds U.one_mem)
  dsimp only
  let e : G ⧸ U.toSubgroup → Bool := fun i ↦ if i = QuotientGroup.mk 1 then false else true
  have he : Function.Injective e := by
    intro i j hij
    rcases eq_mk_one_or_eq_mk_of_index_two hU hs i with rfl | rfl <;>
      rcases eq_mk_one_or_eq_mk_of_index_two hU hs j with rfl | rfl <;>
        simp_all [e, mk_ne_mk_one_of_notMem hs]
  let : LinearOrder (G ⧸ U.toSubgroup) := LinearOrder.lift' e he
  have hlt : (QuotientGroup.mk 1 : G ⧸ U.toSubgroup) < QuotientGroup.mk s := by
    -- This order was transported through `e`, so comparing cosets compares their two labels.
    change e (QuotientGroup.mk 1) < e (QuotientGroup.mk s)
    simp [e, mk_ne_mk_one_of_notMem hs]
  have hzα' : z = evensCharacterRepresentative U.toSubgroup α hα :=
    hzα.trans (evensCharacterRepresentative_def U.toSubgroup α hα).symm
  clear hzα
  subst z
  rw [smoothTensorInducedDiagonalClass_eq]
  exact tensorContraction_class_graph U hU s hs α hα hlt
    (by simpa only [Subgroup.index_eq_card, Nat.card_eq_fintype_card, mul_one] using hU)
    _ _ _

end TensorRead

end TauCeti.ContCohomology
