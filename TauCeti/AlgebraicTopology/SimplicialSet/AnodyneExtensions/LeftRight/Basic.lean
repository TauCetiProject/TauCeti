/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Left and right fibrations, left and right anodyne extensions

A *left horn* is a horn `Λ[n, i] ⊆ Δ[n]` with `i < n`, i.e. one missing a face other than the
last one, and a *right horn* is one with `0 < i`. A morphism of simplicial sets is a
*left fibration* (resp. a *right fibration*) when it has the right lifting property with respect
to the left (resp. right) horn inclusions, and a *left anodyne extension* (resp. *right anodyne
extension*) when it has the left lifting property with respect to all left (resp. right)
fibrations.

Inner horns are both left and right horns, and left and right horns are horns of positive
dimension, so every Kan fibration is a left and a right fibration, and both are inner
fibrations; in particular, by Mathlib's `SSet.quasicategory_of_innerFibration`, the total space
of a left or right fibration over a quasicategory is a quasicategory. Left and right fibrations
are the covariant and contravariant models of space-valued functors on their base. For instance,
the projections from the coslices and slices of a quasicategory to it are left and right
fibrations, and they underlie the Yoneda embedding, the theory of final maps and straightening.

As for Mathlib's inner anodyne extensions, the small object argument identifies left (resp.
right) anodyne extensions with the retracts of transfinite compositions of pushouts of
coproducts of left (resp. right) horn inclusions. A regular pairing of a subcomplex in the sense
of Moss whose type (II) simplices are never the last (resp. first) face of their partners gives
a left (resp. right) anodyne extension (`SSet.Subcomplex.Pairing.leftAnodyneExtensions`,
`SSet.Subcomplex.Pairing.rightAnodyneExtensions`).

## Main definitions

* `SSet.leftHornInclusions`, `SSet.rightHornInclusions`: the left and right horn inclusions.
* `SSet.leftFibrations`, `SSet.rightFibrations`, with the classes `SSet.LeftFibration` and
  `SSet.RightFibration`.
* `SSet.leftAnodyneExtensions`, `SSet.rightAnodyneExtensions`.

## References

* J. Lurie, *Higher Topos Theory*, Definition 2.0.0.3 and Section 2.1.2.
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty Limits

open scoped Simplicial

namespace SSet

/-- The left horn inclusions `Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]`, for `0 < n` and `i < n`. -/
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
    leftHornInclusions Λ[n + 1, i].ι

/-- The right horn inclusions `Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]`, for `0 < i ≤ n`. -/
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) :
    rightHornInclusions Λ[n + 1, i].ι

lemma horn_ι_mem_leftHornInclusions {n : ℕ} {i : Fin (n + 1)} (hn : i < Fin.last n) :
    leftHornInclusions (horn.{u} n i).ι := by
  obtain _ | n := n
  · grind
  · exact ⟨i, hn⟩

lemma horn_ι_mem_rightHornInclusions {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) :
    rightHornInclusions (horn.{u} n i).ι := by
  obtain _ | n := n
  · grind
  · exact ⟨i, h0⟩

lemma leftHornInclusions_eq_iSup :
    leftHornInclusions.{u} =
      ⨆ n, .ofHoms (fun p : {p : Fin (n + 2) // p < Fin.last (n + 1)} ↦ Λ[n + 1, p].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    exact ⟨n, i, hn, rfl⟩
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, hn⟩, _, _⟩ := h
    exact horn_ι_mem_leftHornInclusions hn

lemma rightHornInclusions_eq_iSup :
    rightHornInclusions.{u} =
      ⨆ n, .ofHoms (fun p : {p : Fin (n + 2) // 0 < p} ↦ Λ[n + 1, p].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, h0⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    exact ⟨n, i, h0, rfl⟩
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, h0⟩, _, _⟩ := h
    exact horn_ι_mem_rightHornInclusions h0

lemma innerHornInclusions_le_leftHornInclusions :
    innerHornInclusions.{u} ≤ leftHornInclusions :=
  fun _ _ _ ⟨_, _, hn⟩ ↦ horn_ι_mem_leftHornInclusions hn

lemma innerHornInclusions_le_rightHornInclusions :
    innerHornInclusions.{u} ≤ rightHornInclusions :=
  fun _ _ _ ⟨_, h0, _⟩ ↦ horn_ι_mem_rightHornInclusions h0

lemma leftHornInclusions_le_J : leftHornInclusions.{u} ≤ modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _⟩ ↦ modelCategoryQuillen.horn_ι_mem_J ..

lemma rightHornInclusions_le_J : rightHornInclusions.{u} ≤ modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _⟩ ↦ modelCategoryQuillen.horn_ι_mem_J ..

/-- The left fibrations are the morphisms which have the right lifting property with respect to
the left horn inclusions `Λ[n, i] ⟶ Δ[n]`, `i < n`. -/
def leftFibrations : MorphismProperty SSet.{u} := leftHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange, IsStableUnderRetracts

/-- The right fibrations are the morphisms which have the right lifting property with respect to
the right horn inclusions `Λ[n, i] ⟶ Δ[n]`, `0 < i`. -/
def rightFibrations : MorphismProperty SSet.{u} := rightHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange, IsStableUnderRetracts

lemma leftFibrations_eq_rlp : leftFibrations.{u} = leftHornInclusions.rlp :=
  (rfl)

lemma rightFibrations_eq_rlp : rightFibrations.{u} = rightHornInclusions.rlp :=
  (rfl)

/-- A morphism `p` satisfies `[LeftFibration p]` if it belongs to `leftFibrations`. -/
@[mk_iff]
class LeftFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : leftFibrations p

/-- A morphism `p` satisfies `[RightFibration p]` if it belongs to `rightFibrations`. -/
@[mk_iff]
class RightFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : rightFibrations p

lemma mem_leftFibrations {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] : leftFibrations p :=
  LeftFibration.mem

lemma mem_rightFibrations {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    rightFibrations p :=
  RightFibration.mem

lemma leftFibration_iff_hasLiftingProperty {X Y : SSet.{u}} (p : X ⟶ Y) :
    LeftFibration p ↔
      ∀ ⦃n : ℕ⦄ (i : Fin (n + 1)), i < Fin.last n → HasLiftingProperty Λ[n, i].ι p := by
  rw [leftFibration_iff]
  exact ⟨fun h _ _ hn ↦ h _ (horn_ι_mem_leftHornInclusions hn), fun h _ _ _ ⟨i, hn⟩ ↦ h i hn⟩

lemma rightFibration_iff_hasLiftingProperty {X Y : SSet.{u}} (p : X ⟶ Y) :
    RightFibration p ↔
      ∀ ⦃n : ℕ⦄ (i : Fin (n + 1)), 0 < i → HasLiftingProperty Λ[n, i].ι p := by
  rw [rightFibration_iff]
  exact ⟨fun h _ _ h0 ↦ h _ (horn_ι_mem_rightHornInclusions h0), fun h _ _ _ ⟨i, h0⟩ ↦ h i h0⟩

section

variable {X Y Z : SSet.{u}}

instance (p : X ⟶ Y) [IsIso p] : LeftFibration p := ⟨of_isIso _ _⟩

instance (p : X ⟶ Y) [IsIso p] : RightFibration p := ⟨of_isIso _ _⟩

instance (p : X ⟶ Y) (q : Y ⟶ Z) [LeftFibration p] [LeftFibration q] :
    LeftFibration (p ≫ q) :=
  ⟨comp_mem _ _ _ (mem_leftFibrations p) (mem_leftFibrations q)⟩

instance (p : X ⟶ Y) (q : Y ⟶ Z) [RightFibration p] [RightFibration q] :
    RightFibration (p ≫ q) :=
  ⟨comp_mem _ _ _ (mem_rightFibrations p) (mem_rightFibrations q)⟩

/-- Left fibrations are stable under base change. -/
lemma LeftFibration.of_isPullback {X' Y' : SSet.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {f : X' ⟶ X} {g : Y' ⟶ Y} (h : IsPullback f p' p g) [LeftFibration p] :
    LeftFibration p' :=
  ⟨leftFibrations.of_isPullback h (mem_leftFibrations p)⟩

/-- Right fibrations are stable under base change. -/
lemma RightFibration.of_isPullback {X' Y' : SSet.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {f : X' ⟶ X} {g : Y' ⟶ Y} (h : IsPullback f p' p g) [RightFibration p] :
    RightFibration p' :=
  ⟨rightFibrations.of_isPullback h (mem_rightFibrations p)⟩

open modelCategoryQuillen in
/-- Kan fibrations are left fibrations. -/
instance (p : X ⟶ Y) [Fibration p] : LeftFibration p :=
  ⟨antitone_rlp leftHornInclusions_le_J _ ((modelCategoryQuillen.fibration_iff p).1 ‹_›)⟩

open modelCategoryQuillen in
/-- Kan fibrations are right fibrations. -/
instance (p : X ⟶ Y) [Fibration p] : RightFibration p :=
  ⟨antitone_rlp rightHornInclusions_le_J _ ((modelCategoryQuillen.fibration_iff p).1 ‹_›)⟩

/-- Left fibrations are inner fibrations. -/
instance (p : X ⟶ Y) [LeftFibration p] : InnerFibration p :=
  ⟨antitone_rlp innerHornInclusions_le_leftHornInclusions _ (mem_leftFibrations p)⟩

/-- Right fibrations are inner fibrations. -/
instance (p : X ⟶ Y) [RightFibration p] : InnerFibration p :=
  ⟨antitone_rlp innerHornInclusions_le_rightHornInclusions _ (mem_rightFibrations p)⟩

end

/-- In the category of simplicial sets, a *left anodyne extension* is a morphism that has the left
lifting property with respect to left fibrations. -/
def leftAnodyneExtensions : MorphismProperty SSet.{u} := leftFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition, IsStableUnderCoproducts

/-- In the category of simplicial sets, a *right anodyne extension* is a morphism that has the left
lifting property with respect to right fibrations. -/
def rightAnodyneExtensions : MorphismProperty SSet.{u} := rightFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition, IsStableUnderCoproducts

lemma leftAnodyneExtensions_eq_llp :
    leftAnodyneExtensions.{u} = leftFibrations.llp :=
  (rfl)

lemma rightAnodyneExtensions_eq_llp :
    rightAnodyneExtensions.{u} = rightFibrations.llp :=
  (rfl)

lemma leftAnodyneExtensions_eq_llp_rlp :
    leftAnodyneExtensions.{u} = leftHornInclusions.rlp.llp :=
  (rfl)

lemma rightAnodyneExtensions_eq_llp_rlp :
    rightAnodyneExtensions.{u} = rightHornInclusions.rlp.llp :=
  (rfl)

lemma leftAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)} (hn : i < Fin.last n) :
    leftAnodyneExtensions.{u} Λ[n, i].ι :=
  le_llp_rlp _ _ (horn_ι_mem_leftHornInclusions hn)

lemma rightAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) :
    rightAnodyneExtensions.{u} Λ[n, i].ι :=
  le_llp_rlp _ _ (horn_ι_mem_rightHornInclusions h0)

lemma leftAnodyneExtensions.hasLiftingProperty {A B X Y : SSet.{u}} {i : A ⟶ B}
    (hi : leftAnodyneExtensions i) (p : X ⟶ Y) [LeftFibration p] : HasLiftingProperty i p :=
  hi _ (mem_leftFibrations p)

lemma rightAnodyneExtensions.hasLiftingProperty {A B X Y : SSet.{u}} {i : A ⟶ B}
    (hi : rightAnodyneExtensions i) (p : X ⟶ Y) [RightFibration p] : HasLiftingProperty i p :=
  hi _ (mem_rightFibrations p)

lemma innerAnodyneExtensions_le_leftAnodyneExtensions :
    innerAnodyneExtensions.{u} ≤ leftAnodyneExtensions :=
  antitone_llp (antitone_rlp innerHornInclusions_le_leftHornInclusions)

lemma innerAnodyneExtensions_le_rightAnodyneExtensions :
    innerAnodyneExtensions.{u} ≤ rightAnodyneExtensions :=
  antitone_llp (antitone_rlp innerHornInclusions_le_rightHornInclusions)

lemma leftAnodyneExtensions_le_anodyneExtensions :
    leftAnodyneExtensions.{u} ≤ anodyneExtensions :=
  antitone_llp (antitone_rlp leftHornInclusions_le_J)

lemma rightAnodyneExtensions_le_anodyneExtensions :
    rightAnodyneExtensions.{u} ≤ anodyneExtensions :=
  antitone_llp (antitone_rlp rightHornInclusions_le_J)

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} leftHornInclusions.{u} := by
  rw [leftHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u}
        fun p : {p : Fin (n + 2) // p < Fin.last (n + 1)} ↦ Λ[n + 1, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : MorphismProperty.IsSmall.{u} rightHornInclusions.{u} := by
  rw [rightHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u} fun p : {p : Fin (n + 2) // 0 < p} ↦ Λ[n + 1, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument leftHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [leftHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : IsCardinalForSmallObjectArgument rightHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [rightHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} leftHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

instance : HasSmallObjectArgument.{u} rightHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- Left anodyne extensions are the retracts of transfinite compositions of pushouts of
coproducts of left horn inclusions. -/
lemma leftAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    leftAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} leftHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [leftAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- Right anodyne extensions are the retracts of transfinite compositions of pushouts of
coproducts of right horn inclusions. -/
lemma rightAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    rightAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} rightHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [rightAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

namespace Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing) [P.IsRegular]

/-- The inclusion of a subcomplex admitting a regular pairing in which no type (II) simplex is the
last face of the corresponding type (I) simplex is a left anodyne extension. -/
lemma leftAnodyneExtensions
    (hP : ∀ (x : P.II) {d : ℕ} (hd : x.1.dim = d),
      (P.isUniquelyCodimOneFace x).index hd ≠ Fin.last _) :
    SSet.leftAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact .horn_ι (Fin.lt_last_iff_ne_last.mpr (hP c.s rfl))⟩

/-- The inclusion of a subcomplex admitting a regular pairing in which no type (II) simplex is the
first face of the corresponding type (I) simplex is a right anodyne extension. -/
lemma rightAnodyneExtensions
    (hP : ∀ (x : P.II) {d : ℕ} (hd : x.1.dim = d), (P.isUniquelyCodimOneFace x).index hd ≠ 0) :
    SSet.rightAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact .horn_ι (Fin.pos_iff_ne_zero.mpr (hP c.s rfl))⟩

end Subcomplex.Pairing

end SSet
