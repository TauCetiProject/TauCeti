/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Injective

/-!
# The Ext-trivial ideals of an exact category

For an exact structure `E`, a morphism `f : X ⟶ Y` is *projectively trivial* when it kills
`Ext¹` from the left, `f^* = 0 : Ext¹_E(Y, W) → Ext¹_E(X, W)` for every object `W`, and
*injectively trivial* when it kills `Ext¹` from the right, `f_* = 0 : Ext¹_E(W, X) → Ext¹_E(W, Y)`
for every `W`. These morphisms form two-sided ideals `𝒫_E` and `ℐ_E` of the category, and the
quotients `E/𝒫_E` and `E/ℐ_E` are the categories between which an Auslander–Reiten duality is an
equivalence, in exact categories that need not have enough projectives or injectives.

By exactness of the `Hom`–`Ext` sequences at `Hom(X, Y)`, `f` is projectively trivial exactly when
it factors through every deflation onto `Y`, and injectively trivial exactly when it extends
across every inflation out of `X`. The ideals are defined by these lifting and extension
properties, and the `Ext¹` descriptions are theorems. The lifting description compares them with
the ideals of morphisms factoring through relative projectives and relative injectives: those lie
in `𝒫_E` and `ℐ_E` respectively, with equality when `E` has enough relative projectives,
respectively injectives. In that case `E/𝒫_E` is the projective stable category
`TauCeti.ExactStructure.ProjectiveStableCategory`, and `E/ℐ_E` the injective stable category
`TauCeti.ExactStructure.InjectiveStableCategory`. In general an object `X` is relatively projective
exactly when its identity is projectively trivial, that is, when `Ext¹_E(X, -)` vanishes; dually
for relative injectives.

## Main definitions

* `TauCeti.ExactStructure.projectivelyTrivialIdeal E`: the ideal `𝒫_E` of the morphisms that
  factor through every deflation onto their target.
* `TauCeti.ExactStructure.injectivelyTrivialIdeal E`: the ideal `ℐ_E` of the morphisms that extend
  across every inflation out of their source.

## Main results

* `TauCeti.ExactStructure.mem_projectivelyTrivialIdeal_iff_forall_ext1` and
  `TauCeti.ExactStructure.mem_injectivelyTrivialIdeal_iff_forall_ext1`: `f ∈ 𝒫_E` exactly when
  `f^* = 0` on `Ext¹_E(-, W)` for every `W`, and `f ∈ ℐ_E` exactly when `f_* = 0` on
  `Ext¹_E(W, -)` for every `W`.
* `TauCeti.ExactStructure.projectiveStableIdeal_le_projectivelyTrivialIdeal` and
  `TauCeti.ExactStructure.EnoughProjectives.projectivelyTrivialIdeal_eq`: a morphism factoring
  through a relative projective is projectively trivial, and conversely with enough projectives.
* `TauCeti.ExactStructure.injectiveStableIdeal_le_injectivelyTrivialIdeal` and
  `TauCeti.ExactStructure.EnoughInjectives.injectivelyTrivialIdeal_eq`: the dual statements.
* `TauCeti.ExactStructure.isProjective_iff_forall_ext1_eq_zero` and
  `TauCeti.ExactStructure.isInjective_iff_forall_ext1_eq_zero`: relative projectives and
  injectives are detected by the vanishing of `Ext¹`.
* For the split exact structure both ideals are the ideal of all morphisms.

## References

* Osamu Iyama, Hiroyuki Nakaoka, Yann Palu, *Auslander–Reiten theory in extriangulated
  categories*, <https://arxiv.org/abs/1805.03776> (v3). Definition 1.21 and Remark 1.22 define the
  two ideals, there for extriangulated categories.
* Haruhisa Enomoto, *Classifications of exact structures and Cohen–Macaulay-finite algebras*,
  Adv. Math. **335** (2018), 838–877, <https://arxiv.org/abs/1705.02163>. Section A.2 treats the
  Ext-trivial morphisms of an exact category.
* Helmut Lenzing, Rosa Zuazua, *Auslander–Reiten duality for abelian categories*, Bol. Soc. Mat.
  Mexicana (3) **10** (2004), 169–177, Section 2, for projectively and injectively trivial
  morphisms of an abelian category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {X Y : C}

/-! ### Projectively trivial morphisms -/

variable (E) in
/-- The ideal `𝒫_E` of **projectively trivial** morphisms: the `f : X ⟶ Y` that factor through
every deflation onto `Y`. Equivalently, the base change `f^* : Ext¹_E(Y, W) → Ext¹_E(X, W)` is
zero for every object `W`
(`TauCeti.ExactStructure.mem_projectivelyTrivialIdeal_iff_forall_ext1`). -/
def projectivelyTrivialIdeal : MorphismIdeal C where
  hom X Y :=
    { carrier := {f | ∀ ⦃Y' : C⦄ {p : Y' ⟶ Y}, E.IsDeflation p → ∃ t : X ⟶ Y', t ≫ p = f}
      zero_mem' := fun _ _ _ ↦ ⟨0, zero_comp⟩
      add_mem' := fun ha hb _ _ hp ↦
        have ⟨s, hs⟩ := ha hp
        have ⟨t, ht⟩ := hb hp
        ⟨s + t, by rw [Preadditive.add_comp, hs, ht]⟩
      neg_mem' := fun ha _ _ hp ↦
        have ⟨s, hs⟩ := ha hp
        ⟨-s, by rw [Preadditive.neg_comp, hs]⟩ }
  comp_mem_left f g hg _ _ hp :=
    have ⟨t, ht⟩ := hg hp
    ⟨f ≫ t, by rw [Category.assoc, ht]⟩
  comp_mem_right g hf _ q hq := by
    obtain ⟨K, i, zero, hc⟩ := (E.isDeflation_iff q).mp hq
    let e : E.Extension _ K := ⟨_, i, q, zero, hc⟩
    obtain ⟨t, ht⟩ := hf (E.isDeflation_g (e.pullback g).conflation)
    exact ⟨t ≫ e.pullbackFst g, by rw [Category.assoc, e.pullbackFst_g, reassoc_of% ht]⟩

/-- A morphism is projectively trivial when it factors through every deflation onto its
target. -/
@[simp]
theorem mem_projectivelyTrivialIdeal_iff {f : X ⟶ Y} :
    f ∈ E.projectivelyTrivialIdeal.hom X Y ↔
      ∀ ⦃Y' : C⦄ {p : Y' ⟶ Y}, E.IsDeflation p → ∃ t : X ⟶ Y', t ≫ p = f :=
  Iff.rfl

/-- **The `Ext¹` description of `𝒫_E`.** A morphism `f : X ⟶ Y` is projectively trivial exactly
when its base change `f^* : Ext¹_E(Y, W) → Ext¹_E(X, W)` vanishes for every `W`. This is the
exactness of `Hom(X, Y') → Hom(X, Y) → Ext¹_E(X, K)` for every conflation `K ⟶ Y' ⟶ Y`. -/
theorem mem_projectivelyTrivialIdeal_iff_forall_ext1 {f : X ⟶ Y} :
    f ∈ E.projectivelyTrivialIdeal.hom X Y ↔ ∀ (W : C) (ξ : E.Ext1 Y W), ξ.pullback f = 0 := by
  refine ⟨fun h W ξ ↦ ?_, fun h Y' p hp ↦ ?_⟩
  · induction ξ using Ext1.induction with
    | h e => exact (Ext1.mk_pullback_eq_zero_iff e f).mpr (h (E.isDeflation_g e.conflation))
  · obtain ⟨K, i, zero, hc⟩ := (E.isDeflation_iff p).mp hp
    exact (Ext1.mk_pullback_eq_zero_iff ⟨Y', i, p, zero, hc⟩ f).mp (h K _)

/-- A morphism factoring through a relative projective is projectively trivial. -/
theorem projectiveStableIdeal_le_projectivelyTrivialIdeal :
    E.projectiveStableIdeal ≤ E.projectivelyTrivialIdeal := by
  refine MorphismIdeal.le_def.mpr fun X Y f hf ↦ ?_
  obtain ⟨Q, hQ, i, p, rfl⟩ :=
    (ObjectProperty.factorsThrough_iff _ _).mp ((mem_projectiveStableIdeal_iff E).mp hf)
  exact mem_projectivelyTrivialIdeal_iff.mpr fun _ q hq ↦
    ⟨i ≫ hQ.factorThru hq p, by simp⟩

/-- **With enough relative projectives, the projectively trivial morphisms are those factoring
through a relative projective**, so that `E/𝒫_E` is the projective stable category. -/
theorem EnoughProjectives.projectivelyTrivialIdeal_eq (h : E.EnoughProjectives) :
    E.projectivelyTrivialIdeal = E.projectiveStableIdeal := by
  refine le_antisymm (MorphismIdeal.le_def.mpr fun X Y f hf ↦ ?_)
    projectiveStableIdeal_le_projectivelyTrivialIdeal
  let P := h.projectivePresentation Y
  obtain ⟨t, ht⟩ := mem_projectivelyTrivialIdeal_iff.mp hf (E.isDeflation_g P.conflation)
  rw [mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  exact ⟨P.P, P.isProjective, t, P.p, ht.symm⟩

/-- **An object is relatively projective exactly when its identity is projectively trivial.** -/
@[simp high]
theorem id_mem_projectivelyTrivialIdeal_iff (X : C) :
    𝟙 X ∈ E.projectivelyTrivialIdeal.hom X X ↔ E.isProjective X := by
  refine ⟨fun h ↦ isProjective_iff.mpr fun Y' Y p hp g ↦ ?_, fun hX ↦ ?_⟩
  · have hg := E.projectivelyTrivialIdeal.comp_mem_right g h
    rw [Category.id_comp] at hg
    exact mem_projectivelyTrivialIdeal_iff.mp hg hp
  · refine MorphismIdeal.le_def.mp projectiveStableIdeal_le_projectivelyTrivialIdeal _ ?_
    rw [mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
    exact ⟨X, hX, 𝟙 X, 𝟙 X, by simp⟩

/-- **An object `X` is relatively projective exactly when `Ext¹_E(X, -)` vanishes.** -/
theorem isProjective_iff_forall_ext1_eq_zero (X : C) :
    E.isProjective X ↔ ∀ (W : C) (ξ : E.Ext1 X W), ξ = 0 := by
  rw [← id_mem_projectivelyTrivialIdeal_iff, mem_projectivelyTrivialIdeal_iff_forall_ext1]
  simp only [Ext1.pullback_id]

/-! ### Injectively trivial morphisms -/

variable (E) in
/-- The ideal `ℐ_E` of **injectively trivial** morphisms: the `f : X ⟶ Y` that extend across
every inflation out of `X`. Equivalently, the cobase change `f_* : Ext¹_E(W, X) → Ext¹_E(W, Y)`
is zero for every object `W`
(`TauCeti.ExactStructure.mem_injectivelyTrivialIdeal_iff_forall_ext1`). -/
def injectivelyTrivialIdeal : MorphismIdeal C where
  hom X Y :=
    { carrier := {f | ∀ ⦃X' : C⦄ {i : X ⟶ X'}, E.IsInflation i → ∃ t : X' ⟶ Y, i ≫ t = f}
      zero_mem' := fun _ _ _ ↦ ⟨0, comp_zero⟩
      add_mem' := fun ha hb _ _ hi ↦
        have ⟨s, hs⟩ := ha hi
        have ⟨t, ht⟩ := hb hi
        ⟨s + t, by rw [Preadditive.comp_add, hs, ht]⟩
      neg_mem' := fun ha _ _ hi ↦
        have ⟨s, hs⟩ := ha hi
        ⟨-s, by rw [Preadditive.comp_neg, hs]⟩ }
  comp_mem_left f g hg _ j hj := by
    obtain ⟨Z, p, zero, hc⟩ := (E.isInflation_iff j).mp hj
    let e : E.Extension Z _ := ⟨_, j, p, zero, hc⟩
    obtain ⟨t, ht⟩ := hg (E.isInflation_f (e.pushout f).conflation)
    exact ⟨e.pushoutInl f ≫ t, by rw [e.f_pushoutInl_assoc, ht]⟩
  comp_mem_right g hf _ _ hi :=
    have ⟨t, ht⟩ := hf hi
    ⟨t ≫ g, by rw [← Category.assoc, ht]⟩

/-- A morphism is injectively trivial when it extends across every inflation out of its
source. -/
@[simp]
theorem mem_injectivelyTrivialIdeal_iff {f : X ⟶ Y} :
    f ∈ E.injectivelyTrivialIdeal.hom X Y ↔
      ∀ ⦃X' : C⦄ {i : X ⟶ X'}, E.IsInflation i → ∃ t : X' ⟶ Y, i ≫ t = f :=
  Iff.rfl

/-- **The `Ext¹` description of `ℐ_E`.** A morphism `f : X ⟶ Y` is injectively trivial exactly
when its cobase change `f_* : Ext¹_E(W, X) → Ext¹_E(W, Y)` vanishes for every `W`. This is the
exactness of `Hom(X', Y) → Hom(X, Y) → Ext¹_E(Z, Y)` for every conflation `X ⟶ X' ⟶ Z`. -/
theorem mem_injectivelyTrivialIdeal_iff_forall_ext1 {f : X ⟶ Y} :
    f ∈ E.injectivelyTrivialIdeal.hom X Y ↔ ∀ (W : C) (ξ : E.Ext1 W X), ξ.pushout f = 0 := by
  refine ⟨fun h W ξ ↦ ?_, fun h X' i hi ↦ ?_⟩
  · induction ξ using Ext1.induction with
    | h e => exact (Ext1.mk_pushout_eq_zero_iff e f).mpr (h (E.isInflation_f e.conflation))
  · obtain ⟨Z, p, zero, hc⟩ := (E.isInflation_iff i).mp hi
    exact (Ext1.mk_pushout_eq_zero_iff ⟨X', i, p, zero, hc⟩ f).mp (h Z _)

/-- A morphism factoring through a relative injective is injectively trivial. -/
theorem injectiveStableIdeal_le_injectivelyTrivialIdeal :
    E.injectiveStableIdeal ≤ E.injectivelyTrivialIdeal := by
  refine MorphismIdeal.le_def.mpr fun X Y f hf ↦ ?_
  obtain ⟨I, hI, a, b, rfl⟩ :=
    (ObjectProperty.factorsThrough_iff _ _).mp ((mem_injectiveStableIdeal_iff E).mp hf)
  exact mem_injectivelyTrivialIdeal_iff.mpr fun _ i hi ↦
    ⟨hI.factorThru hi a ≫ b, by simp⟩

/-- **With enough relative injectives, the injectively trivial morphisms are those factoring
through a relative injective**, so that `E/ℐ_E` is the injective stable category. -/
theorem EnoughInjectives.injectivelyTrivialIdeal_eq (h : E.EnoughInjectives) :
    E.injectivelyTrivialIdeal = E.injectiveStableIdeal := by
  refine le_antisymm (MorphismIdeal.le_def.mpr fun X Y f hf ↦ ?_)
    injectiveStableIdeal_le_injectivelyTrivialIdeal
  let P := h.injectivePresentation X
  rw [mem_injectiveStableIdeal_iff,
    E.factorsThrough_injective_iff_exists_extension P.i (E.isInflation_f P.conflation)
      P.isInjective]
  exact mem_injectivelyTrivialIdeal_iff.mp hf (E.isInflation_f P.conflation)

/-- **An object is relatively injective exactly when its identity is injectively trivial.** -/
@[simp high]
theorem id_mem_injectivelyTrivialIdeal_iff (X : C) :
    𝟙 X ∈ E.injectivelyTrivialIdeal.hom X X ↔ E.isInjective X := by
  refine ⟨fun h ↦ isInjective_iff.mpr fun Y Y' i hi g ↦ ?_, fun hX ↦ ?_⟩
  · have hg := E.injectivelyTrivialIdeal.comp_mem_left g h
    rw [Category.comp_id] at hg
    exact mem_injectivelyTrivialIdeal_iff.mp hg hi
  · refine MorphismIdeal.le_def.mp injectiveStableIdeal_le_injectivelyTrivialIdeal _ ?_
    rw [mem_injectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
    exact ⟨X, hX, 𝟙 X, 𝟙 X, by simp⟩

/-- **An object `X` is relatively injective exactly when `Ext¹_E(-, X)` vanishes.** -/
theorem isInjective_iff_forall_ext1_eq_zero (X : C) :
    E.isInjective X ↔ ∀ (W : C) (ξ : E.Ext1 W X), ξ = 0 := by
  rw [← id_mem_injectivelyTrivialIdeal_iff, mem_injectivelyTrivialIdeal_iff_forall_ext1]
  simp only [Ext1.pushout_id]

/-! ### The split exact structure -/

/-- For the split exact structure every morphism is projectively trivial, since every `Ext¹`
vanishes. -/
@[simp]
theorem split_projectivelyTrivialIdeal :
    (ExactStructure.split C).projectivelyTrivialIdeal = ⊤ :=
  eq_top_iff.mpr <| MorphismIdeal.le_def.mpr fun _ _ _ _ ↦
    mem_projectivelyTrivialIdeal_iff_forall_ext1.mpr fun _ _ ↦ Subsingleton.elim _ _

/-- For the split exact structure every morphism is injectively trivial, since every `Ext¹`
vanishes. -/
@[simp]
theorem split_injectivelyTrivialIdeal :
    (ExactStructure.split C).injectivelyTrivialIdeal = ⊤ :=
  eq_top_iff.mpr <| MorphismIdeal.le_def.mpr fun _ _ _ _ ↦
    mem_injectivelyTrivialIdeal_iff_forall_ext1.mpr fun _ _ ↦ Subsingleton.elim _ _

end ExactStructure

end TauCeti
