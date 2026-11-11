/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject

/-!
# Monomorphisms as transfinite compositions of enlargements

Let `C` be a Grothendieck abelian category, `X : C`, and `W` a class of morphisms of `C`. Suppose
that a property `Q` of subobjects of `X` holds for `⊤` and is preserved under suprema of directed
families, and that every proper subobject `A` of `X` satisfying `Q` is contained in a strictly
larger subobject `A'` satisfying `Q` such that the inclusion `A ⟶ A'` belongs to `W`. Then every
monomorphism `f : A ⟶ X` whose subobject satisfies `Q` is a transfinite composition of morphisms
in `W` (`CategoryTheory.IsGrothendieckAbelian.IsEnlargeable.exists_transfiniteCompositionOfShape`).

The subobjects are enlarged by transfinite iteration, taking suprema at limit stages; these
suprema are colimits because filtered colimits are exact in `C`. The iteration reaches `X`
before the well-ordered index type outgrows the set of subobjects of `X`. This is how Grothendieck
shows that every monomorphism is a transfinite composition of pushouts of inclusions of subobjects
of a generator, in which case `Q` holds for every subobject. The property `Q` lets the same
argument apply when the enlargements are only available under a condition on `A`, such as the
monomorphic quasi-isomorphisms of complexes, which are enlarged only along acyclic complexes.

## References

* The proof of `exists_transfiniteCompositionOfShape` in the namespace
  `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms` of Mathlib's
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, by Joël Riou, which is
  the case where `Q` always holds and this file follows.
* A. Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J. 9 (1957).
-/

public section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] {X : C}
  (W : MorphismProperty C) (Q : Subobject X → Prop)

/-- Hypotheses under which every subobject of `X` satisfying `Q` can be enlarged along `W`
transfinitely until it becomes `⊤`: a proper subobject satisfying `Q` has a strictly larger one
satisfying `Q`, reached by a morphism in `W`; moreover `Q` holds for `⊤` and is preserved by
directed suprema. -/
structure IsEnlargeable : Prop where
  exists_lt (A : Subobject X) (hA : Q A) (hA' : A ≠ ⊤) :
    ∃ (A' : Subobject X) (h : A < A'), Q A' ∧ W (Subobject.ofLE A A' h.le)
  top : Q ⊤
  iSup {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Subobject X)
    (hA : Monotone A) (hQ : ∀ i, Q (A i)) : Q (⨆ i, A i)

namespace IsEnlargeable

variable {W Q} (h : IsEnlargeable W Q)

open scoped Classical in
/-- A subobject `A` satisfying `Q` and different from `⊤` is sent to a strictly larger
subobject given by `IsEnlargeable.exists_lt`; every other subobject is sent to `⊤`. -/
private noncomputable def larger (A : Subobject X) : Subobject X :=
  if hA : Q A ∧ A ≠ ⊤ then (h.exists_lt A hA.1 hA.2).choose else ⊤

private lemma larger_of_ne_top (A : Subobject X) (hA : Q A) (hA' : A ≠ ⊤) :
    h.larger A = (h.exists_lt A hA hA').choose :=
  dite_eq_left ⟨hA, hA'⟩

private lemma lt_larger (A : Subobject X) (hA : A ≠ ⊤) : A < h.larger A := by
  by_cases hQ : Q A
  · rw [h.larger_of_ne_top A hQ hA]
    exact (h.exists_lt A hQ hA).choose_spec.choose
  · rw [larger, dite_eq_right (fun h' ↦ hQ h'.1)]
    exact lt_top_iff_ne_top.2 hA

private lemma le_larger (A : Subobject X) : A ≤ h.larger A := by
  by_cases hA : A = ⊤
  · subst hA
    simp [larger]
  · exact (h.lt_larger A hA).le

@[simp]
private lemma larger_top : h.larger (⊤ : Subobject X) = ⊤ := by
  simp [larger]

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The transfinite iteration of `IsEnlargeable.larger` is monotone. -/
private lemma transfiniteIterate_le (A₀ : Subobject X) {k k' : J} (hkk' : k ≤ k') :
    transfiniteIterate h.larger k A₀ ≤ transfiniteIterate h.larger k' A₀ :=
  monotone_transfiniteIterate _ _ h.le_larger hkk'

/-- Every stage of the transfinite iteration of `IsEnlargeable.larger` starting from a
subobject satisfying `Q` satisfies `Q`. -/
private lemma prop_transfiniteIterate {A₀ : Subobject X} (hA₀ : Q A₀) (j : J) :
    Q (transfiniteIterate h.larger j A₀) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using hA₀
  | succ j hj hj' =>
    rw [transfiniteIterate_succ _ _ _ hj]
    by_cases hA : transfiniteIterate h.larger j A₀ = ⊤
    · rw [hA, larger_top]
      exact h.top
    · rw [h.larger_of_ne_top _ hj' hA]
      exact (h.exists_lt _ hj' hA).choose_spec.choose_spec.1
  | isSuccLimit j hj hj' =>
    rw [transfiniteIterate_limit _ _ _ hj]
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    exact h.iSup _ (fun k k' hkk' ↦ h.transfiniteIterate_le A₀ hkk')
      (fun k ↦ hj' k.1 k.2)

private lemma exists_transfiniteIterate_eq_top (A₀ : Subobject X)
    (hJ : HasCardinalLT (Subobject X) (Cardinal.mk J)) :
    ∃ j : J, transfiniteIterate h.larger j A₀ = ⊤ :=
  top_mem_range_transfiniteIterate h.larger A₀ h.lt_larger (by simp)
    (fun h' ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h')

variable (J) (A₀ : Subobject X)

/-- The functor `J ⥤ MonoOver X` given by the transfinite iteration of
`IsEnlargeable.larger` starting from `A₀`. -/
@[simps]
private noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk (transfiniteIterate h.larger j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE (transfiniteIterate h.larger j A₀)
    (transfiniteIterate h.larger j' A₀) (h.transfiniteIterate_le A₀ (leOfHom f)))

/-- The functor `J ⥤ C` induced by `IsEnlargeable.functorToMonoOver`. -/
private noncomputable abbrev functor : J ⥤ C :=
  h.functorToMonoOver J A₀ ⋙ MonoOver.forget _ ⋙ Over.forget _

variable {J} in
private lemma functor_map {k k' : J} (f : k ⟶ k') :
    (h.functor J A₀).map f = Subobject.ofLE (transfiniteIterate h.larger k A₀)
      (transfiniteIterate h.larger k' A₀)
        (h.transfiniteIterate_le A₀ (leOfHom f)) :=
  (rfl)

private instance : (h.functor J A₀).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (h.functorToMonoOver J A₀ ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ h.functorToMonoOver J A₀) c
    have (j : J) : Subobject.mk ((h.functorToMonoOver J A₀).obj j).obj.hom =
        transfiniteIterate h.larger j A₀ :=
      Subobject.mk_arrow _
    dsimp [c]
    simpa only [this] using transfiniteIterate_limit h.larger A₀ m hm⟩

variable {J A₀} in
/-- The inclusion of a subobject `A` satisfying `Q` and different from `⊤` into its enlargement
`IsEnlargeable.larger` belongs to `W`. -/
private lemma mem_ofLE_larger {A B : Subobject X} (hA : Q A) (hA' : A ≠ ⊤) (hB : B = h.larger A)
    (hAB : A ≤ B) : W (Subobject.ofLE A B hAB) := by
  rw [h.larger_of_ne_top A hA hA'] at hB
  subst hB
  exact (h.exists_lt A hA hA').choose_spec.choose_spec.2

variable {J} in
/-- If no stage of the transfinite iteration before `j` is `⊤`, the inclusion of `A₀` into the
`j`-th stage is a transfinite composition of morphisms in `W`, indexed by `Set.Iic j`. -/
private noncomputable def transfiniteCompositionOfShapeMapFromBot (hA₀ : Q A₀) (j : J)
    (hj : ∀ k < j, transfiniteIterate h.larger k A₀ ≠ ⊤) :
    W.TransfiniteCompositionOfShape (Set.Iic j)
      ((h.functor J A₀).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ h.functor J A₀
  isoBot := Iso.refl _
  incl :=
    { app k := (h.functor J A₀).map (homOfLE k.2)
      naturality k k' f := by
        have := (h.functor J A₀).map_comp (homOfLE (leOfHom f) : (k : J) ⟶ k')
          (homOfLE (k'.2 : (k' : J) ≤ j))
        exact (this.symm.trans (congrArg _ (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  fac := Category.id_comp _
  map_mem k hk := by
    have hkj : (k : J) < j := lt_of_le_of_ne k.2 (fun h' ↦ hk (by
      rw [isMax_iff_eq_top]
      exact Subtype.ext h'))
    rw [Functor.comp_map, functor_map]
    exact h.mem_ofLE_larger (h.prop_transfiniteIterate hA₀ (k : J)) (hj k hkj)
      (by simp [Set.Iic.succ_eq_of_not_isMax hk,
        transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]) _

include h in
/-- Let `C` be a Grothendieck abelian category and `X : C`. Assume that every proper subobject of
`X` satisfying `Q` is strictly contained in a subobject satisfying `Q` through a morphism in `W`,
and that `Q` holds for `⊤` and is preserved by directed suprema. Then every monomorphism
`f : A ⟶ X` whose subobject satisfies `Q` is a transfinite composition of morphisms in `W`. -/
theorem exists_transfiniteCompositionOfShape {A : C} (f : A ⟶ X)
    [Mono f] (hf : Q (Subobject.mk f)) :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty (W.TransfiniteCompositionOfShape J f) := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  obtain ⟨j, hj⟩ := h.exists_transfiniteIterate_eq_top (J := κ.ord.ToType) (Subobject.mk f)
    (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))
  obtain ⟨j₀, hj₀, hmin⟩ := WellFounded.has_min wellFounded_lt
    {k : κ.ord.ToType | transfiniteIterate h.larger k (Subobject.mk f) = ⊤} ⟨j, hj⟩
  have ht : IsIso (transfiniteIterate h.larger j₀ (Subobject.mk f)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hj₀
  refine ⟨Set.Iic j₀, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have key : Subobject.ofLE _ _ (h.transfiniteIterate_le (Subobject.mk f) bot_le) ≫
      (transfiniteIterate h.larger j₀ (Subobject.mk f)).arrow =
        (Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫ Subobject.underlyingIso f).hom ≫
          f := by
    rw [Subobject.ofLE_arrow, Iso.trans_hom, Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
  exact (h.transfiniteCompositionOfShapeMapFromBot _ hf j₀
    (fun k hk hk' ↦ hmin k hk' hk)).ofArrowIso (Arrow.isoMk ((Subobject.isoOfEq _ _
      (transfiniteIterate_bot _ _) ≪≫ Subobject.underlyingIso f))
      (@asIso _ _ _ _ (transfiniteIterate h.larger j₀ (Subobject.mk f)).arrow ht) key.symm)

end IsEnlargeable

end CategoryTheory.IsGrothendieckAbelian
