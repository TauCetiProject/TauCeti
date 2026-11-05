/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Isofibrations

A functor `p : X ⟶ Y` of `∞`-categories is an *isofibration* when it is an inner fibration and
equivalences lift along it with a prescribed source: for every vertex `x₀` of `X` and every
equivalence `e : p x₀ ⟶ y₁` of `Y` there is an equivalence `e' : x₀ ⟶ x₁` of `X` with
`p e' = e` (Kerodon, Definition 4.4.1.4). The target is required to be a quasicategory; since `p`
is an inner fibration, so is the source. HTT has no name for this notion: by HTT Corollary 2.4.6.5
these maps are exactly the categorical fibrations between `∞`-categories, the fibrations of the
Joyal model structure. Isofibrations are the maps along which relative left Kan extensions and
relative colimits are formed: inner horn lifting alone does not suffice, since equivalences also
have to lift.

For an arbitrary target, isofibrations are defined by the right lifting property against
monomorphisms that are categorical equivalences (Kerodon, Definition 4.5.6.5), and over a
quasicategory this agrees with the definition here (Kerodon, Proposition 4.5.6.1). Equivalence
lifting alone is not the right condition when the target is not a quasicategory, so it is not used
as a definition there.

Isomorphisms are isofibrations, and isofibrations are closed under composition. A map to a
terminal simplicial set is an isofibration exactly when its source is a quasicategory, and the
projections from a product of quasicategories to its factors are isofibrations. For a functor `F`
between ordinary categories, the nerve of `F` is always an inner fibration, and it is an
isofibration exactly when every isomorphism `F a ≅ b` lifts to an isomorphism out of `a`. For
instance, the inclusion of one object into the codiscrete groupoid on two objects is not an
isofibration: the isomorphism to the missing object has no lift.

## Main definitions

* `SSet.Isofibration p`: for a quasicategory `Y`, `p : X ⟶ Y` is an inner fibration along which
  equivalences lift with prescribed source, characterized by `SSet.isofibration_iff`.

## Main results

* `SSet.exists_isEquivalence_lift_of_section`: a section through a vertex lifts the equivalences
  out of its image.
* `SSet.Isofibration.of_isIso`, `SSet.Isofibration.comp`: isomorphisms are isofibrations, and
  isofibrations compose.
* `SSet.isofibration_iff_of_isTerminal`: a map to a terminal simplicial set is an isofibration
  exactly when its source is a quasicategory.
* `SSet.isofibration_fst`, `SSet.isofibration_snd`: the projections from a product of
  quasicategories onto a factor are isofibrations.
* `CategoryTheory.nerve.isofibration_nerveMap_iff`: the nerve of a functor is an isofibration
  exactly when isomorphisms lift along the functor with prescribed source.
* `CategoryTheory.Codiscrete.isofibration_nerveMap_functorOfFun_iff`: the nerve of the functor
  between codiscrete categories induced by a map `f` of types is an isofibration exactly when `f`
  is surjective or its source is empty.

## References

* J. Lurie, *Kerodon*, Definition 4.4.1.4, Proposition 4.5.6.1 and Definition 4.5.6.5.
* J. Lurie, *Higher Topos Theory*, Corollary 2.4.6.5 (printed p. 137) and §4.3.2.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial

universe u v

namespace SSet

variable {X Y Z : SSet.{u}}

/-- A map `p : X ⟶ Y` to a quasicategory is an *isofibration* when it is an inner fibration along
which equivalences lift with prescribed source: every equivalence of `Y` out of the image of a
vertex `x₀` of `X` is the image of an equivalence of `X` out of `x₀` (Kerodon, Definition 4.4.1.4).
These are the categorical fibrations to `Y`, the fibrations of the Joyal model structure (HTT
Corollary 2.4.6.5). -/
@[mk_iff]
class Isofibration (p : X ⟶ Y) [Quasicategory Y] : Prop extends InnerFibration p where
  /-- Equivalences out of the image of a vertex lift to equivalences out of that vertex. -/
  exists_isEquivalence_lift (x₀ : X _⦋0⦌) {y₁ : Y _⦋0⦌} (e : Edge (p.app _ x₀) y₁) :
    e.IsEquivalence →
      ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁), e'.IsEquivalence ∧ p.app _ e'.edge = e.edge

/-- If a section `s` of `p` passes through `x₀`, then `s` lifts equivalences out of `p x₀` to
equivalences out of `x₀`. -/
lemma exists_isEquivalence_lift_of_section {p : X ⟶ Y} (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    {x₀ : X _⦋0⦌} (hx₀ : s.app _ (p.app _ x₀) = x₀) {y₁ : Y _⦋0⦌} (e : Edge (p.app _ x₀) y₁)
    (he : e.IsEquivalence) :
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁), e'.IsEquivalence ∧ p.app _ e'.edge = e.edge := by
  refine ⟨_, (e.map s).ofEq hx₀ rfl, (Edge.isEquivalence_ofEq_iff _ _).2 (he.map s), ?_⟩
  -- The transported edge `(e.map s).ofEq hx₀ rfl` has underlying simplex `s.app _ e.edge`.
  calc p.app _ ((e.map s).ofEq hx₀ rfl).edge = (s ≫ p).app _ e.edge := rfl
    _ = e.edge := by rw [hs, NatTrans.id_app, ConcreteCategory.id_apply]

namespace Isofibration

/-- Isomorphisms to a quasicategory are isofibrations. -/
instance of_isIso [Quasicategory Y] (p : X ⟶ Y) [IsIso p] : Isofibration p where
  mem := innerFibrations.of_isIso p
  exists_isEquivalence_lift _ _ e he :=
    exists_isEquivalence_lift_of_section (inv p) (IsIso.inv_hom_id p) (by simp) e he

/-- Isofibrations are closed under composition. -/
instance comp [Quasicategory Y] [Quasicategory Z] (p : X ⟶ Y) (q : Y ⟶ Z) [Isofibration p]
    [Isofibration q] : Isofibration (p ≫ q) where
  mem := innerFibrations.comp_mem _ _ (mem_innerFibrations p) (mem_innerFibrations q)
  exists_isEquivalence_lift x₀ _ e he := by
    obtain ⟨_, e₁, he₁, hqe₁⟩ := exists_isEquivalence_lift (p := q) (p.app _ x₀) e he
    obtain ⟨x₁, e', he', hpe'⟩ := exists_isEquivalence_lift (p := p) x₀ e₁ he₁
    exact ⟨x₁, e', he', by rw [NatTrans.comp_app_apply, hpe', hqe₁]⟩

end Isofibration

/-- A map to a terminal simplicial set is an isofibration exactly when its source is a
quasicategory: the identity edges lift every edge of the target. -/
theorem isofibration_iff_of_isTerminal [Quasicategory Y] (p : X ⟶ Y) (hY : IsTerminal Y) :
    Isofibration p ↔ Quasicategory X := by
  refine ⟨fun _ ↦ (quasicategory_iff_of_isTerminal p hY).2 inferInstance, fun h ↦ ?_⟩
  have := (quasicategory_iff_of_isTerminal p hY).1 h
  exact { exists_isEquivalence_lift x₀ _ _ _ :=
    ⟨x₀, .id x₀, Edge.isEquivalence_id x₀, yonedaEquiv.symm.injective (hY.hom_ext _ _)⟩ }

/-- The terminal simplicial set is a quasicategory. -/
instance : Quasicategory (⊤_ SSet.{u}) :=
  (quasicategory_iff_of_isTerminal (𝟙 _) terminalIsTerminal).2 ⟨innerFibrations.of_isIso _⟩

/-- A quasicategory maps to the terminal simplicial set by an isofibration. -/
instance [Quasicategory X] : Isofibration (terminal.from X) :=
  (isofibration_iff_of_isTerminal _ terminalIsTerminal).2 inferInstance

/-- For quasicategories `X` and `Z`, the projection `X ⊗ Z ⟶ X` is an isofibration: an
equivalence `e` of `X` lifts to `e` paired with the identity of the second component. -/
instance isofibration_fst [Quasicategory X] [Quasicategory Z] : Isofibration (fst X Z) where
  mem := MorphismProperty.of_isPullback
    (IsPullback.of_is_product' (tensorProductIsBinaryProduct X Z) terminalIsTerminal).flip
    (mem_innerFibrations (terminal.from Z))
  exists_isEquivalence_lift x₀ _ e he := by
    -- The section of the projection through `x₀`.
    refine exists_isEquivalence_lift_of_section (lift (𝟙 X) (const ((snd X Z).app _ x₀)))
      (lift_fst _ _) ?_ e he
    apply yonedaEquiv.symm.injective
    apply CartesianMonoidalCategory.hom_ext <;>
      rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, ← NatTrans.comp_app_apply] <;>
      simp [SimplexCategory.const_eq_id]

/-- For quasicategories `X` and `Z`, the projection `X ⊗ Z ⟶ Z` is an isofibration. -/
instance isofibration_snd [Quasicategory X] [Quasicategory Z] : Isofibration (snd X Z) := by
  -- The braiding is an isomorphism to the quasicategory `Z ⊗ X`, which lies over `Z`.
  have : Quasicategory (Z ⊗ X) := quasicategory_of_innerFibration (fst Z X)
  rw [← braiding_hom_fst]
  infer_instance

end SSet

namespace CategoryTheory

open SSet

namespace nerve

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The nerve of a functor `F` is an isofibration exactly when isomorphisms lift along `F`
with prescribed source: every isomorphism `F a ≅ b` is, as an arrow, the image of an isomorphism
out of `a`. The nerve of `F` is always an inner fibration. -/
theorem isofibration_nerveMap_iff (F : C ⥤ D) :
    Isofibration (nerveMap F) ↔ ∀ (a : C) (b : D) (e : F.obj a ≅ b),
      ∃ (a' : C) (e' : a ≅ a'), Arrow.mk (F.map e'.hom) = Arrow.mk e.hom := by
  refine ⟨fun h a b e ↦ ?_, fun h ↦
    { mem := mem_innerFibrations _
      exists_isEquivalence_lift := fun x₀ y₁ e he ↦ ?_ }⟩
  · obtain ⟨x₁, e', he', hpe'⟩ := h.exists_isEquivalence_lift (nerveEquiv.symm a)
      ((edgeMk e.hom).ofEq (nerveMap_app_mk₀ F a).symm rfl)
      ((Edge.isEquivalence_ofEq_iff _ _).2 ((isEquivalence_edgeMk_iff _).2 inferInstance))
    obtain ⟨a', rfl⟩ := nerveEquiv.symm.surjective x₁
    obtain ⟨g, rfl⟩ := edgeMk_surjective e'
    have : IsIso g := (isEquivalence_edgeMk_iff g).1 he'
    refine ⟨a', asIso g, ComposableArrows.arrowEquiv.symm.injective ?_⟩
    -- The transported edge has the underlying simplex of `edgeMk e.hom`.
    have := hpe'.trans (edgeMk_edge e.hom)
    rw [edgeMk_edge, nerveMap_app_mk₁] at this
    exact this
  · obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective x₀
    obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective y₁
    obtain ⟨f, hf⟩ := edgeMk_surjective (e.ofEq (nerveMap_app_mk₀ F a) rfl)
    have : IsIso f := (isEquivalence_edgeMk_iff f).1 (hf ▸ (Edge.isEquivalence_ofEq_iff _ _).2 he)
    -- The transported edge `e.ofEq _ rfl` has the underlying simplex of `e`.
    have hfe : e.edge = ComposableArrows.mk₁ f := (congrArg Edge.edge hf).symm.trans (edgeMk_edge f)
    obtain ⟨a', e', he'⟩ := h a b (asIso f)
    refine ⟨nerveEquiv.symm a', edgeMk e'.hom, (isEquivalence_edgeMk_iff _).2 inferInstance, ?_⟩
    rw [edgeMk_edge, nerveMap_app_mk₁, hfe]
    exact congrArg ComposableArrows.arrowEquiv.symm he'

end nerve

namespace Codiscrete

variable {A B : Type u}

/-- The nerve of the functor `Codiscrete A ⥤ Codiscrete B` induced by a map `f : A → B` is a
isofibration exactly when `f` is surjective or `A` is empty: an isomorphism from `f a` to
`b` lifts exactly when `b` lies in the image of `f`. -/
theorem isofibration_nerveMap_functorOfFun_iff (f : A → B) :
    Isofibration (nerveMap (functorOfFun f)) ↔ (Nonempty A → Function.Surjective f) := by
  rw [nerve.isofibration_nerveMap_iff]
  refine ⟨fun h ⟨a⟩ b ↦ ?_, fun h a b _ ↦ ?_⟩
  · obtain ⟨a', _, he⟩ := h ⟨a⟩ ⟨b⟩ (iso _ _)
    exact ⟨a'.as, congrArg (fun φ : Arrow (Codiscrete B) ↦ φ.right.as) he⟩
  · obtain ⟨a', ha'⟩ := h ⟨a.as⟩ b.as
    refine ⟨⟨a'⟩, iso _ _, ?_⟩
    obtain ⟨b⟩ := b
    subst ha'
    rfl

/-- The inclusion of one object into the codiscrete groupoid on two objects is not an
isofibration, although its nerve is an inner fibration: the isomorphism to the missing object does
not lift. -/
theorem not_isofibration_nerveMap_functorOfFun_const :
    ¬ Isofibration (nerveMap (functorOfFun fun _ : Unit ↦ false)) := by
  rw [isofibration_nerveMap_functorOfFun_iff]
  exact fun h ↦ absurd (h ⟨()⟩ true) (by simp)

end Codiscrete

end CategoryTheory
