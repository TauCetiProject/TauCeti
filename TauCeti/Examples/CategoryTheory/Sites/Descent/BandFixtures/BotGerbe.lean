/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Lift
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.BotGerbe

/-!
# Checks for constant gerbes on the point

On the point category `Discrete PUnit` with the bottom topology:

* the two-component diagram `Discrete Bool × B(C₃)` is a stack;
* the connected diagrams `B(C₃)` and `B(S₃)` are gerbes;
* in the gerbe `B(S₃)`, without commutative inertia, evaluation of central sections at the
  canonical object is injective;
* in the gerbe `B(C₃)`, with commutative inertia, evaluation at the canonical object is bijective.
-/

public section

namespace TauCeti.Examples.BotGerbe

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.BandFixtures
open Opposite Bicategory

/-- The cyclic group of order three, written multiplicatively. -/
abbrev C₃ : Type := Multiplicative (ZMod 3)

/-- The point category. -/
abbrev pt : Type := Discrete PUnit.{1}

/-- The object of the point category. -/
abbrev star : pt := ⟨PUnit.unit⟩

/-- The constant diagram `B G` on the point. -/
abbrev B (G : Type) [Group G] : LocallyDiscrete ptᵒᵖ ⥤ᵖ Cat :=
  constant pt (Discrete PUnit.{1} × SingleObj G)

/-- The canonical object of `B G`. -/
abbrev canonical (G : Type) [Group G] : (B G).obj (.mk (op star)) :=
  ((⟨PUnit.unit⟩ : Discrete PUnit.{1}), SingleObj.star G)

/-- **Two components: a stack.** -/
example : (constant pt (Discrete Bool × SingleObj C₃)).IsStack ⊥ :=
  inferInstance

/-- **Connected: gerbes.** -/
example : (B C₃).IsGerbe ⊥ ∧ (B (Equiv.Perm (Fin 3))).IsGerbe ⊥ :=
  ⟨inferInstance, inferInstance⟩

/-- **`B(S₃)`: evaluation at the canonical object is injective**, without commutative inertia. -/
example : Function.Injective
    (IntrinsicBandSections.evaluation (F := B (Equiv.Perm (Fin 3))) (𝟙 star)
      (canonical (Equiv.Perm (Fin 3)))) :=
  IntrinsicBandSections.evaluation_injective (J := ⊥) _

/-- The automorphism groups of the fibres of `B C₃` are commutative. -/
theorem aut_comm (_V : pt) (z : (B C₃).obj (.mk (op _V))) (a b : Aut z) : a * b = b * a := by
  refine Aut.ext (Iso.ext (Prod.hom_ext (Subsingleton.elim _ _) ?_))
  change (_ ≫ _ : SingleObj.star C₃ ⟶ SingleObj.star C₃) = _ ≫ _
  rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul]
  exact mul_comm (G := C₃) _ _

/-- **`B(C₃)`: evaluation at the canonical object is bijective.** -/
example : Function.Bijective
    (IntrinsicBandSections.evaluation (F := B C₃) (𝟙 star) (canonical C₃)) :=
  ⟨IntrinsicBandSections.evaluation_injective (J := ⊥) _,
    IntrinsicBandSections.evaluation_surjective ⊥ aut_comm _⟩

end TauCeti.Examples.BotGerbe
