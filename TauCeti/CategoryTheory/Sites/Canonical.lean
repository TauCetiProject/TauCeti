/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sections and morphisms of represented sheaves

For a subcanonical topology `J` on `C`, the sheaf `J.uliftYoneda.obj X` represented by `X` has the
lifted morphisms `T ⟶ X` as its sections over `T`. A morphism of represented sheaves acts on these
sections by composition with the morphism of `C` it comes from, and the global sections of the
sheaf represented by `X` are the morphisms from a terminal object to `X`.

The morphism of represented sheaves induced by a morphism whose singleton sieve is covering is
locally surjective (`CategoryTheory.Sheaf.isLocallySurjective_uliftYoneda_map_of_mem`).
-/

public section

open CategoryTheory Opposite Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [J.Subcanonical]

/-- A morphism `F` of represented sheaves evaluates on a point `z : T ⟶ X` by composition with the
morphism `X ⟶ Y` it comes from. -/
lemma down_hom_app_up_eq_comp_preimage {X Y : C}
    (F : J.uliftYoneda.{w}.obj X ⟶ J.uliftYoneda.{w}.obj Y) {T : C} (z : T ⟶ X) :
    (F.hom.app (op T) (ULift.up z)).down = z ≫ J.fullyFaithfulUliftYoneda.preimage F := by
  conv_lhs => rw [← J.fullyFaithfulUliftYoneda.map_preimage F]
  rfl

variable (J) in
/-- The sheaf represented by `X` has a global section if and only if there is a morphism from a
terminal object `T` to `X`. -/
lemma nonempty_sections_uliftYoneda_obj_iff {T : C} (hT : IsTerminal T) {X : C} :
    (J.uliftYoneda.{w}.obj X).obj.sections.Nonempty ↔ Nonempty (T ⟶ X) := by
  refine ⟨fun ⟨s, _⟩ ↦ ⟨(s (op T)).down⟩, fun ⟨x⟩ ↦ ?_⟩
  refine ⟨fun U ↦ ULift.up (hT.from (unop U) ≫ x), fun {U U'} f ↦ ?_⟩
  exact congrArg ULift.up (by simp [← Category.assoc, hT.comp_from])

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The map of representable sheaves induced by a morphism `q : U ⟶ M` whose singleton sieve is
`J`-covering is `J`-locally surjective: every `T`-point of `M` lifts to `U` on a covering sieve
of `T`. -/
theorem isLocallySurjective_uliftYoneda_map_of_mem [J.Subcanonical] {U M : C} {q : U ⟶ M}
    (hq : Sieve.generate (Presieve.singleton q) ∈ J M) :
    IsLocallySurjective (J.uliftYoneda.{w}.map q) where
  imageSieve_mem {T} x := by
    refine J.superset_covering ?_ (J.pullback_stable x.down hq)
    rintro T' g ⟨W, a, b, ⟨⟩, hab⟩
    -- sections of `h_M` over `T'` are `ULift`-wrapped morphisms `T' ⟶ M`
    exact ⟨ULift.up a, congrArg ULift.up hab⟩

end CategoryTheory.Sheaf
