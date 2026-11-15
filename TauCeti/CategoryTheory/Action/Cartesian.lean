/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.CategoryTheory.Galois.ContAction
public import TauCeti.CategoryTheory.Monoidal.Cartesian.FintypeCat

/-!
# Actions in a cartesian monoidal category

If `V` is a cartesian monoidal category, the monoidal structure of `Action V G` (Mathlib's
`Action.instMonoidalCategory`, the tensor product of the underlying objects with the diagonal
action and the tensor unit with the trivial action) is cartesian: the projections of `V` are
equivariant, and so is the map `lift f g` into a product for equivariant `f` and `g`. This file
records the resulting `CartesianMonoidalCategory (Action V G)` instance, extending Mathlib's
monoidal structure so that no second tensor product is introduced.

For a topological group `G`, the continuous actions on finite sets are closed under finite limits
in `Action FintypeCat G` (Mathlib's `Action.isContinuous`), so the full subcategory
`ContAction FintypeCat G` is cartesian monoidal as well, through Mathlib's
`CartesianMonoidalCategory.fullSubcategory`. A group object in it is a finite group on which `G`
acts continuously by group automorphisms; for `G` the absolute Galois group of a field, these
correspond to the finite étale group schemes over the field
(`TauCeti.FiniteEtaleScheme.galoisEquivalenceGrp`).

## Main definitions

* `Action.cartesianMonoidalCategory`: the cartesian monoidal structure on `Action V G`, with
  `Action.lift_hom` and `Action.toUnit_hom` computing its maps on underlying objects.
* The instance `CartesianMonoidalCategory (ContAction FintypeCat G)`, restricted from
  `Action FintypeCat G`, and the braiding it determines.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace Action

variable {V : Type*} [Category* V] [CartesianMonoidalCategory V] {G : Type*} [Monoid G]

/-- **Actions in a cartesian monoidal category form a cartesian monoidal category.** The product
of two actions is the product of the underlying objects with the diagonal action, and the
terminal object is the terminal object of `V` with the trivial action. This extends Mathlib's
monoidal structure `Action.instMonoidalCategory`. -/
@[simps! fst_hom snd_hom]
instance cartesianMonoidalCategory : CartesianMonoidalCategory (Action V G) where
  __ := instMonoidalCategory
  isTerminalTensorUnit := IsTerminal.ofUniqueHom
    (fun X ↦ ⟨toUnit X.V, fun _ ↦ toUnit_unique _ _⟩) fun _ _ ↦ by ext; exact toUnit_unique _ _
  fst X Y := ⟨fst X.V Y.V, fun g ↦ by simp⟩
  snd X Y := ⟨snd X.V Y.V, fun g ↦ by simp⟩
  tensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
    (fun f g ↦ ⟨lift f.hom g.hom, fun h ↦ by
      apply CartesianMonoidalCategory.hom_ext <;> simp [tensor_ρ, Hom.comm]⟩)
    (fun f g ↦ by ext; simp) (fun f g ↦ by ext; simp)
    (fun f g m hf hg ↦ by
      ext
      apply CartesianMonoidalCategory.hom_ext <;> simp [← hf, ← hg])
  -- The two sides differ only in the choice of a map to the terminal object of `V`, which is
  -- unique.
  fst_def X Y := by
    ext
    simp only [fst_def, Action.whiskerLeft_hom, comp_hom, rightUnitor_hom_hom]
    congr 2
  snd_def X Y := by
    ext
    simp only [snd_def, Action.whiskerRight_hom, comp_hom, leftUnitor_hom_hom]
    congr 2

/-- The map into a product of actions is the map into the product of the underlying objects. -/
@[simp]
theorem lift_hom {T X Y : Action V G} (f : T ⟶ X) (g : T ⟶ Y) :
    (lift f g).hom = (lift f.hom g.hom : T.V ⟶ X.V ⊗ Y.V) :=
  (rfl)

/-- The map to the terminal action is the map to the terminal object of `V`. -/
@[simp]
theorem toUnit_hom (X : Action V G) : (toUnit X).hom = (toUnit X.V : X.V ⟶ 𝟙_ V) :=
  toUnit_unique _ _

end Action

namespace ContAction

open FintypeCatDiscrete

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The braiding of the cartesian monoidal structure on finite continuous `G`-sets, whose tensor
product is the product of finite sets with the diagonal action. -/
noncomputable instance braidedCategory : BraidedCategory (ContAction FintypeCat.{u} G) :=
  .ofCartesianMonoidalCategory

end ContAction
