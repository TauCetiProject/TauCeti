/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Action

/-!
# Geometric orbit images of scheme actions

For a group object `G` acting on `X` in schemes over `S`, a section `x` gives an
orbit morphism `G ⟶ X`. Its geometric orbit is the image of the underlying scheme
map, including nonclosed points. Define its closure and boundary in the same
underlying topological space. Translation by any section of `G` preserves all
three sets, and moving the base section by the action gives the same orbit.
Equivariant morphisms carry orbit images onto orbit images.

No finite-type, smoothness, reducedness or connectedness assumption is needed.
These statements supply the invariant sets on which local closedness and
orbit-dimension arguments can be made with additional geometric hypotheses;
no subscheme structure or comparison with rational-point orbits is asserted here.

The morphism identities come from `TauCeti.orbitMap` and
`TauCeti.translation`, using Mathlib's native internal actions.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {S : Scheme.{u}} (G : Over S) {X Y : Over S}

section Monoid

variable [MonObj G] [ModObj G X] [ModObj G Y]

/-- The full topological image of the orbit morphism of a section. -/
def orbit (x : 𝟙_ (Over S) ⟶ X) : Set X.left :=
  Set.range (orbitMap G x).left

/-- A scheme point lies in the orbit precisely when it lifts along the orbit morphism. -/
@[simp]
theorem mem_orbit (x : 𝟙_ (Over S) ⟶ X) (p : X.left) :
    p ∈ orbit G x ↔ ∃ g : G.left, (orbitMap G x).left g = p := Iff.rfl

/-- The closure of the full geometric orbit image. -/
def orbitClosure (x : 𝟙_ (Over S) ⟶ X) : Set X.left := closure (orbit G x)

/-- The boundary of the orbit inside its closure. -/
def orbitBoundary (x : 𝟙_ (Over S) ⟶ X) : Set X.left := orbitClosure G x \ orbit G x

/-- Membership in the orbit closure is membership in the closure of the orbit image. -/
theorem orbitClosure_def (x : 𝟙_ (Over S) ⟶ X) :
    orbitClosure G x = closure (orbit G x) := (rfl)

/-- Boundary membership consists of closure membership and failure of orbit membership. -/
@[simp]
theorem mem_orbitBoundary (x : 𝟙_ (Over S) ⟶ X) (p : X.left) :
    p ∈ orbitBoundary G x ↔ p ∈ orbitClosure G x ∧ p ∉ orbit G x := Iff.rfl

/-- The geometric orbit is contained in its closure. -/
theorem orbit_subset_orbitClosure (x : 𝟙_ (Over S) ⟶ X) :
    orbit G x ⊆ orbitClosure G x := subset_closure

/-- The orbit closure is closed. -/
theorem isClosed_orbitClosure (x : 𝟙_ (Over S) ⟶ X) :
    IsClosed (orbitClosure G x) := isClosed_closure

/-- Equivariant morphisms carry geometric orbit images onto the corresponding orbit images. -/
theorem image_orbit (x : 𝟙_ (Over S) ⟶ X) (f : X ⟶ Y) [IsModHom G f] :
    f.left '' orbit G x = orbit G (x ≫ f) := by
  have h := congrArg (fun k : G ⟶ Y ↦ k.left) (orbitMap_comp G x f)
  simpa only [orbit, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp] using congrArg (fun k : G.left ⟶ Y.left ↦ Set.range k) h


end Monoid

variable [GrpObj G] [ModObj G X]

/-- Translation by a group section preserves the full orbit image. -/
@[simp]
theorem image_translation_orbit (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    (translation X g).hom.left '' orbit G x = orbit G x := by
  have h := congrArg (fun f : G ⟶ X ↦ f.left)
    (leftTranslation_hom_orbitMap g x)
  have hs : Function.Surjective (leftTranslation g).hom.left :=
    (Scheme.homeoOfIso ((Over.forget S).mapIso (leftTranslation g))).surjective
  simpa only [orbit, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hs.range_eq, Set.image_univ] using
      (congrArg (fun f : G.left ⟶ X.left ↦ Set.range f) h).symm

/-- Translation preserves the closure, including any nonclosed scheme points. -/
@[simp]
theorem image_translation_orbitClosure
    (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    (translation X g).hom.left '' orbitClosure G x = orbitClosure G x := by
  let e := Scheme.homeoOfIso ((Over.forget S).mapIso (translation X g))
  exact (e.image_closure (orbit G x)).trans
    (congrArg closure (image_translation_orbit G g x))

/-- Translation preserves the orbit boundary as a set of all scheme points. -/
@[simp]
theorem image_translation_orbitBoundary
    (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    (translation X g).hom.left '' orbitBoundary G x = orbitBoundary G x := by
  let e := Scheme.homeoOfIso ((Over.forget S).mapIso (translation X g))
  have hi : Function.Injective (translation X g).hom.left := e.injective
  rw [orbitBoundary, Set.image_sdiff hi,
    image_translation_orbitClosure, image_translation_orbit]

/-- Moving the base section by a group section leaves its geometric orbit unchanged. -/
@[simp]
theorem orbit_smul (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    orbit G (g • x) = orbit G x := by
  have h := congrArg (fun f : G ⟶ X ↦ f.left) (orbitMap_smul g x)
  have hs : Function.Surjective (rightTranslation g).hom.left :=
    (Scheme.homeoOfIso ((Over.forget S).mapIso (rightTranslation g))).surjective
  simpa only [orbit, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hs.range_eq, Set.image_univ] using
      congrArg (fun f : G.left ⟶ X.left ↦ Set.range f) h


end TauCeti.SchemeAction
