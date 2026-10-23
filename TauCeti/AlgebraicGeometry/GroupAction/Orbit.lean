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
The translation homeomorphisms assemble into an action of the sections of `G`
on the underlying space of `X`, under which the orbit is invariant.
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

/-- The orbit boundary is the orbit closure with the orbit removed. -/
theorem orbitBoundary_def (x : 𝟙_ (Over S) ⟶ X) :
    orbitBoundary G x = orbitClosure G x \ orbit G x := (rfl)

/-- Boundary membership consists of closure membership and failure of orbit membership. -/
@[simp]
theorem mem_orbitBoundary (x : 𝟙_ (Over S) ⟶ X) (p : X.left) :
    p ∈ orbitBoundary G x ↔ p ∈ orbitClosure G x ∧ p ∉ orbit G x := Iff.rfl

/-- The geometric orbit is contained in its closure. -/
theorem orbit_subset_orbitClosure (x : 𝟙_ (Over S) ⟶ X) :
    orbit G x ⊆ orbitClosure G x := subset_closure

/-- The orbit boundary is contained in the orbit closure. -/
theorem orbitBoundary_subset_orbitClosure (x : 𝟙_ (Over S) ⟶ X) :
    orbitBoundary G x ⊆ orbitClosure G x := Set.sdiff_subset

/-- The orbit closure is closed. -/
theorem isClosed_orbitClosure (x : 𝟙_ (Over S) ⟶ X) :
    IsClosed (orbitClosure G x) := isClosed_closure

/-- The geometric orbit is closed exactly when its boundary is empty. -/
theorem isClosed_orbit_iff_orbitBoundary_eq_empty (x : 𝟙_ (Over S) ⟶ X) :
    IsClosed (orbit G x) ↔ orbitBoundary G x = ∅ := by
  rw [orbitBoundary_def, orbitClosure_def, Set.sdiff_eq_empty, closure_subset_iff_isClosed]

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

section Translation

variable (X)

/-- The global points of a group scheme act on the underlying space of a scheme it acts on, each
acting through its translation automorphism. Install it locally to select this action. -/
@[instance_reducible]
def translationMulAction : MulAction (𝟙_ (Over S) ⟶ G) X.left where
  smul g p := (translation X g).hom.left p
  one_smul p := by simp [HSMul.hSMul]
  mul_smul g h p := by
    simp only [HSMul.hSMul, SMul.smul, translation_mul, Iso.trans_hom, Over.comp_left,
      Scheme.Hom.comp_apply]

variable {G X}

/-- A global point acts through its translation automorphism. -/
theorem translationMulAction_smul (g : 𝟙_ (Over S) ⟶ G) (p : X.left) :
    letI := translationMulAction G X
    g • p = (translation X g).hom.left p :=
  (rfl)

/-- On the point underlying a section, the translation action is the action on sections. -/
theorem translationMulAction_smul_apply (g : 𝟙_ (Over S) ⟶ G) (y : 𝟙_ (Over S) ⟶ X)
    (a : (𝟙_ (Over S)).left) :
    letI := translationMulAction G X
    g • y.left a = (g • y).left a := by
  rw [translationMulAction_smul, ← Scheme.Hom.comp_apply, ← Over.comp_left, comp_translation_hom,
    toUnit_unit, Category.id_comp]

/-- Every global point acts by a homeomorphism. -/
theorem continuousConstSMul_translationMulAction :
    letI := translationMulAction G X
    ContinuousConstSMul (𝟙_ (Over S) ⟶ G) X.left :=
  letI := translationMulAction G X
  ⟨fun g ↦ (translation X g).hom.left.continuous⟩

/-- Translation by a global point preserves the orbit, so the orbit is invariant under the
translation action. -/
theorem preimage_smul_orbit (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    letI := translationMulAction G X
    (fun p : X.left ↦ g • p) ⁻¹' orbit G x = orbit G x := by
  let := translationMulAction G X
  rw [Set.preimage_smul, ← Set.image_smul]
  exact image_translation_orbit G g⁻¹ x

end Translation

end TauCeti.SchemeAction
