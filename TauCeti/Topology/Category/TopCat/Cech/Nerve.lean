/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Connected.Clopen

/-!
# The Čech nerve of a family of open subsets

The disjoint union of the members of a family of open subsets maps to the ambient space. This
map is open, and it is an open quotient map when the family covers. Its Čech nerve packages the
iterated intersections and all face and degeneracy maps in the topological category. Maps of
covered spaces induce maps of the corresponding arrows. A map from a connected space lifts to the
disjoint union exactly when its image lies in one member of the family.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti.TopCat

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The map from the disjoint union of a family of open subsets to the ambient space. -/
def openCoverMap : TopCat.of (Σ i, U i) ⟶ X :=
  TopCat.ofHom ⟨fun p => p.2.1, continuous_sigma fun _ => continuous_subtype_val⟩

/-- The cover map sends a point of a member of the family to the same point of the ambient
space. -/
@[simp]
theorem openCoverMap_apply (p : Σ i, U i) : openCoverMap U p = (p.2 : X) :=
  (rfl)

/-- A continuous map from a connected space lifts along the map from the disjoint union of a family
of open subsets exactly when its image lies in one member of the family. -/
theorem exists_openCoverMap_comp_eq_iff {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z]
    (g : C(Z, X)) :
    (∃ l : C(Z, Σ i, U i), (openCoverMap U).hom.comp l = g) ↔ ∃ i, Set.range g ⊆ U i := by
  constructor
  · rintro ⟨l, rfl⟩
    obtain ⟨i, l', -, hl⟩ := l.continuous.exists_lift_sigma
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : l z = ⟨i, l' z⟩ := congrFun hl z
    rw [ContinuousMap.comp_apply, hz, openCoverMap_apply]
    exact (l' z).2
  · rintro ⟨i, hi⟩
    exact ⟨⟨fun z ↦ ⟨i, ⟨g z, hi ⟨z, rfl⟩⟩⟩, continuous_sigmaMk.comp (g.continuous.subtype_mk _)⟩,
      rfl⟩

/-- The map of a family of opens, regarded as an arrow for its Čech nerve. -/
abbrev openCoverArrow : Arrow TopCat.{u} :=
  Arrow.mk (openCoverMap U)

/-- The map from the disjoint union of open subspaces is open. -/
theorem openCoverMap_isOpenMap : IsOpenMap (openCoverMap U) :=
  isOpenMap_sigma.mpr fun i => (U i).isOpen.isOpenMap_subtype_val

/-- The cover map is surjective exactly when every point lies in a member of the family. -/
theorem openCoverMap_surjective_iff : Function.Surjective (openCoverMap U) ↔
    ∀ x : X, ∃ i, x ∈ U i := by
  constructor
  · intro h x
    obtain ⟨⟨i, y⟩, hy⟩ := h x
    exact ⟨i, hy ▸ y.2⟩
  · intro h x
    obtain ⟨i, hi⟩ := h x
    exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩

/-- For an open cover, the disjoint-union map is an open quotient map. -/
theorem openCoverMap_isOpenQuotientMap (hU : ∀ x : X, ∃ i, x ∈ U i) :
    IsOpenQuotientMap (openCoverMap U) :=
  ⟨openCoverMap_surjective_iff U |>.2 hU, (openCoverMap U).hom.continuous,
    openCoverMap_isOpenMap U⟩

/-- A map of covered spaces gives a map of the corresponding arrows. -/
def openCoverArrowMap {Y : TopCat.{u}} {κ : Type u} (V : κ → Opens Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    openCoverArrow U ⟶ openCoverArrow V where
  left := TopCat.ofHom
    ⟨fun p => ⟨r p.1, ⟨f p.2.1, hf p.1 p.2.2⟩⟩,
      by
        apply continuous_sigma
        intro i
        simpa only [Function.comp_def] using
          ((continuous_sigmaMk (i := r i)).comp
            ((f.hom.continuous.comp continuous_subtype_val).subtype_mk
              (fun a => hf i a.2)))⟩
  right := f
  w := by ext p; rfl

/-- The identity map of a covered space induces the identity arrow map. -/
@[simp]
theorem openCoverArrowMap_id :
    openCoverArrowMap U U (𝟙 X) id (fun _ _ h => h) = 𝟙 (openCoverArrow U) := by
  ext p <;> rfl

/-- Maps of covered spaces compose as maps of Čech-nerve arrows. -/
theorem openCoverArrowMap_comp {Y Z : TopCat.{u}} {κ τ : Type u}
    (V : κ → Opens Y) (W : τ → Opens Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ι → κ) (s : κ → τ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))
    (hg : ∀ j, Set.MapsTo g (V j) (W (s j))) :
    openCoverArrowMap U W (f ≫ g) (s ∘ r)
      (fun i _ hx => hg (r i) (hf i hx)) =
      openCoverArrowMap U V f r hf ≫ openCoverArrowMap V W g s hg := by
  ext p <;> rfl

end TauCeti.TopCat
