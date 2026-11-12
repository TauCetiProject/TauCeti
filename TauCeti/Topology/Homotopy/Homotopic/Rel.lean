/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Shrinking the fixed set of a relative homotopy, and pointed homotopy

A homotopy relative to a set `S` fixes every point of `S` at all times, so it is also a homotopy
relative to every subset of `S`. This lets relative homotopies obtained relative to different sets
be composed relative to a common subset. Precomposed with a map `e`, it is a homotopy relative to
the preimage `e ⁻¹' S`, and composites of relative homotopies are again relative homotopies.

Homotopy relative to a single point is pointed homotopy: it is an equivalence relation on the
pointed maps `(Y, y₀) → (X, x)`, whose classes are the pointed homotopy classes of maps.

## Main declarations

* `ContinuousMap.HomotopyRel.mono`: a homotopy relative to `S` as a homotopy relative to `T ⊆ S`.
* `ContinuousMap.HomotopicRel.mono`: maps homotopic relative to `S` are homotopic relative to
  every `T ⊆ S`.
* `ContinuousMap.HomotopyRel.precomp`, `ContinuousMap.HomotopicRel.precomp`: precomposing a
  homotopy relative to `S` with `e` gives a homotopy relative to `e ⁻¹' S`.
* `ContinuousMap.HomotopicRel.comp`: relative homotopies compose.
* `ContinuousMap.HomotopicRel.comp_id`: self-maps homotopic to the identity relative to `S` are
  closed under composition.
* `ContinuousMap.HomotopicRel.mapsTo_self`: a self-map homotopic to the identity relative to `S`
  maps `S` into itself.
* `TauCeti.pointedHomotopySetoid`: pointed homotopy, as an equivalence relation on pointed maps.
-/

public section

open unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} {S T : Set X}

/-- A homotopy relative to `S` is a homotopy relative to every subset of `S`. -/
def HomotopyRel.mono (F : HomotopyRel f₀ f₁ S) (hTS : T ⊆ S) : HomotopyRel f₀ f₁ T where
  toFun := F
  continuous_toFun := F.continuous
  map_zero_left := F.apply_zero
  map_one_left := F.apply_one
  prop' t _ hx := F.prop t _ (hTS hx)

/-- Shrinking the fixed set does not change the homotopy. -/
@[simp]
lemma HomotopyRel.mono_apply (F : HomotopyRel f₀ f₁ S) (hTS : T ⊆ S) (x : I × X) :
    F.mono hTS x = F x :=
  (rfl)

/-- Maps homotopic relative to `S` are homotopic relative to every subset of `S`. -/
theorem HomotopicRel.mono (h : HomotopicRel f₀ f₁ S) (hTS : T ⊆ S) : HomotopicRel f₀ f₁ T :=
  h.map (·.mono hTS)

variable {W : Type*} [TopologicalSpace W]

/-- Precomposing a homotopy relative to `S` with `e : C(W, X)` gives a homotopy relative to the
preimage `e ⁻¹' S`. -/
def HomotopyRel.precomp (F : HomotopyRel f₀ f₁ S) (e : C(W, X)) :
    HomotopyRel (f₀.comp e) (f₁.comp e) (e ⁻¹' S) where
  toHomotopy := F.toHomotopy.compContinuousMap e
  prop' t _ hx := F.prop t _ hx

/-- The precomposed homotopy is the original homotopy evaluated at the image point. -/
@[simp]
lemma HomotopyRel.precomp_apply (F : HomotopyRel f₀ f₁ S) (e : C(W, X)) (x : I × W) :
    F.precomp e x = F (x.1, e x.2) :=
  (rfl)

/-- If `f₀` and `f₁` are homotopic relative to `S`, then `f₀ ∘ e` and `f₁ ∘ e` are homotopic
relative to `e ⁻¹' S`. -/
theorem HomotopicRel.precomp (h : HomotopicRel f₀ f₁ S) (e : C(W, X)) :
    HomotopicRel (f₀.comp e) (f₁.comp e) (e ⁻¹' S) :=
  h.map (·.precomp e)

/-- A self-map homotopic to the identity relative to `S` fixes `S` pointwise, so it maps `S` into
itself. -/
theorem HomotopicRel.mapsTo_self {f : C(X, X)} (h : HomotopicRel f (ContinuousMap.id X) S) :
    Set.MapsTo f S S :=
  (Set.mapsTo_id S).congr fun _ hx ↦ (h.fst_eq_snd hx).symm

/-- Homotopies relative to `T` and to `S` compose to a homotopy relative to `S` when the inner
map carries `S` into `T`, the relative form of `ContinuousMap.Homotopic.comp`. -/
theorem HomotopicRel.comp {Z : Type*} [TopologicalSpace Z] {g₀ g₁ : C(Y, Z)} {T : Set Y}
    (hg : HomotopicRel g₀ g₁ T) (hf : HomotopicRel f₀ f₁ S) (hST : Set.MapsTo f₀ S T) :
    HomotopicRel (g₀.comp f₀) (g₁.comp f₁) S :=
  ((hg.precomp f₀).mono hST.subset_preimage).trans (hf.comp_continuousMap g₁)

/-- Self-maps homotopic to the identity relative to `S` are closed under composition. -/
theorem HomotopicRel.comp_id {f g : C(X, X)} (hg : HomotopicRel g (ContinuousMap.id X) S)
    (hf : HomotopicRel f (ContinuousMap.id X) S) :
    HomotopicRel (g.comp f) (ContinuousMap.id X) S :=
  hg.comp hf hf.mapsTo_self

end ContinuousMap

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pointed homotopy, homotopy relative to the base point, as an equivalence relation on the
pointed maps `(Y, y₀) → (X, x)`.  Its classes are the pointed homotopy classes of maps. -/
def pointedHomotopySetoid (y₀ : Y) (x : X) : Setoid {f : C(Y, X) // f y₀ = x} where
  r f g := f.1.HomotopicRel g.1 {y₀}
  iseqv := ⟨fun f ↦ .refl f.1, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

lemma pointedHomotopySetoid_iff {y₀ : Y} {x : X} {f g : {f : C(Y, X) // f y₀ = x}} :
    pointedHomotopySetoid y₀ x f g ↔ f.1.HomotopicRel g.1 {y₀} :=
  Iff.rfl

end TauCeti
