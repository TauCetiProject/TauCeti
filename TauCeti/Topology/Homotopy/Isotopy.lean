/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

/-!
# Isotopy and ambient isotopy

An *isotopy* between two continuous maps is a homotopy whose every time-slice is a topological
embedding, and an *ambient isotopy* of a space `Y` is a homotopy from the identity of `Y`
through self-homeomorphisms. These are the point-set foundations that the geometric-topology
roadmap (`TauCetiRoadmap/GeometricTopology`) asks for once, in full generality, before
specialising: knot equivalence is the restriction of `TauCeti.Isotopic` to smooth embeddings
`S¹ ↪ M`, and the same notion underlies locally flat isotopy, diffeotopies, and concordance.

The construction reuses Mathlib's `ContinuousMap.HomotopyWith`, taking the intermediate
predicate to be "is a topological embedding". This is exactly the slot `HomotopyWith` exists to
fill, so `refl`, `symm`, and `trans` come for free, and `TauCeti.Isotopic` is an equivalence
relation on the embeddings.

## Main definitions

* `TauCeti.Isotopy f₀ f₁`: a homotopy from `f₀` to `f₁` through topological embeddings.
* `TauCeti.Isotopic f₀ f₁`: the proposition that such an isotopy exists.
* `TauCeti.AmbientIsotopy Y`: a homotopy of `Y` from the identity through self-homeomorphisms.

## Main results

* `TauCeti.Isotopy.isEmbedding_left` / `isEmbedding_right`: the endpoints of an isotopy are
  embeddings.
* `TauCeti.Isotopic.isEquivalence` style lemmas (`refl`, `symm`, `trans`) and
  `TauCeti.Isotopic.homotopic`: an isotopy is in particular a homotopy.
* `TauCeti.AmbientIsotopy.isotopic`: an ambient isotopy carries any embedding `f` to the
  isotopic embedding `Φ.final ∘ f`. This is the "ambient isotopy implies isotopy" direction.
-/

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An **isotopy** between `f₀ f₁ : C(X, Y)` is a homotopy whose every time-slice is a
topological embedding. -/
abbrev Isotopy (f₀ f₁ : C(X, Y)) : Type _ :=
  HomotopyWith f₀ f₁ fun g => IsEmbedding g

namespace Isotopy

variable {f₀ f₁ : C(X, Y)}

/-- Every time-slice of an isotopy is a topological embedding. -/
theorem isEmbedding_apply (F : Isotopy f₀ f₁) (t : I) : IsEmbedding fun x => F (t, x) :=
  F.prop' t

/-- The map an isotopy starts at is a topological embedding. -/
theorem isEmbedding_left (F : Isotopy f₀ f₁) : IsEmbedding f₀ := by
  simpa using F.isEmbedding_apply 0

/-- The map an isotopy ends at is a topological embedding. -/
theorem isEmbedding_right (F : Isotopy f₀ f₁) : IsEmbedding f₁ := by
  simpa using F.isEmbedding_apply 1

end Isotopy

/-- Two maps `f₀ f₁ : C(X, Y)` are **isotopic** if there is an isotopy between them, i.e. a
homotopy through topological embeddings. -/
def Isotopic (f₀ f₁ : C(X, Y)) : Prop :=
  HomotopicWith f₀ f₁ fun g => IsEmbedding g

namespace Isotopic

variable {f₀ f₁ f₂ : C(X, Y)}

/-- An isotopy witnesses that its endpoints are isotopic. -/
theorem of_isotopy (F : Isotopy f₀ f₁) : Isotopic f₀ f₁ := ⟨F⟩

theorem refl (f : C(X, Y)) (hf : IsEmbedding f) : Isotopic f f :=
  HomotopicWith.refl f hf

@[symm]
theorem symm (h : Isotopic f₀ f₁) : Isotopic f₁ f₀ :=
  HomotopicWith.symm h

@[trans]
theorem trans (h₀ : Isotopic f₀ f₁) (h₁ : Isotopic f₁ f₂) : Isotopic f₀ f₂ :=
  HomotopicWith.trans h₀ h₁

/-- The endpoints of an isotopy relation are embeddings. -/
theorem isEmbedding_left (h : Isotopic f₀ f₁) : IsEmbedding f₀ :=
  Isotopy.isEmbedding_left h.some

theorem isEmbedding_right (h : Isotopic f₀ f₁) : IsEmbedding f₁ :=
  Isotopy.isEmbedding_right h.some

/-- Isotopic maps are homotopic. -/
theorem homotopic (h : Isotopic f₀ f₁) : Homotopic f₀ f₁ :=
  ⟨h.some.toHomotopy⟩

end Isotopic

/-- An **ambient isotopy** of `Y` is a homotopy from the identity map of `Y` through
self-homeomorphisms; the time-`1` map `Φ.final` is the resulting homeomorphism, and the whole
family deforms the identity into it inside the homeomorphism group. -/
structure AmbientIsotopy (Y : Type*) [TopologicalSpace Y] extends C(I × Y, Y) where
  /-- every time-slice of the ambient isotopy is a self-homeomorphism of `Y` -/
  isHomeomorph_apply' : ∀ t : I, IsHomeomorph fun y => toFun (t, y)
  /-- the ambient isotopy starts at the identity of `Y` -/
  map_zero_left' : ∀ y, toFun (0, y) = y

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- The time-`1` homeomorphism produced by an ambient isotopy, as a continuous map. -/
def final : C(Y, Y) := ⟨fun y => Φ.toContinuousMap (1, y), by fun_prop⟩

@[simp]
theorem final_apply (y : Y) : Φ.final y = Φ.toContinuousMap (1, y) := rfl

/-- The constant ambient isotopy at the identity. -/
def refl (Y : Type*) [TopologicalSpace Y] : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => p.2, by fun_prop⟩
  isHomeomorph_apply' _ := .id
  map_zero_left' _ := rfl

instance : Inhabited (AmbientIsotopy Y) := ⟨refl Y⟩

/-- An ambient isotopy carries any embedding `f` to the embedding `Φ.final ∘ f` through an
explicit isotopy: at time `t` the embedding is the homeomorphism `Φ t` postcomposed with `f`. -/
def isotopy {f : C(X, Y)} (hf : IsEmbedding f) : Isotopy f (Φ.final.comp f) where
  toHomotopy :=
    { toFun := fun p => Φ.toContinuousMap (p.1, f p.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Φ.map_zero_left' (f x)
      map_one_left := fun _ => rfl }
  prop' := fun t => ((Φ.isHomeomorph_apply' t).isEmbedding).comp hf

/-- **Ambient isotopy implies isotopy**: an ambient isotopy of `Y` carries any embedding `f`
into `Y` to the isotopic embedding `Φ.final ∘ f`. -/
theorem isotopic {f : C(X, Y)} (hf : IsEmbedding f) : Isotopic f (Φ.final.comp f) :=
  ⟨Φ.isotopy hf⟩

end AmbientIsotopy

end TauCeti
