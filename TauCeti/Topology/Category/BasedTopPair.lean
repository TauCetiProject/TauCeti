/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair

/-!
# Based topological pairs

Relative homology is a functor on Mathlib's category `TopPair` of embeddings `A ↪ X`, with no
basepoint. Relative homotopy groups `π_n(X, A, a₀)` instead need a basepoint, and that basepoint
must lie in the subspace `A`: the boundary map `π_n(X, A, a₀) → π_{n-1}(A, a₀)` lands in a
homotopy group of `A` based at `a₀`. This file introduces the corresponding carrier.

A `TauCeti.BasedTopPair` is a `TopPair` together with an actual point of its subspace, and a
morphism of based pairs is a morphism of pairs whose subspace component preserves that point.
In particular the pair `(X, ∅)` admits no based structure, and no declaration chooses a point
from a bare pair.

## Main declarations

* `TauCeti.BasedTopPair`: a topological pair with a basepoint in its subspace.
* `TauCeti.BasedTopPair.Hom`: basepoint-preserving maps of pairs, forming the category
  `TauCeti.BasedTopPair` with faithful forgetful functor `TauCeti.BasedTopPair.forget` to
  `TopPair`.
-/

public section

universe u

open CategoryTheory

namespace TauCeti

/-- A based topological pair: a topological pair `A ↪ X` together with a basepoint lying in the
subspace `A`. This is the carrier of relative homotopy groups `π_n(X, A, a₀)`. -/
structure BasedTopPair where
  /-- The underlying topological pair. -/
  pair : TopPair.{u}
  /-- The basepoint, a point of the subspace. -/
  basepoint : pair.snd

namespace BasedTopPair

/-- A morphism of based pairs: a map of the underlying pairs whose subspace component preserves
the basepoint. -/
@[ext]
structure Hom (X Y : BasedTopPair.{u}) where
  /-- The underlying map of topological pairs. -/
  toTopPairHom : X.pair ⟶ Y.pair
  /-- The subspace component sends the basepoint to the basepoint. -/
  map_basepoint : TopPair.Hom.snd toTopPairHom X.basepoint = Y.basepoint

attribute [simp] Hom.map_basepoint

instance : Category BasedTopPair.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.pair, rfl⟩
  comp f g := ⟨f.toTopPairHom ≫ g.toTopPairHom, by
    simp [MorphismProperty.Comma.comp_left, Hom.map_basepoint]⟩

variable {X Y Z : BasedTopPair.{u}}

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.toTopPairHom = g.toTopPairHom) : f = g :=
  Hom.ext h

@[simp]
theorem id_toTopPairHom (X : BasedTopPair.{u}) : Hom.toTopPairHom (𝟙 X) = 𝟙 X.pair :=
  rfl

@[simp]
theorem comp_toTopPairHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.toTopPairHom (f ≫ g) = f.toTopPairHom ≫ g.toTopPairHom :=
  rfl

/-- The ambient component of a morphism of based pairs sends the basepoint (viewed in the
ambient space) to the basepoint. -/
@[simp]
theorem Hom.fst_map_basepoint (f : X ⟶ Y) :
    TopPair.Hom.fst f.toTopPairHom (X.pair.map X.basepoint) = Y.pair.map Y.basepoint := by
  rw [← TopPair.Hom.w_apply, f.map_basepoint]

/-- The functor forgetting the basepoint of a based pair. -/
@[expose, simps]
def forget : BasedTopPair.{u} ⥤ TopPair.{u} where
  obj X := X.pair
  map f := f.toTopPairHom

instance : (forget : BasedTopPair.{u} ⥤ TopPair.{u}).Faithful where
  map_injective h := hom_ext h

end BasedTopPair

end TauCeti
