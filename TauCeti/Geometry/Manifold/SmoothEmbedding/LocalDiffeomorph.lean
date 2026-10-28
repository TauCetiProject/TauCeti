/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Composing bundled smooth embeddings with local diffeomorphisms

`TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph` shows that the predicate
`Manifold.IsSmoothEmbedding` survives precomposition with a local diffeomorphism which is a
topological embedding, and postcomposition with a map which is a local diffeomorphism along a set
containing the image and a topological embedding on that set. This file packages these as
operations on the bundled type `TauCeti.SmoothEmbedding`, in the way
`TauCeti.SmoothEmbedding.compDiffeomorph` and `TauCeti.SmoothEmbedding.transDiffeomorph` package
composition with diffeomorphisms.

The basic example of the second operation is a chart: a smooth embedding whose image lies in the
source of a chart of the maximal atlas, read in that chart, is a smooth embedding into the model
space.

## Main definitions

* `TauCeti.SmoothEmbedding.compLocalDiffeomorph`: precompose with a local diffeomorphism which is a
  topological embedding.
* `TauCeti.SmoothEmbedding.transLocalDiffeomorph`: postcompose with a map which is a local
  diffeomorphism along a set containing the image, and a topological embedding on that set.
* `TauCeti.SmoothEmbedding.transChart`: read a smooth embedding in a chart of the maximal atlas
  whose source contains its image.
-/

public section

noncomputable section

namespace TauCeti.SmoothEmbedding

open Manifold Set Topology
open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω}

/-- Precompose a smooth embedding with a local diffeomorphism which is a topological embedding. -/
def compLocalDiffeomorph [IsManifold I n M'] (f : SmoothEmbedding I J n M N) (g : M' → M)
    (hg : IsLocalDiffeomorph I I n g) (hge : IsEmbedding g) : SmoothEmbedding I J n M' N :=
  ofIsSmoothEmbedding (f ∘ g) (isSmoothEmbedding_comp_isLocalDiffeomorph hg hge f.isSmoothEmbedding)

@[simp]
theorem coe_compLocalDiffeomorph [IsManifold I n M'] (f : SmoothEmbedding I J n M N) (g : M' → M)
    (hg : IsLocalDiffeomorph I I n g) (hge : IsEmbedding g) :
    ⇑(f.compLocalDiffeomorph g hg hge) = f ∘ g := by
  rw [compLocalDiffeomorph, coe_ofIsSmoothEmbedding]

@[simp]
theorem compLocalDiffeomorph_apply [IsManifold I n M'] (f : SmoothEmbedding I J n M N)
    (g : M' → M) (hg : IsLocalDiffeomorph I I n g) (hge : IsEmbedding g) (x : M') :
    f.compLocalDiffeomorph g hg hge x = f (g x) := by
  rw [coe_compLocalDiffeomorph, Function.comp_apply]

/-- Postcompose a smooth embedding with a map which is a local diffeomorphism at every point of a
set containing the image, and a topological embedding on that set. -/
def transLocalDiffeomorph [IsManifold J n P] (f : SmoothEmbedding I J n M N) (k : N → P)
    {s : Set N} (hk : ∀ y ∈ s, IsLocalDiffeomorphAt J J n k y)
    (hks : IsEmbedding (s.domRestrict k)) (hfs : range f ⊆ s) : SmoothEmbedding I J n M P :=
  ofIsSmoothEmbedding (k ∘ f)
    (isSmoothEmbedding_isLocalDiffeomorphAt_comp (fun x => hk _ (hfs (mem_range_self x))) hfs hks
      f.isSmoothEmbedding)

@[simp]
theorem coe_transLocalDiffeomorph [IsManifold J n P] (f : SmoothEmbedding I J n M N) (k : N → P)
    {s : Set N} (hk : ∀ y ∈ s, IsLocalDiffeomorphAt J J n k y)
    (hks : IsEmbedding (s.domRestrict k)) (hfs : range f ⊆ s) :
    ⇑(f.transLocalDiffeomorph k hk hks hfs) = k ∘ f := by
  rw [transLocalDiffeomorph, coe_ofIsSmoothEmbedding]

@[simp]
theorem transLocalDiffeomorph_apply [IsManifold J n P] (f : SmoothEmbedding I J n M N)
    (k : N → P) {s : Set N} (hk : ∀ y ∈ s, IsLocalDiffeomorphAt J J n k y)
    (hks : IsEmbedding (s.domRestrict k)) (hfs : range f ⊆ s) (x : M) :
    f.transLocalDiffeomorph k hk hks hfs x = k (f x) := by
  rw [coe_transLocalDiffeomorph, Function.comp_apply]

/-- A smooth embedding whose image lies in the source of a chart of the maximal atlas, read in
that chart: a smooth embedding into the model space. -/
def transChart [IsManifold J n G] (f : SmoothEmbedding I J n M N) {φ : OpenPartialHomeomorph N G}
    (hφ : φ ∈ IsManifold.maximalAtlas J n N) (hf : range f ⊆ φ.source) :
    SmoothEmbedding I J n M G :=
  f.transLocalDiffeomorph φ (fun _ hy => φ.isLocalDiffeomorphAt_of_mem_maximalAtlas hφ hy)
    φ.isOpenEmbedding_restrict.isEmbedding hf

@[simp]
theorem coe_transChart [IsManifold J n G] (f : SmoothEmbedding I J n M N)
    {φ : OpenPartialHomeomorph N G} (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hf : range f ⊆ φ.source) : ⇑(f.transChart hφ hf) = φ ∘ f := by
  rw [transChart, coe_transLocalDiffeomorph]

@[simp]
theorem transChart_apply [IsManifold J n G] (f : SmoothEmbedding I J n M N)
    {φ : OpenPartialHomeomorph N G} (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hf : range f ⊆ φ.source) (x : M) : f.transChart hφ hf x = φ (f x) := by
  rw [coe_transChart, Function.comp_apply]

end TauCeti.SmoothEmbedding
