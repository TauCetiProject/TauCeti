/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Bundled smooth embeddings

Mathlib provides the predicate `Manifold.IsSmoothEmbedding I J n f`, saying that a map between
manifolds is a `C^n` immersion and a topological embedding, but it does not bundle maps satisfying
that predicate. This file adds the small bundled type needed by the geometric-topology roadmap's
first-class geometric knot/link presentations: a smooth presentation is a smooth embedding of the
circle into an ambient manifold, and later files should traffic in the embedding as data rather
than in a bare function plus detached hypotheses.

The file deliberately stays at the general manifold level. The roadmap's circle presentations are
special cases of this type, while the same bundled smooth embeddings are also the right inputs for
later tubular-neighbourhood and surgery interfaces.

## Main definitions

* `TauCeti.SmoothEmbedding I J n M N`: bundled `C^n` smooth embeddings `M → N`.
* `TauCeti.SmoothEmbedding.ofIsSmoothEmbedding`: bundle a map satisfying Mathlib's
  `Manifold.IsSmoothEmbedding` predicate.
* `TauCeti.SmoothEmbedding.id`: the identity smooth embedding.
* `TauCeti.SmoothEmbedding.of_opens`: the inclusion of an open subset as a smooth embedding.
* `TauCeti.SmoothEmbedding.prodMap`: the product of two bundled smooth embeddings.
* `TauCeti.SmoothEmbedding.sumInl` / `sumInr`: the coproduct inclusions as smooth embeddings.

The construction is a thin wrapper around Mathlib's
`Manifold.IsSmoothEmbedding` API, especially `IsSmoothEmbedding.id`, `of_opens`, `prodMap`,
`sumInl`, and `sumInr`.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff
open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {I' : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace G M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- A bundled `C^n` smooth embedding between manifolds.

This is a bundled `ContMDiffMap` whose underlying function satisfies Mathlib's
`Manifold.IsSmoothEmbedding`: it is both a `C^n` immersion and a topological embedding. -/
structure SmoothEmbedding (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (n : ℕ∞ω) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] where
  /-- The underlying bundled smooth map. -/
  toContMDiffMap : C^n⟮I, M; J, N⟯
  /-- The underlying map is a smooth embedding in Mathlib's predicate sense. -/
  isSmoothEmbedding_toFun : Manifold.IsSmoothEmbedding I J n (toContMDiffMap : M → N)

namespace SmoothEmbedding

variable {f g : SmoothEmbedding I J n M N}

instance instFunLike : FunLike (SmoothEmbedding I J n M N) M N where
  coe f := f.toContMDiffMap
  coe_injective f g h := by
    cases f
    cases g
    have hfg := ContMDiffMap.coe_injective h
    cases hfg
    rfl

/-- The bundled `C^n` map underlying a smooth embedding. -/
@[simp]
theorem toContMDiffMap_coe (f : SmoothEmbedding I J n M N) :
    ⇑f.toContMDiffMap = f := rfl

/-- A bundled smooth embedding is a `C^n` map. -/
theorem contMDiff (f : SmoothEmbedding I J n M N) : ContMDiff I J n f :=
  f.toContMDiffMap.contMDiff

/-- A bundled smooth embedding satisfies Mathlib's smooth-embedding predicate. -/
theorem isSmoothEmbedding (f : SmoothEmbedding I J n M N) :
    Manifold.IsSmoothEmbedding I J n f :=
  f.isSmoothEmbedding_toFun

/-- A bundled smooth embedding is an immersion. -/
theorem isImmersion (f : SmoothEmbedding I J n M N) : Manifold.IsImmersion I J n f :=
  f.isSmoothEmbedding.isImmersion

/-- A bundled smooth embedding is a topological embedding. -/
theorem isEmbedding (f : SmoothEmbedding I J n M N) : IsEmbedding f :=
  f.isSmoothEmbedding.isEmbedding

/-- Bundle a map satisfying Mathlib's smooth-embedding predicate as a smooth embedding. -/
def ofIsSmoothEmbedding (f : M → N) (hf : Manifold.IsSmoothEmbedding I J n f) :
    SmoothEmbedding I J n M N where
  toContMDiffMap := ⟨f, hf.contMDiff⟩
  isSmoothEmbedding_toFun := hf

@[simp]
theorem ofIsSmoothEmbedding_coe (f : M → N) (hf : Manifold.IsSmoothEmbedding I J n f) :
    ⇑(ofIsSmoothEmbedding (I := I) (J := J) (n := n) f hf) = f := by
  rw [ofIsSmoothEmbedding.eq_def]
  rfl

@[simp]
theorem ofIsSmoothEmbedding_apply (f : M → N) (hf : Manifold.IsSmoothEmbedding I J n f) (x : M) :
    ofIsSmoothEmbedding (I := I) (J := J) (n := n) f hf x = f x := by
  rw [ofIsSmoothEmbedding.eq_def]
  rfl

/-- Two smooth embeddings are equal when their underlying functions are pointwise equal. -/
@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a bundled smooth embedding. -/
def id [IsManifold I n M] : SmoothEmbedding I I n M M where
  toContMDiffMap := ContMDiffMap.id (I := I) (M := M) (n := n)
  isSmoothEmbedding_toFun := Manifold.IsSmoothEmbedding.id

@[simp]
theorem id_apply [IsManifold I n M] (x : M) :
    (id (I := I) (n := n) (M := M)) x = x := by
  rfl

/-- The inclusion of an open subset of a manifold as a bundled smooth embedding. -/
def of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    SmoothEmbedding I I n s M where
  toContMDiffMap :=
    ⟨Subtype.val, (Manifold.IsSmoothEmbedding.of_opens (I := I) (n := n) s).contMDiff⟩
  isSmoothEmbedding_toFun := Manifold.IsSmoothEmbedding.of_opens (I := I) (n := n) s

@[simp]
theorem of_opens_apply [IsManifold I n M] (s : TopologicalSpace.Opens M) (x : s) :
    of_opens (I := I) (n := n) s x = x := by
  rfl

/-- The product of two bundled smooth embeddings. -/
def prodMap [IsManifold I n M] [IsManifold J n N]
    [IsManifold I' n M'] [IsManifold J' n N']
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n M' N') :
    SmoothEmbedding (I.prod I') (J.prod J') n (M × M') (N × N') where
  toContMDiffMap :=
    (f.toContMDiffMap.comp ContMDiffMap.fst).prodMk (g.toContMDiffMap.comp ContMDiffMap.snd)
  isSmoothEmbedding_toFun := f.isSmoothEmbedding.prodMap g.isSmoothEmbedding

@[simp]
theorem prodMap_apply [IsManifold I n M] [IsManifold J n N]
    [IsManifold I' n M'] [IsManifold J' n N']
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n M' N') (x : M × M') :
    f.prodMap g x = (f x.1, g x.2) := by
  rfl

/-- The left coproduct inclusion as a bundled smooth embedding. -/
def sumInl {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    [IsManifold I n M] [IsManifold I n M₂] :
    SmoothEmbedding I I n M (M ⊕ M₂) where
  toContMDiffMap :=
    ⟨Sum.inl, (Manifold.IsSmoothEmbedding.sumInl (I := I) (n := n) (M := M) (M' := M₂)).contMDiff⟩
  isSmoothEmbedding_toFun := Manifold.IsSmoothEmbedding.sumInl (I := I) (n := n) (M := M) (M' := M₂)

@[simp]
theorem sumInl_apply {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    [IsManifold I n M] [IsManifold I n M₂] (x : M) :
    (sumInl (I := I) (n := n) (M := M) (M₂ := M₂)) x = Sum.inl x := by
  rfl

/-- The right coproduct inclusion as a bundled smooth embedding. -/
def sumInr {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    [IsManifold I n M] [IsManifold I n M₂] :
    SmoothEmbedding I I n M₂ (M ⊕ M₂) where
  toContMDiffMap :=
    ⟨Sum.inr, (Manifold.IsSmoothEmbedding.sumInr (I := I) (n := n) (M := M) (M' := M₂)).contMDiff⟩
  isSmoothEmbedding_toFun := Manifold.IsSmoothEmbedding.sumInr (I := I) (n := n) (M := M) (M' := M₂)

@[simp]
theorem sumInr_apply {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    [IsManifold I n M] [IsManifold I n M₂] (x : M₂) :
    (sumInr (I := I) (n := n) (M := M) (M₂ := M₂)) x = Sum.inr x := by
  rfl

end SmoothEmbedding

end TauCeti
