/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Right uniformities and homomorphisms

The canonical right uniformity makes a topological group a right-uniform group. An inducing
homomorphism between right-uniform groups is uniformly inducing, so an embedding homomorphism
is a uniform embedding. These facts let topological group isomorphisms transport completeness
without requiring two-sided uniformities.

The inducing and embedding lemmas generalize Mathlib's
`MonoidHom.isUniformInducing_of_isInducing` and `MonoidHom.isUniformEmbedding_of_isEmbedding`
from uniform groups to right-uniform groups. All results also have additive forms.
-/

public section

open Topology

/-- The canonical right uniformity on a topological group makes it a right-uniform group. -/
@[to_additive /-- The canonical right uniformity on a topological additive group makes it a
right-uniform additive group. -/]
theorem IsTopologicalGroup.isRightUniformGroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    @IsRightUniformGroup G (IsTopologicalGroup.rightUniformSpace G) _ := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  exact ⟨uniformity_eq_comap_nhds_one' G⟩

variable {G H F : Type*} [Group G] [UniformSpace G] [IsRightUniformGroup G]
  [Group H] [UniformSpace H] [IsRightUniformGroup H] [FunLike F G H] [MonoidHomClass F G H]
  {f : F}

/-- An inducing homomorphism between right-uniform groups is uniformly inducing. -/
@[to_additive /-- An inducing homomorphism between right-uniform additive groups is uniformly
inducing. -/]
theorem MonoidHom.isUniformInducing_of_isInducing_right (hf : IsInducing f) :
    IsUniformInducing f where
  comap_uniformity := by
    simp [uniformity_eq_comap_nhds_one, Filter.comap_comap, Function.comp_def, hf.nhds_eq_comap]

/-- An embedding homomorphism between right-uniform groups is a uniform embedding. -/
@[to_additive /-- An embedding homomorphism between right-uniform additive groups is a uniform
embedding. -/]
theorem MonoidHom.isUniformEmbedding_of_isEmbedding_right (hf : IsEmbedding f) :
    IsUniformEmbedding f where
  toIsUniformInducing := MonoidHom.isUniformInducing_of_isInducing_right hf.isInducing
  injective := hf.injective
