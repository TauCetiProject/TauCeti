/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category

/-!
# Preadditive structure on variable-rank bundle atlases

`TauCeti.FiniteRankAtlas 𝕜 X` inherits its `Preadditive` structure from
`TauCeti.VariableRankBundle.preadditive` in
`TauCeti.Topology.VectorBundle.FiniteRank.Glued.Category`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Composition of bundle-atlas morphisms is bilinear on the pointwise abelian hom groups. -/
instance : Preadditive (FiniteRankAtlas 𝕜 X) := VariableRankBundle.preadditive

end TauCeti.FiniteRankAtlas
