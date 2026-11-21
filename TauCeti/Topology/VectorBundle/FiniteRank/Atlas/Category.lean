/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Basic

/-!
# Category structure on variable-rank bundle atlases

`TauCeti.FiniteRankAtlas 𝕜 X` inherits its `Category` instance from
`TauCeti.VariableRankBundle.category` in `TauCeti.Topology.VectorBundle.FiniteRank.Glued`,
which provides morphisms `VariableRankBundle.Hom`, `totalSpaceFunctor`, `fiberFunctor`, `isoMk`,
and `Iso.variableRankBundle_rank_eq`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Small variable-rank coordinate atlases form a category of continuous fibrewise-linear maps. -/
instance : Category (FiniteRankAtlas 𝕜 X) := VariableRankBundle.category

end TauCeti.FiniteRankAtlas
