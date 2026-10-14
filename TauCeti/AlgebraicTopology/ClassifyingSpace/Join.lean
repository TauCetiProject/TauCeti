/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Family

/-!
# Milnor's total space

For a group `G`, `universalGSpace G` is the weak realization of the countable join of copies of
`G`, with chosen vertex `(0, 1)`. This is the total-space construction used in Milnor's model of
a classifying space; contractibility and the group action are not asserted here. Homomorphisms
induce continuous maps preserving the base point and respecting identities and composition.

The construction follows J. Milnor, *Construction of universal bundles, II*, Ann. of Math.
63 (1956). It uses the indexed join in
`TauCeti.AlgebraicTopology.SimplicialComplex.Join.Family` and the weak realization and simplicial
realization maps in `TauCeti.AlgebraicTopology.SimplicialComplex.Realization`.
-/

public section

open AbstractSimplicialComplex
open PreAbstractSimplicialComplex (SimplicialMap)
open TauCeti.SimplicialComplex

namespace TauCeti.ClassifyingSpace

variable (G : Type*)

/-- Milnor's total space: the weak realization of the countable join of copies of `G`. -/
noncomputable abbrev universalGSpace := Realization (joinComplex (fun _ : ℕ => G))

/-- The chosen base point of the countable join of copies of a group. -/
noncomputable def universalGSpaceBasepoint [One G] : universalGSpace G :=
  vertex (joinComplex (fun _ : ℕ => G)) ⟨0, 1⟩

@[simp]
theorem universalGSpaceBasepoint_val [One G] :
    (universalGSpaceBasepoint G : (Σ _ : ℕ, G) →₀ ℝ) = Finsupp.single ⟨0, 1⟩ 1 :=
  vertex_val _ _

variable {G} {H : Type*} [MulOneClass G] [MulOneClass H]

/-- A homomorphism induces a continuous map of Milnor total spaces by applying it to
vertex labels and leaving indices unchanged. -/
noncomputable def universalGSpaceMap (φ : G →* H) : C(universalGSpace G, universalGSpace H) := by
  classical
  exact (joinComplexMap (fun _ : ℕ => φ)).realizationMap

/-- The induced map pushes forward barycentric coordinates. -/
@[simp]
theorem universalGSpaceMap_val (φ : G →* H) (x : universalGSpace G) :
    (universalGSpaceMap φ x : (Σ _ : ℕ, H) →₀ ℝ) =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G => (⟨v.1, φ v.2⟩ : Σ _ : ℕ, H)) x.1 := by
  classical
  simp [universalGSpaceMap]

@[simp]
theorem universalGSpaceMap_basepoint (φ : G →* H) :
    universalGSpaceMap φ (universalGSpaceBasepoint G) = universalGSpaceBasepoint H := by
  classical
  simp [universalGSpaceMap, universalGSpaceBasepoint]

/-- The induced continuous map respects identities. -/
@[simp]
theorem universalGSpaceMap_id :
    universalGSpaceMap (MonoidHom.id G) = ContinuousMap.id (universalGSpace G) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp [universalGSpaceMap_val]

/-- The induced continuous map respects composition. -/
@[simp]
theorem universalGSpaceMap_comp {K : Type*} [MulOneClass K] (ψ : H →* K) (φ : G →* H) :
    universalGSpaceMap (ψ.comp φ) = (universalGSpaceMap ψ).comp (universalGSpaceMap φ) := by
  classical
  unfold universalGSpaceMap
  rw [← SimplicialMap.realizationMap_comp, joinComplexMap_comp]
  simp only [MonoidHom.coe_comp, Function.comp_def]

end TauCeti.ClassifyingSpace
