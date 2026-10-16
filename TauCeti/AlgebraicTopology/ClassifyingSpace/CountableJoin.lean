/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Indexed

/-!
# The countable join model for a universal group space

Specializing the indexed join to the constant family on `ℕ` gives `universalGSpace G`, the
underlying space in Milnor's join construction.  The distinguished vertex over index zero
supplies its base point when `G` has a chosen unit.  Later constructions can define the diagonal
group action directly on these labelled vertices. Homomorphisms induce continuous maps
preserving the base point and respecting identities and composition.

## Main definitions

* `TauCeti.universalGSpace`: the realization of the countable join of copies of `G`.
* `TauCeti.universalGSpaceBasepoint`: the distinguished vertex over index zero.
* `MonoidHom.universalGSpaceMap`: the map induced by a homomorphism.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

universe u v

namespace TauCeti

attribute [local instance] Classical.decEq

/-- Milnor's countable join of copies of a type, realized with the weak topology. -/
abbrev universalGSpace (G : Type u) : Type _ :=
  (indexedJoin fun _ : ℕ => G).Realization

/-- The distinguished vertex over index zero in the countable join of copies of a type with a
chosen unit. -/
def universalGSpaceBasepoint (G : Type u) [One G] : universalGSpace G :=
  (indexedJoin fun _ : ℕ => G).vertex ⟨0, 1⟩

/-- The barycentric coordinates of the distinguished point are concentrated at the vertex
labelled by index zero and the chosen unit. -/
@[simp]
theorem universalGSpaceBasepoint_val (G : Type u) [One G] :
    (universalGSpaceBasepoint G : (Σ _ : ℕ, G) →₀ ℝ) = Finsupp.single ⟨0, 1⟩ 1 := by
  rw [universalGSpaceBasepoint, AbstractSimplicialComplex.vertex_val]

end TauCeti

namespace MonoidHom

open TauCeti

variable {G : Type u} {H : Type v} [MulOne G] [MulOne H]

/-- A homomorphism induces a continuous map of Milnor total spaces by applying it to
vertex labels and leaving indices unchanged. -/
noncomputable def universalGSpaceMap (φ : G →* H) : C(universalGSpace G, universalGSpace H) := by
  classical
  letI : DecidableEq ℕ := Classical.decEq ℕ
  exact (indexedJoinMap _root_.id Function.injective_id (fun _ : ℕ => φ)).realizationMap

/-- The induced map pushes forward barycentric coordinates. -/
@[simp]
theorem universalGSpaceMap_val (φ : G →* H) (x : universalGSpace G) :
    (universalGSpaceMap φ x : (Σ _ : ℕ, H) →₀ ℝ) =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G => (⟨v.1, φ v.2⟩ : Σ _ : ℕ, H)) x.1 := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  simp [universalGSpaceMap]

/-- The map induced by a homomorphism preserves the distinguished base point. -/
@[simp]
theorem universalGSpaceMap_basepoint (φ : G →* H) :
    universalGSpaceMap φ (universalGSpaceBasepoint G) = universalGSpaceBasepoint H := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
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
theorem universalGSpaceMap_comp {K : Type*} [MulOne K] (ψ : H →* K) (φ : G →* H) :
    universalGSpaceMap (ψ.comp φ) = (universalGSpaceMap ψ).comp (universalGSpaceMap φ) := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  unfold universalGSpaceMap
  rw [← PreAbstractSimplicialComplex.SimplicialMap.realizationMap_comp,
    ← indexedJoinMap_comp]
  congr 1

end MonoidHom
