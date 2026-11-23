/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.GFinite

/-!
# `K`-finite vectors of a continuous representation

Let `π` be a continuous representation of a group `G` on a topological vector space `E` over a
field `k`, and let `K` be a subgroup of `G`, typically a maximal compact subgroup of a real
reductive group. A vector `v` is **`K`-finite** when its `K`-orbit `{π k v | k ∈ K}` spans a
finite-dimensional subspace. This is the `G`-finiteness predicate `Representation.IsGFinite` of the
algebraic representation underlying the restriction `π.restrict K.subtype`, so the `K`-finite
vectors `ContRepresentation.kFiniteSubmodule π K` and their elementary API (closure under the
linear operations, invariance under `K`, preservation by intertwining maps) are those of
`Representation.gFiniteSubmodule`, which is not restated here.

Forgetting continuity and restricting to `K` produce exactly the orbit `{π k v | k ∈ K}` of the
ambient space (`ContRepresentation.isKFinite_iff`), so the `K`-finite submodule is a subset of `E`
itself, and no continuity or compactness hypothesis enters. A `K`-finite vector is also
`K'`-finite for every subgroup `K' ≤ K`; for `K = ⊤` it is `G`-finite for `π.toRepresentation`.

## Main definitions

* `ContRepresentation.IsKFinite π K v`: the `K`-orbit of `v` spans a finite-dimensional subspace.
* `ContRepresentation.kFiniteSubmodule π K`: the submodule of `K`-finite vectors.

## Main statements

* `ContRepresentation.isKFinite_iff`: `K`-finiteness is finite dimensionality of the span of the
  orbit `π k v`, `k ∈ K`.
* `ContRepresentation.mem_kFiniteSubmodule`: membership in the `K`-finite submodule.
* `ContRepresentation.kFinite_of_finiteDimensional`: every vector of a finite-dimensional space is
  `K`-finite.
* `ContRepresentation.IsKFinite.mono`: `K`-finiteness passes to smaller subgroups.
* `ContRepresentation.isKFinite_top_iff`: `⊤`-finiteness is `G`-finiteness.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), §4.1, pp. 20–22.
* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), §1.4.
-/

public section

namespace ContRepresentation

variable {k G E : Type*} [Field k] [Group G] [AddCommGroup E] [Module k E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] (π : ContRepresentation k G E) (K : Subgroup G)

/-- A vector `v` is **`K`-finite** for the continuous representation `π` when its `K`-orbit
`{π k v | k ∈ K}` spans a finite-dimensional subspace: `G`-finiteness for the restriction of `π`
to the subgroup `K`. -/
abbrev IsKFinite (v : E) : Prop :=
  (π.restrict K.subtype).toRepresentation.IsGFinite v

/-- The **`K`-finite vectors** of a continuous representation, as a submodule: the `G`-finite
vectors of the restriction of `π` to the subgroup `K`. -/
abbrev kFiniteSubmodule : Submodule k E :=
  (π.restrict K.subtype).toRepresentation.gFiniteSubmodule

/-- `K`-finiteness is finite dimensionality of the span of the orbit `π k v`, `k ∈ K`, in the
ambient space. -/
theorem isKFinite_iff (v : E) :
    π.IsKFinite K v ↔
      FiniteDimensional k (Submodule.span k (Set.range fun x : K => π (x : G) v)) :=
  Representation.isGFinite_iff _ v

/-- Membership in the `K`-finite submodule is `K`-finiteness. -/
theorem mem_kFiniteSubmodule {v : E} : v ∈ π.kFiniteSubmodule K ↔ π.IsKFinite K v :=
  Representation.mem_gFiniteSubmodule _

/-- Every vector of a finite-dimensional continuous representation is `K`-finite. -/
theorem kFinite_of_finiteDimensional [FiniteDimensional k E] (v : E) : π.IsKFinite K v :=
  Representation.IsGFinite.of_finiteDimensional v

variable {π K} in
/-- A `K`-finite vector is `K'`-finite for every subgroup `K' ≤ K`: the smaller orbit spans a
subspace of the larger span. -/
theorem IsKFinite.mono {K' : Subgroup G} (hK : K' ≤ K) {v : E} (hv : π.IsKFinite K v) :
    π.IsKFinite K' v := by
  have : FiniteDimensional k (Submodule.span k (Set.range fun x : K => π (x : G) v)) :=
    (π.isKFinite_iff K v).mp hv
  exact Representation.IsGFinite.of_forall_apply_mem
    (W := Submodule.span k (Set.range fun x : K => π (x : G) v)) fun x : K' =>
      Submodule.subset_span ⟨⟨x, hK x.property⟩, rfl⟩

/-- `K`-finiteness for the whole group `⊤` is `G`-finiteness of the underlying representation. -/
theorem isKFinite_top_iff (v : E) : π.IsKFinite ⊤ v ↔ π.toRepresentation.IsGFinite v := by
  rw [isKFinite_iff, Representation.isGFinite_iff]
  have : Set.range (fun x : (⊤ : Subgroup G) => π (x : G) v) = Set.range fun g : G => π g v :=
    Set.ext fun w => ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨g, hg⟩ => ⟨⟨g, Subgroup.mem_top g⟩, hg⟩⟩
  rw [this]
  rfl

end ContRepresentation
