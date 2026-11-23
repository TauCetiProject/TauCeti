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
linear operations, preservation by intertwining maps) are those of
`Representation.gFiniteSubmodule`, which is not restated here. Only invariance under `K` is
restated, so that it is phrased with `π (x : G)` rather than the restricted representation.

Forgetting continuity and restricting to `K` produce exactly the orbit `{π k v | k ∈ K}` of the
ambient space (`ContRepresentation.isKFinite_iff`), so the `K`-finite submodule is a subset of `E`
itself, and no continuity or compactness hypothesis enters. A `K`-finite vector is also
`K'`-finite for every subgroup `K' ≤ K`; for `K = ⊤` it is `G`-finite for `π.toRepresentation`.
Every vector of a finite-dimensional space is `K`-finite by
`Representation.IsGFinite.of_finiteDimensional`, and membership in `kFiniteSubmodule` is
`Representation.mem_gFiniteSubmodule`, both of which apply through the abbreviations.

## Main definitions

* `ContRepresentation.IsKFinite π K v`: the `K`-orbit of `v` spans a finite-dimensional subspace.
* `ContRepresentation.kFiniteSubmodule π K`: the submodule of `K`-finite vectors.

## Main statements

* `ContRepresentation.isKFinite_iff`: `K`-finiteness is finite dimensionality of the span of the
  orbit `π k v`, `k ∈ K`.
* `ContRepresentation.IsKFinite.mono`: `K`-finiteness passes to smaller subgroups.
* `ContRepresentation.IsKFinite.apply`, `ContRepresentation.apply_mem_kFiniteSubmodule`: the
  `K`-finite vectors are invariant under `π x`, `x ∈ K`.
* `ContRepresentation.isKFinite_top_iff`: `⊤`-finiteness is `G`-finiteness.
* `ContRepresentation.kFiniteSubmodule_antitone`: the `K`-finite submodule grows as `K` shrinks.
* `ContRepresentation.kFiniteSubmodule_top`: the `⊤`-finite submodule is the `G`-finite submodule.

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
  -- This is the one place where the restriction is unfolded: the restricted representation
  -- acts by `π (x : G)` by definition (`restrict_apply_apply`, `Subgroup.coe_subtype`), and
  -- `toRepresentation` applies the same continuous linear map through
  -- `ContinuousLinearMap.toLinearMapRingHom`. Inside the span the two sides reach `Semiring k`
  -- through different paths (`Ring` and `CommSemiring`), so `simp` does not rewrite this
  -- coercion there and the identification is definitional.
  Representation.isGFinite_iff _ v

variable {π K} in
/-- A `K`-finite vector is `K'`-finite for every subgroup `K' ≤ K`: the smaller orbit spans a
subspace of the larger span. -/
theorem IsKFinite.mono {K' : Subgroup G} (hK : K' ≤ K) {v : E} (hv : π.IsKFinite K v) :
    π.IsKFinite K' v := by
  rw [isKFinite_iff] at hv ⊢
  refine Submodule.finiteDimensional_of_le
    (Submodule.span_mono (t := Set.range fun x : K => π (x : G) v) ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨Subgroup.inclusion hK x, by simp only [Subgroup.coe_inclusion]⟩

variable {π K} in
/-- The `K`-finite vectors are invariant under `π x` for `x ∈ K`. -/
theorem IsKFinite.apply {v : E} (hv : π.IsKFinite K v) (x : K) : π.IsKFinite K (π (x : G) v) :=
  -- `π (x : G) v` is the restricted representation applied to `v`, by definition (see
  -- `isKFinite_iff`).
  Representation.IsGFinite.apply hv x

/-- The `K`-finite submodule is invariant under `π x` for `x ∈ K`. -/
theorem apply_mem_kFiniteSubmodule {v : E} (hv : v ∈ π.kFiniteSubmodule K) (x : K) :
    π (x : G) v ∈ π.kFiniteSubmodule K :=
  (Representation.mem_gFiniteSubmodule _).2 <|
    IsKFinite.apply ((Representation.mem_gFiniteSubmodule _).1 hv) x

/-- `K`-finiteness for the whole group `⊤` is `G`-finiteness of the underlying representation. -/
theorem isKFinite_top_iff (v : E) : π.IsKFinite ⊤ v ↔ π.toRepresentation.IsGFinite v := by
  rw [isKFinite_iff, Representation.isGFinite_iff]
  have : Set.range (fun x : (⊤ : Subgroup G) => π (x : G) v) = Set.range fun g : G => π g v :=
    Set.ext fun w => ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨g, hg⟩ => ⟨⟨g, Subgroup.mem_top g⟩, hg⟩⟩
  rw [this]
  -- `π.toRepresentation g` is `π g` viewed as a linear map, by definition of `toRepresentation`
  -- (see `isKFinite_iff` for why `simp` does not rewrite this coercion).
  rfl

/-- The `K`-finite submodule is antitone in `K`: shrinking the subgroup can only add `K`-finite
vectors. -/
theorem kFiniteSubmodule_antitone : Antitone π.kFiniteSubmodule := fun _ _ hK _ hv =>
  (Representation.mem_gFiniteSubmodule _).2 <|
    IsKFinite.mono hK ((Representation.mem_gFiniteSubmodule _).1 hv)

/-- The `⊤`-finite submodule is the `G`-finite submodule of the underlying representation. -/
theorem kFiniteSubmodule_top : π.kFiniteSubmodule ⊤ = π.toRepresentation.gFiniteSubmodule :=
  Submodule.ext fun v => (Representation.mem_gFiniteSubmodule _).trans <|
    (π.isKFinite_top_iff v).trans (Representation.mem_gFiniteSubmodule _).symm

end ContRepresentation
