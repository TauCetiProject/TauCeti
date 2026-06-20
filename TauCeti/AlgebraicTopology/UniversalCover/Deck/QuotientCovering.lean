/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Covering.Quotient
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient

/-!
# A regular covering is a quotient covering map for its deck group

For a covering map `p : E → B` with preconnected total space whose deck action is regular
(surjective, with `Deck p` acting transitively on every fibre), `p` exhibits `B` as the
quotient of `E` by the deck transformation group: `p` is a `IsQuotientCoveringMap` for
`Deck p`. This is the deck-side formulation of the universal-covers roadmap statement that
`UniversalCover x₀ / π₁(X, x₀) ≃ X`, packaged so that it consumes Mathlib's quotient
covering map theory rather than re-deriving it.

The proof feeds the existing Tau Ceti deck-action API into Mathlib's
`isQuotientCoveringMap_iff_isCoveringMap_and`: the action is free on a preconnected covering
(`TauCeti.Deck.isCancelSMul`) and continuous (the generic subgroup instance), regularity
gives surjectivity and the orbit characterization of fibres, and `p` is the covering map by
hypothesis. Conversely, for a preconnected covering, being a quotient covering map for the
deck group is *equivalent* to the deck action being regular.

## Main declarations

* `TauCeti.Deck.apply_eq_iff_mem_orbit`: for a regular map, two points share a projection
  exactly when they lie in a common deck orbit.
* `TauCeti.Deck.IsRegular.isQuotientCoveringMap`: a regular, preconnected covering map is a
  quotient covering map for its deck group.
* `TauCeti.Deck.isQuotientCoveringMap_iff_isRegular`: for a preconnected covering map, being a
  quotient covering map for the deck group is equivalent to regularity of the deck action.
* `TauCeti.Deck.IsRegular.isOpenQuotientMap`: such a covering map is an open quotient map.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stages 0.3 and 1,
where the quotient of the cover by the deck group is identified with the base via Mathlib's
`IsQuotientCoveringMap` (`Mathlib/Topology/Covering/Quotient.lean`).
-/

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

omit [TopologicalSpace B] in
/-- For a map with regular deck action, two points of the total space have the same
projection exactly when they lie in a common orbit of the deck transformation group. The
forward direction is regularity; the converse holds because deck transformations preserve
the projection. -/
lemma apply_eq_iff_mem_orbit (hreg : IsRegular p) {e₁ e₂ : E} :
    p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit (Deck p) e₂ := by
  change Setoid.ker p e₁ e₂ ↔ MulAction.orbitRel (Deck p) E e₁ e₂
  rw [orbitRel_eq_ker_of_exists_apply_eq (isRegular_iff_exists_apply_eq.mp hreg).2]

/-- A regular covering map with preconnected total space is a quotient covering map for its
deck transformation group: it presents the base as the quotient `E / Deck p`. -/
theorem IsRegular.isQuotientCoveringMap [PreconnectedSpace E] (hreg : IsRegular p)
    (hp : IsCoveringMap p) : IsQuotientCoveringMap p (Deck p) := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  exact ⟨hp, hreg.1, inferInstance, isCancelSMul hp,
    fun {e₁ e₂} => apply_eq_iff_mem_orbit hreg⟩

/-- For a covering map with preconnected total space, being a quotient covering map for the
deck transformation group is equivalent to regularity of the deck action. -/
theorem isQuotientCoveringMap_iff_isRegular [PreconnectedSpace E] (hp : IsCoveringMap p) :
    IsQuotientCoveringMap p (Deck p) ↔ IsRegular p := by
  refine ⟨fun h => ⟨h.surjective, fun b => ⟨fun e e' => ?_⟩⟩,
    fun hreg => hreg.isQuotientCoveringMap hp⟩
  have hee : p e'.1 = p e.1 := (e'.2 : p e'.1 = b).trans (e.2 : p e.1 = b).symm
  obtain ⟨φ, hφ⟩ := h.apply_eq_iff_mem_orbit.mp hee
  exact ⟨φ, Subtype.ext ((fiber_smul_coe_eq_smul φ e).trans hφ)⟩

/-- A regular covering map with preconnected total space is an open quotient map. -/
theorem IsRegular.isOpenQuotientMap [PreconnectedSpace E] (hreg : IsRegular p)
    (hp : IsCoveringMap p) : IsOpenQuotientMap p :=
  (hreg.isQuotientCoveringMap hp).isOpenQuotientMap

end Deck

end TauCeti
