/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Sym.Pi

/-!
# Generators from finite Heegaard intersection data

The generators of a pointed Heegaard diagram choose one intersection point on each `α`-curve
and each `β`-curve. This file records incidence data by assigning each intersection point its
`α`- and `β`-curve labels. A generator is the existing symmetric-power matching datum specialized
to the two label fibers: a permutation of the curve indices and an intersection point in each
paired fiber. The curve count is independent of surface genus; the diagram data relates it to
genus and basepoint count.

This is the generator layer of the combinatorial Heegaard diagram. Surface regions, basepoints,
domains, and admissibility are not encoded here; they are needed to define the differential and
come later.

## Main definitions

* `TauCeti.HeegaardIntersectionSystem`: a finite set of intersection points with
  their two curve labels.
* `TauCeti.HeegaardIntersectionSystem.Generator`: the matching type from
  `TauCeti.Sym.piInterEquiv`, specialized to the system's `α`- and `β`-label fibers.

## References

The generator convention is the one used in Ozsváth--Stipsicz--Szabó, *Holomorphic Disks and
Topological Invariants for Closed Three-Manifolds*, Section 2.
-/

public section

namespace TauCeti

universe u

/-- Finite intersection data for two equally sized curve systems. A point has one `α`-curve label
and one `β`-curve label; geometric surface and region data are additional structure. -/
structure HeegaardIntersectionSystem (n : ℕ) (Point : Type u) where
  /-- The `α`-curve containing an intersection point. -/
  alpha : Point → Fin n
  /-- The `β`-curve containing an intersection point. -/
  beta : Point → Fin n

namespace HeegaardIntersectionSystem

variable {n : ℕ} {Point : Type u}
  (D : HeegaardIntersectionSystem n Point)

/-- The generators of `D` as matchings between the fibers of its `α`- and `β`-labels. -/
abbrev Generator : Type u :=
  (σ : Equiv.Perm (Fin n)) ×
    ∀ i, ↥({p | D.alpha p = i} ∩ {p | D.beta p = σ i})

/-- A diagonal incidence system has one intersection point for each corresponding pair of
curves, and its identity choice is a generator. This supplies a concrete nonempty example of the
generator predicate. -/
abbrev diagonal (n : ℕ) : HeegaardIntersectionSystem n (Fin n) where
  alpha := id
  beta := id

/-- The identity choice is a generator of the diagonal incidence system. -/
def diagonalGenerator (n : ℕ) : (diagonal n).Generator :=
  ⟨Equiv.refl _, fun i => ⟨i, rfl, rfl⟩⟩

end HeegaardIntersectionSystem

end TauCeti
