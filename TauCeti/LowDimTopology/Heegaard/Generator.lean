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
  its enumeration and two curve labels.
* `TauCeti.HeegaardIntersectionSystem.Generator`: the matching type from
  `TauCeti.Sym.piInterEquiv`, specialized to the system's `α`- and `β`-label fibers.

## References

The generator convention is the one used in P. Ozsváth and Z. Szabó, *Holomorphic disks and
topological invariants for closed three-manifolds*, Ann. of Math. **159** (2004),
[arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1.
-/

public section

namespace TauCeti

universe u

/-- Finite intersection data for two equally sized curve systems. The finite enumeration records
the point set, and each point has one `α`-curve label and one `β`-curve label; geometric surface
and region data are additional structure. -/
structure HeegaardIntersectionSystem (n : ℕ) (Point : Type u) where
  /-- The finite enumeration of intersection points. -/
  pointFintype : Fintype Point
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

/-- The generators are finite because the intersection point type is finite. -/
noncomputable instance : Fintype D.Generator := by
  letI := D.pointFintype
  classical
  letI (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fintype
      ↥({p | D.alpha p = i} ∩ {p | D.beta p = σ i}) := inferInstance
  exact Fintype.ofFinite _

/-- The generators of `D` are the common points of the symmetric products of its `α`- and
`β`-label fibers. -/
noncomputable def generatorEquivPiInter : D.Generator ≃
    ↥(Sym.pi (fun i => {p | D.alpha p = i}) ∩ Sym.pi (fun j => {p | D.beta p = j})) :=
  Sym.piInterEquiv (A := fun i => {p | D.alpha p = i}) (B := fun j => {p | D.beta p = j})
    (pairwise_disjoint_fiber D.alpha) (pairwise_disjoint_fiber D.beta)

/-- The generator equivalence sends a matching to its unordered tuple of intersection points. -/
@[simp]
theorem generatorEquivPiInter_apply (g : D.Generator) :
    D.generatorEquivPiInter g = Sym.matchingTuple g := by
  simpa only [generatorEquivPiInter] using
    (Sym.piInterEquiv_apply (A := fun i => {p | D.alpha p = i})
      (B := fun j => {p | D.beta p = j}) (pairwise_disjoint_fiber D.alpha)
      (pairwise_disjoint_fiber D.beta) g)

/-- A diagonal incidence system has one intersection point for each corresponding pair of
curves, and its identity choice is a generator. This supplies a concrete nonempty example of the
generator predicate. -/
abbrev diagonal (n : ℕ) : HeegaardIntersectionSystem n (Fin n) where
  pointFintype := inferInstance
  alpha := id
  beta := id

/-- The identity choice is a generator of the diagonal incidence system. -/
def diagonalGenerator (n : ℕ) : (diagonal n).Generator :=
  ⟨Equiv.refl _, fun i => ⟨i, rfl, rfl⟩⟩

end HeegaardIntersectionSystem

end TauCeti
