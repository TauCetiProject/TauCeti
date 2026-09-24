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
domains, and admissibility are not encoded here; they are needed to define the differential.

## Main definitions

* `TauCeti.HeegaardIntersectionSystem`: finite intersection data with two curve labels.
* `TauCeti.HeegaardIntersectionSystem.Generator`: a permutation of the curve indices together
  with one intersection point in each paired `α`- and `β`-label fiber.

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
@[ext]
structure HeegaardIntersectionSystem (n : ℕ) (Point : Type u) [Fintype Point] where
  /-- The `α`-curve containing an intersection point. -/
  alpha : Point → Fin n
  /-- The `β`-curve containing an intersection point. -/
  beta : Point → Fin n

namespace HeegaardIntersectionSystem

variable {n : ℕ} {Point : Type u} [Fintype Point]
  (D : HeegaardIntersectionSystem n Point)

/-- The generators of `D` as matchings between the fibers of its `α`- and `β`-labels. -/
abbrev Generator : Type u :=
  (σ : Equiv.Perm (Fin n)) ×
    ∀ i, ↥({p | D.alpha p = i} ∩ {p | D.beta p = σ i})

/-- The generators are finite because the intersection point type is finite. -/
instance : Fintype D.Generator := inferInstance

/-- The chosen point over `i` has `α`-label `i`. -/
@[simp]
theorem alpha_coe (g : D.Generator) (i : Fin n) : D.alpha (g.2 i) = i :=
  (g.2 i).property.1

/-- The chosen point over `i` has `β`-label given by the matching permutation. -/
@[simp]
theorem beta_coe (g : D.Generator) (i : Fin n) : D.beta (g.2 i) = g.1 i :=
  (g.2 i).property.2

/-- Two generators with the same chosen points are equal. -/
@[ext]
theorem Generator.ext {g g' : D.Generator} (h : ∀ i, (g.2 i : Point) = g'.2 i) : g = g' := by
  have hσ : g.1 = g'.1 := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hi := D.beta_coe g i
    have hi' := D.beta_coe g' i
    rw [h i] at hi
    exact congrArg Fin.val (hi.symm.trans hi')
  rcases g with ⟨σ, p⟩
  rcases g' with ⟨τ, q⟩
  change σ = τ at hσ
  cases hσ
  congr 1
  funext i
  exact Subtype.ext (h i)

end HeegaardIntersectionSystem

end TauCeti
