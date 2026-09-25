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
`α`- and `β`-curve labels. A generator is the matching datum in the domain of
`TauCeti.Sym.matchingTuple`, specialized through `TauCeti.Sym.piInterEquiv` to the two label
fibers: a permutation of the curve indices and an intersection point in each paired fiber.

The curve count `n` is independent of surface genus. For a multi-pointed diagram of genus `g`
with `k` basepoints on each side, the usual curve count is `g + k - 1`; this file records only
that count and the incidence data. Abstract region incidence data, basepoints, domains, and
admissibility are recorded on top of it in `TauCeti.LowDimTopology.Heegaard.Domain`; they are
needed to define the differential.

## Main definitions

* `TauCeti.HeegaardIntersectionSystem`: finite intersection data with two curve labels.
* `TauCeti.HeegaardIntersectionSystem.Generator`: a permutation of the curve indices together
  with one intersection point in each paired `α`- and `β`-label fiber.
* `TauCeti.HeegaardIntersectionSystem.generatorEquivPiInter`: the identification with common
  points of the two symmetric products.
* `TauCeti.HeegaardIntersectionSystem.generator_card`: the permanent count of generators.
* `TauCeti.HeegaardIntersectionSystem.generatorOf`: the low-level constructor from a chosen
  permutation and point choice.
* `TauCeti.HeegaardIntersectionSystem.generatorOfPointChoice`: the point-choice constructor from
  bijective `β`-labels.
* `TauCeti.HeegaardIntersectionSystem.point` and `TauCeti.HeegaardIntersectionSystem.betaEquiv`:
  accessors for the chosen point and its curve matching.
* `TauCeti.HeegaardIntersectionSystem.generatorChain`: the `0`-chain of the points of a
  generator.

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
structure HeegaardIntersectionSystem (n : ℕ) (Point : Type u) where
  /-- A finite enumeration of the intersection points. -/
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

/-- The generators are finite because the intersection point type has a finite enumeration. -/
instance : Fintype D.Generator := by
  letI := D.pointFintype
  infer_instance

/-- The generators are the common points of the symmetric products of the `α`- and `β`-label
fibers. -/
noncomputable def generatorEquivPiInter : D.Generator ≃
    ↥(Sym.pi (fun i => {p | D.alpha p = i}) ∩ Sym.pi (fun j => {p | D.beta p = j})) :=
  Sym.piInterEquiv (A := fun i => {p | D.alpha p = i})
    (B := fun j => {p | D.beta p = j}) (pairwise_disjoint_fiber D.alpha)
    (pairwise_disjoint_fiber D.beta)

/-- The generator equivalence sends a matching to its unordered tuple of intersection points. -/
@[simp]
theorem generatorEquivPiInter_apply (g : D.Generator) :
    D.generatorEquivPiInter g = Sym.matchingTuple g := by
  simpa only [generatorEquivPiInter] using
    (Sym.piInterEquiv_apply (A := fun i => {p | D.alpha p = i})
      (B := fun j => {p | D.beta p = j}) (pairwise_disjoint_fiber D.alpha)
      (pairwise_disjoint_fiber D.beta) g)

/-- The number of generators is the permanent of the matrix of labeled intersection counts. -/
theorem generator_card :
    Fintype.card D.Generator =
      (Matrix.of (fun i j => Nat.card {p // D.alpha p = i ∧ D.beta p = j})).permanent := by
  have hPoint : (Set.univ : Set Point).Finite :=
    @Set.finite_univ Point (@Finite.of_fintype Point D.pointFintype)
  classical
  rw [Fintype.card_eq_nat_card]
  rw [Nat.card_congr D.generatorEquivPiInter]
  exact Sym.natCard_pi_inter_pi (A := fun i => {p | D.alpha p = i})
    (B := fun j => {p | D.beta p = j}) (pairwise_disjoint_fiber D.alpha)
    (pairwise_disjoint_fiber D.beta) (by
      intro i j
      exact hPoint.subset (by
        intro p hp
        exact Set.mem_univ p))

/-- Construct a generator from a point choice and its two curve-label conditions. -/
def generatorOf (σ : Equiv.Perm (Fin n)) (p : Fin n → Point)
    (hα : ∀ i, D.alpha (p i) = i) (hβ : ∀ i, D.beta (p i) = σ i) :
    D.Generator :=
  ⟨σ, fun i => ⟨p i, hα i, hβ i⟩⟩

/-- The curve-index permutation stored by `generatorOf`. -/
@[simp]
theorem generatorOf_fst (σ : Equiv.Perm (Fin n)) (p : Fin n → Point)
    (hα : ∀ i, D.alpha (p i) = i) (hβ : ∀ i, D.beta (p i) = σ i) :
    (D.generatorOf σ p hα hβ).1 = σ := by
  simp [generatorOf]

/-- The point stored by `generatorOf` at index `i`. -/
@[simp]
theorem generatorOf_val (σ : Equiv.Perm (Fin n)) (p : Fin n → Point)
    (hα : ∀ i, D.alpha (p i) = i) (hβ : ∀ i, D.beta (p i) = σ i)
    (i : Fin n) : ((D.generatorOf σ p hα hβ).2 i : Point) = p i := by
  simp [generatorOf]

/-- Construct a generator from a point choice whose `β`-labels are bijective. -/
noncomputable def generatorOfPointChoice (p : Fin n → Point)
    (hα : ∀ i, D.alpha (p i) = i)
    (hβ : Function.Bijective (D.beta ∘ p)) : D.Generator :=
  ⟨Equiv.ofBijective (D.beta ∘ p) hβ, fun i =>
    ⟨p i, hα i, by
      rw [Equiv.coe_ofBijective, Function.comp_apply]
      rfl⟩⟩

/-- The curve-index matching stored by `generatorOfPointChoice`. -/
@[simp]
theorem generatorOfPointChoice_fst (p : Fin n → Point)
    (hα : ∀ i, D.alpha (p i) = i)
    (hβ : Function.Bijective (D.beta ∘ p)) :
    (D.generatorOfPointChoice p hα hβ).1 = Equiv.ofBijective (D.beta ∘ p) hβ := by
  simp [generatorOfPointChoice]

/-- The point stored by `generatorOfPointChoice` at index `i`. -/
@[simp]
theorem generatorOfPointChoice_val (p : Fin n → Point)
    (hα : ∀ i, D.alpha (p i) = i)
    (hβ : Function.Bijective (D.beta ∘ p)) (i : Fin n) :
    ((D.generatorOfPointChoice p hα hβ).2 i : Point) = p i := by
  simp [generatorOfPointChoice]

/-- The chosen point over `i`. -/
def point (g : D.Generator) (i : Fin n) : Point := g.2 i

/-- The curve-index matching stored by a generator. -/
def betaEquiv (g : D.Generator) : Equiv.Perm (Fin n) := g.1

/-- The chosen-point accessor is the second projection of a matching. -/
@[simp]
theorem point_apply (g : D.Generator) (i : Fin n) : D.point g i = g.2 i := by
  simp [point]

/-- The matching index is the `β`-label of the chosen point. -/
@[simp]
theorem betaEquiv_apply (g : D.Generator) (i : Fin n) :
    D.betaEquiv g i = D.beta (D.point g i) := by
  simpa [betaEquiv, point] using (g.2 i).property.2.symm

/-- The chosen point over `i` has `α`-label `i`. -/
@[simp]
theorem alpha_coe (g : D.Generator) (i : Fin n) : D.alpha (g.2 i) = i :=
  (g.2 i).property.1

/-- The chosen point over `i` has `β`-label given by the matching permutation. -/
@[simp]
theorem beta_coe (g : D.Generator) (i : Fin n) : D.beta (g.2 i) = g.1 i :=
  (g.2 i).property.2

/-- An intersection point belongs to a generator exactly when it is the generator's point on
its own `α`-curve. -/
@[simp]
theorem mem_range_point_iff (g : D.Generator) (q : Point) :
    q ∈ Set.range (D.point g) ↔ D.point g (D.alpha q) = q := by
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro h
    exact ⟨_, h⟩

/-- The `0`-chain of a generator: the indicator function of its intersection points. -/
noncomputable def generatorChain (g : D.Generator) : Point → ℤ :=
  (Set.range (D.point g)).indicator 1

@[simp]
theorem generatorChain_apply [DecidableEq Point] (g : D.Generator) (q : Point) :
    D.generatorChain g q = if D.point g (D.alpha q) = q then 1 else 0 := by
  simp only [generatorChain, Set.indicator_apply, mem_range_point_iff, Pi.one_apply]

/-- Two generators with the same chosen points are equal. -/
@[ext]
theorem Generator.ext {g g' : D.Generator} (h : ∀ i, (g.2 i : Point) = g'.2 i) : g = g' :=
  Sym.matching_ext (A := fun i => {p | D.alpha p = i})
    (B := fun j => {p | D.beta p = j}) (pairwise_disjoint_fiber D.beta) h

end HeegaardIntersectionSystem

end TauCeti
