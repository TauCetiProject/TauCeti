/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Generators from finite Heegaard intersection data

The generators of a pointed Heegaard diagram choose one intersection point on each `α`-curve
and each `β`-curve. This file records just that finite incidence data: a set of intersection
points with their `α`- and `β`-curve labels. A generator is a choice over the `α`-curves for
which the `β` labels form a permutation. The curve count is independent of surface genus; the
diagram data relates it to genus and basepoint count.

This is the generator layer of the combinatorial Heegaard diagram. Surface regions, basepoints,
domains, and admissibility are not encoded here; they are needed to define the differential and
come later.

## Main definitions

* `TauCeti.HeegaardIntersectionSystem`: a finite set of intersection points with
  their two curve labels.
* `TauCeti.HeegaardIntersectionSystem.IsGenerator`: a choice of one point over each `α` label
  whose `β` labels are bijective.
* `TauCeti.HeegaardIntersectionSystem.Generator`: the type of such choices.

## References

The generator convention is the one used in Ozsváth--Stipsicz--Szabó, *Holomorphic Disks and
Topological Invariants for Closed Three-Manifolds*, Section 2.
-/

public section

namespace TauCeti

universe u

/-- Finite intersection data for two equally sized curve systems. A point has one `α`-curve label
and one `β`-curve label; geometric surface and region data are additional structure. -/
structure HeegaardIntersectionSystem (n : ℕ) (Point : Type u) [Fintype Point] where
  /-- The `α`-curve containing an intersection point. -/
  alpha : Point → Fin n
  /-- The `β`-curve containing an intersection point. -/
  beta : Point → Fin n

namespace HeegaardIntersectionSystem

variable {n : ℕ} {Point : Type u} [Fintype Point]
  (D : HeegaardIntersectionSystem n Point)

/-- A choice of intersection points is a generator when it chooses a point on each `α`-curve
and the chosen points lie on distinct `β`-curves. Since there are `n` choices and `n` `β`-curves,
the latter condition is expressed by bijectivity. -/
def IsGenerator (x : Fin n → Point) : Prop :=
  (∀ a, D.alpha (x a) = a) ∧ Function.Bijective (D.beta ∘ x)

/-- The generators determined by finite Heegaard intersection data. -/
abbrev Generator : Type u := {x : Fin n → Point // D.IsGenerator x}

/-- The chosen point of a generator lies on its indexed `α`-curve. -/
@[simp]
theorem alpha_apply (x : D.Generator) (a : Fin n) : D.alpha (x.1 a) = a :=
  x.property.1 a

/-- The `β`-curve labels of a generator form a bijection. -/
theorem beta_bijective (x : D.Generator) : Function.Bijective (D.beta ∘ x.1) :=
  x.property.2

/-- The points chosen by a generator are pairwise distinct. -/
theorem injective (x : D.Generator) : Function.Injective x.1 := by
  intro a b hab
  have h := congrArg D.alpha hab
  simpa only [D.alpha_apply x] using h

/-- The `β`-curve selected by a generator, as an equivalence of curve indices. -/
noncomputable abbrev betaEquiv (x : D.Generator) : Fin n ≃ Fin n :=
  Equiv.ofBijective (D.beta ∘ x.1) (D.beta_bijective x)

theorem betaEquiv_apply (x : D.Generator) (a : Fin n) :
    D.betaEquiv x a = D.beta (x.1 a) :=
  by simp [betaEquiv, Function.comp_apply]

/-- Construct a generator from a point choice with bijective `β` labels. -/
def generatorOfPointChoice (x : Fin n → Point) (hα : ∀ a, D.alpha (x a) = a)
    (hβ : Function.Bijective (D.beta ∘ x)) : D.Generator :=
  ⟨x, ⟨hα, hβ⟩⟩

/-- A diagonal incidence system has one intersection point for each corresponding pair of
curves, and its identity choice is a generator. This supplies a concrete nonempty example of the
generator predicate. -/
abbrev diagonal (n : ℕ) : HeegaardIntersectionSystem n (Fin n) where
  alpha := id
  beta := id

/-- The identity choice is a generator of the diagonal incidence system. -/
def diagonalGenerator (n : ℕ) : (diagonal n).Generator :=
  ⟨id, ⟨fun _ => rfl, Equiv.bijective (Equiv.refl _)⟩⟩

end HeegaardIntersectionSystem

end TauCeti
