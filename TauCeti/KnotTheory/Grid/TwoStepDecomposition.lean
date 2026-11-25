/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# Two-step decompositions of grid domains

Many identities in grid homology compare sums over composite domains: a domain of one kind from a
grid state `x` to an intermediate grid state, followed by a domain of another kind from there to a
grid state `z`. This file packages such a pair, for arbitrary families of domains indexed by their
source and target states, as `TauCeti.GridTwoStepDecomposition`. The two-step rectangle
decompositions of the square of the grid differential and the rectangle--pentagon,
hexagon--rectangle and pentagon--pentagon decompositions of grid commutation all specialize it.

## Main definitions

* `TauCeti.GridTwoStepDecomposition`: a domain followed by a second domain through an
  intermediate grid state.
* `TauCeti.GridTwoStepDecomposition.decompositionsOf`: the finite family of two-step
  decompositions whose constituent domains lie in prescribed finite families.
* `TauCeti.GridTwoStepDecomposition.map`: apply a map of domains to each of the two steps.

## Main results

* `TauCeti.GridTwoStepDecomposition.map_injective`: mapping both steps by injective maps is
  injective.
* `TauCeti.GridTwoStepDecomposition.mem_decompositionsOf` characterizes membership in
  `decompositionsOf`, and `TauCeti.GridTwoStepDecomposition.map_mem_decompositionsOf` that of a
  mapped decomposition.
* `TauCeti.GridTwoStepDecomposition.card_decompositionsOf` counts `decompositionsOf`.
* `TauCeti.GridTwoStepDecomposition.sum_decompositionsOf` rewrites a sum over `decompositionsOf`
  as the iterated sum over the intermediate state and the two constituent domains.
-/

public section

namespace TauCeti

/-- A pair of composable domains through an intermediate grid state. -/
structure GridTwoStepDecomposition {n : ℕ}
    (A B : GridState n → GridState n → Type*) (x z : GridState n) where
  /-- The grid state at which the two domains meet. -/
  middle : GridState n
  /-- The first domain, from the source to the intermediate state. -/
  first : A x middle
  /-- The second domain, from the intermediate state to the target. -/
  second : B middle z

namespace GridTwoStepDecomposition

variable {n : ℕ} {A B : GridState n → GridState n → Type*} {x z : GridState n}

/-- Two two-step decompositions are equal when their intermediate states and domains agree. -/
@[ext]
theorem ext {D E : GridTwoStepDecomposition A B x z}
    (hmiddle : D.middle = E.middle) (hfirst : HEq D.first E.first)
    (hsecond : HEq D.second E.second) : D = E := by
  cases D
  cases E
  simp_all

/-- When each constituent domain is unique between its endpoints, two decompositions are equal
as soon as their intermediate states agree. -/
theorem ext_of_middle_eq [∀ y, Subsingleton (A x y)] [∀ y, Subsingleton (B y z)]
    {D E : GridTwoStepDecomposition A B x z} (hmiddle : D.middle = E.middle) : D = E := by
  obtain ⟨m, P, Q⟩ := D
  obtain ⟨m', P', Q'⟩ := E
  obtain rfl : m = m' := hmiddle
  rw [Subsingleton.elim P P', Subsingleton.elim Q Q']

section map

variable {A' B' : GridState n → GridState n → Type*}

/-- Apply a map of domains to each step of a two-step decomposition from `x` to `z`. As the source
`x` and the target `z` are fixed, the step maps `f` and `g` are indexed by the intermediate state
alone. -/
@[expose] def map (f : ∀ y : GridState n, A x y → A' x y) (g : ∀ y : GridState n, B y z → B' y z)
    (D : GridTwoStepDecomposition A B x z) : GridTwoStepDecomposition A' B' x z :=
  ⟨D.middle, f _ D.first, g _ D.second⟩

/-- `map` on an explicit decomposition. -/
@[simp]
theorem map_mk (f : ∀ y : GridState n, A x y → A' x y) (g : ∀ y : GridState n, B y z → B' y z)
    (m : GridState n) (P : A x m) (Q : B m z) :
    map f g ⟨m, P, Q⟩ = ⟨m, f m P, g m Q⟩ := rfl

/-- `map` keeps the intermediate state. -/
@[simp]
theorem map_middle (f : ∀ y : GridState n, A x y → A' x y)
    (g : ∀ y : GridState n, B y z → B' y z) (D : GridTwoStepDecomposition A B x z) :
    (D.map f g).middle = D.middle := rfl

/-- The first step of a mapped decomposition is the image of the first step. -/
@[simp]
theorem map_first (f : ∀ y : GridState n, A x y → A' x y)
    (g : ∀ y : GridState n, B y z → B' y z) (D : GridTwoStepDecomposition A B x z) :
    (D.map f g).first = f D.middle D.first := rfl

/-- The second step of a mapped decomposition is the image of the second step. -/
@[simp]
theorem map_second (f : ∀ y : GridState n, A x y → A' x y)
    (g : ∀ y : GridState n, B y z → B' y z) (D : GridTwoStepDecomposition A B x z) :
    (D.map f g).second = g D.middle D.second := rfl

/-- Mapping both steps by the identity does nothing. -/
@[simp]
theorem map_id (D : GridTwoStepDecomposition A B x z) :
    D.map (fun _ => id) (fun _ => id) = D := rfl

/-- Mapping twice is mapping by the composites. -/
@[simp]
theorem map_map {A'' B'' : GridState n → GridState n → Type*}
    (f : ∀ y : GridState n, A x y → A' x y) (g : ∀ y : GridState n, B y z → B' y z)
    (f' : ∀ y : GridState n, A' x y → A'' x y) (g' : ∀ y : GridState n, B' y z → B'' y z)
    (D : GridTwoStepDecomposition A B x z) :
    (D.map f g).map f' g' = D.map (fun y => f' y ∘ f y) (fun y => g' y ∘ g y) := rfl

/-- Mapping both steps by injective maps is injective. -/
theorem map_injective {f : ∀ y : GridState n, A x y → A' x y}
    {g : ∀ y : GridState n, B y z → B' y z}
    (hf : ∀ y, Function.Injective (f y)) (hg : ∀ y, Function.Injective (g y)) :
    Function.Injective (map f g) := by
  rintro ⟨m, P, Q⟩ ⟨m', P', Q'⟩ h
  obtain rfl : m = m' := congrArg middle h
  simp only [map_mk, mk.injEq, heq_eq_eq, true_and] at h
  rw [hf _ h.1, hg _ h.2]

end map

private def sigmaEquiv :
    GridTwoStepDecomposition A B x z ≃ Σ y : GridState n, Σ _first : A x y, B y z where
  toFun D := ⟨D.middle, D.first, D.second⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite family of two-step decompositions selected by prescribed domain families. -/
noncomputable def decompositionsOf
    (first : ∀ u v : GridState n, Finset (A u v))
    (second : ∀ u v : GridState n, Finset (B u v))
    (x z : GridState n) : Finset (GridTwoStepDecomposition A B x z) := by
  classical
  exact ((Finset.univ.sigma fun y => (first x y).sigma fun _ => second y z).map
    (sigmaEquiv (A := A) (B := B) (x := x) (z := z)).symm.toEmbedding)

/-- Membership in `decompositionsOf` is membership of both constituent domains. -/
@[simp]
theorem mem_decompositionsOf
    (first : ∀ u v : GridState n, Finset (A u v))
    (second : ∀ u v : GridState n, Finset (B u v))
    (D : GridTwoStepDecomposition A B x z) :
    D ∈ decompositionsOf first second x z ↔
      D.first ∈ first x D.middle ∧ D.second ∈ second D.middle z := by
  classical
  simp [decompositionsOf, sigmaEquiv]

/-- Membership of a mapped decomposition in `decompositionsOf` is membership of the images of its
two steps, stated in terms of the intermediate state `D.middle` of the original decomposition. -/
@[simp high]
theorem map_mem_decompositionsOf {A' B' : GridState n → GridState n → Type*}
    (f : ∀ y : GridState n, A x y → A' x y) (g : ∀ y : GridState n, B y z → B' y z)
    (first : ∀ u v : GridState n, Finset (A' u v))
    (second : ∀ u v : GridState n, Finset (B' u v))
    (D : GridTwoStepDecomposition A B x z) :
    D.map f g ∈ decompositionsOf first second x z ↔
      f D.middle D.first ∈ first x D.middle ∧ g D.middle D.second ∈ second D.middle z :=
  mem_decompositionsOf first second (D.map f g)

/-- The number of selected two-step decompositions is the sum, over intermediate states, of the
products of the numbers of selected constituent domains. -/
theorem card_decompositionsOf
    (first : ∀ u v : GridState n, Finset (A u v))
    (second : ∀ u v : GridState n, Finset (B u v)) (x z : GridState n) :
    (decompositionsOf first second x z).card = ∑ y, (first x y).card * (second y z).card := by
  classical
  simp [decompositionsOf, Finset.card_sigma]

/-- A sum over selected two-step decompositions is the corresponding iterated sum. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (first : ∀ u v : GridState n, Finset (A u v))
    (second : ∀ u v : GridState n, Finset (B u v))
    (w : ∀ y, A x y → B y z → M) :
    ∑ D ∈ decompositionsOf first second x z, w D.middle D.first D.second =
      ∑ y, ∑ P ∈ first x y, ∑ Q ∈ second y z, w y P Q := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

end GridTwoStepDecomposition

end TauCeti
