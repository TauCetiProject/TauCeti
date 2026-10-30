/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
-- Non-public: `Module.finrank_pi_fintype` and `Module.Finite.of_restrictScalars_finite` are used
-- only inside proofs, and no exported statement here mentions a product module or `Module.Finite`
-- over the ring, so downstream importers do not pay for either module.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules over a simple Artinian ring are classified by their dimension

Over a simple Artinian ring `R` all simple modules are isomorphic: Mathlib records this as
`IsSimpleRing.isIsotypic`, which says that any two simple submodules of any `R`-module are
isomorphic. A semisimple module is a direct sum of simple ones, so a finitely generated `R`-module
is `Sⁿ` for a **fixed** simple module `S` and a single natural number `n`, and `n` is the only
invariant there is.

This file turns that into the working statement: if `R` is moreover an algebra over a field `K` and
`M`, `N` are `R`-modules which are finite-dimensional over `K`, then

  `M ≃ₗ[R] N ↔ finrank K M = finrank K N`.

The dimension count is the bookkeeping that converts "the same number of simple summands" into a
condition that can be checked, and it is what makes the classification usable: two `R`-module
structures put on the *same* finite-dimensional `K`-vector space are automatically isomorphic. That
is exactly the input the Skolem-Noether theorem needs, in
`TauCeti/Algebra/CentralSimple/SkolemNoether.lean`.

## Main results

* `TauCeti.IsIsotypicOfType.of_isSimpleRing`: over a simple Artinian ring, every module is isotypic
  of the type of any fixed simple module. This upgrades Mathlib's `IsSimpleRing.isIsotypic`, which
  compares simple submodules of a single module, to a comparison against a fixed simple module,
  which is what lets two different modules be compared with each other.
* `IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`: two finite-dimensional modules over a
  finite-dimensional simple `K`-algebra with the same `K`-dimension are isomorphic.
* `IsSimpleRing.nonempty_linearEquiv_iff_finrank_eq`: the two-way form, the classification
  itself.

## Implementation notes

The simple module the classification compares `M` and `N` against is a minimal left ideal
`S : Submodule R R`, produced as an atom of the lattice of submodules of the regular module rather
than assumed. Taking it inside `R` rather than inside `M` is what makes it available to `M` and `N`
at once, and it inherits the `K`-module structure from `R`, so its dimension is finite and nonzero
and can be cancelled.

The two classification statements ask `R` to be finite-dimensional over `K` and do not also ask it
to be Artinian: `IsArtinianRing.of_finite` derives that from finite-dimensionality, so callers never
have to supply it. Only `TauCeti.IsIsotypicOfType.of_isSimpleRing`, which has no field in sight,
takes `IsArtinianRing R` as a hypothesis.

Simplicity of `R` is not weakened to semisimplicity: over a semisimple ring with more than one block
the dimension is not a complete invariant, since a module can distribute the same total dimension
over the blocks in different ways.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, Chapter 1, and R. S. Pierce,
*Associative Algebras*, GTM 88, Chapter 3.
-/

public section

open Module

variable {R : Type*} [Ring R] [IsSimpleRing R]

namespace TauCeti

variable (R) in
/-- Over a **simple Artinian** ring `R`, every `R`-module is isotypic of the type of any fixed
simple module `S`: every simple submodule of every `R`-module is isomorphic to `S`.

Mathlib's `IsSimpleRing.isIsotypic` compares two simple submodules of one and the same module. The
content added here is that the comparison can be made against a simple module fixed once and for
all, so that simple submodules of *different* modules become comparable. -/
theorem IsIsotypicOfType.of_isSimpleRing [IsArtinianRing R] (S : Type*) [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] (M : Type*) [AddCommGroup M] [Module R M] :
    IsIsotypicOfType R M S := by
  intro m _
  -- `R` is semisimple, so `m` and `S` are both isomorphic to minimal left ideals of `R`, and those
  -- two ideals are isomorphic because `R` is isotypic over itself.
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
  obtain ⟨J, ⟨eS⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R S
  have : IsSimpleModule R I := IsSimpleModule.congr e.symm
  have : IsSimpleModule R J := IsSimpleModule.congr eS.symm
  exact ⟨(e.trans (IsSimpleRing.isIsotypic R R I J).some.symm).trans eS.symm⟩

end TauCeti

namespace IsSimpleRing

variable (K : Type*) [Field K] [Algebra K R] [FiniteDimensional K R]
  {M : Type*} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]
  {N : Type*} [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N]
  [FiniteDimensional K N]

/-- **Modules over a simple Artinian algebra are classified by their dimension.** If `R` is a
finite-dimensional simple `K`-algebra and `M`, `N` are `R`-modules which are finite-dimensional over
`K`, then equal `K`-dimension forces an `R`-linear isomorphism. -/
theorem nonempty_linearEquiv_of_finrank_eq (h : finrank K M = finrank K N) :
    Nonempty (M ≃ₗ[R] N) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  obtain ⟨S, _⟩ := IsSemisimpleModule.exists_simple_submodule R R
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R M
  have : Module.Finite R N := Module.Finite.of_restrictScalars_finite K R N
  -- Both modules are powers `Sⁿ` and `Sᵐ` of the same minimal left ideal `S`.
  obtain ⟨n, ⟨eM⟩⟩ := (TauCeti.IsIsotypicOfType.of_isSimpleRing R ↥S M).linearEquiv_fun
  obtain ⟨m, ⟨eN⟩⟩ := (TauCeti.IsIsotypicOfType.of_isSimpleRing R ↥S N).linearEquiv_fun
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  -- Comparing `K`-dimensions gives `n * finrank K S = m * finrank K S` with `finrank K S ≠ 0`.
  obtain rfl : n = m := by
    simpa [(eM.restrictScalars K).finrank_eq, (eN.restrictScalars K).finrank_eq,
      Module.finrank_pi_fintype, Module.finrank_pos.ne'] using h
  exact ⟨eM.trans eN.symm⟩

/-- **The classification of finite-dimensional modules over a simple Artinian algebra**: the
`K`-dimension is a complete invariant. The forward implication holds over any ring; the content is
the converse, `IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`. -/
theorem nonempty_linearEquiv_iff_finrank_eq :
    Nonempty (M ≃ₗ[R] N) ↔ finrank K M = finrank K N :=
  ⟨fun ⟨e⟩ ↦ (e.restrictScalars K).finrank_eq, nonempty_linearEquiv_of_finrank_eq K⟩

end IsSimpleRing
