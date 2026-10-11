/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of modules of linear maps over a base ring

Let `A` be a semiring and `R` a ring acting on an `A`-module `M` through `A`-linear maps.
If `P` is finitely generated over `A` and `M` is Noetherian over `R`, then the `R`-module
`Hom_A(P, M)` is finitely generated: a surjection `A ^ n → P` embeds it in `M ^ n`.
In particular, this applies when `R` is Noetherian and `M` is finitely generated over `R`.
For example, for a finite group `G` the `ℤ_p`-module of `ℤ_p[G]`-linear maps between finitely
generated `ℤ_p[G]`-modules is finitely generated. No freeness or projectivity is assumed, unlike
Mathlib's `Module.Finite.linearMap`.

## Main results

* `Module.Finite.linearMap_of_isNoetherian`: `Hom_A(P, M)` is finite over `R`.
-/

public section

variable {R A P M : Type*} [Ring R] [Semiring A]
  [AddCommMonoid P] [Module A P] [AddCommGroup M] [Module A M] [Module R M] [SMulCommClass A R M]

/-- For `P` finitely generated over a semiring `A` and `M` Noetherian over a ring `R` whose
action commutes with `A`, the `R`-module of `A`-linear maps `P → M` is finitely generated. -/
theorem Module.Finite.linearMap_of_isNoetherian [Module.Finite A P] [IsNoetherian R M] :
    Module.Finite R (P →ₗ[A] M) := by
  -- Precomposition with a surjection `A ^ n → P` embeds the maps `P → M` into `M ^ n`.
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  exact Module.Finite.of_injective
    ((LinearEquiv.piRing A M (Fin n) R).toLinearMap ∘ₗ LinearMap.lcomp R M π)
    ((LinearEquiv.piRing A M (Fin n) R).injective.comp
      (LinearMap.lcomp_injective_of_surjective π hπ))
