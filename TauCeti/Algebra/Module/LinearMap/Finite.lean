/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of modules of linear maps over a base ring

Let `A` be a ring and `R` a commutative Noetherian ring acting on an `A`-module `M` through
`A`-linear maps. If `P` is finitely generated over `A` and `M` is finitely generated over `R`, then
the `R`-module `Hom_A(P, M)` is finitely generated: a surjection `A ^ n → P` embeds it in `M ^ n`.
For example, for a finite group `G` the `ℤ_p`-module of `ℤ_p[G]`-linear maps between finitely
generated `ℤ_p[G]`-modules is finitely generated. No freeness or projectivity is assumed, unlike
Mathlib's `Module.Finite.linearMap`.

## Main results

* `Module.Finite.linearMap_of_isNoetherianRing`: `Hom_A(P, M)` is finite over `R`.
-/

public section

variable {R A P M : Type*} [CommRing R] [IsNoetherianRing R] [Ring A]
  [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M] [Module R M] [SMulCommClass A R M]

/-- **Linear maps into a finite module over a Noetherian base.** For `P` finitely generated over
`A` and `M` finitely generated over the commutative Noetherian ring `R`, whose action on `M`
commutes with `A`, the `R`-module of `A`-linear maps `P → M` is finitely generated. -/
theorem Module.Finite.linearMap_of_isNoetherianRing [Module.Finite A P] [Module.Finite R M] :
    Module.Finite R (P →ₗ[A] M) := by
  -- Precomposition with a surjection `A ^ n → P` embeds the maps `P → M` into `M ^ n`.
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  refine Module.Finite.of_injective
    ((LinearEquiv.piRing A M (Fin n) R).toLinearMap ∘ₗ LinearMap.lcomp R M π) fun f g hfg ↦ ?_
  have : f ∘ₗ π = g ∘ₗ π := (LinearEquiv.piRing A M (Fin n) R).injective hfg
  exact LinearMap.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := hπ x
    exact LinearMap.congr_fun this y
