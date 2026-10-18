/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finitely generated lattices in a finite module over a scalar tower

Let `R` act on `A` and let `M` be a finite `A`-module on which the actions of `R` and `A` form a
scalar tower. Then `M` contains a finitely generated `R`-submodule spanning `M` over `A`: the
`R`-span of any finite `A`-generating set. The typical case is a subring `R` of `A`, such as a
ring of definition of a Huber ring, where such a submodule is a lattice of `M` over `R` whose
filtrations describe the natural topology of `M`.

## Main results

* `TauCeti.Module.Finite.exists_fg_span_eq_top`: a finite `A`-module has a finitely generated
  `R`-submodule spanning it over `A`.
-/

public section

namespace TauCeti.Module.Finite

/-- A finite `A`-module has a finitely generated `R`-submodule spanning it over `A`, for any
scalar tower `R → A → M`. -/
theorem exists_fg_span_eq_top (R : Type*) {A M : Type*} [Semiring R] [Semiring A] [SMul R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Finite A M] :
    ∃ M₀ : Submodule R M, M₀.FG ∧ Submodule.span A (M₀ : Set M) = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  exact ⟨Submodule.span R s, ⟨s, rfl⟩, by rw [Submodule.span_span_of_tower, hs]⟩

end TauCeti.Module.Finite
