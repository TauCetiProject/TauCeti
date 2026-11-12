/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finitely generated lattices in a finite module

Let `M` be a finite `A`-module and also an `R`-module. Then `M` contains a finitely generated
`R`-submodule spanning `M` over `A`: the `R`-span of any finite `A`-generating set. The typical
case is a subring `R` of `A`, such as a ring of definition of a Huber ring, where such a submodule
is a lattice of `M` over `R` whose filtrations describe the natural topology of `M`.

## Main results

* `TauCeti.Module.Finite.exists_fg_span_eq_top`: a finite `A`-module has a finitely generated
  `R`-submodule spanning it over `A`.
-/

public section

namespace TauCeti.Module.Finite

/-- A finite `A`-module that is also an `R`-module has a finitely generated `R`-submodule
spanning it over `A`. -/
theorem exists_fg_span_eq_top (R : Type*) {A M : Type*} [Semiring R] [Semiring A]
    [AddCommMonoid M] [Module R M] [Module A M] [Module.Finite A M] :
    ∃ M₀ : Submodule R M, M₀.FG ∧ Submodule.span A (M₀ : Set M) = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  refine ⟨Submodule.span R s, ⟨s, rfl⟩, top_unique ?_⟩
  rw [← hs]
  exact Submodule.span_mono Submodule.subset_span

end TauCeti.Module.Finite
