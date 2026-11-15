/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root system that need no further theory.

## Main results

* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.moduleFinite_coweight_of_isRootSystem`: for a finite root system, the coweight
  module is finitely generated.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- For a finite root system over a commutative ring, the coweight module `N` is finitely generated
(in particular `FiniteDimensional R N` when `R` is a field), since it is spanned by the finitely
many coroots. -/
theorem moduleFinite_coweight_of_isRootSystem (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] : Module.Finite R N :=
  .of_fg_top (Submodule.fg_def.mpr
    ⟨Set.range P.coroot, Set.finite_range _, IsRootSystem.span_coroot_eq_top⟩)

end RootPairing
