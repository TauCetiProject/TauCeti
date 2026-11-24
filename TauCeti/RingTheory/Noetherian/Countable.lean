/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.List
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Countably many submodules of a countable Noetherian module

Every submodule of a Noetherian module `M` is spanned by a finite subset of `M`, and is determined
by that subset. So if `M` is countable it has countably many submodules
(`Submodule.instCountableOfIsNoetherian`). In particular a countable Noetherian ring has countably
many ideals.
-/

public section

namespace Submodule

/-- A countable Noetherian module has countably many submodules: each is spanned by a finite
subset, which determines it. -/
instance instCountableOfIsNoetherian {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [IsNoetherian R M] [Countable M] : Countable (Submodule R M) := by
  classical
  refine Function.Injective.countable
    (f := fun N : Submodule R M ↦ (IsNoetherian.noetherian N).choose) fun N N' h ↦ ?_
  rw [← (IsNoetherian.noetherian N).choose_spec, ← (IsNoetherian.noetherian N').choose_spec]
  exact congrArg (fun s : Finset M ↦ span R (s : Set M)) h

end Submodule
