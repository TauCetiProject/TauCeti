/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuous derivations

For a topological `A`-algebra `B` and a topological `B`-module `M` with continuous addition and
continuous scalar multiplication by constants of `B`, the continuous `A`-derivations `B → M`
form a `B`-submodule `TauCeti.continuousDerivationSubmodule A B M` of `Derivation A B M`.

## Main definitions

* `TauCeti.continuousDerivationSubmodule`: the `B`-submodule of continuous `A`-derivations
  `B → M`.
-/

public section

namespace TauCeti

variable (A B M : Type*) [CommSemiring A] [CommSemiring B] [Algebra A B]
  [TopologicalSpace B] [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousConstSMul B M]

/-- The `B`-submodule of continuous `A`-derivations `B → M`. -/
def continuousDerivationSubmodule : Submodule B (Derivation A B M) where
  carrier := {δ | Continuous δ}
  add_mem' h₁ h₂ := h₁.add h₂
  zero_mem' := continuous_zero
  smul_mem' _ _ h := h.const_smul _

variable {A B M}

/-- An `A`-derivation belongs to `TauCeti.continuousDerivationSubmodule A B M` iff it is
continuous. -/
@[simp] theorem mem_continuousDerivationSubmodule {δ : Derivation A B M} :
    δ ∈ continuousDerivationSubmodule A B M ↔ Continuous δ :=
  Iff.rfl

end TauCeti
