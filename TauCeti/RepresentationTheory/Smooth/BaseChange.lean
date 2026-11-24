/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Change of coefficients for smooth representations

Let `A → B` be a homomorphism of commutative rings and `ρ` a representation of a topological group
`G` on an `A`-module `V`. The base change `B ⊗_A V` (`Representation.baseChange`) of a smooth
representation is smooth: the stabilizer of `b ⊗ v` contains the open stabilizer of `v`.

## Main results

* `Representation.stabilizer_le_stabilizer_baseChange_tmul`: the stabilizer of `b ⊗ v` contains
  the stabilizer of `v`.
* `Representation.isSmooth_baseChange`: base change preserves smoothness.
-/

public section

open TensorProduct

namespace Representation

/-! ### Smoothness of the base change -/

section Smooth

variable {A B G V : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Group G]
  [AddCommMonoid V] [Module A V] {ρ : Representation A G V}

/-- The stabilizer of `b ⊗ v` in the base change contains the stabilizer of `v`. -/
theorem stabilizer_le_stabilizer_baseChange_tmul (b : B) (v : V) :
    ρ.stabilizer v ≤ (baseChange B ρ).stabilizer (b ⊗ₜ[A] v) := fun g hg ↦ by
  rw [mem_stabilizer, baseChange_apply, LinearMap.baseChange_tmul, mem_stabilizer.1 hg]

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- **Base change preserves smoothness.** -/
instance isSmooth_baseChange [IsSmooth ρ] : IsSmooth (baseChange B ρ) := by
  rw [isSmooth_iff_forall_mem_smoothVectors]
  intro x
  induction x with
  | add x y hx hy => exact (baseChange B ρ).smoothVectors.toSubmodule.add_mem hx hy
  | tmul b v =>
    exact mem_smoothVectors_iff.2 (Subgroup.isOpen_mono
      (stabilizer_le_stabilizer_baseChange_tmul b v) (IsSmooth.isOpen_stabilizer v))

end Smooth

end Representation
