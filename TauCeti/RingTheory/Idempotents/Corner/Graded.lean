/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Basic
public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Corners of graded algebras

The corner `aAb` of a `ℤ`-graded algebra `A` cut out by two elements of degree zero is a graded
subspace: it contains the homogeneous components of each of its elements.

## Main results

* `TauCeti.coe_decompose_mem_cornerSubmodule`: the homogeneous components of an element of a
  corner `aAb` cut out by elements of degree zero lie in that corner.
-/

public section

namespace TauCeti

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- The homogeneous components of an element of the corner `aAb` cut out by two elements of
degree zero lie in the same corner. -/
theorem coe_decompose_mem_cornerSubmodule {a b x : A} (ha₀ : a ∈ 𝒜 0) (hb₀ : b ∈ 𝒜 0)
    (hx : x ∈ cornerSubmodule k a b) (p : ℤ) :
    (DirectSum.decompose 𝒜 x p : A) ∈ cornerSubmodule k a b := by
  rw [cornerSubmodule_def, LinearMap.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  simp only [LinearMap.mulLeftRight_apply]
  rw [DirectSum.coe_decompose_mul_of_right_mem_zero 𝒜 hb₀,
    DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 ha₀]
  exact mul_mul_mem_cornerSubmodule k a b _

end TauCeti
