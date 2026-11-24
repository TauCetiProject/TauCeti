/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Ideal multiples of the top submodule of a finite product

## Main results

* `Submodule.smul_top_eq_pi`: in a finite product of modules, `I • ⊤` is the product of the
  `I • ⊤` of the factors.
-/

public section

namespace Submodule

variable {R ι : Type*} [Semiring R] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

/-- In a finite product, the ideal multiple `I • ⊤` is the product of the ideal multiples
`I • ⊤` of the factors. -/
theorem smul_top_eq_pi [Finite ι] (I : Ideal R) :
    I • (⊤ : Submodule R (∀ i, M i)) = pi Set.univ fun i ↦ I • (⊤ : Submodule R (M i)) := by
  classical
  have := Fintype.ofFinite ι
  refine le_antisymm (smul_le.mpr fun r hr x _ ↦ mem_pi.mpr fun i _ ↦ smul_mem_smul hr mem_top)
    fun x hx ↦ ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem fun i _ ↦ smul_top_le_comap_smul_top I (LinearMap.single R M i)
    ((mem_pi (p := fun i ↦ I • (⊤ : Submodule R (M i)))).mp hx i (Set.mem_univ i))

end Submodule
