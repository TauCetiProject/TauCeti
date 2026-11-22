/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Ideal multiples of the top submodule of a finite product

## Main results

* `Submodule.smul_top_eq_pi`: in a finite product of modules, `I • ⊤` is the product of the
  `I • ⊤` of the factors.
* `Submodule.smul_top_pi_quotient_eq_bot`: `I` kills `∏ i, R ⧸ J i` when `I ≤ J i` for all `i`.
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

/-- An ideal `I` kills the product `∏ i, R ⧸ J i` when it lies in every `J i`. -/
theorem smul_top_pi_quotient_eq_bot {R : Type*} [CommRing R] {J : ι → Ideal R} {I : Ideal R}
    (h : ∀ i, I ≤ J i) : I • (⊤ : Submodule R (∀ i, R ⧸ J i)) = ⊥ := by
  refine eq_bot_iff.2 (smul_le.2 fun r hr x _ ↦ ?_)
  rw [mem_bot]
  funext i
  obtain ⟨a, ha⟩ := Quotient.mk_surjective (J i) (x i)
  rw [Pi.smul_apply, ← ha, Pi.zero_apply, ← Quotient.mk_smul, Quotient.mk_eq_zero, smul_eq_mul]
  exact Ideal.mul_mem_right a _ (h i hr)

end Submodule
