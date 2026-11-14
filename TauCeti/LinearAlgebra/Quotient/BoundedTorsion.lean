/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bounded power torsion in quotients

A power-torsion bound on the range of a map gives the same bound on its source modulo its
kernel. For a complex, bounds on power torsion in its homology and in the last map's range
give a bound in the preceding cokernel. These statements require no finiteness or regularity
assumptions and are independent of completion.

## References

* [Stacks Project, Lemma 52.12.7](https://stacks.math.columbia.edu/tag/0EII),
  for the three-term complex cokernel bound.
-/

public section

namespace LinearMap

variable {R : Type*} [Ring R] {r : R} {k l : ℕ}
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- A power-torsion bound on the range of a linear map gives the same bound on its source
modulo its kernel. -/
theorem pow_smul_eq_zero_quotient_ker_of_bounded_torsion_range (g : M →ₗ[R] N)
    (hrange : ∀ y ∈ g.range, (∃ n : ℕ, r ^ n • y = 0) → r ^ l • y = 0)
    (x : M ⧸ g.ker) (hx : ∃ n : ℕ, r ^ n • x = 0) : r ^ l • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨n, hn⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_ker,
    map_smul] at hn ⊢
  exact hrange (g y) (mem_range_self g y) ⟨n, hn⟩

/-- In a complex, bounds on power torsion in the homology and in the last map's range give
a bound in the preceding cokernel. Annihilation of the whole homology is not required. -/
theorem pow_smul_eq_zero_coker_of_bounded_torsion_homology (g : M →ₗ[R] N)
    {h : N →ₗ[R] P} (hgh : h ∘ₗ g = 0)
    (hrange : ∀ z ∈ h.range, (∃ n : ℕ, r ^ n • z = 0) → r ^ l • z = 0)
    (hH : ∀ y ∈ h.ker, (∃ n : ℕ, r ^ n • y ∈ g.range) → r ^ k • y ∈ g.range)
    (x : N ⧸ g.range) (hx : ∃ n : ℕ, r ^ n • x = 0) : r ^ (k + l) • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨n, hn⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hn ⊢
  have hhy : r ^ l • h y = 0 := by
    apply hrange (h y) (mem_range_self h y) ⟨n, ?_⟩
    obtain ⟨z, hz⟩ := hn
    rw [← map_smul, ← hz]
    exact LinearMap.congr_fun hgh z
  rw [pow_add, mul_smul]
  apply hH _ (by simpa only [mem_ker, map_smul] using hhy)
  refine ⟨n, ?_⟩
  simpa only [← mul_smul, ← pow_add, Nat.add_comm] using g.range.smul_mem (r ^ l) hn

end LinearMap
