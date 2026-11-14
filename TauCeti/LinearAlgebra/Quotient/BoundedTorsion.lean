/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bounded power torsion in quotients

For a submodule contained in the kernel of a map, bounds on power torsion in the kernel
quotient and in the map's range give a bound in the source quotient. Applied to a complex,
these are bounds in its homology, last map's range, and preceding cokernel. These statements
require no finiteness or regularity assumptions and are independent of completion.

## References

* [Stacks Project, Lemma 52.12.7](https://stacks.math.columbia.edu/tag/0EII),
  for the three-term complex cokernel bound.
-/

public section

namespace Submodule

/-- If `S ≤ ker h`, bounds on power torsion in `ker h / S` and in `range h` give a bound
in the quotient by `S`. Annihilation of the whole kernel quotient is not required. -/
theorem pow_smul_eq_zero_quotient_of_le_ker {R : Type*} [Ring R] {r : R} {k l : ℕ}
    {N P : Type*} [AddCommGroup N] [Module R N] [AddCommMonoid P] [Module R P]
    (S : Submodule R N) {h : N →ₗ[R] P} (hS : S ≤ h.ker)
    (hrange : ∀ (n : ℕ) (z : h.range), r ^ n • z = 0 → r ^ l • z = 0)
    (hH : ∀ (n : ℕ) (y : N), y ∈ h.ker → r ^ n • y ∈ S → r ^ k • y ∈ S)
    (n : ℕ) (x : N ⧸ S) (hx : r ^ n • x = 0) : r ^ (k + l) • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx ⊢
  have hhy : r ^ l • h y = 0 := by
    have hn : r ^ n • (⟨h y, LinearMap.mem_range_self h y⟩ : h.range) = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero, ← map_smul]
        using LinearMap.mem_ker.mp (hS hx)
    exact congrArg Subtype.val (hrange n _ hn)
  rw [pow_add, mul_smul]
  apply hH n _ (by simpa only [LinearMap.mem_ker, map_smul] using hhy)
  simpa only [← mul_smul, ← pow_add, Nat.add_comm] using S.smul_mem (r ^ l) hx

end Submodule

namespace LinearMap

/-- In a complex, bounds on power torsion in the homology and in the last map's range give
a bound in the preceding cokernel. Annihilation of the whole homology is not required. -/
theorem pow_smul_eq_zero_coker_of_bounded_torsion_homology
    {R : Type*} [Ring R] {r : R} {k l : ℕ}
    {M N P : Type*} [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommMonoid P] [Module R P] (g : M →ₗ[R] N)
    {h : N →ₗ[R] P} (hgh : h ∘ₗ g = 0)
    (hrange : ∀ (n : ℕ) (z : h.range), r ^ n • z = 0 → r ^ l • z = 0)
    (hH : ∀ (n : ℕ) (y : N), y ∈ h.ker → r ^ n • y ∈ g.range → r ^ k • y ∈ g.range)
    (n : ℕ) (x : N ⧸ g.range) (hx : r ^ n • x = 0) : r ^ (k + l) • x = 0 :=
  g.range.pow_smul_eq_zero_quotient_of_le_ker (range_le_ker_iff.mpr hgh) hrange hH n x hx

end LinearMap
