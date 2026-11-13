/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Bounded power torsion in quotients

A uniform bound on parameter-power torsion in a cokernel controls the induced filtration on
an inclusion. For a complex, bounds on power torsion in its homology and in the last map's
range give a bound in the preceding cokernel. These statements require no finiteness or
regularity assumptions and are independent of completion.
-/

public section

open scoped Pointwise

namespace LinearMap

variable {R : Type*} [CommRing R] {r : R} {k l : ℕ}
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Bounded power torsion in the cokernel of an inclusion gives a uniform shift between
its induced principal-ideal filtration and its own principal-ideal filtration. -/
theorem comap_span_singleton_pow_smul_le_of_bounded_torsion (f : M →ₗ[R] N)
    (hf : Function.Injective f)
    (hbound : ∀ x : N ⧸ f.range, (∃ n : ℕ, r ^ n • x = 0) → r ^ k • x = 0)
    (n : ℕ) :
    ((Ideal.span {r}) ^ (n + k) • ⊤ : Submodule R N).comap f ≤
      (Ideal.span {r}) ^ n • ⊤ := by
  intro x hx
  rw [Submodule.mem_comap] at hx
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
  obtain ⟨y, -, hy⟩ := hx
  have hq : r ^ k • (Submodule.Quotient.mk y : N ⧸ f.range) = 0 := by
    apply hbound _ ⟨n + k, ?_⟩
    rw [← Submodule.Quotient.mk_smul, hy, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self f x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨z, hz⟩ := hq
  refine ⟨z, Submodule.mem_top, hf ?_⟩
  rw [map_smul, hz, smul_smul, ← pow_add, hy]

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
  exact ⟨n, by simpa only [smul_comm (r ^ n) (r ^ l)] using g.range.smul_mem (r ^ l) hn⟩

end LinearMap
