/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective

/-!
# Projective and injective abelian groups

An abelian group that is both projective and injective as a `ℤ`-module is zero
(`Module.subsingleton_of_projective_of_injective_int`). An injective abelian group is divisible,
while a nonzero projective one has a nonzero linear form to `ℤ`, whose value on a nonzero element
cannot be divisible by every positive integer. So `ℤ` has dominant dimension zero.

## Main results

* `Module.subsingleton_of_projective_of_injective_int`: a projective and injective `ℤ`-module is
  zero.
-/

public section

namespace Module

/-- **A projective and injective `ℤ`-module is zero.** -/
theorem subsingleton_of_projective_of_injective_int (I : Type*) [AddCommGroup I] [Module ℤ I]
    [Module.Projective ℤ I] [Module.Injective ℤ I] : Subsingleton I := by
  refine ⟨fun x y ↦ sub_eq_zero.1 ?_⟩
  generalize x - y = z
  by_contra hz
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective ℤ I›
  have hsz : s z ≠ 0 := fun h ↦ hz (by
    have := LinearMap.congr_fun hs z
    rw [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm)
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hsz
  let φ : I →ₗ[ℤ] ℤ := Finsupp.lapply a ∘ₗ s
  have hφ : φ z ≠ 0 := ha
  -- `z` is divisible by `N = |φ z| + 1`, since `I` is injective.
  let N : ℕ := (φ z).natAbs + 1
  have hN : Function.Injective ((N : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) := fun a b hab ↦
    mul_left_cancel₀ (by positivity : (N : ℤ) ≠ 0) (by simpa using hab)
  obtain ⟨h, hh⟩ := Module.Injective.extension_property ℤ I ℤ ℤ _ hN
    (LinearMap.toSpanSingleton ℤ I z)
  have h1 : h (N : ℤ) = z := by
    have := LinearMap.congr_fun hh 1
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
      mul_one] at this
    exact this.trans (LinearMap.toSpanSingleton_apply_one ℤ I z)
  -- `φ (h N) = N * φ (h 1)`, computed in `ℤ`.
  have hφz : φ z = (N : ℤ) * (φ ∘ₗ h) 1 := by
    rw [← h1, ← LinearMap.comp_apply φ h, ← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul,
      mul_one]
  have hdvd : (N : ℤ) ∣ φ z := ⟨_, hφz⟩
  have := Int.natAbs_le_of_dvd_ne_zero hdvd hφ
  simp only [N, Int.natAbs_natCast] at this
  omega

end Module
