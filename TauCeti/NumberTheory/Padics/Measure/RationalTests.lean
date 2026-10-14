/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Clearing denominators of rational p-adic tests

A continuous `ℚ_[p]`-valued function on a compact space becomes `ℤ_[p]`-valued after
multiplication by one power of `p`, uniformly on its domain. Thus a rational-valued measure
is determined by its values on integral tests, and integration of a rational test can be
recovered from integration of its integral scaling. These facts are useful for uniqueness
of extensions of coefficients from integral to rational measures.

The integral tests are included using `ContinuousMap.subtypeVal`; measures remain on
Mathlib's `AbstractMeasure` carrier. No topology or norm is installed on that carrier.

## References

* Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, §3.2,
  Definitions 3.7–3.8, and Remark 3.28(1–2).
-/

public section

namespace TauCeti

open scoped AbstractMeasure

variable (p : ℕ) [Fact p.Prime] {X : Type*} [TopologicalSpace X]

/-- One power of `p` clears the denominators of a continuous rational p-adic test on a
compact space. The power is uniform in the point of the domain. -/
theorem exists_prime_pow_smul_eq_padicInt_test [CompactSpace X] (f : C(X, ℚ_[p])) :
    ∃ n : ℕ, ∃ g : C(X, ℤ_[p]),
      (ContinuousMap.subtypeVal (PadicInt.subring p)).comp g = (p : ℚ_[p]) ^ n • f := by
  have hpos : 0 < ‖f‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p (one_div_pos.mpr hpos)
  have hbound : ‖(p : ℚ_[p]) ^ n‖ * ‖f‖ ≤ 1 := by
    rw [Padic.norm_p_pow]
    have h := (lt_div_iff₀ hpos).mp hn
    have hnonneg := zpow_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) (-(n : ℤ))
    nlinarith
  have hpoint (x : X) : ‖(p : ℚ_[p]) ^ n * f x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)).trans hbound
  have hmem (x : X) : (p : ℚ_[p]) ^ n * f x ∈ PadicInt.subring p :=
    (PadicInt.mem_subring_iff p).mpr (hpoint x)
  refine ⟨n, ⟨fun x ↦ ⟨(p : ℚ_[p]) ^ n * f x, hmem x⟩,
    (continuous_const.mul f.continuous).subtype_mk hmem⟩, ?_⟩
  ext x
  rfl

/-- Every continuous rational p-adic test on a compact space is an inverse prime power
times an integral test. -/
theorem exists_eq_inv_prime_pow_smul_padicInt_test [CompactSpace X] (f : C(X, ℚ_[p])) :
    ∃ n : ℕ, ∃ g : C(X, ℤ_[p]),
      f = ((p : ℚ_[p]) ^ n)⁻¹ • (ContinuousMap.subtypeVal (PadicInt.subring p)).comp g := by
  obtain ⟨n, g, hg⟩ := exists_prime_pow_smul_eq_padicInt_test p f
  refine ⟨n, g, ?_⟩
  rw [hg, inv_smul_smul₀]
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

section Measures

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℚ_[p] E]

/-- Integration of a rational p-adic test is recovered from integration of any integral
prime-power scaling. This also holds for module-valued measures. -/
theorem measure_apply_eq_inv_prime_pow_smul
    (μ : AbstractMeasure X ℚ_[p] E) (f : C(X, ℚ_[p])) (n : ℕ) (g : C(X, ℤ_[p]))
    (hg : (ContinuousMap.subtypeVal (PadicInt.subring p)).comp g = (p : ℚ_[p]) ^ n • f) :
    μ f = ((p : ℚ_[p]) ^ n)⁻¹ • μ ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g) := by
  rw [hg, map_smul, inv_smul_smul₀]
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- On a compact space, rational p-adic measures agreeing on all integral tests agree
on every continuous test. No disconnectedness or separation hypothesis is needed. -/
theorem measure_ext_of_padicInt_tests [CompactSpace X]
    {μ ν : AbstractMeasure X ℚ_[p] E}
    (h : ∀ g : C(X, ℤ_[p]),
      μ ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g) =
        ν ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g)) : μ = ν := by
  ext f
  obtain ⟨n, g, hg⟩ := exists_prime_pow_smul_eq_padicInt_test p f
  rw [measure_apply_eq_inv_prime_pow_smul p μ f n g hg,
    measure_apply_eq_inv_prime_pow_smul p ν f n g hg, h g]

end Measures

end TauCeti
