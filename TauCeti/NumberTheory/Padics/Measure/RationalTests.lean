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

The integral tests are included using `ContinuousMap.subtypeVal`. The statements about measures
only use that a measure commutes with scalar multiplication, so they are stated for every
`ℚ_[p]`-equivariant map out of `C(X, ℚ_[p])`. This covers Mathlib's `AbstractMeasure` carrier, on
which no topology or norm is installed, as well as linear and continuous linear maps, for instance
elements of the operator-norm dual.

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
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖f‖ (Nat.one_lt_cast.mpr hp.one_lt)
  have hmem (x : X) : (p : ℚ_[p]) ^ n * f x ∈ PadicInt.subring p := by
    rw [PadicInt.mem_subring_iff, norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast,
      inv_mul_le_one₀ (pow_pos (Nat.cast_pos.mpr hp.pos) n)]
    exact (f.norm_coe_le_norm x).trans hn.le
  -- The underlying function of `subtypeVal.comp g` is `p ^ n * f` by construction.
  exact ⟨n, ⟨fun x ↦ ⟨_, hmem x⟩, (continuous_const.mul f.continuous).subtype_mk hmem⟩, rfl⟩

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

variable {E F : Type*} [MulAction ℚ_[p] E] [FunLike F C(X, ℚ_[p]) E]
  [MulActionHomClass F ℚ_[p] C(X, ℚ_[p]) E]

/-- Integration of a rational p-adic test is recovered from integration of any integral
prime-power scaling. This holds for every `ℚ_[p]`-equivariant map `μ`, in particular for
module-valued measures. -/
theorem measure_apply_eq_inv_prime_pow_smul
    (μ : F) (f : C(X, ℚ_[p])) (n : ℕ) (g : C(X, ℤ_[p]))
    (hg : (ContinuousMap.subtypeVal (PadicInt.subring p)).comp g = (p : ℚ_[p]) ^ n • f) :
    μ f = ((p : ℚ_[p]) ^ n)⁻¹ • μ ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g) := by
  rw [hg, map_smul, inv_smul_smul₀]
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- On a compact space, rational p-adic measures agreeing on all integral tests agree
on every continuous test. More generally this holds for any two `ℚ_[p]`-equivariant maps out
of `C(X, ℚ_[p])`, for instance linear maps that are not continuous. No disconnectedness or
separation hypothesis is needed. -/
theorem measure_ext_of_padicInt_tests [CompactSpace X] {μ ν : F}
    (h : ∀ g : C(X, ℤ_[p]),
      μ ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g) =
        ν ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g)) : μ = ν := by
  refine DFunLike.ext _ _ fun f ↦ ?_
  obtain ⟨n, g, hg⟩ := exists_prime_pow_smul_eq_padicInt_test p f
  rw [measure_apply_eq_inv_prime_pow_smul p μ f n g hg,
    measure_apply_eq_inv_prime_pow_smul p ν f n g hg, h g]

-- `measure_ext_of_padicInt_tests` applies to `AbstractMeasure` without any topological-group
-- hypothesis on the coefficient module.
example [CompactSpace X] {M : Type*} [AddCommGroup M] [TopologicalSpace M] [Module ℚ_[p] M]
    {μ ν : AbstractMeasure X ℚ_[p] M}
    (h : ∀ g : C(X, ℤ_[p]),
      μ ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g) =
        ν ((ContinuousMap.subtypeVal (PadicInt.subring p)).comp g)) : μ = ν :=
  measure_ext_of_padicInt_tests p h

end Measures

end TauCeti
