/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Order

/-!
# The Mahler basis on the p-adic integers

This file records identities for Mathlib's Mahler basis functions on `ℤ_p` and for Mathlib's
Mahler isometry `PadicInt.mahlerEquiv E : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)`, which sends a continuous
function to its sequence of Mahler coefficients `Δ^n f (0)`.

Mathlib states Mahler's theorem as a `ℤ_[p]`-linear isometry. Since the forward differences
commute with every scalar action on the coefficient module, the isometry is linear over any
additional scalars `S` acting on `E`; this scalar-linear refinement is
`PadicInt.mahlerLinearIsometryEquiv S E`. It is what turns Mahler's theorem into a statement about
`S`-linear functionals, for instance measures with values in a `ℤ_[p]`-algebra `S = E`.

## Main results

* `TauCeti.id_mul_mahler`: multiplication by the coordinate function satisfies
  `x * mahler n = (n + 1) • mahler (n + 1) + n • mahler n`.
* `PadicInt.mahlerEquiv_smul`: the Mahler coefficients commute with scalar actions.
* `PadicInt.mahlerLinearIsometryEquiv`: Mahler's isometry as an `S`-linear isometric equivalence.
* `PadicInt.mahlerEquiv_symm_single`: the Mahler series of a coordinate vector `single n a` is the
  Mahler term `x ↦ (x choose n) • a`.
* `PadicInt.mahlerTerm_eq_smul`: over a normed ring with a `ℤ_[p]`-action commuting with left
  multiplication, the Mahler term with coefficient `a` is `a` times `mahler n • 1`.
* `PadicInt.mahler_natCast_mul`: for `m : ℕ`, the Mahler function `(m x choose n)` is the integral
  combination of the `(x choose k)`, `k ≤ n`, with coefficients those of `((1 + T) ^ m - 1) ^ k`
  at `T ^ n`.
-/

public section

variable {p : ℕ} [Fact p.Prime]

namespace TauCeti

/-- The Mahler recurrence `x * (x choose n) = (n + 1) * (x choose (n + 1)) + n * (x choose n)`. -/
theorem id_mul_mahler (n : ℕ) :
    ContinuousMap.id ℤ_[p] * mahler n = (n + 1) • mahler (n + 1) + n • mahler n := by
  refine ContinuousMap.ext fun x => ?_
  have hchoose :
      (n + 1) • Ring.choose x (n + 1) = Ring.choose x n * (x - n) := by
    simpa only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] using
      Ring.choose_smul_choose x (Nat.le_add_right n 1)
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.id_apply, mahler_apply]
  rw [hchoose, nsmul_eq_mul]
  ring

end TauCeti

namespace PadicInt

open ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

section Module

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/-- The Mahler coefficients of `c • f` are `c` times those of `f`, for every scalar action on the
coefficient module, since the forward differences commute with it. -/
theorem mahlerEquiv_smul {S : Type*} [Monoid S] [DistribMulAction S E] [ContinuousConstSMul S E]
    (c : S) (f : C(ℤ_[p], E)) : mahlerEquiv E (c • f) = c • mahlerEquiv E f := by
  ext n
  simp [mahlerEquiv_apply]

end Module

/-- **Mahler's theorem, scalar-linear form.** Mathlib's Mahler isometry
`mahlerEquiv E : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)` is linear over any semiring `S` acting on the
coefficient module `E`. -/
noncomputable def mahlerLinearIsometryEquiv (S E : Type*) [Semiring S] [NormedAddCommGroup E]
    [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] [Module S E]
    [ContinuousConstSMul S E] : C(ℤ_[p], E) ≃ₗᵢ[S] C₀(ℕ, E) where
  toFun := mahlerEquiv E
  invFun := (mahlerEquiv E).symm
  map_add' := map_add (mahlerEquiv E)
  map_smul' := mahlerEquiv_smul
  left_inv := (mahlerEquiv E).symm_apply_apply
  right_inv := (mahlerEquiv E).apply_symm_apply
  norm_map' := (mahlerEquiv E).norm_map

section Module

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

@[simp]
theorem coe_mahlerLinearIsometryEquiv :
    ⇑(mahlerLinearIsometryEquiv S E) = mahlerEquiv (p := p) E :=
  (rfl)

@[simp]
theorem coe_mahlerLinearIsometryEquiv_symm :
    ⇑(mahlerLinearIsometryEquiv S E).symm = (mahlerEquiv (p := p) E).symm :=
  (rfl)

end Module

section Module

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/-- The Mahler series of the coordinate vector `single n a` is the single Mahler term
`x ↦ (x choose n) • a`. -/
@[simp]
theorem mahlerEquiv_symm_single (n : ℕ) (a : E) :
    (mahlerEquiv (p := p) E).symm (single n a) = mahlerTerm a n := by
  rw [mahlerEquiv_symm_apply, mahlerSeries, tsum_eq_single n fun k hk ↦ by
    simp [single_apply, hk, mahlerTerm]]
  simp

end Module

/-- For a normed ring `R` with a `ℤ_[p]`-action commuting with left multiplication, the Mahler term
with coefficient `a` is `a` times the Mahler basis function `mahler n • 1`. -/
theorem mahlerTerm_eq_smul {R : Type*} [NormedRing R] [Module ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
    [SMulCommClass ℤ_[p] R R] (a : R) (n : ℕ) :
    mahlerTerm a n = a • ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) := by
  ext x
  simp [mahlerTerm_apply, mul_smul_comm]

section Dilation

open PowerSeries

/-- **Mahler functions of a dilation.** For `m : ℕ`, the function `x ↦ (m x choose n)` is the
integral combination `∑_{k ≤ n} c_{n,k} (x choose k)`, where `c_{n,k}` is the coefficient of `T ^ n`
in `((1 + T) ^ m - 1) ^ k`. This is the coefficientwise form of
`(1 + T) ^ (m x) = ((1 + T) ^ m) ^ x = ∑_k (x choose k) ((1 + T) ^ m - 1) ^ k`. -/
theorem mahler_natCast_mul (m n : ℕ) (x : ℤ_[p]) :
    mahler n ((m : ℤ_[p]) * x) = ∑ k ∈ Finset.range (n + 1),
      ((coeff n (((1 + X) ^ m - 1) ^ k : ℤ⟦X⟧) : ℤ) : ℤ_[p]) * mahler k x := by
  set G : ℤ⟦X⟧ := (1 + X) ^ m - 1
  have hG : constantCoeff G = 0 := by simp [G]
  -- Both sides are continuous in `x`, so it suffices to compare them on `ℕ`.
  have hcont : Continuous fun x : ℤ_[p] ↦ mahler n ((m : ℤ_[p]) * x) :=
    (mahler n).continuous.comp (continuous_const.mul continuous_id)
  refine congrFun (denseRange_natCast.equalizer hcont
    (continuous_finsetSum _ fun k _ ↦ continuous_const.mul (mahler k).continuous)
    (funext fun l ↦ ?_)) x
  simp only [Function.comp_apply, ← Nat.cast_mul, Pi.mul_apply, mahler_natCast_eq]
  -- For natural `l`, expand `(1 + T) ^ (m l) = (G + 1) ^ l` by the binomial theorem.
  have hnat :
      ((m * l).choose n : ℤ) = ∑ k ∈ Finset.range (l + 1), coeff n (G ^ k) * l.choose k := by
    have hpow : ((1 + X : ℤ⟦X⟧) ^ (m * l)) = (G + 1) ^ l := by
      rw [pow_mul, sub_add_cancel]
    have hcoeff := congrArg (coeff n) hpow
    rw [← binomialSeries_nat (R := ℤ), binomialSeries_coeff, Ring.choose_natCast, add_pow,
      map_sum] at hcoeff
    simpa using hcoeff
  -- Both finite sums agree with the sum over `k ≤ n + l`.
  have hsub₁ : ∑ k ∈ Finset.range (l + 1), coeff n (G ^ k) * (l.choose k : ℤ) =
      ∑ k ∈ Finset.range (n + l + 1), coeff n (G ^ k) * (l.choose k : ℤ) :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) fun k _ hk ↦ by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hk), Nat.cast_zero, mul_zero]
  have hsub₂ : ∑ k ∈ Finset.range (n + 1), coeff n (G ^ k) * (l.choose k : ℤ) =
      ∑ k ∈ Finset.range (n + l + 1), coeff n (G ^ k) * (l.choose k : ℤ) :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) fun k _ hk ↦ by
      rw [coeff_of_lt_order _ ((Nat.cast_lt.mpr (by simpa using hk)).trans_le
        (le_order_pow_of_constantCoeff_eq_zero k hG)), zero_mul]
  have hint : ((m * l).choose n : ℤ) =
      ∑ k ∈ Finset.range (n + 1), coeff n (G ^ k) * (l.choose k : ℤ) := by
    rw [hnat, hsub₁, hsub₂]
  exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) hint

end Dilation

end PadicInt
