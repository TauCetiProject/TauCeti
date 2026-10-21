/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

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
* `PadicInt.mahlerTerm_eq_smul`: over a `ℤ_[p]`-algebra `R`, the Mahler term with coefficient `a` is
  `a` times the Mahler basis function `mahler n • 1`.
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

/-- Over a `ℤ_[p]`-algebra `R`, the Mahler term with coefficient `a` is `a` times the Mahler basis
function `mahler n • 1`. -/
theorem mahlerTerm_eq_smul {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
    (a : R) (n : ℕ) :
    mahlerTerm a n = a • ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) := by
  ext x
  rw [mahlerTerm_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply',
    ContinuousMap.one_apply, smul_eq_mul, mul_smul_comm, mul_one]

end PadicInt
