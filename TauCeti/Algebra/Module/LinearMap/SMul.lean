/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Scalar-eigenvalue transport and cross-eigenvalue vanishing for linear maps

Let `A` act on two `k`-modules `S` and `M` compatibly with `k`. An `A`-linear map `f : S →ₗ[A] M`
transports any scalar action `z • s = μ • s` of an element `z ∈ A` on `S` to the image `f s`
(`LinearMap.smul_apply_of_smul_eq`). Consequently, if `z` acts on `S` by `μ : k` and on `M` by
`ν : k` with `μ - ν` acting regularly on `M` (in particular whenever `k` is a division ring and
`μ ≠ ν`), every `A`-linear map `S →ₗ[A] M` vanishes.

## Main results

* `LinearMap.smul_apply_of_smul_eq`: an `A`-linear map carries a `μ`-eigenvector of `z ∈ A` to a
  `μ`-eigenvector of `z`.
* `LinearMap.eq_zero_of_smul_eq_of_isSMulRegular`: cross-eigenvalue vanishing when `μ - ν` is
  `IsSMulRegular` on `M`.
* `TauCeti.subsingleton_linearMap_of_smul_eq_of_isSMulRegular` and
  `TauCeti.subsingleton_linearMap_of_smul_eq_of_ne`: the space `S →ₗ[A] M` is a subsingleton under
  the same condition, and in particular for `μ ≠ ν` over a division ring.
-/

public section

namespace LinearMap

section Semiring

variable {k A S M : Type*} [Semiring k] [Semiring A] [SMul k A]
  [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
  [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- An `A`-linear map carries a `μ`-eigenvector of `z ∈ A` to a `μ`-eigenvector of `z`. -/
theorem smul_apply_of_smul_eq (f : S →ₗ[A] M) {z : A} {μ : k} {s : S}
    (hz : z • s = μ • s) :
    z • f s = μ • f s := by
  rw [← f.map_smul, hz, f.map_smul_of_tower]

end Semiring

section Ring

variable {k A S M : Type*} [Ring k] [Semiring A] [SMul k A]
  [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- **Cross-eigenvalue vanishing.** If `z ∈ A` acts on `S` by `μ : k` and on `M` by `ν : k`, and
`μ - ν` acts regularly on `M`, then every `A`-linear map `S →ₗ[A] M` is zero. -/
theorem eq_zero_of_smul_eq_of_isSMulRegular (f : S →ₗ[A] M) {z : A} {μ ν : k}
    (hzS : ∀ s : S, z • s = μ • s) (hzM : ∀ x : M, z • x = ν • x)
    (hreg : IsSMulRegular M (μ - ν)) :
    f = 0 := by
  ext s
  refine hreg.eq_iff.mp ?_
  rw [LinearMap.zero_apply, smul_zero, sub_smul, ← f.smul_apply_of_smul_eq (hzS s), hzM, sub_self]

end Ring

end LinearMap

namespace TauCeti

/-- The space of `A`-linear maps `S →ₗ[A] M` is a subsingleton when `z ∈ A` acts by scalars `μ` and
`ν` whose difference `μ - ν` is regular on `M`. -/
theorem subsingleton_linearMap_of_smul_eq_of_isSMulRegular
    {k A S M : Type*} [Ring k] [Semiring A] [SMul k A]
    [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {z : A} {μ ν : k} (hzS : ∀ s : S, z • s = μ • s) (hzM : ∀ x : M, z • x = ν • x)
    (hreg : IsSMulRegular M (μ - ν)) :
    Subsingleton (S →ₗ[A] M) :=
  subsingleton_of_forall_eq 0 fun f ↦ f.eq_zero_of_smul_eq_of_isSMulRegular hzS hzM hreg

/-- Over a division ring, `S →ₗ[A] M` is trivial whenever `z ∈ A` acts on `S` and `M` by distinct
scalars `μ ≠ ν`. -/
theorem subsingleton_linearMap_of_smul_eq_of_ne
    {k A S M : Type*} [DivisionRing k] [Semiring A] [SMul k A]
    [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {z : A} {μ ν : k} (hzS : ∀ s : S, z • s = μ • s) (hzM : ∀ x : M, z • x = ν • x)
    (hne : μ ≠ ν) :
    Subsingleton (S →ₗ[A] M) :=
  subsingleton_linearMap_of_smul_eq_of_isSMulRegular hzS hzM
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).isSMulRegular M)

end TauCeti
