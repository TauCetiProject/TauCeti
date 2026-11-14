/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Laurent
public import TauCeti.Algebra.Polynomial.Laurent.Units.Connected
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units

/-!
# Homogeneous generators and shift classification on a connected spectrum

A grading of the free module of rank one over an integer-graded commutative ring has a
homogeneous generator if the ring has preconnected prime spectrum. In particular this holds
for domains. The grading is given by an internal decomposition compatible with the scalar
grading, using Mathlib's `SetLike.GradedSMul`.

The Laurent polynomial recording the homogeneous components of `1` is a unit, without any
connectedness hypothesis. On a connected spectrum, a coefficient of that unit is itself a
unit, hence is the required homogeneous generator. The zero ring is included.

Combining this existence theorem with the shift classification of
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units` shows that over a `ℤ`-graded commutative ring
`A` with preconnected prime spectrum, every compatible `ℤ`-grading `ℳ` of `A` is graded-isomorphic
to a shift `A(d)` whose class `shiftClass 𝒜 ℳ : ShiftClassGroup 𝒜` is uniquely determined, so
`ShiftClassGroup 𝒜` classifies all compatible `ℤ`-gradings of the free module of rank one up to
graded isomorphism.

## Main definitions

* `TauCeti.GradedAlgebra.shiftClass 𝒜 ℳ`: the class in `ShiftClassGroup 𝒜` of a compatible
  `ℤ`-grading `ℳ` of `A` when `PrimeSpectrum A` is preconnected.

## Main results

* `TauCeti.GradedAlgebra.isUnit_decomposeLaurent_one`: the Laurent polynomial of the homogeneous
  components of `1` is a unit.
* `TauCeti.GradedAlgebra.exists_isUnit_mem_of_connected`: every compatible `ℤ`-grading of `A` on a
  preconnected prime spectrum has a homogeneous unit.
* `TauCeti.GradedAlgebra.exists_shift_linearEquiv_of_connected`: every such grading is
  graded-isomorphic to a shift `A(d)`.
* `TauCeti.GradedAlgebra.shiftClass_eq_mk_iff` and `TauCeti.GradedAlgebra.shiftClass_eq_iff`: two
  compatible `ℤ`-gradings of `A` on a preconnected spectrum are graded-isomorphic if and only if
  they have the same `shiftClass` in `ShiftClassGroup 𝒜`.
-/

public section

open DirectSum LaurentPolynomial

namespace TauCeti.GradedAlgebra

section Semiring

variable {A σ τ : Type*} [CommSemiring A]
    [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ A] [AddSubmonoidClass τ A]
    (𝒜 : ℤ → σ) (ℳ : ℤ → τ) [Decomposition 𝒜] [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ]

include 𝒜 in
/-- For a compatible grading on the free module of rank one, the Laurent polynomial of the
homogeneous components of `1` is a unit, even if the spectrum is disconnected. -/
theorem isUnit_decomposeLaurent_one : IsUnit (decomposeLaurent ℳ (1 : A)) := by
  classical
  let m (i : ℤ) : A := decompose ℳ (1 : A) i
  have h (i : ℤ) :
      decomposeLaurent 𝒜 (m i) * decomposeLaurent ℳ (1 : A) = C (m i) * T i := by
    rw [← decomposeLaurent_mul ℳ 𝒜, mul_one]
    exact decomposeLaurent_of_mem ℳ (decompose ℳ (1 : A) i).2
  -- Shifting each identity back by its degree and summing gives an explicit inverse.
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨∑ i ∈ (decompose ℳ (1 : A)).support, decomposeLaurent 𝒜 (m i) * T (-i), ?_⟩
  rw [Finset.sum_mul]
  have hterm (i : ℤ) :
      decomposeLaurent 𝒜 (m i) * T (-i) * decomposeLaurent ℳ (1 : A) = C (m i) := by
    rw [mul_right_comm, h]
    simp
  simp_rw [hterm]
  rw [← map_sum, sum_support_decompose ℳ (1 : A), map_one]

end Semiring

section Ring

variable {A σ τ : Type*} [CommRing A]
    [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ A] [AddSubmonoidClass τ A]
    (𝒜 : ℤ → σ) (ℳ : ℤ → τ) [Decomposition 𝒜] [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] [PreconnectedSpace (PrimeSpectrum A)]

include 𝒜 in
/-- Every compatible integer grading of a free module of rank one over a ring with
preconnected prime spectrum has a homogeneous unit, hence a homogeneous generator. -/
theorem exists_isUnit_mem_of_connected : ∃ c : ℤ, ∃ u : A, IsUnit u ∧ u ∈ ℳ c := by
  obtain ⟨c, hc, -⟩ := exists_isUnit_coeff_of_isUnit (decomposeLaurent ℳ (1 : A))
    (isUnit_decomposeLaurent_one 𝒜 ℳ)
  refine ⟨c, (decompose ℳ (1 : A) c : A), ?_, (decompose ℳ (1 : A) c).2⟩
  simpa using hc

end Ring

section ShiftClass

variable {A σ τ υ : Type*} [CommRing A]
    [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ A] [AddSubmonoidClass τ A]
    [SetLike υ A] [AddSubmonoidClass υ A]
    (𝒜 : ℤ → σ) (ℳ : ℤ → τ) (𝒩 : ℤ → υ)
    [GradedRing 𝒜] [Decomposition ℳ] [Decomposition 𝒩]
    [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]
    [PreconnectedSpace (PrimeSpectrum A)]

/-- Over a `ℤ`-graded commutative ring with preconnected prime spectrum, every compatible
`ℤ`-grading of the free `A`-module `A` is graded-isomorphic to a shift `A(d)`. -/
theorem exists_shift_linearEquiv_of_connected :
    ∃ d : ℤ, ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  obtain ⟨c, u, hu, hmem⟩ := exists_isUnit_mem_of_connected 𝒜 ℳ
  exact ⟨-c, (exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ).mpr ⟨u, hu, by simpa using hmem⟩⟩

/-- The shift class in `ShiftClassGroup 𝒜` of a compatible `ℤ`-grading `ℳ` of `A` when
`PrimeSpectrum A` is preconnected: the unique class `(d : ShiftClassGroup 𝒜)` such that `(A, ℳ)` is
graded-isomorphic to `A(d)`. -/
noncomputable def shiftClass : ShiftClassGroup 𝒜 :=
  ((exists_shift_linearEquiv_of_connected 𝒜 ℳ).choose : ShiftClassGroup 𝒜)

/-- A compatible `ℤ`-grading `ℳ` of `A` on a preconnected prime spectrum has shift class `d` if
and only if `(A, ℳ)` is graded-isomorphic to the shift `A(d)`. -/
theorem shiftClass_eq_mk_iff {d : ℤ} :
    shiftClass 𝒜 ℳ = (d : ShiftClassGroup 𝒜) ↔
      ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  let d₀ := (exists_shift_linearEquiv_of_connected 𝒜 ℳ).choose
  obtain ⟨φ₀, hφ₀⟩ := (exists_shift_linearEquiv_of_connected 𝒜 ℳ).choose_spec
  have hd₀ : shiftClass 𝒜 ℳ = (d₀ : ShiftClassGroup 𝒜) := rfl
  rw [hd₀, ShiftClassGroup.mk_eq_mk_iff]
  refine ⟨fun ⟨ψ, hψ⟩ ↦ ⟨ψ.symm.trans φ₀, fun n x ↦ by rw [LinearEquiv.trans_apply, hφ₀,
      ← hψ n (ψ.symm x), ψ.apply_symm_apply]⟩,
    fun ⟨φ, hφ⟩ ↦ ⟨φ₀.trans φ.symm, fun n x ↦ by rw [LinearEquiv.trans_apply,
      ← hφ n (φ.symm (φ₀ x)), φ.apply_symm_apply, hφ₀]⟩⟩

/-- If `ℳ` contains a homogeneous unit in degree `c`, its shift class is `-c`. -/
theorem shiftClass_eq_neg_mk_of_isUnit_mem {u : A} (hu : IsUnit u) {c : ℤ} (hmem : u ∈ ℳ c) :
    shiftClass 𝒜 ℳ = ((-c : ℤ) : ShiftClassGroup 𝒜) :=
  (shiftClass_eq_mk_iff 𝒜 ℳ).mpr <|
    (exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ).mpr ⟨u, hu, by simpa using hmem⟩

@[simp]
theorem shiftClass_self : shiftClass 𝒜 𝒜 = 0 := by
  simpa using shiftClass_eq_neg_mk_of_isUnit_mem 𝒜 𝒜 isUnit_one (c := 0) (SetLike.one_mem_graded 𝒜)

/-- Over a `ℤ`-graded commutative ring with preconnected prime spectrum, two compatible
`ℤ`-gradings of `A` are graded-isomorphic as `A`-modules if and only if they have the same
`shiftClass` in `ShiftClassGroup 𝒜`. -/
theorem shiftClass_eq_iff :
    shiftClass 𝒜 ℳ = shiftClass 𝒜 𝒩 ↔
      ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ 𝒩 n ↔ x ∈ ℳ n := by
  let d := (exists_shift_linearEquiv_of_connected 𝒜 𝒩).choose
  obtain ⟨φN, hφN⟩ := (exists_shift_linearEquiv_of_connected 𝒜 𝒩).choose_spec
  have hN : shiftClass 𝒜 𝒩 = (d : ShiftClassGroup 𝒜) := rfl
  rw [hN, shiftClass_eq_mk_iff]
  refine ⟨fun ⟨φM, hφM⟩ ↦ ⟨φM.symm.trans φN, fun n x ↦ by
      rw [LinearEquiv.trans_apply, hφN, ← hφM n (φM.symm x), φM.apply_symm_apply]⟩,
    fun ⟨φ, hφ⟩ ↦ ⟨φN.trans φ.symm, fun n x ↦ by
      rw [LinearEquiv.trans_apply, ← hφ n (φ.symm (φN x)), φ.apply_symm_apply, hφN]⟩⟩

end ShiftClass

end TauCeti.GradedAlgebra
