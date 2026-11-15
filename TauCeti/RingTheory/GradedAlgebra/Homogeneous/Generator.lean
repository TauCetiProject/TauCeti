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
# Homogeneous generators and shift classes on a connected spectrum

A grading of the free module of rank one over an integer-graded commutative ring has a
homogeneous generator if the ring has preconnected prime spectrum. In particular this holds
for domains. The grading is given by an internal decomposition compatible with the scalar
grading, using Mathlib's `SetLike.GradedSMul`.

The Laurent polynomial recording the homogeneous components of `1` is a unit, without any
connectedness hypothesis. On a connected spectrum, a coefficient of that unit is itself a
unit, hence is the required homogeneous generator. The zero ring is included.

Combining this existence theorem with the shift classification of
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units` assigns a canonical class
`TauCeti.GradedAlgebra.shiftClass 𝒜 ℳ : ShiftClassGroup 𝒜` to every compatible `ℤ`-grading `ℳ`
on a connected spectrum, classifying such gradings up to graded `A`-linear isomorphism
(`TauCeti.GradedAlgebra.shiftClass_eq_iff`).

## Main definitions

* `TauCeti.GradedAlgebra.shiftClass 𝒜 ℳ`: the class in `ShiftClassGroup 𝒜` of a compatible
  `ℤ`-grading `ℳ` of `A`, over a commutative ring `A` with preconnected prime spectrum.

## Main results

* `TauCeti.GradedAlgebra.isUnit_decomposeLaurent_one`: the Laurent polynomial of the homogeneous
  components of `1` is a unit over any commutative semiring.
* `TauCeti.GradedAlgebra.exists_isUnit_mem_of_connected` and
  `TauCeti.GradedAlgebra.exists_linearEquiv_shift_of_connected`: on a connected spectrum, every
  compatible `ℤ`-grading has a homogeneous unit and is graded-isomorphic to a shift `A(d)`.
* `TauCeti.GradedAlgebra.mk_eq_shiftClass_iff` and `TauCeti.GradedAlgebra.shiftClass_eq_iff`:
  `shiftClass 𝒜 ℳ` classifies compatible `ℤ`-gradings up to graded `A`-linear isomorphism.
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
    (𝒜 : ℤ → σ) (ℳ : ℤ → τ)

section Decomposition

variable [Decomposition 𝒜] [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [PreconnectedSpace (PrimeSpectrum A)]

include 𝒜 in
/-- Every compatible integer grading of a free module of rank one over a ring with
preconnected prime spectrum has a homogeneous unit, hence a homogeneous generator. -/
theorem exists_isUnit_mem_of_connected : ∃ c : ℤ, ∃ u : A, IsUnit u ∧ u ∈ ℳ c := by
  obtain ⟨c, hc, -⟩ := exists_isUnit_coeff_of_isUnit (decomposeLaurent ℳ (1 : A))
    (isUnit_decomposeLaurent_one 𝒜 ℳ)
  refine ⟨c, (decompose ℳ (1 : A) c : A), ?_, (decompose ℳ (1 : A) c).2⟩
  simpa using hc

end Decomposition

section GradedRing

variable [GradedRing 𝒜] [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [PreconnectedSpace (PrimeSpectrum A)]

/-- Over a commutative ring with preconnected prime spectrum, every compatible `ℤ`-grading `ℳ` of
`A` is graded-isomorphic to a shift `A(d)`. -/
theorem exists_linearEquiv_shift_of_connected :
    ∃ d : ℤ, ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  obtain ⟨c, u, hu, hmem⟩ := exists_isUnit_mem_of_connected 𝒜 ℳ
  exact ⟨-c, (exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ).mpr ⟨u, hu, by simpa using hmem⟩⟩

/-- The shift class in `ShiftClassGroup 𝒜` of a compatible `ℤ`-grading `ℳ` of `A`, over a
commutative ring with preconnected prime spectrum. If `u ∈ ℳ c` is a homogeneous unit, this is the
class of `-c` (`shiftClass_eq_mk_of_isUnit_mem`). -/
noncomputable def shiftClass : ShiftClassGroup 𝒜 :=
  (-(exists_isUnit_mem_of_connected 𝒜 ℳ).choose : ℤ)

/-- A shift `A(d)` is graded-isomorphic to `ℳ` if and only if `d` represents `shiftClass 𝒜 ℳ`. -/
theorem mk_eq_shiftClass_iff {d : ℤ} :
    (d : ShiftClassGroup 𝒜) = shiftClass 𝒜 ℳ ↔
      ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  obtain ⟨u, hu, hmem⟩ := (exists_isUnit_mem_of_connected 𝒜 ℳ).choose_spec
  set c := (exists_isUnit_mem_of_connected 𝒜 ℳ).choose
  obtain ⟨φ₀, hφ₀⟩ :=
    (exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ (d := -c)).mpr ⟨u, hu, by simpa using hmem⟩
  rw [shiftClass, ShiftClassGroup.mk_eq_mk_iff]
  refine ⟨fun ⟨ψ, hψ⟩ ↦ ⟨ψ.trans φ₀, fun n x ↦ (hφ₀ n (ψ x)).trans (hψ n x)⟩, fun ⟨φ, hφ⟩ ↦ ?_⟩
  refine ⟨φ.trans φ₀.symm, fun n x ↦ ?_⟩
  rw [LinearEquiv.trans_apply, ← hφ₀ n (φ₀.symm (φ x)), φ₀.apply_symm_apply, hφ n x]

/-- If `ℳ` contains a homogeneous unit in degree `c`, then `shiftClass 𝒜 ℳ` is the class of
`-c`. -/
theorem shiftClass_eq_mk_of_isUnit_mem {c : ℤ} {u : A} (hu : IsUnit u) (hmem : u ∈ ℳ c) :
    shiftClass 𝒜 ℳ = (-c : ℤ) :=
  ((mk_eq_shiftClass_iff 𝒜 ℳ).mpr
    ((exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ).mpr ⟨u, hu, by simpa using hmem⟩)).symm

/-- The tautological grading `𝒜` has trivial shift class. -/
@[simp]
theorem shiftClass_self : shiftClass 𝒜 𝒜 = 0 := by
  simpa using shiftClass_eq_mk_of_isUnit_mem 𝒜 𝒜 isUnit_one (SetLike.one_mem_graded 𝒜)

/-- Over a commutative ring with preconnected prime spectrum, two compatible `ℤ`-gradings `ℳ` and
`𝒩` of `A` are graded-isomorphic if and only if they have the same `shiftClass`. -/
theorem shiftClass_eq_iff {υ : Type*} [SetLike υ A] [AddSubmonoidClass υ A]
    (𝒩 : ℤ → υ) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩] :
    shiftClass 𝒜 ℳ = shiftClass 𝒜 𝒩 ↔ ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒩 n := by
  obtain ⟨d, hd⟩ := QuotientAddGroup.mk_surjective (shiftClass 𝒜 ℳ)
  obtain ⟨φ₁, hφ₁⟩ := (mk_eq_shiftClass_iff 𝒜 ℳ).mp hd
  rw [← hd, mk_eq_shiftClass_iff]
  refine ⟨fun ⟨φ₂, hφ₂⟩ ↦ ⟨φ₂.symm.trans φ₁, fun n x ↦ ?_⟩,
    fun ⟨φ, hφ⟩ ↦ ⟨φ₁.trans φ.symm, fun n x ↦ ?_⟩⟩
  · rw [LinearEquiv.trans_apply, hφ₁ n (φ₂.symm x), ← hφ₂ n (φ₂.symm x), φ₂.apply_symm_apply]
  · rw [LinearEquiv.trans_apply, ← hφ n (φ.symm (φ₁ x)), φ.apply_symm_apply, hφ₁ n x]

end GradedRing

end Ring

end TauCeti.GradedAlgebra
