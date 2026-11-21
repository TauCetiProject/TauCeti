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
# Homogeneous generators on a connected spectrum

A grading of the free module of rank one over an integer-graded commutative ring has a
homogeneous generator if the ring has preconnected prime spectrum. In particular this holds
for domains. The grading is given by an internal decomposition compatible with the scalar
grading, using Mathlib's `SetLike.GradedSMul`.

The Laurent polynomial recording the homogeneous components of `1` is a unit, without any
connectedness hypothesis. On a connected spectrum, a coefficient of that unit is itself a
unit, hence is the required homogeneous generator. The zero ring is included.

Combining the existence of a homogeneous generator with the shift classification of
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units`, every compatible `ℤ`-grading of the free
rank-one module over a `ℤ`-graded commutative ring with preconnected prime spectrum is
graded-isomorphic to a shift `A(d)`, uniquely up to `TauCeti.ShiftClassGroup 𝒜`.
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

section ShiftClassification

variable {A σ τ : Type*} [CommRing A]
    [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ A] [AddSubmonoidClass τ A]
    (𝒜 : ℤ → σ) (ℳ : ℤ → τ) [GradedRing 𝒜] [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] [PreconnectedSpace (PrimeSpectrum A)]

/-- Every compatible `ℤ`-grading of the free rank-one module over a `ℤ`-graded commutative ring
with preconnected prime spectrum is graded-isomorphic to a shift `A(d)`. -/
theorem exists_shift_linearEquiv_of_connected :
    ∃ d : ℤ, ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  obtain ⟨c, u, hu, hmem⟩ := exists_isUnit_mem_of_connected 𝒜 ℳ
  exact ⟨-c,
    (exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ).mpr ⟨u, hu, by simpa using hmem⟩⟩

/-- **Classification of rank-one gradings on a connected spectrum.** Over a `ℤ`-graded commutative
ring with preconnected prime spectrum, every compatible `ℤ`-grading of the free rank-one module is
graded-isomorphic to the shift `A(d)` if and only if `d` represents a unique class in
`TauCeti.ShiftClassGroup 𝒜`. -/
theorem existsUnique_shiftClass_of_connected :
    ∃! c : ShiftClassGroup 𝒜,
      ∀ d : ℤ, (∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d)) ↔
        (d : ShiftClassGroup 𝒜) = c := by
  obtain ⟨d₀, φ₀, hφ₀⟩ := exists_shift_linearEquiv_of_connected 𝒜 ℳ
  refine ⟨d₀, fun d ↦ ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun hd ↦ ?_⟩,
    fun c hc ↦ ((hc d₀).mp ⟨φ₀, hφ₀⟩).symm⟩
  · exact (ShiftClassGroup.mk_eq_mk_iff 𝒜).mpr
      ⟨φ.trans φ₀.symm, fun n x ↦ by
        rw [LinearEquiv.trans_apply, ← hφ n x]
        simpa using (hφ₀ n (φ₀.symm (φ x))).symm⟩
  · obtain ⟨ψ, hψ⟩ := (ShiftClassGroup.mk_eq_mk_iff 𝒜).mp hd
    exact ⟨ψ.trans φ₀, fun n x ↦ by simp [hφ₀, hψ]⟩

/-- Over a `ℤ`-graded commutative ring with preconnected prime spectrum whose homogeneous units
all have degree zero, every compatible `ℤ`-grading of the free rank-one module is
graded-isomorphic to a shift `A(d)` for a unique integer `d`. -/
theorem existsUnique_shift_linearEquiv_of_connected (hbot : homogeneousUnitDegrees 𝒜 = ⊥) :
    ∃! d : ℤ, ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  obtain ⟨c, hc, -⟩ := existsUnique_shiftClass_of_connected 𝒜 ℳ
  obtain ⟨d₀, rfl⟩ := QuotientAddGroup.mk_surjective c
  refine ⟨d₀, (hc d₀).mpr rfl, fun d hd ↦ ?_⟩
  have hmk : (d : ShiftClassGroup 𝒜) = d₀ := (hc d).mp hd
  rwa [QuotientAddGroup.eq, hbot, AddSubgroup.mem_bot, neg_add_eq_zero] at hmk

end ShiftClassification

end TauCeti.GradedAlgebra
