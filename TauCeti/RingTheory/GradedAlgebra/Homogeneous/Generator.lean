/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Laurent
public import TauCeti.Algebra.Polynomial.Laurent.Units.Connected
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units
import TauCeti.Algebra.Module.Equiv.Basic

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
* `TauCeti.GradedAlgebra.shiftClass_eq_mk_iff`: a compatible `ℤ`-grading `ℳ` of `A` on a
  preconnected spectrum has `shiftClass 𝒜 ℳ = (d : ShiftClassGroup 𝒜)` if and only if `(A, ℳ)` is
  graded-isomorphic to the shift `A(d)`.
* `TauCeti.GradedAlgebra.shiftClass_eq_iff`: two compatible `ℤ`-gradings of `A` on a preconnected
  spectrum are graded-isomorphic if and only if they have the same `shiftClass` in
  `ShiftClassGroup 𝒜`.
* `TauCeti.GradedAlgebra.instDecompositionShift` and `TauCeti.GradedAlgebra.gradedSMul_shift`:
  scoped instances in `TauCeti.GradedAlgebra` showing that shifting the degree of a grading
  preserves direct-sum decomposition and compatibility with the scalar grading.
* `TauCeti.GradedAlgebra.shiftClass_shift`: for every `d : ℤ`, the translated grading
  `fun n ↦ 𝒜 (n + d)` has `shiftClass` equal to `(d : ShiftClassGroup 𝒜)`.
-/

public section

open DirectSum LaurentPolynomial

namespace TauCeti.GradedAlgebra

section Shift

/-- Shifting the degree of a compatible module grading by `d : ι` preserves compatibility with
the scalar grading `𝒜`. -/
@[scoped instance]
theorem gradedSMul_shift {ι A M σA σM : Type*} [AddSemigroup ι] [SMul A M] [SetLike σA A]
    [SetLike σM M] (𝒜 : ι → σA) (ℳ : ι → σM) [SetLike.GradedSMul 𝒜 ℳ] (d : ι) :
    SetLike.GradedSMul 𝒜 (fun n ↦ ℳ (n + d)) :=
  ⟨fun _ _ _ _ ha hb ↦ by
    simpa only [vadd_eq_add, add_assoc] using SetLike.GradedSMul.smul_mem (B := ℳ) ha hb⟩

/-- Shifting the degree of an internal direct-sum decomposition by `d : ι` preserves the
decomposition. -/
noncomputable scoped instance instDecompositionShift {ι M σ : Type*} [AddGroup ι]
    [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M] [DecidableEq ι] (ℳ : ι → σ)
    [Decomposition ℳ] (d : ι) : Decomposition (fun n ↦ ℳ (n + d)) :=
  DirectSum.Decomposition.compEquiv ℳ (Equiv.addRight d)

end Shift

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
    exact decomposeLaurent_of_mem ℳ (decompose ℳ (1 : A) i).property
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
  refine ⟨c, (decompose ℳ (1 : A) c : A), ?_, (decompose ℳ (1 : A) c).property⟩
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

private theorem shiftClass_spec :
    ∃ (d₀ : ℤ) (φ₀ : A ≃ₗ[A] A),
      shiftClass 𝒜 ℳ = (d₀ : ShiftClassGroup 𝒜) ∧ ∀ n x, φ₀ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d₀) :=
  let ⟨φ₀, hφ₀⟩ := (exists_shift_linearEquiv_of_connected 𝒜 ℳ).choose_spec
  ⟨_, φ₀, rfl, hφ₀⟩

/-- A compatible `ℤ`-grading `ℳ` of `A` on a preconnected prime spectrum has shift class `d` if
and only if `(A, ℳ)` is graded-isomorphic to the shift `A(d)`. -/
theorem shiftClass_eq_mk_iff {d : ℤ} :
    shiftClass 𝒜 ℳ = (d : ShiftClassGroup 𝒜) ↔
      ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ ℳ n ↔ x ∈ 𝒜 (n + d) := by
  obtain ⟨d₀, φ₀, hd₀, hφ₀⟩ := shiftClass_spec 𝒜 ℳ
  rw [hd₀, ShiftClassGroup.mk_eq_mk_iff]
  exact φ₀.exists_forall_iff_of_forall_iff hφ₀

/-- If `ℳ` contains a homogeneous unit in degree `c`, its shift class is `-c`. -/
theorem shiftClass_eq_mk_neg_of_isUnit_mem {u : A} (hu : IsUnit u) {c : ℤ} (hmem : u ∈ ℳ c) :
    shiftClass 𝒜 ℳ = ((-c : ℤ) : ShiftClassGroup 𝒜) :=
  (shiftClass_eq_mk_iff 𝒜 ℳ).mpr <|
    (exists_linearEquiv_iff_exists_isUnit_mem 𝒜 ℳ).mpr ⟨u, hu, by simpa using hmem⟩

@[simp]
theorem shiftClass_self : shiftClass 𝒜 𝒜 = 0 := by
  simpa using shiftClass_eq_mk_neg_of_isUnit_mem 𝒜 𝒜 isUnit_one (c := 0) (SetLike.one_mem_graded 𝒜)

/-- Over a `ℤ`-graded commutative ring with preconnected prime spectrum, two compatible
`ℤ`-gradings of `A` are graded-isomorphic as `A`-modules if and only if they have the same
`shiftClass` in `ShiftClassGroup 𝒜`. -/
theorem shiftClass_eq_iff :
    shiftClass 𝒜 ℳ = shiftClass 𝒜 𝒩 ↔
      ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ 𝒩 n ↔ x ∈ ℳ n := by
  obtain ⟨d, φN, hN, hφN⟩ := shiftClass_spec 𝒜 𝒩
  rw [hN, shiftClass_eq_mk_iff]
  exact φN.exists_forall_iff_of_forall_iff hφN

/-- For every `d : ℤ`, the translated grading `fun n ↦ 𝒜 (n + d)` has shift class
`(d : ShiftClassGroup 𝒜)`. -/
theorem shiftClass_shift (d : ℤ) [Decomposition (fun n ↦ 𝒜 (n + d))]
    [SetLike.GradedSMul 𝒜 (fun n ↦ 𝒜 (n + d))] :
    shiftClass 𝒜 (fun n ↦ 𝒜 (n + d)) = (d : ShiftClassGroup 𝒜) :=
  (shiftClass_eq_mk_iff 𝒜 (fun n ↦ 𝒜 (n + d))).mpr
    ⟨LinearEquiv.refl A A, fun _ _ ↦ Iff.rfl⟩

end ShiftClass

end TauCeti.GradedAlgebra
