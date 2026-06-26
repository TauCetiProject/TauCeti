/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup
public import TauCeti.Analysis.PositiveDefinite.KernelBounds
public import Mathlib.Topology.Constructions

/-!
# Time slices of semigroup-group positive-definite functions

A Berg--Christensen--Ressel positive-definite function on `ℝ≥0 × V` is positive definite in the
spatial variable at every fixed time. Indeed, to test the kernel
`(v, w) ↦ F (t, v - w)`, apply the BCR kernel to the family of points `(t / 2, v)`.

This file records that fixed-time-slice API in kernel form, together with the finite
quadratic-form restatement, conjugate symmetry, diagonal nonnegativity, the scalar
Cauchy--Schwarz bound on each slice, and the elementary continuity statement for continuous
`F`. These lemmas are prerequisites for the BCR representation milestone in the
`OneParameterSemigroups` roadmap: later proofs can apply the spatial Bochner theorem to each
time slice before handling the remaining Laplace/semigroup structure.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"), specifically the reduction of a bounded continuous
positive-definite function on `[0,∞) × V` to spatial positive-definite functions.

## Main declarations

* `TauCeti.IsSemigroupGroupPD.timeSlice_isPositiveDefiniteKernel`: the fixed-time spatial
  kernel is positive definite.
* `TauCeti.IsSemigroupGroupPD.timeSlice_sum_nonneg`: the finite quadratic-form version.
* `TauCeti.IsSemigroupGroupPD.timeSlice_conj_symm`,
  `TauCeti.IsSemigroupGroupPD.timeSlice_apply_zero_nonneg`, and
  `TauCeti.IsSemigroupGroupPD.timeSlice_normSq_le`: basic consequences on a fixed time slice.
* `TauCeti.IsSemigroupGroupPD.timeSlice_isPositiveDefinite`: the predicate form when the
  spatial involution is negation.
* `TauCeti.continuous_timeSlice`: continuity of a fixed-time slice of a continuous function.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F : ℝ≥0 × V → ℂ}

namespace IsSemigroupGroupPD

/-- At every fixed time `t`, a semigroup-group positive-definite function gives the spatial
positive-definite kernel `(v, w) ↦ F (t, v - w)`. -/
theorem timeSlice_isPositiveDefiniteKernel (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    IsPositiveDefiniteKernel fun v w : V => F (t, v - w) := by
  have hK := isPositiveDefiniteKernel_comp hF.isPositiveDefiniteKernel
    (fun v : V => (t / 2, v))
  simpa [add_halves] using hK

/-- The finite quadratic-form restatement of fixed-time spatial positive definiteness. -/
theorem timeSlice_sum_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → V) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (t, v i - v j) := by
  have hK := hF.timeSlice_isPositiveDefiniteKernel t
  have hpos := (isPositiveDefiniteKernel_iff.mp hK).2 v (fun i => conj (c i))
  simpa only [Complex.conj_conj] using hpos

/-- The `2 × 2` Hermitian sub-form of a fixed-time spatial slice. -/
theorem timeSlice_quadForm_two_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0)
    (v w : V) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (t, v - v) + c₀ * conj c₁ * F (t, v - w)
      + c₁ * conj c₀ * F (t, w - v) + c₁ * conj c₁ * F (t, w - w) := by
  have h := hF.timeSlice_sum_nonneg t ![c₀, c₁] ![v, w]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact le_of_le_of_eq h (by ring)

/-- A fixed-time spatial slice is conjugate symmetric:
`conj (F (t, v - w)) = F (t, w - v)`. -/
@[simp]
theorem timeSlice_conj_symm (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v w : V) :
    conj (F (t, v - w)) = F (t, w - v) :=
  isPositiveDefiniteKernel_conj_symm (hF.timeSlice_isPositiveDefiniteKernel t) v w

/-- The value at the spatial origin of a fixed-time slice is nonnegative. -/
theorem timeSlice_apply_zero_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    0 ≤ F (t, 0) := by
  simpa using isPositiveDefiniteKernel_apply_self_nonneg
    (hF.timeSlice_isPositiveDefiniteKernel t) (0 : V)

/-- The value at the spatial origin of a fixed-time slice has zero imaginary part. -/
@[simp]
theorem timeSlice_apply_zero_im (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    (F (t, 0)).im = 0 :=
  ((Complex.nonneg_iff.mp (hF.timeSlice_apply_zero_nonneg t)).2).symm

/-- The real part of the value at the spatial origin of a fixed-time slice is nonnegative. -/
theorem timeSlice_apply_zero_re_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    0 ≤ (F (t, 0)).re :=
  (Complex.nonneg_iff.mp (hF.timeSlice_apply_zero_nonneg t)).1

/-- On a fixed-time slice, the squared norm of an off-diagonal value is bounded by the square of
the real diagonal value. -/
theorem timeSlice_normSq_le (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v w : V) :
    Complex.normSq (F (t, v - w)) ≤ (F (t, 0)).re * (F (t, 0)).re := by
  simpa [sub_self] using
    isPositiveDefiniteKernel_normSq_le (hF.timeSlice_isPositiveDefiniteKernel t) v w

/-- If the spatial type is equipped with the negation involution, then each fixed-time slice is a
positive-definite function in the generic `IsPositiveDefinite` sense. -/
theorem timeSlice_isPositiveDefinite [StarAddMonoid V]
    (hF : IsSemigroupGroupPD F) (hstar : ∀ v : V, star v = -v) (t : ℝ≥0) :
    IsPositiveDefinite fun v : V => F (t, v) :=
  (isPositiveDefinite_iff_isPositiveDefiniteKernel_sub hstar).mpr
    (hF.timeSlice_isPositiveDefiniteKernel t)

end IsSemigroupGroupPD

section Topology

variable {W : Type*} [TopologicalSpace W]

/-- A fixed-time slice of a continuous function on `ℝ≥0 × V` is continuous. -/
theorem continuous_timeSlice {F : ℝ≥0 × W → ℂ} (hF : Continuous F) (t : ℝ≥0) :
    Continuous fun v : W => F (t, v) :=
  hF.comp (continuous_const.prodMk continuous_id)

variable [TopologicalSpace V] {F : ℝ≥0 × V → ℂ}

/-- A continuous semigroup-group positive-definite function has continuous positive-definite
spatial kernels on every fixed time slice. -/
theorem IsSemigroupGroupPD.continuous_timeSlice_isPositiveDefiniteKernel
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) (t : ℝ≥0) :
    IsPositiveDefiniteKernel (fun v w : V => F (t, v - w)) ∧ Continuous (fun v : V => F (t, v)) :=
  ⟨hFpd.timeSlice_isPositiveDefiniteKernel t, continuous_timeSlice hFcont t⟩

end Topology

end TauCeti
