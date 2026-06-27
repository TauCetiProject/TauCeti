/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.KernelBounds
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup
public import Mathlib.Topology.Constructions.SumProd

/-!
# Time slices of semigroup-group positive-definite functions

A Berg--Christensen--Ressel positive-definite function on `ℝ≥0 × V` is positive definite in the
spatial variable at every fixed time. Indeed, to test the kernel
`(v, w) ↦ F (t, v - w)`, apply the BCR kernel to the family of points `(t / 2, v)`.

This file records that fixed-time-slice API in kernel form, together with the predicate form for
the fixed-time slice. These lemmas are prerequisites for the BCR representation milestone in the
`OneParameterSemigroups` roadmap: later proofs can apply the spatial Bochner theorem to each time
slice before handling the remaining Laplace/semigroup structure.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"), specifically the reduction of a bounded continuous
positive-definite function on `[0,∞) × V` to spatial positive-definite functions.

## Main declarations

* `TauCeti.IsSemigroupGroupPD.timeSlice_isPositiveDefiniteKernel`: the fixed-time spatial
  kernel is positive definite.
* `TauCeti.IsSemigroupGroupPD.timeSlice_conj_symm` and diagonal lemmas: basic symmetry and
  real-nonnegative diagonal facts for fixed-time slices.
* `TauCeti.IsSemigroupGroupPD.timeSlice_sum_nonneg`: the fixed-time spatial quadratic form is
  nonnegative for arbitrary finite families.
* `TauCeti.IsSemigroupGroupPD.timeSlice_normSq_le`: the fixed-time spatial Cauchy--Schwarz
  estimate.
* `TauCeti.IsSemigroupGroupPD.timeSlice_isPositiveDefinite`: the predicate form when the
  spatial involution is negation.
* `TauCeti.IsSemigroupGroupPD.timeSlice_isPositiveDefiniteKernel_and_continuous`: packages
  the fixed-time positive-definite kernel with continuity of the fixed-time slice.

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

/-- Fixed-time slices are conjugate-symmetric in the spatial variable:
`conj (F (t, v - w)) = F (t, w - v)`. -/
@[simp]
theorem timeSlice_conj_symm (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v w : V) :
    conj (F (t, v - w)) = F (t, w - v) :=
  isPositiveDefiniteKernel_conj_symm (hF.timeSlice_isPositiveDefiniteKernel t) v w

/-- The diagonal value `F (t, 0)` of a fixed-time slice is real and nonnegative. -/
theorem timeSlice_diagonal_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : 0 ≤ F (t, 0) := by
  simpa using isPositiveDefiniteKernel_apply_self_nonneg (hF.timeSlice_isPositiveDefiniteKernel t)
    (0 : V)

/-- The diagonal value `F (t, 0)` of a fixed-time slice has zero imaginary part. -/
@[simp]
theorem timeSlice_diagonal_im (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : (F (t, 0)).im = 0 :=
  ((Complex.nonneg_iff.mp (hF.timeSlice_diagonal_nonneg t)).2).symm

/-- The real part of the diagonal value `F (t, 0)` of a fixed-time slice is nonnegative. -/
theorem timeSlice_diagonal_re_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    0 ≤ (F (t, 0)).re :=
  (Complex.nonneg_iff.mp (hF.timeSlice_diagonal_nonneg t)).1

/-- The diagonal value `F (t, 0)` of a fixed-time slice is equal to its real part, viewed as a
complex number. -/
theorem timeSlice_diagonal_eq_ofReal_re (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    F (t, 0) = ((F (t, 0)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hF.timeSlice_diagonal_im t

/-- The fixed-time spatial quadratic form is nonnegative for arbitrary finite families. -/
theorem timeSlice_sum_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) {ι : Type*} [Fintype ι]
    (v : ι → V) (x : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, conj (x i) * x j * F (t, v i - v j) :=
  (isPositiveDefiniteKernel_iff.mp (hF.timeSlice_isPositiveDefiniteKernel t)).2 v x

/-- The fixed-time spatial Cauchy--Schwarz bound for the kernel entry `F (t, v - w)`. -/
theorem timeSlice_normSq_le (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v w : V) :
    RCLike.normSq (F (t, v - w)) ≤ RCLike.re (F (t, 0)) * RCLike.re (F (t, 0)) := by
  simpa using isPositiveDefiniteKernel_normSq_le (hF.timeSlice_isPositiveDefiniteKernel t) v w

/-- If the spatial type is equipped with the negation involution, then each fixed-time slice is a
positive-definite function in the generic `IsPositiveDefinite` sense. -/
theorem timeSlice_isPositiveDefinite [StarAddMonoid V]
    (hF : IsSemigroupGroupPD F) (hstar : ∀ v : V, star v = -v) (t : ℝ≥0) :
    IsPositiveDefinite fun v : V => F (t, v) :=
  (isPositiveDefinite_iff_isPositiveDefiniteKernel_sub hstar).mpr
    (hF.timeSlice_isPositiveDefiniteKernel t)

end IsSemigroupGroupPD

section Topology

variable [TopologicalSpace V] {F : ℝ≥0 × V → ℂ}

/-- Package the positive-definite kernel on a fixed-time slice with continuity of the
one-variable fixed-time slice. -/
theorem IsSemigroupGroupPD.timeSlice_isPositiveDefiniteKernel_and_continuous
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) (t : ℝ≥0) :
    IsPositiveDefiniteKernel (fun v w : V => F (t, v - w)) ∧ Continuous (fun v : V => F (t, v)) :=
  ⟨hFpd.timeSlice_isPositiveDefiniteKernel t, hFcont.comp (.prodMk_right t)⟩

end Topology

end TauCeti
