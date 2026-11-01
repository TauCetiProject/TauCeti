/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sign
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.ModEq

/-!
# The signed count of a fibre over a regular value

Let `f : M → N` be a map between real manifolds of the same finite dimension, with orientations
`o` of `M` and `o'` of `N`. The *degree of `f` at `y`* is the sum of the orientation signs
(`TauCeti.Manifold.Orientation.orientationSign`) over the fibre `f ⁻¹' {y}`. Over a
regular value of a `C¹` map from a compact manifold to a `T1` manifold the fibre is finite
(`TauCeti.IsRegularValue.finite_preimage`) and every sign is `1` or `-1`, so this is the signed
count of preimages through which the mapping degree is defined [Lee, Ch. 17, Degree Theory;
Milnor, §5]. The value is defined at every `y`; at a non-regular value, or when the fibre is
infinite, it carries no geometric meaning.

Since the orientation sign vanishes where the derivative is singular, reversing either orientation
negates the degree unconditionally, and the degree of a constant map into a manifold of positive
dimension is `0` at every value.

## Main definition

* `TauCeti.degreeAtRegularValue o o' f y`: the sum of the orientation signs of `f` over the fibre
  of `f` over `y`.

## Main results

* `TauCeti.degreeAtRegularValue_eq_sum_of_finite`: over a finite fibre the degree is a finite sum
  of orientation signs.
* `TauCeti.degreeAtRegularValue_of_notMem_range`: the degree vanishes at a value outside the range.
* `TauCeti.degreeAtRegularValue_id`, `TauCeti.degreeAtRegularValue_const`: the identity has degree
  `1` and a constant map into a manifold of positive dimension has degree `0`.
* `TauCeti.degreeAtRegularValue_modEq_ncard`: over a regular value with finite fibre the degree has
  the parity of the number of preimages.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Function Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {ι : Type*} [Fintype ι]

open Manifold.Orientation

variable {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation J N ι} {f : M → N} {y : N}

/-- The degree of `f` at `y` with respect to orientations `o` of the source and `o'` of the target:
the sum of the orientation signs of `f` over the fibre `f ⁻¹' {y}`, as a `finsum`. At a regular
value with finite fibre, such as any regular value of a `C¹` map from a compact manifold to a `T1`
manifold, this is the signed count of the preimages of `y`; elsewhere the value is a junk value. -/
def degreeAtRegularValue (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (f : M → N) (y : N) : ℤ :=
  ∑ᶠ x ∈ f ⁻¹' {y}, orientationSign o o' f x

/-- The degree is the sum of the orientation signs over any finset enumerating the fibre. -/
theorem degreeAtRegularValue_eq_sum {s : Finset M} (hs : ∀ x, x ∈ s ↔ f x = y) :
    degreeAtRegularValue o o' f y = ∑ x ∈ s, orientationSign o o' f x := by
  rw [degreeAtRegularValue, ← finsum_mem_coe_finset]
  exact finsum_mem_congr (Set.ext fun x ↦ (hs x).symm) fun _ _ ↦ rfl

/-- Over a finite fibre the degree is a finite sum of orientation signs. -/
theorem degreeAtRegularValue_eq_sum_of_finite (h : (f ⁻¹' {y}).Finite) :
    degreeAtRegularValue o o' f y = ∑ x ∈ h.toFinset, orientationSign o o' f x :=
  degreeAtRegularValue_eq_sum fun x ↦ by simp

/-- The degree vanishes at a value outside the range. -/
theorem degreeAtRegularValue_of_notMem_range (h : y ∉ range f) :
    degreeAtRegularValue o o' f y = 0 := by
  rw [degreeAtRegularValue, preimage_singleton_eq_empty.2 h, finsum_mem_empty]

/-- A value at which the degree is nonzero is attained. -/
theorem mem_range_of_degreeAtRegularValue_ne_zero (h : degreeAtRegularValue o o' f y ≠ 0) :
    y ∈ range f :=
  not_not.1 fun hy ↦ h (degreeAtRegularValue_of_notMem_range hy)

/-- Reversing the orientation of the source negates the degree. -/
@[simp]
theorem degreeAtRegularValue_neg_left :
    degreeAtRegularValue (-o) o' f y = -degreeAtRegularValue o o' f y := by
  simp only [degreeAtRegularValue, orientationSign_neg_left, finsum_mem_def, finsum_neg_distrib]

/-- Reversing the orientation of the target negates the degree. -/
@[simp]
theorem degreeAtRegularValue_neg_right :
    degreeAtRegularValue o (-o') f y = -degreeAtRegularValue o o' f y := by
  simp only [degreeAtRegularValue, orientationSign_neg_right, finsum_mem_def, finsum_neg_distrib]

/-- The identity has degree `1` at every point. -/
@[simp]
theorem degreeAtRegularValue_id (o : Manifold.Orientation I M ι) (x : M) :
    degreeAtRegularValue (J := I) (N := M) o o id x = 1 := by
  rw [degreeAtRegularValue, preimage_id, finsum_mem_singleton, orientationSign_id]

/-- A constant map into a manifold of positive dimension has degree `0` at every value: its
derivative vanishes, so every orientation sign is `0`. -/
theorem degreeAtRegularValue_const (hpos : 0 < Module.finrank ℝ E') (y₀ y : N) :
    degreeAtRegularValue o o' (fun _ : M ↦ y₀) y = 0 := by
  refine finsum_mem_eq_zero_of_forall_eq_zero fun x _ ↦ orientationSign_of_not_isInvertible ?_
  rw [mfderiv_const, ContinuousLinearMap.isInvertible_zero_iff]
  rintro ⟨-, h⟩
  exact hpos.ne' (Module.finrank_zero_of_subsingleton (R := ℝ) (M := TangentSpace J y₀))

/-- Over a finite fibre the absolute value of the degree is at most the number of preimages. -/
theorem abs_degreeAtRegularValue_le_ncard (h : (f ⁻¹' {y}).Finite) :
    |degreeAtRegularValue o o' f y| ≤ (f ⁻¹' {y}).ncard := by
  rw [degreeAtRegularValue_eq_sum_of_finite h, ncard_eq_toFinset_card _ h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa using Finset.sum_le_sum fun x (_ : x ∈ h.toFinset) ↦
    abs_orientationSign_le_one (o := o) (o' := o') (f := f) (x := x)

/-- Over a regular value with finite fibre, the degree has the parity of the number of preimages:
every orientation sign is `1` or `-1`. -/
theorem degreeAtRegularValue_modEq_ncard (hy : IsRegularValue I J f y) (h : (f ⁻¹' {y}).Finite) :
    degreeAtRegularValue o o' f y ≡ (f ⁻¹' {y}).ncard [ZMOD 2] := by
  rw [degreeAtRegularValue_eq_sum_of_finite h, ncard_eq_toFinset_card _ h, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one]
  refine Int.ModEq.sum fun x hx ↦ ?_
  rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o')
    (hy.isRegularPoint ((Finite.mem_toFinset h).1 hx)) with h' | h'
  · rw [h']
  · rw [h']
    decide

end TauCeti
