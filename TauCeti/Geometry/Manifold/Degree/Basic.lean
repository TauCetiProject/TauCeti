/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.RegularValue
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.ModEq

/-!
# The signed count of a fibre over a regular value

Let `f : M → N` be a map between real manifolds of the same finite dimension, with orientations
`o` of `M` and `o'` of `N`. The *orientation sign* of `f` at `x` is `1` where `f` preserves the
orientations, `-1` where it reverses them, and `0` where its manifold derivative is not invertible.
The *degree of `f` at `y`* is the sum of the orientation signs over the fibre `f ⁻¹' {y}`. Over a
regular value of a `C¹` map from a compact manifold to a `T1` manifold the fibre is finite
(`TauCeti.IsRegularValue.finite_preimage`) and every sign is `1` or `-1`, so this is the signed
count of preimages through which the mapping degree is defined [Lee, Ch. 17, Degree Theory;
Milnor, §5]. The value is defined at every `y`; at a non-regular value, or when the fibre is
infinite, it carries no geometric meaning.

The orientation sign vanishes where the derivative is singular rather than being forced to `±1`.
With this convention reversing either orientation negates the sign and the degree unconditionally,
the sign of a composite of differentiable maps is the product of the signs, and the degree of a
constant map into a manifold of positive dimension is `0` at every value.

## Main definitions

* `TauCeti.Manifold.Orientation.orientationSign o o' f x`: the local orientation sign of `f` at
  `x`.
* `TauCeti.degreeAtRegularValue o o' f y`: the sum of the orientation signs of `f` over the fibre
  of `f` over `y`.

## Main results

* `TauCeti.Manifold.Orientation.orientationSign_comp`: the orientation sign of a composite of
  differentiable maps is the product of the orientation signs.
* `TauCeti.Manifold.Orientation.orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint`: at a
  regular point the orientation sign is `1` or `-1`.
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
  {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P]
  [ChartedSpace H'' P] [IsManifold K 1 P]
  {ι : Type*} [Fintype ι]

namespace Manifold.Orientation

variable {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation J N ι}
  {o'' : Manifold.Orientation K P ι} {f : M → N} {g : N → P} {x : M}

open scoped Classical in
/-- The orientation sign of `f` at `x` with respect to orientations `o` of the source and `o'` of
the target: `1` where `f` preserves orientations, `-1` where it reverses them, and `0` where the
manifold derivative of `f` at `x` is not invertible. -/
def orientationSign (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (f : M → N) (x : M) : ℤ :=
  if IsOrientationPreservingAt o o' f x then 1
  else if IsOrientationReversingAt o o' f x then -1 else 0

theorem orientationSign_of_isOrientationPreservingAt (h : IsOrientationPreservingAt o o' f x) :
    orientationSign o o' f x = 1 := by
  simp [orientationSign, h]

theorem orientationSign_of_isOrientationReversingAt (h : IsOrientationReversingAt o o' f x) :
    orientationSign o o' f x = -1 := by
  have hp : ¬IsOrientationPreservingAt o o' f x := fun hp ↦
    not_isOrientationPreservingAt_and_isOrientationReversingAt o o' f x ⟨hp, h⟩
  simp [orientationSign, hp, h]

theorem orientationSign_of_not_isInvertible (h : ¬(mfderiv I J f x).IsInvertible) :
    orientationSign o o' f x = 0 := by
  have hp : ¬IsOrientationPreservingAt o o' f x := fun hp ↦ h hp.isInvertible_mfderiv
  have hr : ¬IsOrientationReversingAt o o' f x := fun hr ↦ h hr.isInvertible_mfderiv
  simp [orientationSign, hp, hr]

/-- Where the manifold derivative is invertible, the orientation sign is `1` or `-1`. -/
theorem orientationSign_eq_one_or_eq_neg_one (h : (mfderiv I J f x).IsInvertible) :
    orientationSign o o' f x = 1 ∨ orientationSign o o' f x = -1 := by
  obtain ⟨e, he⟩ := h
  exact (isOrientationPreservingAt_or_isOrientationReversingAt o o' f x e he).imp
    orientationSign_of_isOrientationPreservingAt orientationSign_of_isOrientationReversingAt

@[simp]
theorem orientationSign_eq_one_iff :
    orientationSign o o' f x = 1 ↔ IsOrientationPreservingAt o o' f x := by
  refine ⟨fun h ↦ ?_, orientationSign_of_isOrientationPreservingAt⟩
  unfold orientationSign at h
  split_ifs at h with hp <;> first | exact hp | omega

@[simp]
theorem orientationSign_eq_neg_one_iff :
    orientationSign o o' f x = -1 ↔ IsOrientationReversingAt o o' f x := by
  refine ⟨fun h ↦ ?_, orientationSign_of_isOrientationReversingAt⟩
  unfold orientationSign at h
  split_ifs at h with _ hr
  exact hr

@[simp]
theorem orientationSign_eq_zero_iff :
    orientationSign o o' f x = 0 ↔ ¬(mfderiv I J f x).IsInvertible := by
  refine ⟨fun h hinv ↦ ?_, orientationSign_of_not_isInvertible⟩
  rcases orientationSign_eq_one_or_eq_neg_one (o := o) (o' := o') hinv with h' | h' <;>
    simp [h'] at h

theorem abs_orientationSign_le_one : |orientationSign o o' f x| ≤ 1 := by
  unfold orientationSign
  split_ifs <;> simp

/-- Reversing the orientation of the source negates the orientation sign. -/
@[simp]
theorem orientationSign_neg_left : orientationSign (-o) o' f x = -orientationSign o o' f x := by
  simp only [orientationSign, isOrientationPreservingAt_neg_left,
    isOrientationReversingAt_neg_left]
  by_cases hp : IsOrientationPreservingAt o o' f x
  · have hr : ¬IsOrientationReversingAt o o' f x := fun hr ↦
      not_isOrientationPreservingAt_and_isOrientationReversingAt o o' f x ⟨hp, hr⟩
    simp [hp, hr]
  · by_cases hr : IsOrientationReversingAt o o' f x <;> simp [hp, hr]

/-- Reversing the orientation of the target negates the orientation sign. -/
@[simp]
theorem orientationSign_neg_right : orientationSign o (-o') f x = -orientationSign o o' f x := by
  simp only [orientationSign, isOrientationPreservingAt_neg_right,
    isOrientationReversingAt_neg_right]
  by_cases hp : IsOrientationPreservingAt o o' f x
  · have hr : ¬IsOrientationReversingAt o o' f x := fun hr ↦
      not_isOrientationPreservingAt_and_isOrientationReversingAt o o' f x ⟨hp, hr⟩
    simp [hp, hr]
  · by_cases hr : IsOrientationReversingAt o o' f x <;> simp [hp, hr]

@[simp]
theorem orientationSign_id : orientationSign (I := I) (J := I) (N := M) o o id x = 1 :=
  orientationSign_of_isOrientationPreservingAt (isOrientationPreservingAt_id o x)

/-- At a regular point the orientation sign is `1` or `-1`. -/
theorem orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (h : IsRegularPoint I J f x) :
    orientationSign o o' f x = 1 ∨ orientationSign o o' f x = -1 :=
  -- The two orientations force the source and target models to have the same dimension.
  orientationSign_eq_one_or_eq_neg_one
    ((isRegularPoint_iff_isInvertible_mfderiv (o.card_eq.symm.trans o'.card_eq)).1 h)

omit [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold K 1 P] in
/-- Between manifolds of the same finite dimension, a composite of differentiable maps with
invertible derivative has invertible derivative factors. -/
private theorem isInvertible_mfderiv_of_isInvertible_mfderiv_comp (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation J N ι) (o'' : Manifold.Orientation K P ι)
    (hg : MDifferentiableAt J K g (f x)) (hf : MDifferentiableAt I J f x)
    (h : (mfderiv I K (g ∘ f) x).IsInvertible) :
    (mfderiv I J f x).IsInvertible ∧ (mfderiv J K g (f x)).IsInvertible := by
  rw [mfderiv_comp x hg hf] at h
  refine ⟨(isRegularPoint_iff_isInvertible_mfderiv (o.card_eq.symm.trans o'.card_eq)).1 ?_,
    (isRegularPoint_iff_isInvertible_mfderiv (o'.card_eq.symm.trans o''.card_eq)).1
      (isRegularPoint_iff.2 fun z ↦ ?_)⟩
  · -- The derivative of `f` is injective since the composite is, and injectivity is regularity
    -- between models of the same dimension.
    exact (isRegularPoint_iff_injective_mfderiv (o.card_eq.symm.trans o'.card_eq)).2
      (Injective.of_comp (f := mfderiv J K g (f x)) h.injective)
  · -- The derivative of `g` is surjective since the composite is.
    obtain ⟨v, rfl⟩ := h.surjective z
    exact ⟨_, rfl⟩

/-- The orientation sign of a composite of differentiable maps is the product of the orientation
signs. -/
theorem orientationSign_comp (hg : MDifferentiableAt J K g (f x))
    (hf : MDifferentiableAt I J f x) :
    orientationSign o o'' (g ∘ f) x =
      orientationSign o' o'' g (f x) * orientationSign o o' f x := by
  by_cases hinv : (mfderiv I J f x).IsInvertible ∧ (mfderiv J K g (f x)).IsInvertible
  · obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hinv
    rcases isOrientationPreservingAt_or_isOrientationReversingAt o o' f x e he with hpf | hrf <;>
      rcases isOrientationPreservingAt_or_isOrientationReversingAt o' o'' g (f x) e' he'
        with hpg | hrg
    · rw [orientationSign_of_isOrientationPreservingAt (hpg.comp hpf),
        orientationSign_of_isOrientationPreservingAt hpg,
        orientationSign_of_isOrientationPreservingAt hpf, one_mul]
    · rw [orientationSign_of_isOrientationReversingAt (hrg.comp_preserving hpf),
        orientationSign_of_isOrientationReversingAt hrg,
        orientationSign_of_isOrientationPreservingAt hpf, mul_one]
    · rw [orientationSign_of_isOrientationReversingAt (hpg.comp_reversing hrf),
        orientationSign_of_isOrientationPreservingAt hpg,
        orientationSign_of_isOrientationReversingAt hrf, one_mul]
    · rw [orientationSign_of_isOrientationPreservingAt (hrg.comp hrf),
        orientationSign_of_isOrientationReversingAt hrg,
        orientationSign_of_isOrientationReversingAt hrf, neg_one_mul, neg_neg]
  · rw [orientationSign_of_not_isInvertible fun h ↦
      hinv (isInvertible_mfderiv_of_isInvertible_mfderiv_comp o o' o'' hg hf h)]
    rcases not_and_or.1 hinv with h | h
    · rw [orientationSign_of_not_isInvertible h, mul_zero]
    · rw [orientationSign_of_not_isInvertible h, zero_mul]

end Manifold.Orientation

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
