/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# The orientation sign of a map at a point

Let `f : M → N` be a map between real manifolds of the same finite dimension, with orientations
`o` of `M` and `o'` of `N`. The *orientation sign* of `f` at `x` is `1` where `f` preserves the
orientations, `-1` where it reverses them, and `0` where its manifold derivative is not invertible.
It is the local contribution of a preimage to the mapping degree [Lee, Ch. 17, Degree Theory;
Milnor, §5].

The orientation sign vanishes where the derivative is singular rather than being forced to `±1`.
With this convention reversing either orientation negates the sign unconditionally, and the sign of
a composite of differentiable maps is the product of the signs.

## Main definitions

* `TauCeti.Manifold.Orientation.orientationSign o o' f x`: the local orientation sign of `f` at
  `x`.

## Main results

* `TauCeti.Manifold.Orientation.orientationSign_eq_one_iff`,
  `TauCeti.Manifold.Orientation.orientationSign_eq_neg_one_iff`,
  `TauCeti.Manifold.Orientation.orientationSign_eq_zero_iff`: the sign is `1`, `-1` or `0` exactly
  where `f` preserves orientations, reverses them, or has singular derivative.
* `TauCeti.Manifold.Orientation.orientationSign_comp`: the orientation sign of a composite of
  differentiable maps is the product of the orientation signs.
* `TauCeti.Manifold.Orientation.orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint`: at a
  regular point the orientation sign is `1` or `-1`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Function
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

/-- The orientation sign is `1` exactly where `f` preserves the orientations. -/
@[simp]
theorem orientationSign_eq_one_iff :
    orientationSign o o' f x = 1 ↔ IsOrientationPreservingAt o o' f x := by
  refine ⟨fun h ↦ ?_, orientationSign_of_isOrientationPreservingAt⟩
  unfold orientationSign at h
  split_ifs at h with hp <;> first | exact hp | omega

/-- The orientation sign is `-1` exactly where `f` reverses the orientations. -/
@[simp]
theorem orientationSign_eq_neg_one_iff :
    orientationSign o o' f x = -1 ↔ IsOrientationReversingAt o o' f x := by
  refine ⟨fun h ↦ ?_, orientationSign_of_isOrientationReversingAt⟩
  unfold orientationSign at h
  split_ifs at h with _ hr
  exact hr

/-- The orientation sign is `0` exactly where the manifold derivative of `f` is singular, that is,
not invertible. -/
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
      hinv (isInvertible_mfderiv_of_isInvertible_mfderiv_comp
        (o.card_eq.symm.trans o'.card_eq) (o'.card_eq.symm.trans o''.card_eq) hg hf h)]
    rcases not_and_or.1 hinv with h | h
    · rw [orientationSign_of_not_isInvertible h, mul_zero]
    · rw [orientationSign_of_not_isInvertible h, zero_mul]

end Manifold.Orientation

end TauCeti
