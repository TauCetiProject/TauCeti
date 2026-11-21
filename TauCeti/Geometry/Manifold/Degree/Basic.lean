/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sign
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Set.Card.Arithmetic

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

The *mapping degree* `TauCeti.degree o o' f` is the signed count at a regular value chosen
arbitrarily, and `0` when there is none, for instance when `N` is empty. That this choice does not
matter, for a proper smooth map from a Hausdorff boundaryless manifold to a connected σ-compact
Hausdorff boundaryless one, is proved in `TauCeti.Geometry.Manifold.Degree.Global`.

## Main definitions

* `TauCeti.degreeAtRegularValue o o' f y`: the sum of the orientation signs of `f` over the fibre
  of `f` over `y`.
* `TauCeti.degree o o' f`: the mapping degree, the signed count of the fibre over a regular value.

## Main results

* `TauCeti.degreeAtRegularValue_eq_sum_of_finite`: over a finite fibre the degree is a finite sum
  of orientation signs.
* `TauCeti.degreeAtRegularValue_of_notMem_range`: the degree vanishes at a value outside the range.
* `TauCeti.degreeAtRegularValue_id`, `TauCeti.degreeAtRegularValue_const`: the identity has degree
  `1` and a constant map into a manifold of positive dimension has degree `0`.
* `TauCeti.degreeAtRegularValue_comp_of_bijective`: precomposing with a bijection that preserves
  orientation on the fibre does not change the degree.
* `TauCeti.degreeAtRegularValue_comp_left`: postcomposing with a map that is
  orientation-preserving at a value and has no other preimage of its image there does not change
  the degree at that value.
* `TauCeti.degreeAtRegularValue_eq_ncard`: where `f` preserves orientations along the fibre, the
  degree is the number of preimages.
* `TauCeti.degreeAtRegularValue_modEq_ncard`: over a regular value the degree has the parity of
  the number of preimages.
* `TauCeti.degree_id`, `TauCeti.degree_const`: the identity of a nonempty manifold has degree `1`
  and a constant map into a manifold of positive dimension has degree `0`.
* `TauCeti.degree_of_isEmpty`: a map to an empty manifold has degree `0`.
* `TauCeti.degree_eq_zero_of_not_exists`: a map with no regular value has degree `0`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

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

/-- Unfolding `degreeAtRegularValue`: the `finsum` of orientation signs over `f ⁻¹' {y}`. -/
theorem degreeAtRegularValue_def (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation J N ι) (f : M → N) (y : N) :
    degreeAtRegularValue o o' f y = ∑ᶠ x ∈ f ⁻¹' {y}, orientationSign o o' f x :=
  (rfl)

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

section Comp

variable {E₀ H₀ M₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M₀]
  [ChartedSpace H₀ M₀] [IsManifold I₀ 1 M₀] {o₀ : Manifold.Orientation I₀ M₀ ι}

/-- **Precomposing with an orientation-preserving bijection preserves the degree.** If
`e : M₀ → M` is a bijection preserving the orientations `o₀` and `o` on the fibre over `y` and `f`
is differentiable at the image points of that fibre, then `f ∘ e` has the same degree as `f` at
`y`: `e` matches the fibres of `f ∘ e` and `f`, and the orientation signs at matched points
agree. -/
theorem degreeAtRegularValue_comp_of_bijective {e : M₀ → M} (he : Bijective e)
    (hpres : ∀ x, f (e x) = y → IsOrientationPreservingAt o₀ o e x)
    (hf : ∀ x, f (e x) = y → MDifferentiableAt I J f (e x)) :
    degreeAtRegularValue o₀ o' (f ∘ e) y = degreeAtRegularValue o o' f y := by
  refine finsum_mem_eq_of_bijOn e (he.bijOn_preimage (t := f ⁻¹' {y})) fun x hx ↦ ?_
  rw [orientationSign_comp (hf x hx)
    (mdifferentiableAt_of_isInvertible_mfderiv (hpres x hx).isInvertible_mfderiv),
    orientationSign_of_isOrientationPreservingAt (hpres x hx), mul_one]

variable {E₁ H₁ N₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {J₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace N₁]
  [ChartedSpace H₁ N₁] [IsManifold J₁ 1 N₁] {o₁ : Manifold.Orientation J₁ N₁ ι}

/-- **Postcomposing with a map that is orientation-preserving over the value preserves the
degree.** If `y` is the only preimage of `e y` under `e : N → N₁`, `e` preserves the orientations
`o'` and `o₁` at `y`, and `f` is differentiable along its fibre over `y`, then `e ∘ f` has the same
degree at `e y` as `f` at `y`: the two maps have the same fibres over these points, and the
orientation signs agree. -/
theorem degreeAtRegularValue_comp_left {e : N → N₁} {y : N} (he : e ⁻¹' {e y} ⊆ {y})
    (hpres : IsOrientationPreservingAt o' o₁ e y)
    (hf : ∀ x ∈ f ⁻¹' {y}, MDifferentiableAt I J f x) :
    degreeAtRegularValue o o₁ (e ∘ f) (e y) = degreeAtRegularValue o o' f y := by
  have hfib : (e ∘ f) ⁻¹' {e y} = f ⁻¹' {y} :=
    Subset.antisymm (fun x hx ↦ he hx) fun x hx ↦ by simp_all
  rw [degreeAtRegularValue, degreeAtRegularValue, hfib]
  refine finsum_mem_congr rfl fun x hx ↦ ?_
  have hfx := hf x hx
  rw [mem_preimage, mem_singleton_iff] at hx
  subst hx
  rw [orientationSign_comp
      (mdifferentiableAt_of_isInvertible_mfderiv hpres.isInvertible_mfderiv) hfx,
    orientationSign_of_isOrientationPreservingAt hpres, one_mul]

end Comp

/-- Over a finite fibre the absolute value of the degree is at most the number of preimages. -/
theorem abs_degreeAtRegularValue_le_ncard (h : (f ⁻¹' {y}).Finite) :
    |degreeAtRegularValue o o' f y| ≤ (f ⁻¹' {y}).ncard := by
  rw [degreeAtRegularValue_eq_sum_of_finite h, ncard_eq_toFinset_card _ h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa using Finset.sum_le_sum fun x (_ : x ∈ h.toFinset) ↦
    abs_orientationSign_le_one (o := o) (o' := o') (f := f) (x := x)

/-- If `f` preserves orientations at every point of the fibre over `y`, the degree at `y` is the
number of preimages. For an infinite fibre both sides are `0` by the `finsum` and `ncard`
conventions. -/
theorem degreeAtRegularValue_eq_ncard
    (h : ∀ x ∈ f ⁻¹' {y}, IsOrientationPreservingAt o o' f x) :
    degreeAtRegularValue o o' f y = (f ⁻¹' {y}).ncard := by
  rw [degreeAtRegularValue, finsum_mem_congr rfl fun x hx ↦
    orientationSign_of_isOrientationPreservingAt (h x hx)]
  rcases (f ⁻¹' {y}).finite_or_infinite with hf | hf
  · rw [← finsum_one, Nat.cast_finsum_mem hf, Nat.cast_one]
  · rw [hf.ncard, Nat.cast_zero]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const one_ne_zero] using hf)

/-- Over a regular value, the degree has the parity of the number of preimages: every orientation
sign is `1` or `-1`. For an infinite fibre both sides are `0` by the `finsum` and `ncard`
conventions. -/
theorem degreeAtRegularValue_modEq_ncard (hy : IsRegularValue I J f y) :
    degreeAtRegularValue o o' f y ≡ (f ⁻¹' {y}).ncard [ZMOD 2] := by
  by_cases h : (f ⁻¹' {y}).Finite
  · rw [degreeAtRegularValue_eq_sum_of_finite h, ncard_eq_toFinset_card _ h,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Int.ModEq.sum fun x hx ↦ ?_
    rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o')
      (hy.isRegularPoint ((Finite.mem_toFinset h).1 hx)) with h' | h'
    · rw [h']
    · rw [h']
      decide
  · have h0 : degreeAtRegularValue o o' f y = 0 := by
      refine finsum_mem_eq_zero_of_infinite ?_
      rw [inter_eq_left.mpr fun x hx ↦ ?_]
      · exact h
      · rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o')
          (hy.isRegularPoint hx) with h' | h' <;> simp [h']
    rw [h0, Set.Infinite.ncard h]
    rfl

open Classical in
/-- The *mapping degree* of `f : M → N` with respect to orientations `o` of `M` and `o'` of `N`:
the signed count `degreeAtRegularValue o o' f y` of the fibre over a regular value `y`, chosen
arbitrarily, and `0` if `f` has no regular value. For a proper smooth map from a Hausdorff
boundaryless manifold to a connected σ-compact Hausdorff boundaryless manifold of the same
dimension the choice does not matter (`TauCeti.degree_eq_degreeAtRegularValue`). -/
def degree (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι) (f : M → N) : ℤ :=
  if h : ∃ y, IsRegularValue I J f y then degreeAtRegularValue o o' f h.choose else 0

/-- If `f` has a regular value, its degree is the signed count at the chosen one. -/
theorem degree_eq_degreeAtRegularValue_choose (h : ∃ y, IsRegularValue I J f y) :
    degree o o' f = degreeAtRegularValue o o' f h.choose :=
  dite_eq_left h

/-- If `f` has no regular value, its degree is `0`. -/
theorem degree_eq_zero_of_not_exists (h : ¬∃ y, IsRegularValue I J f y) :
    degree o o' f = 0 :=
  dite_eq_right h

/-- A map to an empty manifold has degree `0`, since it has no regular value. -/
@[simp]
theorem degree_of_isEmpty [IsEmpty N] : degree o o' f = 0 :=
  degree_eq_zero_of_not_exists (by simp)

/-- Reversing the orientation of the source negates the degree. -/
@[simp]
theorem degree_neg_left : degree (-o) o' f = -degree o o' f := by
  unfold degree
  split_ifs <;> simp

/-- Reversing the orientation of the target negates the degree. -/
@[simp]
theorem degree_neg_right : degree o (-o') f = -degree o o' f := by
  unfold degree
  split_ifs <;> simp

/-- The identity of a nonempty manifold has degree `1`. -/
@[simp]
theorem degree_id [Nonempty M] (o : Manifold.Orientation I M ι) :
    degree (J := I) (N := M) o o id = 1 := by
  have h : ∃ y, IsRegularValue I I (id : M → M) y :=
    ⟨Classical.arbitrary M, isRegularValue_iff.2 fun x _ ↦ by
      rw [isRegularPoint_iff, mfderiv_id]
      exact surjective_id⟩
  rw [degree_eq_degreeAtRegularValue_choose h, degreeAtRegularValue_id]

/-- A constant map into a manifold of positive dimension has degree `0`. -/
@[simp]
theorem degree_const (hpos : 0 < Module.finrank ℝ E') (y₀ : N) :
    degree o o' (fun _ : M ↦ y₀) = 0 := by
  unfold degree
  split_ifs
  · exact degreeAtRegularValue_const hpos y₀ _
  · rfl

end TauCeti
