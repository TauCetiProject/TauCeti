/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Square partitions of unity

A *square partition of unity* of a set `s` in a smooth real manifold is a locally finite family of
nonnegative smooth functions `χ i` with `∑ᶠ i, χ i x ^ 2 = 1` for `x ∈ s`. Square partitions are
the natural way to glue operators symmetrically: if each `P i` is formally self-adjoint, so is
`∑ i, χ i P i χ i`, and when every `P i` is the identity this sum is the identity on functions
supported in `s`. An ordinary partition of unity `ρ` would instead lead to the asymmetric
expression `∑ i, ρ i P i`.

The square roots `√(ρ i)` of a smooth partition of unity need not be smooth, so square partitions
are obtained by normalizing instead. For a smooth partition of unity `ρ` of `s`, put

`D x = ∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2`.

This is a smooth and everywhere positive function: if `∑ᶠ j, ρ j x ^ 2 = 0` then every `ρ j x`
vanishes, and the second term equals `1`. Hence `χ i = ρ i / √D` is smooth, with the same support
as `ρ i`, and `∑ᶠ i, χ i x ^ 2 = (∑ᶠ i, ρ i x ^ 2) / D x ≤ 1`, with equality on `s` where
`∑ᶠ j, ρ j x = 1`. On `s` the normalization is the familiar `χ i = ρ i / √(∑ᶠ j, ρ j ^ 2)`; the
second summand of `D` only keeps `D` positive off `s`, where the sum of squares may vanish.

## Main definitions and results

* `SmoothPartitionOfUnity.sqrtNormalized`: the normalized functions `ρ i / √D`.
* `SmoothPartitionOfUnity.sum_sq_sqrtNormalized_eq_one`: their squares sum to one on `s`.
* `SmoothPartitionOfUnity.support_sqrtNormalized`: they have the same supports as `ρ`, so they
  are subordinate to every cover `ρ` is subordinate to
  (`SmoothPartitionOfUnity.IsSubordinate.tsupport_sqrtNormalized_subset`).
* `SmoothPartitionOfUnity.sqNormalized`: the smooth partition of unity of `s` formed by their
  squares (`SmoothPartitionOfUnity.sqNormalized_apply`); conversely `sqrtNormalized` is its
  pointwise square root (`SmoothPartitionOfUnity.sqrtNormalized_eq_sqrt_sqNormalized`).
* `SmoothPartitionOfUnity.exists_isSubordinate_sq`: on a Hausdorff σ-compact finite-dimensional
  manifold, every open cover of a closed set `s` has a subordinate smooth partition of unity of
  `s` whose functions are squares of nonnegative smooth functions.
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  (ρ : SmoothPartitionOfUnity ι I M s)

/-- The supports of the squares of a smooth partition of unity are locally finite. -/
private theorem locallyFinite_support_sq :
    LocallyFinite fun i ↦ support fun x ↦ ρ i x ^ 2 := by
  simpa only [support_pow _ two_ne_zero] using ρ.locallyFinite

private theorem hasFiniteSupport_sq (x : M) : (support fun i ↦ ρ i x ^ 2).Finite :=
  (ρ.locallyFinite_support_sq).point_finite x

/-- If the squares of a partition of unity sum to zero at `x`, every function vanishes at `x`. -/
private theorem eq_zero_of_sum_sq_eq_zero {x : M} (h : ∑ᶠ j, ρ j x ^ 2 = 0) (i : ι) :
    ρ i x = 0 := by
  rw [finsum_eq_sum _ (ρ.hasFiniteSupport_sq x),
    Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _] at h
  by_contra hi
  exact pow_ne_zero 2 hi (h i (by simpa using hi))

/-- The normalizing function `∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2` is positive. -/
private theorem normalizer_pos (x : M) :
    0 < ∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2 := by
  rcases (finsum_nonneg fun j ↦ sq_nonneg (ρ j x)).eq_or_lt with h | h
  · simp [ρ.eq_zero_of_sum_sq_eq_zero h.symm]
  · positivity

private theorem contMDiff_normalizer :
    ContMDiff I 𝓘(ℝ) ∞ fun x ↦ ∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2 :=
  (contMDiff_finsum (fun j ↦ (ρ j).contMDiff.pow 2) ρ.locallyFinite_support_sq).add
    ((contMDiff_const.sub ρ.contMDiff_sum).pow 2)

private theorem contMDiff_sqrt_normalizer :
    ContMDiff I 𝓘(ℝ) ∞ fun x ↦ √(∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2) := fun x ↦
  (Real.contDiffAt_sqrt (ρ.normalizer_pos x).ne').comp_contMDiffAt
    (f := fun x ↦ ∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2) (ρ.contMDiff_normalizer x)

/-- The functions `ρ i / √(∑ᶠ j, ρ j ^ 2 + (1 - ∑ᶠ j, ρ j) ^ 2)` obtained by normalizing a smooth
partition of unity `ρ` of `s`. They are smooth, nonnegative, have the same supports as `ρ`, and
their squares sum to one on `s` (`SmoothPartitionOfUnity.sum_sq_sqrtNormalized_eq_one`). -/
def sqrtNormalized (i : ι) : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
  ⟨fun x ↦ ρ i x / √(∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2),
    (ρ i).contMDiff.div₀ ρ.contMDiff_sqrt_normalizer
      fun x ↦ (Real.sqrt_pos.2 (ρ.normalizer_pos x)).ne'⟩

/-- Unfolding `SmoothPartitionOfUnity.sqrtNormalized`. -/
theorem sqrtNormalized_apply (i : ι) (x : M) :
    ρ.sqrtNormalized i x = ρ i x / √(∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2) :=
  (rfl)

/-- On `s`, the normalized functions are `ρ i / √(∑ᶠ j, ρ j ^ 2)`. -/
theorem sqrtNormalized_apply_of_mem (i : ι) {x : M} (hx : x ∈ s) :
    ρ.sqrtNormalized i x = ρ i x / √(∑ᶠ j, ρ j x ^ 2) := by
  rw [sqrtNormalized_apply, ρ.sum_eq_one hx, sub_self, zero_pow two_ne_zero, add_zero]

/-- The normalized functions are nonnegative. -/
theorem sqrtNormalized_nonneg (i : ι) (x : M) : 0 ≤ ρ.sqrtNormalized i x :=
  div_nonneg (ρ.nonneg i x) (Real.sqrt_nonneg _)

/-- A normalized function vanishes exactly where the original function does. -/
@[simp]
theorem sqrtNormalized_eq_zero_iff {i : ι} {x : M} : ρ.sqrtNormalized i x = 0 ↔ ρ i x = 0 := by
  rw [sqrtNormalized_apply, div_eq_zero_iff,
    or_iff_left (Real.sqrt_pos.2 (ρ.normalizer_pos x)).ne']

/-- Normalizing does not change supports. -/
@[simp]
theorem support_sqrtNormalized (i : ι) : support (ρ.sqrtNormalized i) = support (ρ i) :=
  Set.ext fun _ ↦ not_congr ρ.sqrtNormalized_eq_zero_iff

@[simp]
theorem tsupport_sqrtNormalized (i : ι) : tsupport (ρ.sqrtNormalized i) = tsupport (ρ i) := by
  rw [tsupport, support_sqrtNormalized, tsupport]

/-- The supports of the normalized functions form a locally finite family. -/
theorem locallyFinite_support_sqrtNormalized :
    LocallyFinite fun i ↦ support (ρ.sqrtNormalized i) := by
  simpa only [support_sqrtNormalized] using ρ.locallyFinite

/-- The sum of the squares of the normalized functions is the sum of the squares of `ρ` divided by
the normalizer `∑ᶠ j, ρ j ^ 2 + (1 - ∑ᶠ j, ρ j) ^ 2`. -/
theorem sum_sq_sqrtNormalized (x : M) :
    ∑ᶠ i, ρ.sqrtNormalized i x ^ 2 =
      (∑ᶠ j, ρ j x ^ 2) / (∑ᶠ j, ρ j x ^ 2 + (1 - ∑ᶠ j, ρ j x) ^ 2) := by
  simp_rw [sqrtNormalized_apply, div_pow, Real.sq_sqrt (ρ.normalizer_pos x).le, div_eq_mul_inv]
  exact (finsum_mul _ _).symm

/-- The squares of the normalized functions sum to one on `s`. -/
theorem sum_sq_sqrtNormalized_eq_one {x : M} (hx : x ∈ s) :
    ∑ᶠ i, ρ.sqrtNormalized i x ^ 2 = 1 := by
  rw [sum_sq_sqrtNormalized, ρ.sum_eq_one hx, sub_self, zero_pow two_ne_zero, add_zero,
    div_self]
  intro h
  simpa [ρ.eq_zero_of_sum_sq_eq_zero h] using ρ.sum_eq_one hx

/-- The squares of the normalized functions sum to at most one everywhere. -/
theorem sum_sq_sqrtNormalized_le_one (x : M) : ∑ᶠ i, ρ.sqrtNormalized i x ^ 2 ≤ 1 := by
  rw [sum_sq_sqrtNormalized, div_le_one (ρ.normalizer_pos x)]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The smooth partition of unity of `s` formed by the squares of the normalized functions
`SmoothPartitionOfUnity.sqrtNormalized`. It has the same supports as `ρ`. -/
def sqNormalized : SmoothPartitionOfUnity ι I M s where
  toFun i := ⟨fun x ↦ ρ.sqrtNormalized i x ^ 2, (ρ.sqrtNormalized i).contMDiff.pow 2⟩
  locallyFinite' := by
    simpa only [ContMDiffMap.coeFn_mk, support_pow _ two_ne_zero] using
      ρ.locallyFinite_support_sqrtNormalized
  nonneg' i x := by simpa using sq_nonneg (ρ.sqrtNormalized i x)
  sum_eq_one' x hx := by simpa using ρ.sum_sq_sqrtNormalized_eq_one hx
  sum_le_one' x := by simpa using ρ.sum_sq_sqrtNormalized_le_one x

@[simp]
theorem sqNormalized_apply (i : ι) (x : M) : ρ.sqNormalized i x = ρ.sqrtNormalized i x ^ 2 :=
  (rfl)

/-- The normalized functions are the pointwise square roots of the partition of unity
`SmoothPartitionOfUnity.sqNormalized`. -/
theorem sqrtNormalized_eq_sqrt_sqNormalized (i : ι) (x : M) :
    ρ.sqrtNormalized i x = √(ρ.sqNormalized i x) := by
  rw [sqNormalized_apply, Real.sqrt_sq (ρ.sqrtNormalized_nonneg i x)]

/-- The squared partition of unity has the same supports as `ρ`. -/
@[simp]
theorem support_sqNormalized (i : ι) : support (ρ.sqNormalized i) = support (ρ i) := by
  ext x
  simp

@[simp]
theorem tsupport_sqNormalized (i : ι) : tsupport (ρ.sqNormalized i) = tsupport (ρ i) := by
  rw [tsupport, support_sqNormalized, tsupport]

variable {ρ}

/-- The normalized functions are subordinate to every cover `ρ` is subordinate to. -/
theorem IsSubordinate.tsupport_sqrtNormalized_subset {U : ι → Set M} (hρ : ρ.IsSubordinate U)
    (i : ι) : tsupport (ρ.sqrtNormalized i) ⊆ U i := by
  simpa using hρ i

/-- The squared partition of unity is subordinate to every cover `ρ` is subordinate to. -/
theorem IsSubordinate.sqNormalized {U : ι → Set M} (hρ : ρ.IsSubordinate U) :
    ρ.sqNormalized.IsSubordinate U := fun i ↦ by
  simpa using hρ i

/-- On a Hausdorff σ-compact finite-dimensional manifold, every open cover of a closed set `s` has
a subordinate smooth partition of unity of `s` whose functions are the squares of nonnegative
smooth functions. -/
theorem exists_isSubordinate_sq [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U ∧
      ∃ χ : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, ∀ i x, 0 ≤ χ i x ∧ f i x = χ i x ^ 2 := by
  obtain ⟨ρ, hρ⟩ := exists_isSubordinate I hs U ho hU
  exact ⟨ρ.sqNormalized, hρ.sqNormalized, ρ.sqrtNormalized,
    fun i x ↦ ⟨ρ.sqrtNormalized_nonneg i x, ρ.sqNormalized_apply i x⟩⟩

end SmoothPartitionOfUnity
