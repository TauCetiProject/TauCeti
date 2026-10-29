/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.FiniteSlopeMultiset
public import TauCeti.Analysis.Convex.Sequence.Minkowski.Face

/-!
# Minkowski sums of finite slope data

The Minkowski sum of two nonempty convex polygons with finite domain is again such a polygon.
This file transports `minkowskiSum` to the finite unit-slope presentation
`FiniteSlopeData ℝ`. The first points add, the horizontal lengths add, and the finite slope
multisets add. The last statement is the geometric input to the additivity of the slope
multisets of Newton polygons of polynomials under multiplication.

The slope multiset is compared through face widths: at every real slope `σ` both polygons
have a finite face, the face of the sum at `σ` is the sum of these faces, and the
multiplicity of `σ` is the width of the face.

## Main results

* `FiniteSlopeData.minkowskiSum`: the slope data of the Minkowski sum of the represented
  polygons, with `FiniteSlopeData.heights_minkowskiSum`.
* `FiniteSlopeData.minkowskiSum_start`, `FiniteSlopeData.minkowskiSum_initialHeight`,
  `FiniteSlopeData.minkowskiSum_length`: anchors and horizontal lengths add.
* `FiniteSlopeData.slopeMultiset_minkowskiSum`: finite slope multisets add.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

namespace TauCeti

namespace FiniteSlopeData

variable (d₁ d₂ : FiniteSlopeData ℝ)

/-- The Minkowski sum of two represented polygons is finite exactly on
`[start₁ + start₂, start₁ + start₂ + (length₁ + length₂)]`. -/
private theorem minkowskiSum_heights_ne_top_iff {n : ℕ} :
    TauCeti.minkowskiSum d₁.heights d₂.heights n ≠ ⊤ ↔
      d₁.start + d₂.start ≤ n ∧ n ≤ d₁.start + d₂.start + (d₁.length + d₂.length) := by
  simp only [minkowskiSum_ne_top_iff, ne_eq, heights_eq_top_iff, not_or, not_lt]
  constructor
  · rintro ⟨i, j, rfl, hi, hj⟩
    omega
  · rintro ⟨hn₁, hn₂⟩
    exact ⟨min (n - d₂.start) (d₁.start + d₁.length),
      n - min (n - d₂.start) (d₁.start + d₁.length), by omega, by omega, by omega⟩

/-- The finite slope data of the Minkowski sum of the polygons represented by `d₁` and `d₂`.
Its heights are the min-convolution of their heights. -/
noncomputable def minkowskiSum : FiniteSlopeData ℝ :=
  ofIsConvexSeq (d₁.isConvexSeq_heights.minkowskiSum d₂.isConvexSeq_heights)
    fun _ ↦ minkowskiSum_heights_ne_top_iff d₁ d₂

/-- The Minkowski sum of slope data represents the Minkowski sum of the heights. -/
@[simp]
theorem heights_minkowskiSum :
    (d₁.minkowskiSum d₂).heights = TauCeti.minkowskiSum d₁.heights d₂.heights :=
  heights_ofIsConvexSeq _ _

/-- Slope data represents a Minkowski sum exactly when it is the Minkowski sum of the slope
data. -/
theorem eq_minkowskiSum_iff {d : FiniteSlopeData ℝ} :
    d = d₁.minkowskiSum d₂ ↔ d.heights = TauCeti.minkowskiSum d₁.heights d₂.heights := by
  rw [← heights_minkowskiSum]
  exact heights_injective.eq_iff.symm

/-- The first index of a Minkowski sum is the sum of the first indices. -/
@[simp]
theorem minkowskiSum_start : (d₁.minkowskiSum d₂).start = d₁.start + d₂.start :=
  ofIsConvexSeq_start _ _

/-- The horizontal length of a Minkowski sum is the sum of the horizontal lengths. -/
@[simp]
theorem minkowskiSum_length : (d₁.minkowskiSum d₂).length = d₁.length + d₂.length :=
  ofIsConvexSeq_length _ _

/-- The initial height of a Minkowski sum is the sum of the initial heights. -/
@[simp]
theorem minkowskiSum_initialHeight :
    (d₁.minkowskiSum d₂).initialHeight = d₁.initialHeight + d₂.initialHeight := by
  rw [minkowskiSum, ofIsConvexSeq_initialHeight,
    minkowskiSum_add_eq_of_forall_lt (fun k hk ↦ d₁.heights_eq_top_iff.mpr (.inl hk))
      (fun k hk ↦ d₂.heights_eq_top_iff.mpr (.inl hk)),
    heights_start, heights_start, ← WithTop.coe_add, WithTop.untop₀_coe]

/-- The Minkowski sum of finite slope data is commutative. -/
theorem minkowskiSum_comm : d₁.minkowskiSum d₂ = d₂.minkowskiSum d₁ := by
  rw [eq_minkowskiSum_iff, heights_minkowskiSum, TauCeti.minkowskiSum_comm]

/-- The Minkowski sum of finite slope data is associative. -/
theorem minkowskiSum_assoc (d₃ : FiniteSlopeData ℝ) :
    (d₁.minkowskiSum d₂).minkowskiSum d₃ = d₁.minkowskiSum (d₂.minkowskiSum d₃) := by
  rw [eq_minkowskiSum_iff, heights_minkowskiSum, heights_minkowskiSum, heights_minkowskiSum,
    TauCeti.minkowskiSum_assoc]

/-- The finite slope multiset of a Minkowski sum is the sum of the finite slope multisets. -/
@[simp]
theorem slopeMultiset_minkowskiSum :
    (d₁.minkowskiSum d₂).slopeMultiset = d₁.slopeMultiset + d₂.slopeMultiset := by
  classical
  ext σ
  obtain ⟨l₁, u₁, hf₁⟩ := d₁.exists_isFiniteFace_heights σ
  obtain ⟨l₂, u₂, hf₂⟩ := d₂.exists_isFiniteFace_heights σ
  have hf := hf₁.minkowskiSum hf₂
  rw [← heights_minkowskiSum] at hf
  rw [Multiset.count_add, count_slopeMultiset_of_isFiniteFace _ hf,
    count_slopeMultiset_of_isFiniteFace _ hf₁, count_slopeMultiset_of_isFiniteFace _ hf₂]
  have := hf₁.left_le_right
  have := hf₂.left_le_right
  omega

end FiniteSlopeData

end TauCeti
