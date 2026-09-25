/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Half-planes bounded by a geodesic line

The imaginary axis splits `ℍ` into two open half-planes, `{z | 0 < z.re}` and
`{z | z.re < 0}`, and the axis itself, `{z | z.re = 0}`. This file transports that picture by
`g : PSL(2, ℝ)`, the same idiom `Geodesic.lean` uses for the line itself: `rightHalfPlane g`
and `leftHalfPlane g` are the `g`-images of the two canonical sides, `Set.range (geodesicLine g)`
(via `range_geodesicLine`) is the `g`-image of the axis, and the three are pairwise disjoint and
cover `ℍ` (`rightHalfPlane_union_range_geodesicLine_union_leftHalfPlane`).

Only the *unordered* pair of sides is determined by `geodesicLine g`: which one is called
`right` depends on the chosen representing `g`, not on the line's image alone. `swapMatrix`,
the determinant-`1` matrix representing `z ↦ -1/z`, witnesses this: for `g' = g * swapMatrix`,
`Set.range (geodesicLine g') = Set.range (geodesicLine g)` (`range_geodesicLine_mul_swapMatrix`)
but `rightHalfPlane g' = leftHalfPlane g` (`rightHalfPlane_mul_swapMatrix`) — `z ↦ -1/z` fixes
`{z | z.re = 0}` setwise and sends `1 + i` to `-1/2 + i/2`.

## Main declarations

* `TauCeti.UpperHalfPlane.rightHalfPlane g`, `TauCeti.UpperHalfPlane.leftHalfPlane g` — the two
  open half-planes bounded by `geodesicLine g`, as `g`-translates of the canonical pair for the
  raw imaginary axis; `rightHalfPlane_def`/`leftHalfPlane_def` restate the body.
  `mem_rightHalfPlane_iff` and `mem_leftHalfPlane_iff` test membership directly, without
  unfolding the translate;
  `rightHalfPlane_one`/`leftHalfPlane_one` and `smul_rightHalfPlane`/`smul_leftHalfPlane` give
  their value at `g = 1` and their equivariance, matching `Geodesic.lean`'s own API for the line.
* `TauCeti.UpperHalfPlane.isOpen_rightHalfPlane`, `isOpen_leftHalfPlane` — both are open.
* `TauCeti.UpperHalfPlane.disjoint_rightHalfPlane_leftHalfPlane`,
  `disjoint_rightHalfPlane_range_geodesicLine`, `disjoint_leftHalfPlane_range_geodesicLine` — the
  three pieces are pairwise disjoint, and
  `TauCeti.UpperHalfPlane.rightHalfPlane_union_range_geodesicLine_union_leftHalfPlane` says
  they cover `ℍ`.
* `TauCeti.UpperHalfPlane.frontier_rightHalfPlane`, `frontier_leftHalfPlane` — the geodesic line
  is the topological boundary of each half-plane it bounds, via `closure_rightHalfPlane` and
  `closure_leftHalfPlane`.
* `TauCeti.UpperHalfPlane.swapMatrix` — the matrix of `z ↦ -1/z`, witnessing that `rightHalfPlane`
  and `leftHalfPlane` depend on the chosen representative of a geodesic line, not just its image:
  `rightHalfPlane_mul_swapMatrix`, `leftHalfPlane_mul_swapMatrix`, and
  `range_geodesicLine_mul_swapMatrix`.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- The right half-plane bounded by `geodesicLine g`: the `g`-translate of the points with
positive real part. -/
def rightHalfPlane (g : PSL(2, ℝ)) : Set ℍ := g • {z : ℍ | 0 < z.re}

/-- The left half-plane bounded by `geodesicLine g`: the `g`-translate of the points with
negative real part. -/
def leftHalfPlane (g : PSL(2, ℝ)) : Set ℍ := g • {z : ℍ | z.re < 0}

/-- Restatement of the body of `rightHalfPlane`, unfolded from the `def`. -/
theorem rightHalfPlane_def (g : PSL(2, ℝ)) :
    rightHalfPlane g = g • {z : ℍ | 0 < z.re} := by rfl

/-- Restatement of the body of `leftHalfPlane`, unfolded from the `def`. -/
theorem leftHalfPlane_def (g : PSL(2, ℝ)) : leftHalfPlane g = g • {z : ℍ | z.re < 0} := by rfl

/-- Membership test for the right half-plane, without unfolding the smul-image. -/
@[simp]
theorem mem_rightHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ rightHalfPlane g ↔ 0 < (g⁻¹ • z : ℍ).re := by
  rw [rightHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq]

/-- Membership test for the left half-plane, without unfolding the smul-image. -/
@[simp]
theorem mem_leftHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ leftHalfPlane g ↔ (g⁻¹ • z : ℍ).re < 0 := by
  rw [leftHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq]

/-- The right half-plane of the identity is the canonical `{z | 0 < z.re}`. -/
@[simp]
theorem rightHalfPlane_one : rightHalfPlane (1 : PSL(2, ℝ)) = {z : ℍ | 0 < z.re} := one_smul _ _

/-- The left half-plane of the identity is the canonical `{z | z.re < 0}`. -/
@[simp]
theorem leftHalfPlane_one : leftHalfPlane (1 : PSL(2, ℝ)) = {z : ℍ | z.re < 0} := one_smul _ _

/-- Translating a right half-plane by `h` gives the right half-plane of `h * g`. -/
@[simp]
theorem smul_rightHalfPlane (h g : PSL(2, ℝ)) :
    h • rightHalfPlane g = rightHalfPlane (h * g) := by
  rw [rightHalfPlane, rightHalfPlane, smul_smul]

/-- Translating a left half-plane by `h` gives the left half-plane of `h * g`. -/
@[simp]
theorem smul_leftHalfPlane (h g : PSL(2, ℝ)) :
    h • leftHalfPlane g = leftHalfPlane (h * g) := by
  rw [leftHalfPlane, leftHalfPlane, smul_smul]

/-- The right half-plane bounded by `geodesicLine g` is open. -/
theorem isOpen_rightHalfPlane (g : PSL(2, ℝ)) : IsOpen (rightHalfPlane g) :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_re).smul g

/-- The left half-plane bounded by `geodesicLine g` is open. -/
theorem isOpen_leftHalfPlane (g : PSL(2, ℝ)) : IsOpen (leftHalfPlane g) :=
  (isOpen_lt UpperHalfPlane.continuous_re continuous_const).smul g

/-- The right and left half-planes bounded by the same `geodesicLine g` are disjoint. -/
theorem disjoint_rightHalfPlane_leftHalfPlane (g : PSL(2, ℝ)) :
    Disjoint (rightHalfPlane g) (leftHalfPlane g) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_rightHalfPlane_iff] at hz
  rw [mem_leftHalfPlane_iff] at hz'
  linarith

/-- The right half-plane bounded by `geodesicLine g` is disjoint from the line itself. -/
theorem disjoint_rightHalfPlane_range_geodesicLine (g : PSL(2, ℝ)) :
    Disjoint (rightHalfPlane g) (Set.range (geodesicLine g)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_rightHalfPlane_iff] at hz
  rw [mem_range_geodesicLine_iff] at hz'
  linarith

/-- The left half-plane bounded by `geodesicLine g` is disjoint from the line itself. -/
theorem disjoint_leftHalfPlane_range_geodesicLine (g : PSL(2, ℝ)) :
    Disjoint (leftHalfPlane g) (Set.range (geodesicLine g)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_leftHalfPlane_iff] at hz
  rw [mem_range_geodesicLine_iff] at hz'
  linarith

/-- The right half-plane, the geodesic line, and the left half-plane, all bounded by
`geodesicLine g`, cover `ℍ`. With the three `disjoint_*` lemmas above, every point lies in
exactly one of the three. -/
theorem rightHalfPlane_union_range_geodesicLine_union_leftHalfPlane (g : PSL(2, ℝ)) :
    rightHalfPlane g ∪ Set.range (geodesicLine g) ∪ leftHalfPlane g = Set.univ := by
  have : ({z : ℍ | 0 < z.re} ∪ {z : ℍ | z.re = 0} ∪ {z : ℍ | z.re < 0}) = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rcases lt_trichotomy z.re 0 with h | h | h
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
  rw [rightHalfPlane, leftHalfPlane, range_geodesicLine, ← Set.smul_set_union,
    ← Set.smul_set_union, this, Set.smul_set_univ]

/-- The closure of the right half-plane adds exactly the geodesic line, its boundary. -/
@[simp]
theorem closure_rightHalfPlane (g : PSL(2, ℝ)) :
    closure (rightHalfPlane g) = rightHalfPlane g ∪ Set.range (geodesicLine g) := by
  rw [rightHalfPlane, closure_smul, closure_setOfPred_lt_re, range_geodesicLine,
    ← Set.smul_set_union]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_union, le_iff_lt_or_eq, eq_comm]

/-- The closure of the left half-plane adds exactly the geodesic line, its boundary. -/
@[simp]
theorem closure_leftHalfPlane (g : PSL(2, ℝ)) :
    closure (leftHalfPlane g) = leftHalfPlane g ∪ Set.range (geodesicLine g) := by
  rw [leftHalfPlane, closure_smul, closure_setOfPred_re_lt, range_geodesicLine,
    ← Set.smul_set_union]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_union, le_iff_lt_or_eq]

/-- The geodesic line is the boundary of the right half-plane it bounds. -/
@[simp]
theorem frontier_rightHalfPlane (g : PSL(2, ℝ)) :
    frontier (rightHalfPlane g) = Set.range (geodesicLine g) := by
  rw [frontier, (isOpen_rightHalfPlane g).interior_eq, closure_rightHalfPlane,
    Set.union_sdiff_left]
  exact sdiff_eq_self_iff_disjoint.mpr (disjoint_rightHalfPlane_range_geodesicLine g)

/-- The geodesic line is the boundary of the left half-plane it bounds. -/
@[simp]
theorem frontier_leftHalfPlane (g : PSL(2, ℝ)) :
    frontier (leftHalfPlane g) = Set.range (geodesicLine g) := by
  rw [frontier, (isOpen_leftHalfPlane g).interior_eq, closure_leftHalfPlane,
    Set.union_sdiff_left]
  exact sdiff_eq_self_iff_disjoint.mpr (disjoint_leftHalfPlane_range_geodesicLine g)

/-! ### `swapMatrix`: the non-canonicity witness

The representing matrix of `z ↦ -1/z`. Multiplying any representative `g` by it fixes the
geodesic line's image but swaps which half-plane is called `right`, so the labelling is a choice
of representative, not an invariant of the line. -/

/-- The determinant-`1` matrix `!![0, -1; 1, 0]` representing the Möbius map `z ↦ -1/z`. -/
def swapMatrixSL : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

/-- The `PSL(2, ℝ)` class of `swapMatrixSL`. -/
def swapMatrix : PSL(2, ℝ) := (swapMatrixSL : PSL(2, ℝ))

/-- `swapMatrix` acts as `z ↦ -1/z`. -/
theorem swapMatrix_smul (z : ℍ) :
    swapMatrix • z = UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos := by
  change (swapMatrixSL : PSL(2, ℝ)) • z = _
  rw [pslMk_smul, specialLinearGroup_apply]
  simp [swapMatrixSL, neg_div, inv_neg]

/-- `z ↦ -1/z` is an involution. -/
theorem swapMatrix_smul_swapMatrix_smul (z : ℍ) : swapMatrix • swapMatrix • z = z := by
  rw [swapMatrix_smul, swapMatrix_smul]
  ext
  push_cast
  rw [neg_inv, neg_neg, inv_inv]

/-- `swapMatrix` is its own inverse, by faithfulness of the `PSL(2, ℝ)`-action together with
`swapMatrix_smul_swapMatrix_smul`. -/
theorem swapMatrix_mul_self : swapMatrix * swapMatrix = 1 :=
  eq_of_smul_eq_smul fun z : ℍ ↦ by
    rw [mul_smul, swapMatrix_smul_swapMatrix_smul, one_smul]

/-- The real part after applying `swapMatrix` is the negated, rescaled real part. -/
theorem re_swapMatrix_smul (z : ℍ) :
    (swapMatrix • z : ℍ).re = -z.re / Complex.normSq (z : ℂ) := by
  rw [swapMatrix_smul]
  change ((-z : ℂ)⁻¹).re = _
  rw [Complex.inv_re, Complex.normSq_neg, Complex.neg_re, UpperHalfPlane.coe_re, div_eq_mul_inv]

/-- Multiplying by `swapMatrix` swaps the right and left half-planes: which side is called
`right` depends on the chosen representative of the geodesic line, not on the line's image
alone (see `range_geodesicLine_mul_swapMatrix`). -/
theorem rightHalfPlane_mul_swapMatrix (g : PSL(2, ℝ)) :
    rightHalfPlane (g * swapMatrix) = leftHalfPlane g := by
  ext z
  have hinv : swapMatrix⁻¹ = swapMatrix := inv_eq_of_mul_eq_one_right swapMatrix_mul_self
  rw [mem_rightHalfPlane_iff, mem_leftHalfPlane_iff, mul_inv_rev, hinv, mul_smul,
    re_swapMatrix_smul, div_pos_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, hpos⟩)
    · linarith
    · exact absurd (UpperHalfPlane.normSq_pos _) (by linarith)
  · intro h
    exact Or.inl ⟨by linarith, UpperHalfPlane.normSq_pos _⟩

/-- The dual of `rightHalfPlane_mul_swapMatrix`: multiplying by `swapMatrix` swaps the left half
into the right half. -/
theorem leftHalfPlane_mul_swapMatrix (g : PSL(2, ℝ)) :
    leftHalfPlane (g * swapMatrix) = rightHalfPlane g := by
  ext z
  have hinv : swapMatrix⁻¹ = swapMatrix := inv_eq_of_mul_eq_one_right swapMatrix_mul_self
  rw [mem_leftHalfPlane_iff, mem_rightHalfPlane_iff, mul_inv_rev, hinv, mul_smul,
    re_swapMatrix_smul, div_neg_iff]
  constructor
  · rintro (⟨h, hpos⟩ | ⟨h, -⟩)
    · exact absurd (UpperHalfPlane.normSq_pos (g⁻¹ • z)) (by linarith)
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, UpperHalfPlane.normSq_pos _⟩

/-- Unlike the half-planes, the geodesic line's image is unaffected by multiplying by
`swapMatrix`: only which side is called `right` depends on the representative. -/
theorem range_geodesicLine_mul_swapMatrix (g : PSL(2, ℝ)) :
    Set.range (geodesicLine (g * swapMatrix)) = Set.range (geodesicLine g) := by
  ext z
  have hinv : swapMatrix⁻¹ = swapMatrix := inv_eq_of_mul_eq_one_right swapMatrix_mul_self
  rw [mem_range_geodesicLine_iff, mem_range_geodesicLine_iff, mul_inv_rev, hinv, mul_smul,
    re_swapMatrix_smul, div_eq_zero_iff]
  simp [(UpperHalfPlane.normSq_pos (g⁻¹ • z)).ne']

end TauCeti.UpperHalfPlane
