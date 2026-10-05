/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# Half-planes bounded by a geodesic line

The imaginary axis splits `ℍ` into two open half-planes, `{z | 0 < z.re}` and
`{z | z.re < 0}`, and the axis itself, `{z | z.re = 0}`. This file transports that picture by
`g : PSL(2, ℝ)`, the same idiom `Geodesic.lean` uses for the line itself: `rightHalfPlane g`
and `leftHalfPlane g` are the `g`-images of the two canonical sides, `Set.range (geodesicLine g)`
(via `range_geodesicLine`) is the `g`-image of the axis, and the three are pairwise disjoint and
cover `ℍ` (`rightHalfPlane_union_range_geodesicLine_union_leftHalfPlane`).

The labelling is not determined by `geodesicLine g` alone: which side is called `right` depends
on the chosen representing `g`, and the two sides are genuinely distinct
(`rightHalfPlane_ne_leftHalfPlane`). `pslS`, the element of `PSL(2, ℝ)` representing `z ↦ -1/z`,
witnesses this non-canonicity: for `g' = g * pslS`,
`Set.range (geodesicLine g') = Set.range (geodesicLine g)` (`range_geodesicLine_mul_pslS`)
but `rightHalfPlane g' = leftHalfPlane g` (`rightHalfPlane_mul_pslS`) — `z ↦ -1/z` fixes
`{z | z.re = 0}` setwise and sends `1 + i` to `-1/2 + i/2`. That every pair of representatives
with the same line image gives the same *unordered* pair of sides is not proved here.

The sides also have an equation. For a representative `!![a, b; c, d]` of `g`, the real part of
`g⁻¹ • z` is a positive multiple of `sideForm g z = -(c d) |z|² + (a d + b c) Re z - a b`
(`exists_pos_re_inv_smul_eq`), a quantity unchanged by negating the representative. Hence the
left half-plane of `g` is `{sideForm g < 0}`, the geodesic line is `{sideForm g = 0}` and the
right half-plane is `{sideForm g > 0}`.

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
* `TauCeti.UpperHalfPlane.rightHalfPlane_nonempty`, `leftHalfPlane_nonempty`, and
  `rightHalfPlane_ne_leftHalfPlane` — the two half-planes are nonempty and genuinely distinct.
* `TauCeti.UpperHalfPlane.frontier_rightHalfPlane`, `frontier_leftHalfPlane` — the geodesic line
  is the topological boundary of each half-plane it bounds, via `closure_rightHalfPlane` and
  `closure_leftHalfPlane`; `mem_closure_rightHalfPlane_iff`/`mem_closure_leftHalfPlane_iff` test
  membership in the closed half-planes directly.
* `TauCeti.UpperHalfPlane.rightHalfPlane_mul_pslS`, `leftHalfPlane_mul_pslS` — witness that
  `rightHalfPlane`/`leftHalfPlane` depend on the chosen representative of a geodesic line, not
  just its image (`TauCeti.pslS` is the `PSL(2, ℝ)` element of `z ↦ -1/z`;
  `Geodesic.lean`'s `range_geodesicLine_mul_pslS` is the companion fact for the line itself).
* `TauCeti.UpperHalfPlane.rightHalfPlane_mul_dilation`, `leftHalfPlane_mul_dilation` — by
  contrast, reparametrising a geodesic line by a dilation (`geodesicLine_mul_dilation`) changes
  neither half-plane.
* `TauCeti.UpperHalfPlane.sideForm g`: the real quadratic form whose sign is the side of
  `geodesicLine g`, with `sideForm_mk` and `sideForm_mk_ofReal` in the entries of a
  representative; `mem_leftHalfPlane_iff_sideForm_neg`, `mem_rightHalfPlane_iff_sideForm_pos`,
  `mem_range_geodesicLine_iff_sideForm_eq_zero`, `mem_closure_leftHalfPlane_iff_sideForm_nonpos`;
  `sideForm_mul_dilation`: it too is unchanged by a dilation;
  `exists_sideForm_eq_mul_normSq_sub`: a side form vanishing at two points of a circle centred on
  the real axis, with distinct real parts, is a multiple of the circle's equation.
-/

public section

noncomputable section

open UpperHalfPlane
open Matrix.ProjectiveSpecialLinearGroup (upperRightHom)
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

/-- The right half-plane of the translation by `x` is `{x < re}`. -/
theorem mem_rightHalfPlane_upperRightHom_iff (x : ℝ) (z : ℍ) :
    z ∈ rightHalfPlane (upperRightHom x) ↔ x < z.re := by
  rw [mem_rightHalfPlane_iff, ← AddChar.map_neg_eq_inv, upperRightHom_smul, vadd_re,
    neg_add_eq_sub, sub_pos]

/-- The left half-plane of the translation by `x` is `{re < x}`. -/
theorem mem_leftHalfPlane_upperRightHom_iff (x : ℝ) (z : ℍ) :
    z ∈ leftHalfPlane (upperRightHom x) ↔ z.re < x := by
  rw [mem_leftHalfPlane_iff, ← AddChar.map_neg_eq_inv, upperRightHom_smul, vadd_re,
    neg_add_eq_sub, sub_neg]

-- Not `@[simp]`, like `range_geodesicLine_one`: it would strip `rightHalfPlane` before the
-- `smul`/`closure`/`frontier` simp lemmas about it could fire.
/-- The right half-plane of the identity is the canonical `{z | 0 < z.re}`. -/
theorem rightHalfPlane_one : rightHalfPlane (1 : PSL(2, ℝ)) = {z : ℍ | 0 < z.re} := one_smul _ _

-- Not `@[simp]`, for the same reason as `rightHalfPlane_one`.
/-- The left half-plane of the identity is the canonical `{z | z.re < 0}`. -/
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

/-- The right half-plane is nonempty. -/
theorem rightHalfPlane_nonempty (g : PSL(2, ℝ)) : (rightHalfPlane g).Nonempty :=
  ⟨g • UpperHalfPlane.mk ⟨1, 1⟩ one_pos, by simp⟩

/-- The left half-plane is nonempty. -/
theorem leftHalfPlane_nonempty (g : PSL(2, ℝ)) : (leftHalfPlane g).Nonempty :=
  ⟨g • UpperHalfPlane.mk ⟨-1, 1⟩ one_pos, by simp⟩

/-- The right and left half-planes bounded by the same `geodesicLine g` are genuinely distinct
sets, not merely disjoint. -/
theorem rightHalfPlane_ne_leftHalfPlane (g : PSL(2, ℝ)) : rightHalfPlane g ≠ leftHalfPlane g :=
  (disjoint_rightHalfPlane_leftHalfPlane g).ne (rightHalfPlane_nonempty g).ne_empty

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

-- Not `@[simp]`: `closure_rightHalfPlane` already rewrites `closure (rightHalfPlane g)` first.
/-- A point `z` lies in the closed right half-plane of `g` iff `0 ≤ (g⁻¹ • z).re`. -/
theorem mem_closure_rightHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ closure (rightHalfPlane g) ↔ 0 ≤ (g⁻¹ • z : ℍ).re := by
  simp only [closure_rightHalfPlane, Set.mem_union, mem_rightHalfPlane_iff,
    mem_range_geodesicLine_iff, le_iff_lt_or_eq, eq_comm]

-- Not `@[simp]`, for the same reason as `mem_closure_rightHalfPlane_iff`.
/-- A point `z` lies in the closed left half-plane of `g` iff `(g⁻¹ • z).re ≤ 0`. -/
theorem mem_closure_leftHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ closure (leftHalfPlane g) ↔ (g⁻¹ • z : ℍ).re ≤ 0 := by
  simp only [closure_leftHalfPlane, Set.mem_union, mem_leftHalfPlane_iff,
    mem_range_geodesicLine_iff, le_iff_lt_or_eq]

/-- The geodesic line is the boundary of the right half-plane it bounds. -/
@[simp]
theorem frontier_rightHalfPlane (g : PSL(2, ℝ)) :
    frontier (rightHalfPlane g) = Set.range (geodesicLine g) := by
  rw [(isOpen_rightHalfPlane g).frontier_eq, closure_rightHalfPlane, Set.union_sdiff_left]
  exact sdiff_eq_self_iff_disjoint.mpr (disjoint_rightHalfPlane_range_geodesicLine g)

/-- The geodesic line is the boundary of the left half-plane it bounds. -/
@[simp]
theorem frontier_leftHalfPlane (g : PSL(2, ℝ)) :
    frontier (leftHalfPlane g) = Set.range (geodesicLine g) := by
  rw [(isOpen_leftHalfPlane g).frontier_eq, closure_leftHalfPlane, Set.union_sdiff_left]
  exact sdiff_eq_self_iff_disjoint.mpr (disjoint_leftHalfPlane_range_geodesicLine g)

/-! ### The non-canonicity witness

`pslS` is the `PSL(2, ℝ)` element of `z ↦ -1/z`. Multiplying any
representative `g` by it fixes the geodesic line's image (`range_geodesicLine_mul_pslS` in
`Geodesic.lean`) but swaps which half-plane is called `right`, so the labelling is a choice of
representative, not an invariant of the line. -/

/-- Multiplying by `pslS` swaps the right half-plane into the left one, although the geodesic
line's image is unchanged (`range_geodesicLine_mul_pslS`). -/
@[simp]
theorem rightHalfPlane_mul_pslS (g : PSL(2, ℝ)) :
    rightHalfPlane (g * pslS) = leftHalfPlane g := by
  ext z
  rw [mem_rightHalfPlane_iff, mem_leftHalfPlane_iff, re_mul_pslS_inv_smul,
    div_pos_iff_of_pos_right (UpperHalfPlane.normSq_pos _), neg_pos]

/-- Multiplying by `pslS` swaps the left half-plane into the right one. -/
@[simp]
theorem leftHalfPlane_mul_pslS (g : PSL(2, ℝ)) :
    leftHalfPlane (g * pslS) = rightHalfPlane g := by
  rw [← rightHalfPlane_mul_pslS (g * pslS), mul_assoc, pslS_mul_self, mul_one]

/-! ### Reparametrisation by dilations -/

section Dilation

open Matrix.SpecialLinearGroup (dilation)

/-- Reparametrising a geodesic line by a dilation does not change its right half-plane. -/
@[simp]
theorem rightHalfPlane_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    rightHalfPlane (g * ↑(dilation s)) = rightHalfPlane g := by
  ext z
  rw [mem_rightHalfPlane_iff, mem_rightHalfPlane_iff, mul_inv_rev, mul_smul,
    ← QuotientGroup.mk_inv, Matrix.SpecialLinearGroup.dilation_inv, UpperHalfPlane.pslMk_smul,
    ← UpperHalfPlane.coe_re, coe_dilation_smul, Complex.re_ofReal_mul, UpperHalfPlane.coe_re]
  exact mul_pos_iff_of_pos_left (Real.exp_pos _)

/-- Reparametrising a geodesic line by a dilation does not change its left half-plane. -/
@[simp]
theorem leftHalfPlane_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    leftHalfPlane (g * ↑(dilation s)) = leftHalfPlane g := by
  ext z
  rw [mem_leftHalfPlane_iff, mem_leftHalfPlane_iff, mul_inv_rev, mul_smul,
    ← QuotientGroup.mk_inv, Matrix.SpecialLinearGroup.dilation_inv, UpperHalfPlane.pslMk_smul,
    ← UpperHalfPlane.coe_re, coe_dilation_smul, Complex.re_ofReal_mul, UpperHalfPlane.coe_re]
  exact ⟨fun h ↦ neg_of_mul_neg_right h (Real.exp_pos _).le,
    fun h ↦ mul_neg_of_pos_of_neg (Real.exp_pos _) h⟩

end Dilation

/-! ### The side form -/

section SideForm

open Matrix.SpecialLinearGroup (dilation)

/-- The real quadratic form `-(c d) |z|² + (a d + b c) Re z - a b` of a representative
`!![a, b; c, d]` of `g`, which does not depend on the representative. Its sign on `ℍ` is the side
of `geodesicLine g` (`mem_leftHalfPlane_iff_sideForm_neg`). -/
def sideForm (g : PSL(2, ℝ)) (z : ℂ) : ℝ :=
  Quotient.liftOn' g (fun A : SL(2, ℝ) ↦ -(A 1 0 * A 1 1) * Complex.normSq z +
      (A 0 0 * A 1 1 + A 0 1 * A 1 0) * z.re - A 0 0 * A 0 1) fun A B hAB ↦ by
    rw [QuotientGroup.leftRel_apply,
      Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hAB
    rcases hAB with h | h
    · rw [inv_mul_eq_one.mp h]
    · rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at h
      subst h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      ring

/-- The side form of the class of a matrix, as a formula in its entries. -/
theorem sideForm_mk (A : SL(2, ℝ)) (z : ℂ) :
    sideForm (A : PSL(2, ℝ)) z = -(A 1 0 * A 1 1) * Complex.normSq z +
      (A 0 0 * A 1 1 + A 0 1 * A 1 0) * z.re - A 0 0 * A 0 1 :=
  (rfl)

/-- At a real point the side form factors as `(d x - b) (a - c x)`. -/
theorem sideForm_mk_ofReal (A : SL(2, ℝ)) (x : ℝ) :
    sideForm (A : PSL(2, ℝ)) x = (A 1 1 * x - A 0 1) * (-A 1 0 * x + A 0 0) := by
  rw [sideForm_mk, Complex.normSq_ofReal, Complex.ofReal_re]
  ring

/-- The real part of `g⁻¹ • z` is a positive multiple of the side form at `z`. -/
theorem exists_pos_re_inv_smul_eq (g : PSL(2, ℝ)) (z : ℍ) :
    ∃ κ : ℝ, 0 < κ ∧ (g⁻¹ • z : ℍ).re = κ * sideForm g z := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [← QuotientGroup.mk_inv, UpperHalfPlane.pslMk_smul, UpperHalfPlane.re,
    UpperHalfPlane.coe_specialLinearGroup_apply, Matrix.SpecialLinearGroup.SL2_inv_expl,
    sideForm_mk]
  have hne : -(A 1 0 : ℂ) * z + A 0 0 ≠ 0 := by
    convert UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A⁻¹) z using 1
    simp [denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.inv_def,
      Matrix.adjugate_fin_two]
  refine ⟨(Complex.normSq (-(A 1 0 : ℂ) * z + A 0 0))⁻¹,
    inv_pos.2 (Complex.normSq_pos.2 hne), ?_⟩
  simp [Complex.div_re, Complex.normSq_apply]
  ring

/-- The left half-plane of `geodesicLine g` is where the side form is negative. -/
theorem mem_leftHalfPlane_iff_sideForm_neg (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ leftHalfPlane g ↔ sideForm g z < 0 := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_smul_eq g z
  rw [mem_leftHalfPlane_iff, h]
  exact ⟨fun h' ↦ neg_of_mul_neg_right h' hκ.le, mul_neg_of_pos_of_neg hκ⟩

/-- The right half-plane of `geodesicLine g` is where the side form is positive. -/
theorem mem_rightHalfPlane_iff_sideForm_pos (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ rightHalfPlane g ↔ 0 < sideForm g z := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_smul_eq g z
  rw [mem_rightHalfPlane_iff, h, mul_pos_iff_of_pos_left hκ]

/-- The geodesic line of `g` is the zero set of the side form in `ℍ`. -/
theorem mem_range_geodesicLine_iff_sideForm_eq_zero (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ Set.range (geodesicLine g) ↔ sideForm g z = 0 := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_smul_eq g z
  rw [mem_range_geodesicLine_iff, h, mul_eq_zero, or_iff_right hκ.ne']

/-- The closed left half-plane of `geodesicLine g` is where the side form is nonpositive. -/
theorem mem_closure_leftHalfPlane_iff_sideForm_nonpos (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ closure (leftHalfPlane g) ↔ sideForm g z ≤ 0 := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_smul_eq g z
  rw [mem_closure_leftHalfPlane_iff, h]
  exact ⟨fun h' ↦ le_of_mul_le_mul_left (by rwa [mul_zero]) hκ,
    mul_nonpos_of_nonneg_of_nonpos hκ.le⟩

/-- Reparametrising a geodesic line by a dilation does not change its side form. -/
@[simp]
theorem sideForm_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    sideForm (g * ↑(dilation s)) = sideForm g := by
  funext z
  induction g using QuotientGroup.induction_on with | H A => ?_
  have h : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [← QuotientGroup.mk_mul, sideForm_mk, sideForm_mk]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_dilation,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, add_zero, zero_add]
  linear_combination (-(A 1 0 * A 1 1) * Complex.normSq z +
      (A 0 0 * A 1 1 + A 0 1 * A 1 0) * z.re - A 0 0 * A 0 1) * h

/-- A side form vanishing at two points of a circle centred on the real axis, with distinct real
parts, is a nonzero multiple of the equation of that circle. -/
theorem exists_sideForm_eq_mul_normSq_sub {g : PSL(2, ℝ)} {z₁ z₂ : ℂ} {m r : ℝ}
    (h₁ : sideForm g z₁ = 0) (h₂ : sideForm g z₂ = 0) (hz₁ : Complex.normSq (z₁ - m) = r)
    (hz₂ : Complex.normSq (z₂ - m) = r) (hre : z₁.re ≠ z₂.re) :
    ∃ α : ℝ, α ≠ 0 ∧ ∀ z : ℂ, sideForm g z = α * (Complex.normSq (z - m) - r) := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  have hn (z : ℂ) : Complex.normSq (z - m) = Complex.normSq z - 2 * m * z.re + m ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero]
    ring
  rw [sideForm_mk] at h₁ h₂
  rw [hn] at hz₁ hz₂
  -- the coefficients of `Re z` and `1` are those of the circle's equation
  have hb : A 0 0 * A 1 1 + A 0 1 * A 1 0 = 2 * m * (A 1 0 * A 1 1) := by
    have h : (A 0 0 * A 1 1 + A 0 1 * A 1 0 - 2 * m * (A 1 0 * A 1 1)) * (z₁.re - z₂.re) = 0 := by
      linear_combination h₁ - h₂ + A 1 0 * A 1 1 * (hz₁ - hz₂)
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hre))
  have hc : A 0 0 * A 0 1 = -(A 1 0 * A 1 1) * (r - m ^ 2) := by
    linear_combination -h₁ + z₁.re * hb - A 1 0 * A 1 1 * hz₁
  refine ⟨-(A 1 0 * A 1 1), fun h0 ↦ ?_, fun z ↦ ?_⟩
  · -- otherwise the side form vanishes identically, but the left half-plane is nonempty
    obtain ⟨w, hw⟩ := leftHalfPlane_nonempty (A : PSL(2, ℝ))
    rw [mem_leftHalfPlane_iff_sideForm_neg, sideForm_mk, hb, hc, neg_eq_zero.1 h0] at hw
    simp at hw
  · rw [sideForm_mk, hn, hb, hc]
    ring

end SideForm

end TauCeti.UpperHalfPlane
