/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Pair
public import TauCeti.GroupTheory.GroupAction.Orbit.IntUnits
import TauCeti.Data.Int.Round

/-!
# The coordinate pair and the projective `x`-coordinate of a Montgomery point

A native point of the monic Montgomery model `TauCeti.Montgomery.model A B`, the Weierstrass
curve `y'² = x'³ + A B x'² + B² x'`, comes from the point `(x, y) = (x' / B, y' / B²)` of the
Montgomery curve `B y² = x³ + A x² + x`. Montgomery's `x`-only arithmetic tracks the Montgomery
coordinate `x = x' / B` as a raw pair, so the **coordinate pair** of a native point is `(1, 0)`
at infinity and `(x', B)` at an affine point `(x', y')`. It is Mathlib's
`WeierstrassCurve.Affine.Point.xRep`, which represents the Weierstrass coordinate `x'`, with its
second entry scaled by `B`.

For `B ≠ 0` the coordinate pair is never `(0, 0)`; its second field vanishes exactly at infinity
and its first field exactly at the distinguished point of order two `(0, 0)`. It is invariant
under negation. Over a field, the coordinate pair defines the **projective `x`-coordinate**, a
point of `ℙ K (Fin 2 → K)`, and two native points have the same projective `x`-coordinate, or
equivalently coordinate pairs with vanishing cross difference, exactly when they are equal or
negatives of each other. This is what makes `x`-only arithmetic well defined on the native
point group up to sign.

Applied to scalar multiples of one point `Q`, this gives the cross-difference criterion behind
the second stage of the elliptic-curve factorization method: the coordinate pairs of `[m] Q` and
`[n] Q` have vanishing cross difference exactly when `[m - n] Q = 0` or `[m + n] Q = 0`. So if
`[q] Q = 0`, writing `q = i w ± j` with `0 ≤ j` and `2 j ≤ w` for a fixed step `w > 0` (see
`Int.exists_two_mul_abs_sub_mul_le`) makes the cross difference of the coordinate pairs of
`[i w] Q` and `[j] Q` vanish.

Since negation is the only identification it makes, the projective `x`-coordinate identifies
the quotient of the native point group by negation, the orbit quotient of the sign action of
`ℤˣ`, with its image. That image need not be the whole projective line: when `model A B` is
elliptic (`2 ≠ 0`, `B ≠ 0` and `A² ≠ 4`, so every solution is nonsingular), `(r : 1)` comes from
a `K`-rational point exactly when `(r³ + A r² + r) / B` is a square in `K`.

## Main definitions

* `TauCeti.Montgomery.coordinates A B P`: the coordinate pair of a native point `P` of
  `model A B`.
* `TauCeti.Montgomery.projectiveX A hB P`: the projective `x`-coordinate of `P` over a field,
  for `hB : B ≠ 0`.
* `TauCeti.Montgomery.orbitRelQuotientEquivRangeProjectiveX`: the identification of the
  quotient of the native point group by negation with the image of the projective
  `x`-coordinate.

## Main results

* `TauCeti.Montgomery.coordinates_ne_zero`: for `B ≠ 0` the coordinate pair is nonzero.
* `TauCeti.Montgomery.coordinates_z_eq_zero_iff` and
  `TauCeti.Montgomery.coordinates_x_eq_zero_iff`: its fields vanish exactly at infinity and at
  the distinguished point of order two, respectively.
* `TauCeti.Montgomery.coordinates_neg`: the coordinate pair of `-P` is that of `P`.
* `TauCeti.Montgomery.cross_coordinates_eq_zero_iff`: over a domain, the coordinate pairs of `P`
  and `Q` have vanishing cross difference exactly when `P = Q` or `P = -Q`.
* `TauCeti.Montgomery.projectiveX_eq_projectiveX_iff`: the fibres of the projective
  `x`-coordinate are the sets `{P, -P}`;
  `TauCeti.Montgomery.projectiveX_eq_projectiveX_iff_orbitRel` says the same with the orbits of
  `ℤˣ`.
* `TauCeti.Montgomery.toProj_mem_range_projectiveX_iff`: for an elliptic model, `(r : 1)` lies in
  the image of the projective `x`-coordinate exactly when `(r³ + A r² + r) / B` is a square.
* `TauCeti.Montgomery.cross_coordinates_zsmul_eq_zero_iff`: the coordinate pairs of `[m] Q` and
  `[n] Q` have vanishing cross difference exactly when `[m - n] Q = 0` or `[m + n] Q = 0`.
* `TauCeti.Montgomery.exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero`: the stage-2
  criterion, for `[q] Q = 0` and a step `w > 0`.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1.
* P. Zimmermann, *20 years of ECM*, ANTS VII, Lecture Notes in Computer Science 4076 (2006),
  §1 (stage 2 of the method).
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve
open scoped LinearAlgebra.Projectivization

section CommRing

variable {R : Type*} [CommRing R]

/-- The **coordinate pair** of a native point of the monic Montgomery model `model A B`: `(1, 0)`
at infinity and `(x', B)` at the affine point `(x', y')`, which stands for the Montgomery
coordinate `x = x' / B`. It is Mathlib's `xRep` with its second entry scaled by `B`. -/
noncomputable def coordinates (A B : R) (P : (model A B).toAffine.Point) : Pair R :=
  ⟨P.xRep 0, B * P.xRep 1⟩

variable (A B : R)

/-- The coordinate pair of the point at infinity is `(1, 0)`. -/
@[simp]
theorem coordinates_zero : coordinates A B 0 = ⟨1, 0⟩ := by
  simp [coordinates]

/-- The coordinate pair of the affine point `(x', y')` is `(x', B)`. -/
@[simp]
theorem coordinates_some {x y : R} (h : (model A B).toAffine.Nonsingular x y) :
    coordinates A B (.some x y h) = ⟨x, B⟩ := by
  simp [coordinates]

/-- The coordinate pair is invariant under negation. -/
@[simp]
theorem coordinates_neg (P : (model A B).toAffine.Point) :
    coordinates A B (-P) = coordinates A B P := by
  simp [coordinates]

variable {A B}

/-- For `B ≠ 0`, the coordinate pair of a native point is nonzero. -/
@[simp]
theorem coordinates_ne_zero (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    coordinates A B P ≠ 0 := by
  have : Nontrivial R := nontrivial_of_ne B 0 hB
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def, Pair.eq_zero_iff]
  · simp [Pair.eq_zero_iff, hB]

/-- For `B ≠ 0`, the second field of the coordinate pair vanishes exactly at infinity. -/
@[simp]
theorem coordinates_z_eq_zero_iff (hB : B ≠ 0) {P : (model A B).toAffine.Point} :
    (coordinates A B P).z = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · simp [hB, Affine.Point.some_ne_zero]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {A B : R}

/-- The coordinate pair of the distinguished point of order two is `(0, B)`. -/
@[simp]
theorem coordinates_twoTorsionPoint (hB : B ≠ 0) :
    coordinates A B (twoTorsionPoint A hB) = ⟨0, B⟩ := by
  simp [twoTorsionPoint_def]

/-- For `B ≠ 0`, the first field of the coordinate pair vanishes exactly at the distinguished
point of order two `(0, 0)`. -/
@[simp]
theorem coordinates_x_eq_zero_iff (hB : B ≠ 0) {P : (model A B).toAffine.Point} :
    (coordinates A B P).x = 0 ↔ P = twoTorsionPoint A hB := by
  have : Nontrivial R := nontrivial_of_ne B 0 hB
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, coordinates_zero, one_ne_zero, false_iff]
    exact (twoTorsionPoint_ne_zero A hB).symm
  · rw [coordinates_some, some_eq_twoTorsionPoint_iff hB]

/-- **The coordinate pairs of two native points have vanishing cross difference exactly when the
points are equal or negatives of each other**, for `B ≠ 0` over a domain. This includes the case
where one of them is the point at infinity. -/
theorem cross_coordinates_eq_zero_iff (hB : B ≠ 0) {P Q : (model A B).toAffine.Point} :
    (coordinates A B P).cross (coordinates A B Q) = 0 ↔ P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · simp [← Affine.Point.zero_def]
  · simp [← Affine.Point.zero_def, Pair.cross_def, hB, (Affine.Point.some_ne_zero _).symm]
  · simp [← Affine.Point.zero_def, Pair.cross_def, hB, Affine.Point.some_ne_zero]
  · rw [coordinates_some, coordinates_some, Pair.cross_def, ← sub_mul, mul_eq_zero, sub_eq_zero,
      or_iff_left hB]
    refine ⟨fun hx ↦ ?_, by rintro (h | h) <;> simp_all [Affine.Point.neg_some]⟩
    subst hx
    have e₁ := (Affine.equation_iff ..).mp h₁.1
    have e₂ := (Affine.equation_iff ..).mp h₂.1
    simp_rw [Affine.Point.neg_some, Affine.Point.some.injEq, true_and, ← sub_eq_zero (a := y₁),
      ← mul_eq_zero, Affine.negY]
    linear_combination e₁ - e₂

end Domain

section Field

variable {K : Type*} [Field K] {A B : K}

/-- The coordinate pairs of multiples of the distinguished point of order two alternate
between infinity and that point. This includes characteristic two. -/
theorem coordinates_nsmul_twoTorsionPoint [DecidableEq K] (hB : B ≠ 0) (k : ℕ) :
    coordinates A B (k • twoTorsionPoint A hB) =
      if k % 2 = 0 then ⟨1, 0⟩ else ⟨0, B⟩ := by
  rw [← mod_addOrderOf_nsmul, addOrderOf_twoTorsionPoint]
  by_cases hk : k % 2 = 0
  · simp [hk]
  · have hk' : k % 2 = 1 := by omega
    simp [hk']

/-- The **projective `x`-coordinate** of a native point of `model A B` over a field, for
`B ≠ 0`: the point of the projective line `ℙ K (Fin 2 → K)` defined by its coordinate pair. It is
`(1 : 0)` at infinity and `(x' : B)` at the affine point `(x', y')`. -/
noncomputable def projectiveX (A : K) (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    ℙ K (Fin 2 → K) :=
  (coordinates A B P).toProj (coordinates_ne_zero hB P)

theorem projectiveX_def (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    projectiveX A hB P = (coordinates A B P).toProj (coordinates_ne_zero hB P) := (rfl)

/-- **The fibres of the projective `x`-coordinate.** Two native points have the same projective
`x`-coordinate exactly when they are equal or negatives of each other. -/
theorem projectiveX_eq_projectiveX_iff (hB : B ≠ 0) {P Q : (model A B).toAffine.Point} :
    projectiveX A hB P = projectiveX A hB Q ↔ P = Q ∨ P = -Q := by
  rw [projectiveX_def, projectiveX_def, Pair.toProj_eq_toProj_iff,
    cross_coordinates_eq_zero_iff hB]

/-- The projective `x`-coordinate is invariant under negation. -/
@[simp]
theorem projectiveX_neg (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    projectiveX A hB (-P) = projectiveX A hB P :=
  (projectiveX_eq_projectiveX_iff hB).mpr (.inr rfl)

/-- **The rational points of the projective line that lift to the curve.** For an elliptic
model, the point `(r : 1)` is the projective `x`-coordinate of a native point exactly when
`(r³ + A r² + r) / B` is a square in `K`; the point `(1 : 0)` is always that of infinity. -/
theorem toProj_mem_range_projectiveX_iff [(model A B).IsElliptic] (hB : B ≠ 0) (r : K) :
    Pair.toProj ⟨r, 1⟩ (Pair.ne_zero_iff.mpr (.inr one_ne_zero)) ∈ Set.range (projectiveX A hB) ↔
      IsSquare ((r ^ 3 + A * r ^ 2 + r) / B) := by
  constructor
  · rintro ⟨_ | ⟨x, y, h⟩, hP⟩
    · rw [projectiveX_def, Pair.toProj_eq_toProj_iff] at hP
      simp [← Affine.Point.zero_def, Pair.cross_def] at hP
    · rw [projectiveX_def, Pair.toProj_eq_toProj_iff, coordinates_some, Pair.cross_def] at hP
      obtain rfl : x = B * r := by linear_combination hP
      obtain ⟨t, rfl⟩ : ∃ t, y = B ^ 2 * t := ⟨y / B ^ 2, by field_simp⟩
      refine ⟨t, ?_⟩
      rw [← (equation_model_iff hB r t).mp h.1]
      field_simp
  · rintro ⟨t, ht⟩
    have he : (model A B).toAffine.Equation (B * r) (B ^ 2 * t) :=
      (equation_model_iff hB r t).mpr (by rw [div_eq_iff hB] at ht; linear_combination -ht)
    refine ⟨.some _ _ ((model A B).toAffine.equation_iff_nonsingular.mp he), ?_⟩
    rw [projectiveX_def, Pair.toProj_eq_toProj_iff, coordinates_some, Pair.cross_def]
    ring

variable [DecidableEq K]

/-- **The cross-difference criterion for scalar multiples.** For `B ≠ 0`, the coordinate pairs of
`[m] Q` and `[n] Q` have vanishing cross difference exactly when `[m - n] Q = 0` or
`[m + n] Q = 0`. -/
theorem cross_coordinates_zsmul_eq_zero_iff (hB : B ≠ 0) {Q : (model A B).toAffine.Point}
    {m n : ℤ} :
    (coordinates A B (m • Q)).cross (coordinates A B (n • Q)) = 0 ↔
      (m - n) • Q = 0 ∨ (m + n) • Q = 0 := by
  rw [cross_coordinates_eq_zero_iff hB, sub_zsmul, add_zsmul, add_neg_eq_zero,
    add_eq_zero_iff_eq_neg]

/-- If `[q] Q = 0` and `q = m + n` or `q = m - n`, then the coordinate pairs of `[m] Q` and
`[n] Q` have vanishing cross difference. -/
theorem cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero
    {Q : (model A B).toAffine.Point} {q : ℤ} (hq : q • Q = 0) {m n : ℤ}
    (h : q = m + n ∨ q = m - n) :
    (coordinates A B (m • Q)).cross (coordinates A B (n • Q)) = 0 := by
  rcases h with rfl | rfl
  · rw [add_zsmul] at hq
    rw [eq_neg_of_add_eq_zero_left hq, coordinates_neg, Pair.cross_self]
  · rw [sub_zsmul, add_neg_eq_zero] at hq
    rw [hq, Pair.cross_self]

/-- **The stage-2 cross-difference criterion.** Let `w > 0` and `[q] Q = 0`. Then there is an
integer `i` such that `j = |q - i w|` satisfies `2 j ≤ w`, so that `q = i w + j` or
`q = i w - j`, and the coordinate pairs of `[i w] Q` and `[j] Q` have vanishing cross
difference. -/
theorem exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero
    {Q : (model A B).toAffine.Point} {q : ℤ} (hq : q • Q = 0) {w : ℤ} (hw : 0 < w) :
    ∃ i : ℤ, 2 * |q - i * w| ≤ w ∧
      (coordinates A B ((i * w) • Q)).cross (coordinates A B (|q - i * w| • Q)) = 0 := by
  obtain ⟨i, hi⟩ := Int.exists_two_mul_abs_sub_mul_le q hw.ne'
  rw [abs_of_pos hw] at hi
  refine ⟨i, hi, cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero hq ?_⟩
  rcases abs_choice (q - i * w) with h | h <;> rw [h]
  exacts [.inl (by ring), .inr (by ring)]

/-- **The fibres of the projective `x`-coordinate are the orbits of `ℤˣ`**, the sign action of
`±1` on the native point group. -/
theorem projectiveX_eq_projectiveX_iff_orbitRel (hB : B ≠ 0)
    {P Q : (model A B).toAffine.Point} :
    projectiveX A hB P = projectiveX A hB Q ↔ MulAction.orbitRel ℤˣ _ P Q := by
  rw [projectiveX_eq_projectiveX_iff hB, MulAction.orbitRel_intUnits_iff]

/-- **The quotient of the native point group by negation is the image of the projective
`x`-coordinate**: `projectiveX` induces a bijection from the orbit quotient of the sign action of
`ℤˣ` onto its range. -/
noncomputable def orbitRelQuotientEquivRangeProjectiveX (hB : B ≠ 0) :
    MulAction.orbitRel.Quotient ℤˣ (model A B).toAffine.Point ≃ Set.range (projectiveX A hB) :=
  (Quotient.congrRight fun _ _ ↦ (projectiveX_eq_projectiveX_iff_orbitRel hB).symm).trans
    (Setoid.quotientKerEquivRange _)

/-- The identification of the quotient by negation with the image of the projective
`x`-coordinate sends the class of `P` to the projective `x`-coordinate of `P`. -/
@[simp]
theorem coe_orbitRelQuotientEquivRangeProjectiveX_mk (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) :
    (orbitRelQuotientEquivRangeProjectiveX hB (Quotient.mk _ P) : ℙ K (Fin 2 → K)) =
      projectiveX A hB P :=
  (rfl)

end Field

end TauCeti.Montgomery
