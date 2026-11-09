/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates

/-!
# Montgomery differential addition

Montgomery's `x`-only arithmetic cannot add two points knowing only their `x`-coordinates, since
`x(P)` and `x(Q)` determine `P + Q` only up to replacing it by `P - Q`. Knowing `x(P - Q)` as well
removes the ambiguity: **differential addition** `diffAdd P Q D` computes a raw pair for
`x(P + Q)` from raw pairs `P`, `Q` and `D` for `x(P)`, `x(Q)` and `x(P - Q)`. With
`a = (X_P + Z_P)(X_Q - Z_Q)` and `b = (X_P - Z_P)(X_Q + Z_Q)` it is
`(Z_D (a + b)², X_D (a - b)²)`. It is a polynomial map, homogeneous of degree `2` in `P`, `2` in
`Q` and `1` in `D`, symmetric in `P` and `Q`, and it commutes with ring homomorphisms, so it
makes sense over any commutative ring, in particular over `ZMod n` for a composite `n`.

`diffAdd_coordinates` proves its correctness on the native point group of the monic Montgomery
model `model A B`, over a field in which `2 ≠ 0` and for `B ≠ 0`, with no ellipticity
assumption: applied to the coordinate pairs of `P`, `Q` and `P - Q`, its output has vanishing
cross difference with the coordinate pair of `P + Q`, and it is nonzero exactly when `P - Q` is
neither the point at infinity nor the distinguished point of order two `(0, 0)`. Every other point
of order two is therefore a non-exceptional difference: with infinity as second point, differential
addition scales the first pair `P` by `4 X_P Z_P` (`diffAdd_one_zero`), so it is nonzero at every
affine point `(x, y)` with `x ≠ 0`, in particular at every point `(r, 0)` of order two with
`r ≠ 0` (`diffAdd_coordinates_some_ne_zero`). The theorems
`diffAdd_cross_eq_zero_of_cross_eq_zero` and `diffAdd_ne_zero_iff_of_cross_eq_zero` extend this to
arbitrary representatives, which is the form a Montgomery ladder uses; the first of them needs no
assumption on the characteristic, since in characteristic two the output is always `(0, 0)`.

At affine points with distinct `x`-coordinates `x₁ ≠ x₂` the correctness statement is Montgomery's
relation `x(P + Q) x(P - Q) (x₁ - x₂)² = (x₁ x₂ - B²)²` on the monic model. When `P = -Q`, the
output is nonzero exactly when `P + P ≠ (0, 0)`, and `add_self_eq_twoTorsionPoint_iff` identifies
the affine points with `P + P = (0, 0)` as those with `x² = B²`, that is, with Montgomery
coordinate `±1`.

## Main definitions

* `TauCeti.Montgomery.diffAdd`: Montgomery's differential-addition formula on raw pairs.

## Main results

* `TauCeti.Montgomery.diffAdd_coordinates`: correctness of differential addition on native points,
  with its exact exceptional set.
* `TauCeti.Montgomery.diffAdd_coordinates_zero_right` and
  `TauCeti.Montgomery.diffAdd_coordinates_some_ne_zero`: adding infinity, and the
  non-exceptional points of order two.
* `TauCeti.Montgomery.diffAdd_cross_eq_zero_of_cross_eq_zero` and
  `TauCeti.Montgomery.diffAdd_ne_zero_iff_of_cross_eq_zero`: the same for arbitrary
  representatives of the coordinate pairs.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, pp. 260–261: the relation
  `x(P₁ + P₂) x(P₁ - P₂) (x₁ - x₂)² = (x₁ x₂ - 1)²` and the projective addition display.
* D. J. Bernstein and T. Lange, *Explicit-Formulas Database*, Montgomery curves in `XZ`
  coordinates, entry `dadd-1987-m-3`.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Montgomery's **differential addition** of raw pairs: with `a = (X_P + Z_P)(X_Q - Z_Q)` and
`b = (X_P - Z_P)(X_Q + Z_Q)`, the pair `(Z_D (a + b)², X_D (a - b)²)`. When `P`, `Q` and `D`
represent the `x`-coordinates of points `P`, `Q` and `P - Q`, it represents the `x`-coordinate of
`P + Q` (see `diffAdd_coordinates`). The output is a raw pair and can be zero. -/
def diffAdd (P Q D : Pair R) : Pair R :=
  let a := (P.x + P.z) * (Q.x - Q.z)
  let b := (P.x - P.z) * (Q.x + Q.z)
  ⟨D.z * (a + b) ^ 2, D.x * (a - b) ^ 2⟩

/-- The first field of differential addition, in expanded form. -/
theorem diffAdd_x (P Q D : Pair R) :
    (diffAdd P Q D).x = 4 * D.z * (P.x * Q.x - P.z * Q.z) ^ 2 := by
  simp only [diffAdd]
  ring

/-- The second field of differential addition is a multiple of the square of the cross
difference of `P` and `Q`. -/
theorem diffAdd_z (P Q D : Pair R) :
    (diffAdd P Q D).z = 4 * D.x * P.cross Q ^ 2 := by
  simp only [diffAdd, Pair.cross_def]
  ring

/-- Differential addition is symmetric in its first two arguments. -/
theorem diffAdd_comm (P Q D : Pair R) : diffAdd P Q D = diffAdd Q P D := by
  ext
  · simp only [diffAdd_x]
    ring
  · simp only [diffAdd_z, Pair.cross_def]
    ring

/-- Differential addition is homogeneous of degree `2` in its first argument. -/
@[simp]
theorem diffAdd_smul_left (c : R) (P Q D : Pair R) :
    diffAdd (c • P) Q D = c ^ 2 • diffAdd P Q D := by
  ext <;> simp only [diffAdd, Pair.smul_x, Pair.smul_z] <;> ring

/-- Differential addition is homogeneous of degree `2` in its second argument. -/
@[simp]
theorem diffAdd_smul_right (c : R) (P Q D : Pair R) :
    diffAdd P (c • Q) D = c ^ 2 • diffAdd P Q D := by
  rw [diffAdd_comm, diffAdd_smul_left, diffAdd_comm]

/-- Differential addition is homogeneous of degree `1` in its third argument, the pair standing
for the difference. -/
@[simp]
theorem diffAdd_smul_diff (c : R) (P Q D : Pair R) :
    diffAdd P Q (c • D) = c • diffAdd P Q D := by
  ext <;> simp only [diffAdd, Pair.smul_x, Pair.smul_z] <;> ring

/-- Differential addition with the infinity pair `(1, 0)` as second point and `P` itself as
difference scales `P` by `4 X_P Z_P`. -/
@[simp]
theorem diffAdd_one_zero (P : Pair R) : diffAdd P ⟨1, 0⟩ P = (4 * P.x * P.z) • P := by
  ext
  · simp only [diffAdd_x, Pair.smul_x]
    ring
  · simp only [diffAdd_z, Pair.cross_def, Pair.smul_z]
    ring

/-- Differential addition commutes with any change of coefficient ring. -/
@[simp]
theorem map_diffAdd (f : R →+* S) (P Q D : Pair R) :
    (diffAdd P Q D).map f = diffAdd (P.map f) (Q.map f) (D.map f) := by
  ext <;> simp [diffAdd]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {A B : R}

/-- **Differential addition of a point and infinity.** Over a commutative ring without zero
divisors in which `2 ≠ 0`, and for `B ≠ 0`, differential addition of the coordinate pairs of `P`,
infinity and `P` has vanishing cross difference with the coordinate pair of `P`, and it is nonzero
exactly when `P` is neither the point at infinity nor the distinguished point of order two
`(0, 0)`. In particular every other point of order two, an affine point `(r, 0)` with `r ≠ 0`, is a
non-exceptional difference. -/
theorem diffAdd_coordinates_zero_right (h₂ : (2 : R) ≠ 0) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) :
    (diffAdd (coordinates A B P) ⟨1, 0⟩ (coordinates A B P)).cross (coordinates A B P) = 0 ∧
      (diffAdd (coordinates A B P) ⟨1, 0⟩ (coordinates A B P) ≠ 0 ↔
        P ≠ 0 ∧ P ≠ twoTorsionPoint A hB) := by
  have h₄ : (4 : R) ≠ 0 := by
    convert mul_ne_zero h₂ h₂ using 1
    norm_num
  rw [diffAdd_one_zero, Pair.smul_cross, Pair.cross_self, mul_zero, Ne, Pair.smul_eq_zero,
    or_iff_left (coordinates_ne_zero hB P)]
  simp [h₄, not_or, coordinates_x_eq_zero_iff hB, coordinates_z_eq_zero_iff hB, and_comm]

/-- **An affine point other than `(0, 0)` is a non-exceptional difference.** Over a commutative
ring without zero divisors in which `2 ≠ 0`, and for `B ≠ 0`, differential addition of the
coordinate pairs of an affine point `(x, y)` with `x ≠ 0`, infinity and `(x, y)` is nonzero.
This includes every point `(r, 0)` of order two with `r ≠ 0`, so the distinguished point `(0, 0)`
is the only point of order two that is an exceptional difference. -/
theorem diffAdd_coordinates_some_ne_zero (h₂ : (2 : R) ≠ 0) (hB : B ≠ 0) {x y : R}
    (h : (model A B).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    diffAdd (coordinates A B (.some x y h)) ⟨1, 0⟩ (coordinates A B (.some x y h)) ≠ 0 :=
  (diffAdd_coordinates_zero_right h₂ hB _).2.mpr
    ⟨Affine.Point.some_ne_zero h, (some_eq_twoTorsionPoint_iff hB h).not.mpr hx⟩

end Domain

section Field

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

/-- Montgomery's relation `x(P + Q) x(P - Q) (x₁ - x₂)² = (x₁ x₂ - B²)²` for affine points of the
monic model with distinct `x`-coordinates `x₁ ≠ x₂`. -/
private theorem addX_mul_addX_negY {x₁ x₂ y₁ y₂ : K}
    (h₁ : (model A B).toAffine.Equation x₁ y₁) (h₂ : (model A B).toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (model A B).toAffine.addX x₁ x₂ ((model A B).toAffine.slope x₁ x₂ y₁ y₂) *
        (model A B).toAffine.addX x₁ x₂
          ((model A B).toAffine.slope x₁ x₂ y₁ ((model A B).toAffine.negY x₂ y₂)) *
        (x₁ - x₂) ^ 2 =
      (x₁ * x₂ - B ^ 2) ^ 2 := by
  have e₁ : y₁ ^ 2 = x₁ ^ 3 + A * B * x₁ ^ 2 + B ^ 2 * x₁ := by
    simpa [Affine.equation_iff] using h₁
  have e₂ : y₂ ^ 2 = x₂ ^ 3 + A * B * x₂ ^ 2 + B ^ 2 * x₂ := by
    simpa [Affine.equation_iff] using h₂
  have hd : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  rw [Affine.addX_of_X_ne hx, Affine.addX_of_X_ne hx, div_mul_div_comm, div_mul_eq_mul_div,
    div_eq_iff (mul_ne_zero hd hd)]
  simp only [model_a₁, model_a₂, model_a₃, Affine.negY, zero_mul, sub_zero, add_zero]
  linear_combination (x₁ - x₂) ^ 2 * (
    (y₁ ^ 2 - y₂ ^ 2 + (x₁ ^ 3 + A * B * x₁ ^ 2 + B ^ 2 * x₁) -
      (x₂ ^ 3 + A * B * x₂ ^ 2 + B ^ 2 * x₂) - 2 * (A * B + x₁ + x₂) * (x₁ - x₂) ^ 2) * e₁ +
    (-(y₁ ^ 2 - y₂ ^ 2 + (x₁ ^ 3 + A * B * x₁ ^ 2 + B ^ 2 * x₁) -
      (x₂ ^ 3 + A * B * x₂ ^ 2 + B ^ 2 * x₂)) - 2 * (A * B + x₁ + x₂) * (x₁ - x₂) ^ 2) * e₂)

/-- Differential addition of the coordinate pair of `Q` with itself, with difference `Q + Q`: this
is the case `P = -Q`, where `P - Q = -(Q + Q)` and `P + Q` is the point at infinity. -/
private theorem diffAdd_coordinates_self (h₄ : (4 : K) ≠ 0) (hB : B ≠ 0)
    (Q : (model A B).toAffine.Point) :
    (diffAdd (coordinates A B Q) (coordinates A B Q) (coordinates A B (Q + Q))).cross ⟨1, 0⟩ = 0 ∧
      (diffAdd (coordinates A B Q) (coordinates A B Q) (coordinates A B (Q + Q)) ≠ 0 ↔
        Q + Q ≠ 0 ∧ Q + Q ≠ twoTorsionPoint A hB) := by
  refine ⟨by simp [Pair.cross_def, diffAdd_z], ?_⟩
  rw [Pair.ne_zero_iff, diffAdd_z, Pair.cross_self, diffAdd_x]
  simp only [ne_eq, mul_eq_zero, h₄, false_or, pow_eq_zero_iff two_ne_zero, zero_pow two_ne_zero,
    mul_zero, not_true, or_false, not_or, coordinates_z_eq_zero_iff hB]
  refine and_congr_right fun hQ ↦ ?_
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd (add_zero _) hQ
  · rw [coordinates_some, add_self_eq_twoTorsionPoint_iff hB, sub_eq_zero, ← sq, ← sq]

/-- **Correctness of Montgomery differential addition on native points.** Over a field with
`2 ≠ 0` and for `B ≠ 0`, differential addition of the coordinate pairs of `P`, `Q` and `P - Q`
has vanishing cross difference with the coordinate pair of `P + Q`, and it is nonzero exactly
when `P - Q` is neither the point at infinity nor the distinguished point of order two `(0, 0)`.
No ellipticity assumption is needed. -/
theorem diffAdd_coordinates (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0) (P Q : (model A B).toAffine.Point) :
    (diffAdd (coordinates A B P) (coordinates A B Q) (coordinates A B (P - Q))).cross
        (coordinates A B (P + Q)) = 0 ∧
      (diffAdd (coordinates A B P) (coordinates A B Q) (coordinates A B (P - Q)) ≠ 0 ↔
        P - Q ≠ 0 ∧ P - Q ≠ twoTorsionPoint A hB) := by
  have h₄ : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h₂ h₂
  have h₀ (p : Pair K) : diffAdd p p ⟨1, 0⟩ = 0 := by
    ext <;> simp [diffAdd_x, diffAdd_z]
  rcases P with _ | ⟨x₁, y₁, hP⟩ <;> rcases Q with _ | ⟨x₂, y₂, hQ⟩
  · simp [← Affine.Point.zero_def, h₀]
  · rw [← Affine.Point.zero_def, zero_sub, zero_add, coordinates_neg, coordinates_zero]
    simp only [ne_eq, neg_eq_iff_eq_neg, neg_twoTorsionPoint]
    rw [diffAdd_comm]
    exact diffAdd_coordinates_zero_right h₂ hB _
  · rw [← Affine.Point.zero_def, sub_zero, add_zero, coordinates_zero]
    exact diffAdd_coordinates_zero_right h₂ hB _
  by_cases hx : x₁ = x₂
  · rcases Affine.Point.X_eq_iff.mp hx with h | h
    · rw [h, sub_self, coordinates_zero]
      simp [h₀]
    · rw [h, neg_add_cancel, neg_sub_left, coordinates_neg, coordinates_neg, coordinates_zero]
      simp only [ne_eq, neg_eq_iff_eq_neg, neg_twoTorsionPoint]
      exact diffAdd_coordinates_self h₄ hB _
  -- Both points are affine with distinct `x`-coordinates, so `P + Q` and `P - Q` are affine too.
  have key := addX_mul_addX_negY hP.1 hQ.1 hx
  rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx,
    Affine.Point.add_of_X_ne hx, coordinates_some, coordinates_some, coordinates_some,
    coordinates_some]
  refine ⟨?_, ?_⟩
  · rw [Pair.cross_def, diffAdd_x, diffAdd_z, Pair.cross_def]
    linear_combination (-4 * B ^ 2) * key
  · rw [and_iff_right (Affine.Point.some_ne_zero _)]
    refine Iff.trans ?_ (some_eq_twoTorsionPoint_iff hB _).not.symm
    rw [Pair.ne_zero_iff, diffAdd_x, diffAdd_z, Pair.cross_def]
    dsimp only
    constructor
    · rintro (h | h) h₄'
      · have hsq : (x₁ * x₂ - B ^ 2) ^ 2 = 0 := by rw [← key, h₄']; ring
        exact h (by linear_combination 4 * B * hsq)
      · exact h (by rw [h₄']; ring)
    · intro h₄'
      refine .inr ?_
      rw [show x₁ * B - x₂ * B = (x₁ - x₂) * B by ring]
      exact mul_ne_zero (mul_ne_zero h₄ h₄') (pow_ne_zero 2 (mul_ne_zero (sub_ne_zero.mpr hx) hB))

/-- **Differential addition of arbitrary representatives.** Over a field and for `B ≠ 0`, if the
pairs `SP`, `SQ` and `SD` have vanishing cross difference with the coordinate pairs of `P`, `Q` and
`P - Q`, then their differential addition has vanishing cross difference with the coordinate pair
of `P + Q`. In characteristic two this holds because the output is always `(0, 0)`. -/
theorem diffAdd_cross_eq_zero_of_cross_eq_zero (hB : B ≠ 0)
    {P Q : (model A B).toAffine.Point} {SP SQ SD : Pair K}
    (hP : SP.cross (coordinates A B P) = 0) (hQ : SQ.cross (coordinates A B Q) = 0)
    (hD : SD.cross (coordinates A B (P - Q)) = 0) :
    (diffAdd SP SQ SD).cross (coordinates A B (P + Q)) = 0 := by
  by_cases h₂ : (2 : K) = 0
  · have h₄ : (4 : K) = 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num, h₂, zero_mul]
    have h₀ : diffAdd SP SQ SD = 0 := by
      ext <;> simp [diffAdd_x, diffAdd_z, h₄]
    rw [h₀, Pair.zero_cross]
  obtain ⟨a, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB P)).mp hP
  obtain ⟨b, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB Q)).mp hQ
  obtain ⟨c, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB (P - Q))).mp hD
  simp [(diffAdd_coordinates h₂ hB P Q).1]

/-- **The exceptional set of differential addition, for arbitrary representatives.** Over a field
with `2 ≠ 0` and for `B ≠ 0`, if the nonzero pairs `SP`, `SQ` and `SD` have vanishing cross
difference with the coordinate pairs of `P`, `Q` and `P - Q`, then their differential addition is
nonzero exactly when `P - Q` is neither the point at infinity nor the distinguished point of order
two `(0, 0)`. -/
theorem diffAdd_ne_zero_iff_of_cross_eq_zero (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0)
    {P Q : (model A B).toAffine.Point} {SP SQ SD : Pair K} (hSP : SP ≠ 0) (hSQ : SQ ≠ 0)
    (hSD : SD ≠ 0) (hP : SP.cross (coordinates A B P) = 0)
    (hQ : SQ.cross (coordinates A B Q) = 0) (hD : SD.cross (coordinates A B (P - Q)) = 0) :
    diffAdd SP SQ SD ≠ 0 ↔ P - Q ≠ 0 ∧ P - Q ≠ twoTorsionPoint A hB := by
  obtain ⟨a, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB P)).mp hP
  obtain ⟨b, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB Q)).mp hQ
  obtain ⟨c, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB (P - Q))).mp hD
  simp only [ne_eq, Pair.smul_eq_zero, not_or] at hSP hSQ hSD
  rw [← (diffAdd_coordinates h₂ hB P Q).2]
  simp [hSP.1, hSQ.1, hSD.1]

/-- For `B ≠ 0`, differential addition of arbitrary representatives is the zero raw pair
when the difference is infinity or the distinguished point of order two. No restriction on the
characteristic or nonvanishing of the representatives is needed. -/
theorem diffAdd_eq_zero_of_cross_eq_zero (hB : B ≠ 0)
    {P Q : (model A B).toAffine.Point} {SP SQ SD : Pair K}
    (hP : SP.cross (coordinates A B P) = 0) (hQ : SQ.cross (coordinates A B Q) = 0)
    (hD : SD.cross (coordinates A B (P - Q)) = 0)
    (h : P - Q = 0 ∨ P - Q = twoTorsionPoint A hB) : diffAdd SP SQ SD = 0 := by
  by_cases h₂ : (2 : K) = 0
  · have h₄ : (4 : K) = 0 := by linear_combination 2 * h₂
    ext <;> simp [diffAdd_x, diffAdd_z, h₄]
  obtain ⟨a, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB P)).mp hP
  obtain ⟨b, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB Q)).mp hQ
  obtain ⟨c, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero hB (P - Q))).mp hD
  have h₀ : diffAdd (coordinates A B P) (coordinates A B Q)
      (coordinates A B (P - Q)) = 0 := by
    by_contra hn
    obtain ⟨hzero, hT⟩ := (diffAdd_coordinates h₂ hB P Q).2.mp hn
    exact h.elim hzero hT
  simp [h₀]

end Field

end TauCeti.Montgomery
