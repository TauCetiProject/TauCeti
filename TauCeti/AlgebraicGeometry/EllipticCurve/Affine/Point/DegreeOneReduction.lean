/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.PolePoints
-- Proof-only: the chord identities relating `y₁ - y₂` to `x₁ - x₂`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Chord
-- Proof-only: a point with integral `x`-coordinate has integral `y`-coordinate.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.ValuationIntegrality
-- Proof-only: `λ² + a₁λ - c` has a pole exactly where `λ` does.
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Reduction of points at a place of degree one

Let `W` be an elliptic curve over `F`, let `K` be a field extension of `F` and let `w` be a place
of `K / F`. The points of `W` over `K` with a pole of `x` at `w`, together with the point at
infinity, form the subgroup `polePoints W w` (`Affine/Point/PolePoints.lean`), the kernel of
reduction at `w`. This file identifies that kernel in coordinates, and uses it to build the
reduction map when `w` has degree one.

The coordinate criterion is `some_sub_baseChange_mem_polePoints_iff`: for an affine point
`A = (x₁, y₁)` of `W` over `K` and an affine point `(a, b)` of `W` over `F`, the difference
`A - (a, b)` lies in the kernel of reduction exactly when `x₁ ≡ a` and `y₁ ≡ b` modulo `w`. The
subtraction is computed by the chord through `A` and `-(a, b)`, whose `x`-coordinate is
`λ² + a₁λ - a₂ - x₁ - a`; this has a pole exactly when the slope `λ` does, and the chord identity
`(y₁ - b') (y₁ + b' + a₁ x₁ + a₃) = (x₁ - a) M` (`Affine/Formula/Chord.lean`), with `b'` the
`y`-coordinate of `-(a, b)` and `M` integral, shows that `λ` has a pole exactly when `A` is
congruent to `(a, b)`.

The residues `(a, b)` of the coordinates of an integral point of `W` over `K` satisfy the equation
of `W`, the defect of that equation at `(a, b)` being a constant congruent to `0`
(`nonsingular_of_valuation_sub_lt_one`). When `w` has degree one its residue field is `F`, so
every integral point of `W` over `K` is congruent to a point of `W` over `F`
(`exists_sub_mem_polePoints`). That point is unique, since a nonzero constant affine point has
no pole (`eq_of_sub_mem_polePoints`, in `Affine/Point/PolePoints.lean`). So every point `A` has
a unique reduction `Q ∈ W(F)` with `A - Q ∈ polePoints W w`, and `A ↦ Q` is additive because
`polePoints W w` is a subgroup.

This is the reduction map `W(K) → W(F)` of Silverman VII.2.1, at a place whose residue field is
the base field. `WeierstrassCurve.Affine.Point.reduction` (`Affine/Point/Reduction.lean`) reduces
modulo an arbitrary valuation into the projective plane over the residue field; at a place of
degree one it sends `A` to the projective class of the reduction here, read through
`TauCeti.Place.residueFieldEquivOfDegreeEqOne`.

## Main definitions

* `WeierstrassCurve.Affine.reductionOfDegreeEqOne`: the reduction `W(K) →+ W(F)` at a place of
  degree one.

## Main results

* `WeierstrassCurve.Affine.nonsingular_of_valuation_sub_lt_one`: the residues of the coordinates
  of a point of `W` over `K` form a point of `W` over `F`.
* `WeierstrassCurve.Affine.some_sub_baseChange_mem_polePoints_iff`: `A - (a, b)` lies in the
  kernel of reduction exactly when both coordinates of `A` are congruent to those of `(a, b)`.
* `WeierstrassCurve.Affine.exists_sub_mem_polePoints`: at a place of degree one, every point of
  `W` over `K` is congruent to a point of `W` over `F`.
* `WeierstrassCurve.Affine.reductionOfDegreeEqOne_eq_iff`: the reduction of `A` is the unique
  point `Q` of `W` over `F` with `A - Q` in the kernel of reduction.
* `WeierstrassCurve.Affine.reductionOfDegreeEqOne_some`: an integral affine point reduces to the
  residues of its coordinates.
* `WeierstrassCurve.Affine.ker_reductionOfDegreeEqOne`: the kernel of the reduction map is
  `polePoints W w`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1, VII.2.2.
-/

public section

open TauCeti

namespace WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : Affine F) (w : Place F K)

section Valuation

variable {w}

-- An element near `0` plus a nonzero constant is a unit at `w`.
private theorem valuation_add_algebraMap_eq_one {z : K} (hz : w.valuation z < 1) {c : F}
    (hc : c ≠ 0) : w.valuation (z + algebraMap F K c) = 1 := by
  have h1 := Valuation.IsTrivialOn.eq_one (v := w.valuation) c hc
  rw [Valuation.map_add_eq_of_lt_right _ (hz.trans_eq h1.symm), h1]

-- An integral multiple of an element near `0` is near `0`, on either side.
private theorem valuation_mul_lt_one_of_lt_one {z m : K} (hz : w.valuation z < 1)
    (hm : m ∈ w.integers) : w.valuation (z * m) < 1 :=
  (map_mul _ _ _).trans_lt (mul_lt_one_of_lt_of_le hz (w.mem_integers_iff.mp hm))

private theorem valuation_mul_lt_one_of_mem_integers {m z : K} (hm : m ∈ w.integers)
    (hz : w.valuation z < 1) : w.valuation (m * z) < 1 := by
  rw [mul_comm]
  exact valuation_mul_lt_one_of_lt_one hz hm

-- An element congruent to a constant is integral.
private theorem mem_integers_of_valuation_sub_lt_one {z : K} {c : F}
    (h : w.valuation (z - algebraMap F K c) < 1) : z ∈ w.integers := by
  simpa using add_mem (w.mem_integers_iff.mpr h.le) (w.algebraMap_mem_integers c)

end Valuation

-- The chord identity divided by `x₁ - a`: the slope from `(x₁, y₁)` to the constant point
-- `(a, b')`, times `y₁ + b' + a₁ x₁ + a₃`, is a polynomial in `x₁` with constant coefficients.
private theorem slope_mul_eq {x₁ y₁ : K} (h₁ : (W⁄K).toAffine.Equation x₁ y₁) {a b' : F}
    (hQ : W.Equation a b') (hx : x₁ ≠ algebraMap F K a) :
    (y₁ - algebraMap F K b') / (x₁ - algebraMap F K a) *
        (y₁ + algebraMap F K b' + algebraMap F K W.a₁ * x₁ + algebraMap F K W.a₃) =
      x₁ ^ 2 + x₁ * algebraMap F K a + algebraMap F K a ^ 2 +
        algebraMap F K W.a₂ * (x₁ + algebraMap F K a) + algebraMap F K W.a₄ -
        algebraMap F K W.a₁ * algebraMap F K b' := by
  have hchord : (y₁ - algebraMap F K b') *
      (y₁ + algebraMap F K b' + algebraMap F K W.a₁ * x₁ + algebraMap F K W.a₃) =
      (x₁ - algebraMap F K a) * (x₁ ^ 2 + x₁ * algebraMap F K a + algebraMap F K a ^ 2 +
        algebraMap F K W.a₂ * (x₁ + algebraMap F K a) + algebraMap F K W.a₄ -
        algebraMap F K W.a₁ * algebraMap F K b') :=
    Y_sub_Y_mul_Y_add_Y_eq h₁ ((W.map_equation (algebraMap F K).injective a b').mpr hQ)
  rw [div_mul_eq_mul_div, hchord, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hx)]

-- If the slope from an integral `(x₁, y₁)` to `-(a, b)` has a pole, `(x₁, y₁)` reduces to `(a, b)`.
-- Otherwise either `x₁ - a` is a unit and the slope is integral, or `y₁` is near `-(a, b)` but not
-- near `(a, b)`, so that `y₁ + b' + a₁ x₁ + a₃` is a unit and `slope_mul_eq` makes the slope
-- integral.
private theorem valuation_sub_lt_one_of_one_lt_slope {x₁ y₁ : K}
    (h₁ : (W⁄K).toAffine.Equation x₁ y₁) {a b : F} (hQ : W.Equation a b)
    (hx₁ : w.valuation x₁ ≤ 1) (hy₁ : w.valuation y₁ ≤ 1) (hx : x₁ ≠ algebraMap F K a)
    (hl : 1 < w.valuation ((y₁ - algebraMap F K (W.negY a b)) / (x₁ - algebraMap F K a))) :
    w.valuation (x₁ - algebraMap F K a) < 1 ∧ w.valuation (y₁ - algebraMap F K b) < 1 := by
  set v := w.valuation
  have hx₁m : x₁ ∈ w.integers := w.mem_integers_iff.mpr hx₁
  have hy₁m : y₁ ∈ w.integers := w.mem_integers_iff.mpr hy₁
  have hsl := slope_mul_eq W h₁ ((W.equation_neg a b).mpr hQ) hx
  set b' := W.negY a b with hb'
  have hxlt : v (x₁ - algebraMap F K a) < 1 := by
    by_contra hge
    push Not at hge
    rw [map_div₀, le_antisymm (v.map_sub_le hx₁
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one v a)) hge, div_one] at hl
    exact hl.not_ge (v.map_sub_le hy₁ (Valuation.IsTrivialOn.valuation_algebraMap_le_one v b'))
  refine ⟨hxlt, ?_⟩
  by_contra hge
  push Not at hge
  have hy1 : v (y₁ - algebraMap F K b) = 1 :=
    le_antisymm (v.map_sub_le hy₁ (Valuation.IsTrivialOn.valuation_algebraMap_le_one v b)) hge
  -- the two points over `a`: `y₁` is near `-(a, b)`
  have hy'lt : v (y₁ - algebraMap F K b') < 1 := by
    have hfib : (y₁ - algebraMap F K b) * (y₁ - algebraMap F K b') =
        (x₁ - algebraMap F K a) * (x₁ ^ 2 + x₁ * algebraMap F K a + algebraMap F K a ^ 2 +
          (W⁄K).a₂ * (x₁ + algebraMap F K a) + (W⁄K).a₄ - (W⁄K).a₁ * y₁) := by
      rw [hb', ← W.map_negY (algebraMap F K) a b]
      exact Y_sub_Y_mul_Y_sub_negY_eq h₁ ((W.map_equation (algebraMap F K).injective a b).mpr hQ)
    have := congrArg v hfib
    rw [map_mul, hy1, one_mul] at this
    rw [this]
    exact valuation_mul_lt_one_of_lt_one hxlt (by
      apply_rules [add_mem, sub_mem, mul_mem, pow_mem, w.algebraMap_mem_integers])
  have hne : b' - b ≠ 0 := fun h0 ↦ by
    rw [sub_eq_zero.mp h0] at hy'lt
    exact absurd hy1 hy'lt.ne
  -- so `y₁ + b' + a₁ x₁ + a₃ ≡ b' - b` is a unit
  have hD1 : v (y₁ + algebraMap F K b' + algebraMap F K W.a₁ * x₁ + algebraMap F K W.a₃) = 1 := by
    rw [show y₁ + algebraMap F K b' + algebraMap F K W.a₁ * x₁ + algebraMap F K W.a₃ =
        (y₁ - algebraMap F K b' + algebraMap F K W.a₁ * (x₁ - algebraMap F K a)) +
          algebraMap F K (b' - b) by simp only [hb', negY, map_sub, map_neg, map_mul]; ring]
    exact valuation_add_algebraMap_eq_one (v.map_add_lt hy'lt
      (valuation_mul_lt_one_of_mem_integers (w.algebraMap_mem_integers _) hxlt)) hne
  have := congrArg v hsl
  rw [map_mul, hD1, mul_one] at this
  exact (this ▸ hl).not_ge (w.mem_integers_iff.mp (by
    apply_rules [add_mem, sub_mem, mul_mem, pow_mem, w.algebraMap_mem_integers]))

-- If `(a, b)` is `2`-torsion and an integral `(x₁, y₁)` reduces to it, the slope to
-- `-(a, b) = (a, b)` has a pole: `y₁ + b + a₁ x₁ + a₃` is near `0`, while the polynomial side of
-- `slope_mul_eq` is a unit, `(a, b)` being nonsingular with a vertical tangent.
private theorem one_lt_slope_of_negY_eq {x₁ y₁ : K} (h₁ : (W⁄K).toAffine.Equation x₁ y₁)
    {a b : F} (hQ : W.Nonsingular a b) (hx₁ : w.valuation x₁ ≤ 1) (hx : x₁ ≠ algebraMap F K a)
    (hbb : W.negY a b = b) (hxlt : w.valuation (x₁ - algebraMap F K a) < 1)
    (hylt : w.valuation (y₁ - algebraMap F K b) < 1) :
    1 < w.valuation ((y₁ - algebraMap F K b) / (x₁ - algebraMap F K a)) := by
  set v := w.valuation
  have hx₁m : x₁ ∈ w.integers := w.mem_integers_iff.mpr hx₁
  have hsl := slope_mul_eq W h₁ hQ.1 hx
  set M := x₁ ^ 2 + x₁ * algebraMap F K a + algebraMap F K a ^ 2 +
    algebraMap F K W.a₂ * (x₁ + algebraMap F K a) + algebraMap F K W.a₄ -
    algebraMap F K W.a₁ * algebraMap F K b with hM
  have hDlt : v (y₁ + algebraMap F K b + algebraMap F K W.a₁ * x₁ + algebraMap F K W.a₃) < 1 := by
    have h2 := congrArg (algebraMap F K) hbb
    simp only [negY, map_sub, map_neg, map_mul] at h2
    rw [show y₁ + algebraMap F K b + algebraMap F K W.a₁ * x₁ + algebraMap F K W.a₃ =
        (y₁ - algebraMap F K b) + algebraMap F K W.a₁ * (x₁ - algebraMap F K a) by
      linear_combination -h2]
    exact v.map_add_lt hylt
      (valuation_mul_lt_one_of_mem_integers (w.algebraMap_mem_integers _) hxlt)
  -- the vertical tangent at `(a, b)`: `3 a² + 2 a₂ a + a₄ - a₁ b ≠ 0` by nonsingularity
  have hM₀ : 3 * a ^ 2 + 2 * W.a₂ * a + W.a₄ - W.a₁ * b ≠ 0 := by
    have hns := (W.nonsingular_iff a b).mp hQ
    rw [negY] at hbb
    exact sub_ne_zero.mpr (Ne.symm (hns.2.resolve_right (not_not.mpr hbb.symm)))
  have hM1 : v M = 1 := by
    rw [show M = (x₁ - algebraMap F K a) * (x₁ + 2 * algebraMap F K a + algebraMap F K W.a₂) +
        algebraMap F K (3 * a ^ 2 + 2 * W.a₂ * a + W.a₄ - W.a₁ * b) by
      rw [hM]; simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]; ring]
    exact valuation_add_algebraMap_eq_one (valuation_mul_lt_one_of_lt_one hxlt
      (by apply_rules [add_mem, mul_mem, w.algebraMap_mem_integers, ofNat_mem])) hM₀
  have := congrArg v hsl
  rw [map_mul, hM1] at this
  exact not_le.mp fun hle ↦ ((mul_comm _ _).trans_lt (mul_lt_one_of_lt_of_le hDlt hle)).ne this

-- The slope core: for integral `x₁, y₁` off the vertical line through the constant point `(a, b)`,
-- the chord slope to `-(a, b)` has a pole exactly when `(x₁, y₁)` reduces to `(a, b)`.
private theorem one_lt_valuation_slope_iff {x₁ y₁ : K} (h₁ : (W⁄K).toAffine.Equation x₁ y₁)
    {a b : F} (hQ : W.Nonsingular a b) (hx₁ : w.valuation x₁ ≤ 1) (hy₁ : w.valuation y₁ ≤ 1)
    (hx : x₁ ≠ algebraMap F K a) :
    1 < w.valuation ((y₁ - algebraMap F K (W.negY a b)) / (x₁ - algebraMap F K a)) ↔
      w.valuation (x₁ - algebraMap F K a) < 1 ∧ w.valuation (y₁ - algebraMap F K b) < 1 := by
  refine ⟨valuation_sub_lt_one_of_one_lt_slope W w h₁ hQ.1 hx₁ hy₁ hx, fun ⟨hxlt, hylt⟩ ↦ ?_⟩
  by_cases hbb : W.negY a b = b
  · rw [hbb]
    exact one_lt_slope_of_negY_eq W w h₁ hQ hx₁ hx hbb hxlt hylt
  -- otherwise the numerator `y₁ - b'` is a unit, and the slope has the pole of `1 / (x₁ - a)`
  have hnum : w.valuation (y₁ - algebraMap F K (W.negY a b)) = 1 := by
    rw [show y₁ - algebraMap F K (W.negY a b) =
        (y₁ - algebraMap F K b) + algebraMap F K (b - W.negY a b) by rw [map_sub]; ring]
    exact valuation_add_algebraMap_eq_one hylt (sub_ne_zero.mpr (Ne.symm hbb))
  rw [map_div₀, hnum, lt_div_iff₀ ((w.valuation.pos_iff).mpr (sub_ne_zero.mpr hx)), one_mul]
  exact hxlt

/-- **The residues of the coordinates of a point of `W` over `K` form a point of `W` over `F`.**
If `(x, y)` lies on `W` over `K` and `x ≡ a`, `y ≡ b` modulo `w` for constants `a, b : F`, then
`(a, b)` is a nonsingular point of `W`: the defect of the equation of `W` at `(a, b)` is a
constant congruent to `0`, hence `0`. -/
theorem nonsingular_of_valuation_sub_lt_one [W.IsElliptic] {x y : K}
    (h : (W⁄K).toAffine.Equation x y) {a b : F} (ha : w.valuation (x - algebraMap F K a) < 1)
    (hb : w.valuation (y - algebraMap F K b) < 1) : W.Nonsingular a b := by
  set v := w.valuation
  set δ := b ^ 2 + W.a₁ * a * b + W.a₃ * b - (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆) with hδ
  have hxm := mem_integers_of_valuation_sub_lt_one ha
  have hym := mem_integers_of_valuation_sub_lt_one hb
  have heq := (equation_iff _ _).mp h
  have hδK : algebraMap F K δ = -((y - algebraMap F K b) * (y + algebraMap F K b +
      algebraMap F K W.a₁ * x + algebraMap F K W.a₃) + algebraMap F K W.a₁ * algebraMap F K b *
      (x - algebraMap F K a) - (x - algebraMap F K a) * (x ^ 2 + x * algebraMap F K a +
      algebraMap F K a ^ 2 + algebraMap F K W.a₂ * (x + algebraMap F K a) +
      algebraMap F K W.a₄)) := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
    simp only [hδ, map_sub, map_add, map_mul, map_pow]
    linear_combination heq
  have hδ0 : δ = 0 := by
    by_contra hne
    refine absurd (Valuation.IsTrivialOn.eq_one (v := v) δ hne) (ne_of_lt ?_)
    rw [hδK, Valuation.map_neg]
    refine v.map_sub_lt (v.map_add_lt ?_ ?_) ?_
    · exact valuation_mul_lt_one_of_lt_one hb (by
        apply_rules [add_mem, mul_mem, w.algebraMap_mem_integers])
    · exact valuation_mul_lt_one_of_mem_integers (by
        apply_rules [mul_mem, w.algebraMap_mem_integers]) ha
    · exact valuation_mul_lt_one_of_lt_one ha (by
        apply_rules [add_mem, mul_mem, pow_mem, w.algebraMap_mem_integers])
  exact (equation_iff_nonsingular).mp ((equation_iff _ _).mpr
    (by rw [hδ, sub_eq_zero] at hδ0; exact hδ0))

-- A nonsingular point of `W` over `K` with coordinates in `F` is a nonsingular point over `F`.
private theorem nonsingular_of_nonsingular_algebraMap {a b : F}
    (h : (W⁄K).toAffine.Nonsingular (algebraMap F K a) (algebraMap F K b)) :
    (W⁄F).toAffine.Nonsingular a b :=
  (W.map_nonsingular (algebraMap F F).injective a b).mpr
    ((W.map_nonsingular (algebraMap F K).injective a b).mp h)

-- An affine point of `W` over `K` with coordinates in `F` is a point of `W` over `F`.
private theorem some_algebraMap_eq_baseChange [DecidableEq F] [DecidableEq K] {a b : F}
    (h : (W⁄K).toAffine.Nonsingular (algebraMap F K a) (algebraMap F K b)) :
    Point.some _ _ h =
      Point.baseChange (W' := W) F K (.some a b (nonsingular_of_nonsingular_algebraMap W h)) := by
  rw [Point.baseChange, Point.map_some]
  simp only [Algebra.ofId_apply]

variable [DecidableEq K] [W.IsElliptic]

-- Over the `x`-coordinate of the constant point `(a, b)` a point is `(a, b)` or `-(a, b)`. The
-- difference is `0` in the first case; in the second both points are constant, so the difference
-- is not in the kernel of reduction, and `y₁` is the unit distance `b' - b` away from `b`.
private theorem some_sub_some_mem_polePoints_iff_of_X_eq {y₁ : K} {a b : F}
    (h₁ : (W⁄K).toAffine.Nonsingular (algebraMap F K a) y₁)
    (hQK : (W⁄K).toAffine.Nonsingular (algebraMap F K a) (algebraMap F K b)) :
    Point.some (algebraMap F K a) y₁ h₁ - Point.some (algebraMap F K a) (algebraMap F K b) hQK ∈
        polePoints W w ↔ w.valuation (y₁ - algebraMap F K b) < 1 := by
  classical
  by_cases hy : y₁ = algebraMap F K b
  · subst hy
    simp only [sub_self, map_zero, zero_lt_one, iff_true]
    exact zero_mem _
  obtain rfl : y₁ = algebraMap F K (W.negY a b) :=
    ((Y_eq_of_X_eq h₁.1 hQK.1 rfl).resolve_left hy).trans (W.map_negY (algebraMap F K) a b)
  have hbb : W.negY a b ≠ b := fun h ↦ hy (by rw [h])
  rw [some_algebraMap_eq_baseChange W h₁, some_algebraMap_eq_baseChange W hQK, ← map_sub,
    baseChange_mem_polePoints_iff, sub_eq_zero, ← map_sub,
    Valuation.IsTrivialOn.eq_one _ (sub_ne_zero.mpr hbb)]
  simp only [Point.some.injEq, true_and, hbb, lt_self_iff_false]

-- The coordinate criterion, with the constant point written through its coordinates: the chord
-- through `(x₁, y₁)` and `-(a, b)` has `x`-coordinate `λ² + a₁λ - a₂ - x₁ - a`, which has a pole
-- exactly when `λ` does.
private theorem some_sub_algebraMap_mem_polePoints_iff {x₁ y₁ : K}
    (h₁ : (W⁄K).toAffine.Nonsingular x₁ y₁) {a b : F}
    (hQK : (W⁄K).toAffine.Nonsingular (algebraMap F K a) (algebraMap F K b)) :
    Point.some x₁ y₁ h₁ - Point.some (algebraMap F K a) (algebraMap F K b) hQK ∈
        polePoints W w ↔
      w.valuation (x₁ - algebraMap F K a) < 1 ∧ w.valuation (y₁ - algebraMap F K b) < 1 := by
  classical
  set v := w.valuation
  by_cases hx : x₁ = algebraMap F K a
  · subst hx
    simp only [sub_self, map_zero, zero_lt_one, true_and]
    exact some_sub_some_mem_polePoints_iff_of_X_eq W w h₁ hQK
  by_cases hx₁ : 1 < v x₁
  · -- `(x₁, y₁)` itself has a pole, and the constant point does not
    have hxa : v (x₁ - algebraMap F K a) = v x₁ := Valuation.map_sub_eq_of_lt_left _
      ((Valuation.IsTrivialOn.valuation_algebraMap_le_one v a).trans_lt hx₁)
    refine ⟨fun h ↦ ?_, fun h ↦ absurd (hxa ▸ h.1) (not_lt.mpr hx₁.le)⟩
    have hA : Point.some x₁ y₁ h₁ ∈ polePoints W w :=
      (mem_polePoints_iff _ _ _).mpr (Or.inr (by rwa [Point.xCoord_some]))
    have hQm := sub_mem hA h
    rw [sub_sub_cancel, some_algebraMap_eq_baseChange W hQK, baseChange_mem_polePoints_iff] at hQm
    exact absurd hQm (Point.some_ne_zero _)
  push Not at hx₁
  have hy₁ : v y₁ ≤ 1 := valuation_y_le_one_of_valuation_x_le_one v h₁.1 hx₁
  have hnegY : (W⁄K).toAffine.negY (algebraMap F K a) (algebraMap F K b) =
      algebraMap F K (W.negY a b) := W.map_negY (algebraMap F K) a b
  rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hx]
  simp only [mem_polePoints_iff, reduceCtorEq, false_or, Point.xCoord_some]
  rw [slope_of_X_ne hx, hnegY, addX]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
  rw [sub_sub, sub_sub, Valuation.one_lt_map_sq_add_mul_sub_iff v
    (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _)
    (v.map_add_le (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _)
      (v.map_add_le hx₁ (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _)))]
  exact one_lt_valuation_slope_iff W w h₁.1
    ((W.map_nonsingular (algebraMap F K).injective a b).mp hQK) hx₁ hy₁ hx

variable [DecidableEq F]

/-- **A point minus a point of `W` over `F` lies in the kernel of reduction exactly when it reduces
to that point.** For a place `w` of `K / F`, an affine point `(x₁, y₁)` of `W` over `K` and an
affine point `(a, b)` of `W` over `F`, the difference `(x₁, y₁) - (a, b)` is the point at infinity
or has `x`-coordinate with a pole at `w` exactly when `x₁ ≡ a` and `y₁ ≡ b` modulo `w`. -/
-- not `@[simp]`: `mem_polePoints_iff` is, and it unfolds the membership on the left-hand side
-- first, so this lemma would never fire and `simpNF` rejects it. Apply it, or `rw` with it.
theorem some_sub_baseChange_mem_polePoints_iff {x₁ y₁ : K}
    (h₁ : (W⁄K).toAffine.Nonsingular x₁ y₁) {a b : F} (hQ : (W⁄F).toAffine.Nonsingular a b) :
    Point.some x₁ y₁ h₁ - Point.baseChange (W' := W) F K (.some a b hQ) ∈ polePoints W w ↔
      w.valuation (x₁ - algebraMap F K a) < 1 ∧ w.valuation (y₁ - algebraMap F K b) < 1 := by
  rw [Point.baseChange, Point.map_some]
  simp only [Algebra.ofId_apply]
  exact some_sub_algebraMap_mem_polePoints_iff W w h₁ _

/-- **Every point reduces to a point of `W` over `F` at a place of degree one.** For a place `w` of
`K / F` with residue field `F`, every point of `W` over `K` differs from a point of `W` over `F` by
an element of the kernel of reduction. -/
theorem exists_sub_mem_polePoints (hw : w.degree = 1) (A : (W⁄K).toAffine.Point) :
    ∃ Q : (W⁄F).toAffine.Point, A - Point.baseChange (W' := W) F K Q ∈ polePoints W w := by
  rcases A with _ | ⟨x, y, h⟩
  · exact ⟨0, by rw [map_zero, sub_zero]; exact zero_mem _⟩
  by_cases hx : 1 < w.valuation x
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, mem_polePoints_iff, Point.xCoord_some]
    exact Or.inr hx
  push Not at hx
  -- a point with integral coordinates reduces to the residues of its coordinates
  have hy : w.valuation y ≤ 1 := valuation_y_le_one_of_valuation_x_le_one _ h.1 hx
  obtain ⟨a, ha⟩ := (w.degree_eq_one_iff_forall_exists_valuation_sub_lt_one).mp hw x
    (w.mem_integers_iff.mpr hx)
  obtain ⟨b, hb⟩ := (w.degree_eq_one_iff_forall_exists_valuation_sub_lt_one).mp hw y
    (w.mem_integers_iff.mpr hy)
  have habF : (W⁄F).toAffine.Nonsingular a b :=
    (W.map_nonsingular (algebraMap F F).injective a b).mpr
      (nonsingular_of_valuation_sub_lt_one W w h.1 ha hb)
  exact ⟨.some a b habF, (some_sub_baseChange_mem_polePoints_iff W w h habF).mpr ⟨ha, hb⟩⟩

variable {w} (hw : w.degree = 1)

/-- **The reduction of points at a place of degree one**: each point of `W` over `K` goes to the
unique point of `W` over `F` it is congruent to modulo the kernel of reduction. It is additive
because that kernel is a subgroup. -/
noncomputable def reductionOfDegreeEqOne : (W⁄K).toAffine.Point →+ (W⁄F).toAffine.Point where
  toFun A := (exists_sub_mem_polePoints W w hw A).choose
  map_zero' := eq_of_sub_mem_polePoints W w (exists_sub_mem_polePoints W w hw 0).choose_spec
    (by rw [map_zero, sub_zero]; exact zero_mem _)
  map_add' A B := by
    refine eq_of_sub_mem_polePoints W w (exists_sub_mem_polePoints W w hw (A + B)).choose_spec ?_
    rw [map_add, add_sub_add_comm]
    exact add_mem (exists_sub_mem_polePoints W w hw A).choose_spec
      (exists_sub_mem_polePoints W w hw B).choose_spec

/-- A point is congruent to its reduction modulo the kernel of reduction. -/
-- not `@[simp]`: `mem_polePoints_iff` is, and it unfolds the membership on the left-hand side
-- first, so this lemma would never fire and `simpNF` rejects it. Apply it, or `rw` with it.
theorem sub_reductionOfDegreeEqOne_mem_polePoints (A : (W⁄K).toAffine.Point) :
    A - Point.baseChange (W' := W) F K (reductionOfDegreeEqOne W hw A) ∈ polePoints W w :=
  (exists_sub_mem_polePoints W w hw A).choose_spec

/-- **The reduction of `A` is the unique point `Q` of `W` over `F` with `A - Q` in the kernel of
reduction.** -/
theorem reductionOfDegreeEqOne_eq_iff {A : (W⁄K).toAffine.Point} {Q : (W⁄F).toAffine.Point} :
    reductionOfDegreeEqOne W hw A = Q ↔ A - Point.baseChange (W' := W) F K Q ∈ polePoints W w :=
  ⟨fun h ↦ h ▸ sub_reductionOfDegreeEqOne_mem_polePoints W hw A,
    eq_of_sub_mem_polePoints W w (sub_reductionOfDegreeEqOne_mem_polePoints W hw A)⟩

/-- **An integral affine point reduces to the residues of its coordinates**: if `x ≡ a` and
`y ≡ b` modulo `w`, then `(x, y)` reduces to `(a, b)`. -/
theorem reductionOfDegreeEqOne_some {x y : K} (h : (W⁄K).toAffine.Nonsingular x y) {a b : F}
    (ha : w.valuation (x - algebraMap F K a) < 1) (hb : w.valuation (y - algebraMap F K b) < 1) :
    reductionOfDegreeEqOne W hw (.some x y h) = .some a b
      ((W.map_nonsingular (algebraMap F F).injective a b).mpr
        (nonsingular_of_valuation_sub_lt_one W w h.1 ha hb)) :=
  (reductionOfDegreeEqOne_eq_iff W hw).mpr
    ((some_sub_baseChange_mem_polePoints_iff W w h _).mpr ⟨ha, hb⟩)

/-- **Reduction fixes the points of `W` over `F`.** -/
@[simp]
theorem reductionOfDegreeEqOne_baseChange (Q : (W⁄F).toAffine.Point) :
    reductionOfDegreeEqOne W hw (Point.baseChange (W' := W) F K Q) = Q := by
  rw [reductionOfDegreeEqOne_eq_iff, sub_self]
  exact zero_mem _

/-- **The kernel of the reduction map is the kernel of reduction** `polePoints W w`. -/
@[simp]
theorem ker_reductionOfDegreeEqOne : (reductionOfDegreeEqOne W hw).ker = polePoints W w := by
  ext A
  rw [AddMonoidHom.mem_ker, reductionOfDegreeEqOne_eq_iff, map_zero, sub_zero]

end WeierstrassCurve.Affine
