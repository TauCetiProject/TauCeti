/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.ValuationIntegrality

/-!
# Reduction of points modulo a valuation

Let `v` be a valuation on a field `F`, with valuation ring `O` and residue field `k`, and let `W`
be a Weierstrass curve over `F` with an integral model `W_O` over `O`. Every point of `W(F)`
reduces to a `k`-point of the projective plane lying on the reduced curve `W̃ = W_O ⊗ k`: write
the point in projective coordinates `(X : Y : Z)` with `X, Y, Z ∈ O` not all in the maximal
ideal, and reduce the coordinates. This is the reduction map `E(K) → Ẽ(k)` of Silverman VII.2,
here for an arbitrary valuation and an arbitrary integral model.

The value is a class of `Fin 3 → k` modulo scaling, Mathlib's
`WeierstrassCurve.Projective.PointClass`. It need not be a nonsingular point: at a point
reducing to the singular point of a curve with bad reduction it is not.

`Point.reduction` is defined by cases rather than through a choice of primitive coordinates. An
affine point `(x, y)` with `v(x) ≤ 1` has `v(y) ≤ 1` as well, and reduces to `(x̄ : ȳ : 1)`; one
with `1 < v(x)` has `v(x) < v(y)`, so `(x : y : 1) = (x / y : 1 : 1 / y)` with `x / y` and `1 / y`
in the maximal ideal, and it reduces to `(0 : 1 : 0)`. That this agrees with reducing *any*
primitive representative is `Point.reduction_some_eq_mk`.

## Main definitions

* `WeierstrassCurve.Affine.Point.reduction`: the reduction of a point of `W(F)`.

## Main results

* `WeierstrassCurve.Affine.Point.reduction_some_eq_mk`: the reduction of a point is the reduction
  of any primitive integral representative of it.
* `WeierstrassCurve.Affine.Point.equation_of_reduction_eq`: every representative of the reduction
  lies on the reduced curve.
* `WeierstrassCurve.Affine.Point.reduction_eq_zero_iff`: a point reduces to `(0 : 1 : 0)` exactly
  when it is the point at infinity or its `x`-coordinate has a pole. This is the set `E₁(F)`, the
  kernel of reduction.
* `WeierstrassCurve.Affine.Point.reduction_neg`: reduction commutes with negation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.
-/

public section

open IsLocalRing

namespace WeierstrassCurve.Affine.Point

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [WeierstrassCurve.IsIntegral v.valuationSubring W]

/-- **The reduction of a point modulo a valuation**, as a point class of the projective plane over
the residue field. The point at infinity, and an affine point whose `x`-coordinate has a pole,
reduce to `(0 : 1 : 0)`; an affine point with integral `x`-coordinate, whose `y`-coordinate is
then integral too, reduces to `(x̄ : ȳ : 1)`. -/
noncomputable def reduction : W.Point → Projective.PointClass (ResidueField v.valuationSubring)
  | 0 => ⟦![0, 1, 0]⟧
  | some x y h =>
    if hx : v x ≤ 1 then
      ⟦![residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩,
        residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩, 1]⟧
    else ⟦![0, 1, 0]⟧

@[simp]
theorem reduction_zero : reduction v (0 : W.Point) = ⟦![0, 1, 0]⟧ := (rfl)

/-- A point with integral `x`-coordinate reduces to the reduction of its coordinates. -/
theorem reduction_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y) (hx : v x ≤ 1) :
    reduction v (some x y h) = ⟦![residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩,
      residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
        (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩, 1]⟧ := by
  simp [reduction, hx]

/-- A point whose `x`-coordinate has a pole reduces to `(0 : 1 : 0)`. -/
theorem reduction_some_of_one_lt {x y : F} (h : W.Nonsingular x y) (hx : 1 < v x) :
    reduction v (some x y h) = ⟦![0, 1, 0]⟧ := by
  simp [reduction, hx.not_ge]

/-- **Reduction is computed by any primitive representative.** If `(X : Y : Z)`, with coordinates
in the valuation ring and at least one of them a unit, represents the affine point `(x, y)`, then
the point reduces to `(X̄ : Ȳ : Z̄)`. -/
theorem reduction_some_eq_mk {x y : F} (h : W.Nonsingular x y) {X Y Z : v.valuationSubring}
    (hX : (X : F) = x * Z) (hY : (Y : F) = y * Z) (hu : IsUnit X ∨ IsUnit Y ∨ IsUnit Z) :
    reduction v (some x y h) = ⟦![residue _ X, residue _ Y, residue _ Z]⟧ := by
  have hle : ∀ a : v.valuationSubring, v a ≤ 1 := fun a ↦ (v.mem_valuationSubring_iff _).mp a.2
  have isUnit_iff : ∀ {a : v.valuationSubring}, IsUnit a ↔ v a = 1 :=
    (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one
  rcases le_or_gt (v x) 1 with hx | hx
  · -- `x` and `y` are integral, so `Z` must be the unit and `(X : Y : Z) = Z • (x : y : 1)`.
    have hy := valuation_y_le_one_of_valuation_x_le_one v h.left hx
    set a : v.valuationSubring := ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩
    set b : v.valuationSubring := ⟨y, (v.mem_valuationSubring_iff y).mpr hy⟩
    have hXa : X = a * Z := Subtype.ext hX
    have hYb : Y = b * Z := Subtype.ext hY
    have hZ : IsUnit Z := by
      by_contra hZ
      have hZ1 : v Z < 1 := lt_of_le_of_ne (hle Z) (isUnit_iff.not.mp hZ)
      have hlt : ∀ c : v.valuationSubring, v (c * Z : v.valuationSubring) < 1 := fun c ↦ by
        rw [Subring.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) hZ1
      rcases hu with hX' | hY' | hZ'
      · exact (hlt a).ne (hXa ▸ isUnit_iff.mp hX')
      · exact (hlt b).ne (hYb ▸ isUnit_iff.mp hY')
      · exact hZ hZ'
    rw [reduction_some_of_valuation_le_one v h hx, hXa, hYb, map_mul, map_mul,
      ← Projective.smul_eq _ (hZ.map (residue v.valuationSubring))]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm, a, b]
  · -- `x` has a pole, so `X` and `Z` lie in the maximal ideal, `Y` is the unit, and
    -- `(X : Y : Z)` reduces to `Ȳ • (0 : 1 : 0)`.
    rw [reduction_some_of_one_lt v h hx]
    have hxy := valuation_x_lt_valuation_y v h.left hx
    have hY1 : v (Y : F) ≤ 1 := hle Y
    have hZ1 : v (Z : F) < 1 := by
      by_contra hZ
      rw [not_lt] at hZ
      rw [hY, map_mul] at hY1
      exact absurd hY1 (not_le.mpr (lt_of_lt_of_le (hx.trans hxy) (le_mul_of_one_le_right' hZ)))
    have hX1 : v (X : F) < 1 := by
      rw [hX, map_mul]
      rcases eq_or_ne (v (Z : F)) 0 with h0 | h0
      · rw [h0, mul_zero]; exact zero_lt_one
      · refine lt_of_lt_of_le ?_ hY1
        rw [hY, map_mul]
        exact mul_lt_mul_of_pos_right hxy (zero_lt_iff.mpr h0)
    have hYu : IsUnit Y := by
      rcases hu with hX' | hY' | hZ'
      · exact absurd (isUnit_iff.mp hX') hX1.ne
      · exact hY'
      · exact absurd (isUnit_iff.mp hZ') hZ1.ne
    rw [(residue_eq_zero_iff _).mpr ((Valuation.mem_maximalIdeal_iff (v := v)).mpr hX1),
      (residue_eq_zero_iff _).mpr ((Valuation.mem_maximalIdeal_iff (v := v)).mpr hZ1),
      ← Projective.smul_eq _ (hYu.map (residue v.valuationSubring))]
    congr 1
    ext i
    fin_cases i <;> simp

/-- **The kernel of reduction.** A point reduces to `(0 : 1 : 0)` exactly when it is the point at
infinity or its `x`-coordinate has a pole; these points form `E₁(F)`. -/
theorem reduction_eq_zero_iff (P : W.Point) :
    reduction v P = ⟦![0, 1, 0]⟧ ↔ P = 0 ∨ 1 < v P.xCoord := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← zero_def]
  · rcases le_or_gt (v x) 1 with hx | hx
    · simp only [reduction_some_of_valuation_le_one v h hx, xCoord_some, hx.not_gt, or_false]
      exact ⟨fun h0 ↦ (Projective.not_equiv_of_Z_eq_zero_right one_ne_zero rfl
        (Quotient.exact h0)).elim, fun h0 ↦ nomatch h0⟩
    · simp [reduction_some_of_one_lt v h hx, hx]

/-- **The reduction lies on the reduced curve**: every representative of the reduction of a point
satisfies the projective equation of the integral model read over the residue field. -/
theorem equation_of_reduction_eq {P : W.Point} {Q : Fin 3 → ResidueField v.valuationSubring}
    (hQ : reduction v P = ⟦Q⟧) :
    ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.Equation
      Q := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← zero_def, reduction_zero] at hQ
    exact (Projective.equation_of_equiv (Quotient.exact hQ)).mp Projective.equation_zero
  · rcases le_or_gt (v x) 1 with hx | hx
    · rw [reduction_some_of_valuation_le_one v h hx] at hQ
      refine (Projective.equation_of_equiv (Quotient.exact hQ)).mp ?_
      rw [Projective.equation_some]
      -- the coordinates satisfy the equation of the integral model, which then reduces
      have hM := h.left
      rw [← baseChange_integralModel_eq v.valuationSubring W] at hM
      exact (((integralModel v.valuationSubring W).toAffine.map_equation
        (IsFractionRing.injective v.valuationSubring F) ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩
        ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩).mp hM).map _
    · rw [reduction_some_of_one_lt v h hx] at hQ
      exact (Projective.equation_of_equiv (Quotient.exact hQ)).mp Projective.equation_zero

/-- **Reduction commutes with negation**, the negation on the right being that of the reduced
curve. -/
theorem reduction_neg (P : W.Point) :
    reduction v (-P) =
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.negMap
        (reduction v P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← zero_def, neg_zero, reduction_zero,
      Projective.negMap_of_Z_eq_zero Projective.nonsingular_zero rfl]
  · rw [neg_some]
    rcases le_or_gt (v x) 1 with hx | hx
    · set M := integralModel v.valuationSubring W
      -- the negated `y`-coordinate, computed in the valuation ring
      set c : v.valuationSubring := -⟨y, (v.mem_valuationSubring_iff y).mpr
        (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩ -
          M.a₁ * ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩ - M.a₃
      have hc : ((c : v.valuationSubring) : F) = W.negY x y * 1 := by
        simp [c, Affine.negY, ← integralModel_a₁_eq v.valuationSubring W,
          ← integralModel_a₃_eq v.valuationSubring W, M]
      rw [reduction_some_eq_mk v _ (X := ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩) (Y := c)
        (Z := 1) (by simp) hc (Or.inr (Or.inr isUnit_one)),
        reduction_some_of_valuation_le_one v h hx, Projective.negMap_eq]
      congr 1
      ext i
      fin_cases i <;> simp [Projective.neg, Projective.negY, c, M]
    · rw [reduction_some_of_one_lt v _ hx, reduction_some_of_one_lt v h hx,
        Projective.negMap_of_Z_eq_zero Projective.nonsingular_zero rfl]

end WeierstrassCurve.Affine.Point

end
