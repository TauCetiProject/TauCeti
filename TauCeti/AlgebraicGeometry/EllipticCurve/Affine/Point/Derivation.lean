/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Derivation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Derivations and the sum of two points

For two nonzero points `P`, `Q` of a Weierstrass curve `W⁄K` with `P + Q ≠ 0`, and a derivation `D`
on `K` over `R`, the derivation of the `x`-coordinate of `P + Q` is expressed through the
derivations of the `x`-coordinates of `P` and `Q`: this is `Affine/Formula/Derivation.lean`'s
identity for the coordinates of the addition law, read on the points through `Point.xCoord` and
`Point.yCoord`.

## Main statements

* `WeierstrassCurve.Affine.Point.derivation_xCoord_add`: if `W_Y = 2Y + a₁X + a₃` does not vanish
  at `P` and `Q` (when their `x`-coordinates differ), then
  `D x(P + Q) = W_Y(P + Q) • (W_Y(P)⁻¹ • D x(P) + W_Y(Q)⁻¹ • D x(Q))`.
* `WeierstrassCurve.Affine.Point.inv_smul_derivation_xCoord_add`: for nonzero `P`, `Q` with
  `P + Q ≠ 0`, if `W_Y` does not vanish at `P + Q`, nor at `P` and `Q` when their `x`-coordinates
differ, then
  `W_Y(P + Q)⁻¹ • D x(P + Q) = W_Y(P)⁻¹ • D x(P) + W_Y(Q)⁻¹ • D x(Q)`.
-/

public section

open WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

variable {R K M : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module R M]
  [Module K M] {W : WeierstrassCurve R} (D : Derivation R K M) [DecidableEq K]
  {P Q : (W⁄K).toAffine.Point}

/-- **The derivation of the `x`-coordinate of a sum of points.** For nonzero points `P`, `Q` of
`W⁄K` with `P + Q ≠ 0`, at both of which `W_Y = 2Y + a₁X + a₃` does not vanish when their
`x`-coordinates differ, `D x(P + Q) = W_Y(P + Q) • (W_Y(P)⁻¹ • D x(P) + W_Y(Q)⁻¹ • D x(Q))`. -/
theorem derivation_xCoord_add (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P + Q ≠ 0)
    (huP : xCoord P ≠ xCoord Q → (W⁄K).toAffine.polynomialY.evalEval (xCoord P) (yCoord P) ≠ 0)
    (huQ : xCoord P ≠ xCoord Q → (W⁄K).toAffine.polynomialY.evalEval (xCoord Q) (yCoord Q) ≠ 0) :
    D (xCoord (P + Q)) =
      (W⁄K).toAffine.polynomialY.evalEval (xCoord (P + Q)) (yCoord (P + Q)) •
        (((W⁄K).toAffine.polynomialY.evalEval (xCoord P) (yCoord P))⁻¹ • D (xCoord P) +
          ((W⁄K).toAffine.polynomialY.evalEval (xCoord Q) (yCoord Q))⁻¹ • D (xCoord Q)) := by
  obtain ⟨x₁, y₁, h₁, rfl⟩ : ∃ x y h, P = some x y h := ⟨_, _, _, (some_coords hP).symm⟩
  obtain ⟨x₂, y₂, h₂, rfl⟩ : ∃ x y h, Q = some x y h := ⟨_, _, _, (some_coords hQ).symm⟩
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (W⁄K).toAffine.negY x₂ y₂) := fun hxy ↦
    h (add_of_Y_eq hxy.1 hxy.2)
  rw [add_some hxy]
  simp only [xCoord_some, yCoord_some] at huP huQ ⊢
  exact derivation_addX_slope D h₁.left h₂.left hxy huP huQ

/-- **The differential `dx / W_Y` is additive on points**: for nonzero points `P`, `Q` of `W⁄K` with
`P + Q ≠ 0`, if `W_Y` does not vanish at `P + Q`, nor at `P` and `Q` when their `x`-coordinates
differ, then
`W_Y(P + Q)⁻¹ • D x(P + Q) = W_Y(P)⁻¹ • D x(P) + W_Y(Q)⁻¹ • D x(Q)`. -/
theorem inv_smul_derivation_xCoord_add (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P + Q ≠ 0)
    (huP : xCoord P ≠ xCoord Q → (W⁄K).toAffine.polynomialY.evalEval (xCoord P) (yCoord P) ≠ 0)
    (huQ : xCoord P ≠ xCoord Q → (W⁄K).toAffine.polynomialY.evalEval (xCoord Q) (yCoord Q) ≠ 0)
    (hu : (W⁄K).toAffine.polynomialY.evalEval (xCoord (P + Q)) (yCoord (P + Q)) ≠ 0) :
    ((W⁄K).toAffine.polynomialY.evalEval (xCoord (P + Q)) (yCoord (P + Q)))⁻¹ •
        D (xCoord (P + Q)) =
      ((W⁄K).toAffine.polynomialY.evalEval (xCoord P) (yCoord P))⁻¹ • D (xCoord P) +
        ((W⁄K).toAffine.polynomialY.evalEval (xCoord Q) (yCoord Q))⁻¹ • D (xCoord Q) := by
  rw [derivation_xCoord_add D hP hQ h huP huQ, smul_smul, inv_mul_cancel₀ hu, one_smul]

end WeierstrassCurve.Affine.Point

end
