/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Injectivity
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Line
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Line
import TauCeti.Analysis.Normed.Field.ZPowers
import TauCeti.Algebra.Group.MapMulMulEqOne

/-!
# The Tate uniformisation is a group homomorphism

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. This file proves
that the Tate uniformisation `Kˣ / q^ℤ → E_q(K)` sends products of parameters to sums of points
(`TauCeti.tateUniformization_mul`), and bundles it as an injective homomorphism out of
`Additive (Kˣ / q^ℤ)`. The same holds over every complete normed extension `L` of `K`, for the
map `Lˣ / q^ℤ → E_q(L)`.

Let `P` denote the uniformisation. For classes `x, y` such that `x`, `y` and `(x y)⁻¹` are
pairwise distinct and different from `1`, there is a line `Y = μ X + ν` through `P x`, `P y` and
`P (x y)⁻¹` (`TauCeti.exists_tateQuotientCoordinates_snd_eq_iff`), and the three points have
pairwise distinct first coordinates (`TauCeti.tateQuotientCoordinates_fst_eq_iff`). So the three
points sum to zero (`WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero`).

The remaining triples with product `1`, including the tangent case `x = y`, follow from this
secant case by `TauCeti.map_mul_mul_eq_one_of_pairwise_ne`, which moves a pair into general
position with an auxiliary parameter. This needs infinitely many squares in `Kˣ / q^ℤ`
(`TauCeti.infinite_range_sq_quotient_zpowers`). Neither a discrete value group nor any restriction
on the characteristic is needed.

## Main results

* `TauCeti.tateUniformization_mul`: the Tate uniformisation is additive.
* `TauCeti.tateUniformizationHom`: the injective homomorphism `Additive (Kˣ / q^ℤ) →+ E_q(K)`.
* `TauCeti.tateUniformizationBaseChange_mul`, `TauCeti.tateUniformizationBaseChangeHom`: the
  same over a complete normed extension `L`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The secant case.** If `x`, `y` and `z` are pairwise distinct, different from `1`, and
`x y z = 1`, then `P x + P y + P z = 0`: the three points lie on the line through `P x` and
`P y`. -/
private theorem tateUniformization_add_add_eq_zero [DecidableEq K] (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y z : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1) (hy : y ≠ 1)
    (hz : z ≠ 1) (hne : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hxyz : x * y * z = 1) :
    tateUniformization q hq x + tateUniformization q hq y + tateUniformization q hq z = 0 := by
  obtain rfl : z = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxyz).symm
  have hxy : x * y ≠ 1 := fun h ↦ hz (by rw [h, inv_one])
  obtain ⟨μ, ν, hline⟩ := exists_tateQuotientCoordinates_snd_eq_iff q hq hx hy hxy
  have d₁₂ : (tateQuotientCoordinates q x).1 ≠ (tateQuotientCoordinates q y).1 := by
    rw [Ne, tateQuotientCoordinates_fst_eq_iff q hq hx hy]
    rintro (h | rfl)
    · exact hne h
    · exact hxy (inv_mul_cancel y)
  have d₃₁ : (tateQuotientCoordinates q (x * y)⁻¹).1 ≠ (tateQuotientCoordinates q x).1 := by
    rw [Ne, tateQuotientCoordinates_fst_eq_iff q hq hz hx]
    rintro (h | h)
    · exact hxz h.symm
    · have h' : x * y = x := inv_inj.mp h
      exact hy (by rw [← inv_mul_cancel_left x y, h', inv_mul_cancel])
  have d₃₂ : (tateQuotientCoordinates q (x * y)⁻¹).1 ≠ (tateQuotientCoordinates q y).1 := by
    rw [Ne, tateQuotientCoordinates_fst_eq_iff q hq hz hy]
    rintro (h | h)
    · exact hyz h.symm
    · have h' : x * y = y := inv_inj.mp h
      exact hx (by rw [← mul_inv_cancel_right x y, h', mul_inv_cancel])
  -- the images of `x`, `y` and `(x y)⁻¹` lie on the line and sum to zero
  rw [tateUniformization_of_ne_one q hq hx, tateUniformization_of_ne_one q hq hy,
    tateUniformization_of_ne_one q hq hz]
  exact Point.some_add_some_add_some_eq_zero _ _ _ d₁₂ d₃₁.symm d₃₂.symm
    ((hline x hx).mpr (.inl rfl)) ((hline y hy).mpr (.inr (.inl rfl)))
    ((hline _ hz).mpr (.inr (.inr rfl)))

/-- **The Tate uniformisation is additive.** For a complete non-archimedean normed field `K` and
`q ∈ Kˣ` with `‖q‖ < 1`, the map `Kˣ / q^ℤ → E_q(K)` sends products of parameters to sums of
points. -/
@[simp]
theorem tateUniformization_mul [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x y : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformization q hq (x * y) = tateUniformization q hq x + tateUniformization q hq y := by
  -- the secant case extends to all triples with product `1`, in the multiplicative target
  have h : tateUniformization q hq x + tateUniformization q hq y +
      tateUniformization q hq (x * y)⁻¹ = 0 :=
    map_mul_mul_eq_one_of_pairwise_ne
      (f := fun w ↦ Multiplicative.ofAdd (tateUniformization q hq w))
      (infinite_range_sq_quotient_zpowers q hq)
      (congrArg Multiplicative.ofAdd (tateUniformization_one q hq))
      (fun w ↦ congrArg Multiplicative.ofAdd (tateUniformization_inv q hq w))
      (fun _ _ _ ha hb hc hab hac hbc habc ↦ congrArg Multiplicative.ofAdd
        (tateUniformization_add_add_eq_zero q hq ha hb hc hab hac hbc habc))
      (mul_inv_cancel (x * y))
  rw [tateUniformization_inv, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

/-- **The Tate uniformisation as a group homomorphism** `Kˣ / q^ℤ → E_q(K)`, written additively on
the source. It is injective (`tateUniformizationHom_injective`). -/
noncomputable def tateUniformizationHom [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Additive (Kˣ ⧸ Subgroup.zpowers q) →+ (tateCurveAt q hq).toAffine.Point where
  toFun x := tateUniformization q hq x.toMul
  map_zero' := tateUniformization_one q hq
  map_add' x y := tateUniformization_mul q hq x.toMul y.toMul

@[simp]
theorem tateUniformizationHom_apply [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Additive (Kˣ ⧸ Subgroup.zpowers q)) :
    tateUniformizationHom q hq x = tateUniformization q hq x.toMul :=
  (rfl)

/-- **The Tate uniformisation homomorphism is injective.** -/
theorem tateUniformizationHom_injective [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Injective (tateUniformizationHom q hq) :=
  (tateUniformization_injective q hq).comp Additive.toMul.injective

/-! ### The uniformisation over an extension -/

section Extension

variable (L : Type*) [NormedField L] [NormedAlgebra K L] [CompleteSpace L] [IsUltrametricDist L]
  [DecidableEq L]

/-- **The Tate uniformisation over an extension is additive.** For a complete normed extension `L`
of `K`, the map `Lˣ / q^ℤ → E_q(L)` sends products of parameters to sums of points. -/
@[simp]
theorem tateUniformizationBaseChange_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x y : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateUniformizationBaseChange L q hq (x * y) =
      tateUniformizationBaseChange L q hq x + tateUniformizationBaseChange L q hq y := by
  rw [tateUniformizationBaseChange_def, tateUniformizationBaseChange_def,
    tateUniformizationBaseChange_def, tateUniformization_mul]
  exact map_add (AddEquiv.cast (M := fun W : WeierstrassCurve L ↦ W.toAffine.Point)
    (baseChange_tateCurveAt L q hq).symm) _ _

/-- **The Tate uniformisation over an extension as a group homomorphism** `Lˣ / q^ℤ → E_q(L)`,
written additively on the source. It is injective
(`tateUniformizationBaseChangeHom_injective`). -/
noncomputable def tateUniformizationBaseChangeHom (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Additive (Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) →+
      ((tateCurveAt q hq)⁄L).toAffine.Point where
  toFun x := tateUniformizationBaseChange L q hq x.toMul
  map_zero' := tateUniformizationBaseChange_one L q hq
  map_add' x y := tateUniformizationBaseChange_mul L q hq x.toMul y.toMul

@[simp]
theorem tateUniformizationBaseChangeHom_apply (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Additive (Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q))) :
    tateUniformizationBaseChangeHom L q hq x = tateUniformizationBaseChange L q hq x.toMul :=
  (rfl)

/-- **The Tate uniformisation homomorphism over an extension is injective.** -/
theorem tateUniformizationBaseChangeHom_injective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Injective (tateUniformizationBaseChangeHom L q hq) :=
  (tateUniformizationBaseChange_injective L q hq).comp Additive.toMul.injective

end Extension

end TauCeti

end
