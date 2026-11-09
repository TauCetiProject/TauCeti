/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Height two in characteristic three

For an elliptic Weierstrass curve over a field of characteristic three, the formal group has
height two exactly when `b₂ = 0`, equivalently when the curve is supersingular. The computation
uses the tangent in the coordinates `T = -x/y`, `w = -1/y`: when `b₂ = 0`, its third intersection
parameter differs from `T` first in degree nine. This works for a general Weierstrass equation,
without completing the square or changing its coordinates. Over any commutative ring of
characteristic three, the coefficient computation gives `[3](T) = -b₄² T⁹ + ⋯` when `b₂ = 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.7 and V.3.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

section Ring

variable {R : Type*} [CommRing R] [CharP R 3] (W : WeierstrassCurve R)

private theorem tangentNumerator_mul_denom_sq (hb : W.b₂ = 0) :
    let l := PowerSeries.derivative W.formalW
    let v := W.formalW - PowerSeries.X * l
    (PowerSeries.C W.a₁ * l + PowerSeries.C W.a₂ * v + PowerSeries.C W.a₃ * l ^ 2 +
        2 * PowerSeries.C W.a₄ * l * v + 3 * PowerSeries.C W.a₆ * l ^ 2 * v) *
      W.formalInvariantDifferentialDenom ^ 2 =
        -PowerSeries.C (W.b₄ ^ 2) * W.formalW ^ 3 := by
  dsimp only
  have : CharP (PowerSeries R) 3 :=
    charP_of_injective_ringHom PowerSeries.C_injective 3
  let a := PowerSeries.C W.a₁
  let b := PowerSeries.C W.a₂
  let c := PowerSeries.C W.a₃
  let d := PowerSeries.C W.a₄
  let t := (PowerSeries.X : PowerSeries R)
  let w := W.formalW
  let l := PowerSeries.derivative w
  let D := W.formalInvariantDifferentialDenom
  have hl := W.derivative_formalW_mul_formalInvariantDifferentialDenom
  simp only [PowerSeries.smul_eq_C_mul, map_mul, map_ofNat] at hl
  have h₁ : l * D = w * (a - b * t + d * w) := by
    linear_combination (norm := (dsimp only [a, b, c, d, t, w, l, D]; ring_nf; reduce_mod_char!)) hl
  have h₂ : a ^ 2 + b = 0 := by
    have h := congrArg PowerSeries.C hb
    simp only [b₂, map_add, map_pow, map_mul, map_ofNat, map_zero] at h
    linear_combination (norm := (dsimp only [a, b, c, d, t, w, l, D]; ring_nf; reduce_mod_char!)) h
  have h₃ : D = 1 - a * t - b * t ^ 2 + c * w + d * t * w := by
    dsimp [D, a, b, c, d, t, w]
    rw [formalInvariantDifferentialDenom_def]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_ofNat]
    linear_combination (norm := (ring_nf; reduce_mod_char!))
  simp only [b₄, map_pow, map_add, map_mul, map_ofNat]
  -- In characteristic three the left side is
  -- `(a - b*t - d*w) * (l*D) * D + (c + d*t) * (l*D)^2 + b*w*D^2`.
  -- The multiplier of `h₁` is its divided difference in `l*D`, replacing that variable
  -- by `w * (a - b*t + d*w)`. The multiplier of `h₂` then eliminates `a^2` using
  -- `a^2 = -b`, and the multiplier of `h₃` replaces `D` by its displayed formula.
  -- The resulting remainder is `-(a*c - d)^2 * w^3`, as `C b₄ = a*c - d`.
  linear_combination (norm := (dsimp only [a, b, c, d, t, w, l, D]; ring_nf; reduce_mod_char!))
    ((a - b * t) * D + (c + d * t) * (l * D + w * (a - b * t + d * w)) - d * w * D) * h₁ +
    (w * (-a * t - b * t ^ 2 + c ^ 2 * w ^ 2 - c * w - d * t * w + 1)) * h₂ +
    ((a - b * t - d * w) * w * (a - b * t + d * w) +
      b * w * (D + 1 - a * t - b * t ^ 2 + c * w + d * t * w)) * h₃

private theorem exists_formalThirdRoot_diagonal (hb : W.b₂ = 0) :
    ∃ r : PowerSeries R,
      subst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R)) W.formalThirdRoot =
        PowerSeries.X + PowerSeries.X ^ 9 * r ∧
      PowerSeries.constantCoeff r = W.b₄ ^ 2 := by
  let hX : HasSubst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R)) :=
    hasSubst_of_constantCoeff_zero fun _ => PowerSeries.constantCoeff_X
  have : CharP (PowerSeries R) 3 :=
    charP_of_injective_ringHom PowerSeries.C_injective 3
  let l := PowerSeries.derivative W.formalW
  let v := W.formalW - PowerSeries.X * l
  let D := W.formalInvariantDifferentialDenom
  let d := PowerSeries.invOfUnit D 1
  let E := 1 + C W.a₂ * W.formalSlope + C W.a₄ * W.formalSlope ^ 2 +
    C W.a₆ * W.formalSlope ^ 3
  let e : PowerSeries R :=
    subst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R)) (invOfUnit E 1)
  let N := PowerSeries.C W.a₁ * l + PowerSeries.C W.a₂ * v +
    PowerSeries.C W.a₃ * l ^ 2 + 2 * PowerSeries.C W.a₄ * l * v +
      3 * PowerSeries.C W.a₆ * l ^ 2 * v
  -- The tangent numerator has a cubic factor in `w`; the two denominators are units.
  have hd : D * d = 1 := PowerSeries.mul_invOfUnit _ 1
    W.constantCoeff_formalInvariantDifferentialDenom
  have hN : N = -PowerSeries.C (W.b₄ ^ 2) * W.formalW ^ 3 * d ^ 2 := by
    have h : N * D ^ 2 = -PowerSeries.C (W.b₄ ^ 2) * W.formalW ^ 3 :=
      W.tangentNumerator_mul_denom_sq hb
    linear_combination d ^ 2 * h -
      (N * (D * d + 1)) * hd
  -- Evaluate the chord construction on the diagonal, where its slope is `w'`.
  have hv : subst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R))
      W.formalIntercept = v := by
    dsimp [v, l]
    rw [formalIntercept_def, subst_sub hX, subst_mul hX,
      PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.subst_def,
      subst_comp_subst_apply (PowerSeries.HasSubst.X (Sum.inl ())).const hX]
    simp only [subst_X hX, ← PowerSeries.subst_def, PowerSeries.X_subst,
      W.subst_X_formalSlope]
    ring
  have hroot : subst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R))
      W.formalThirdRoot = -PowerSeries.X - PowerSeries.X - N * e := by
    rw [formalThirdRoot_def, ← coe_substAlgHom hX]
    simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat,
      coe_substAlgHom, subst_X hX, subst_C]
    rw [W.subst_X_formalSlope, hv]
    simp only [N, e, E, l, PowerSeries.C_eq_algebraMap, c_eq_algebraMap]
  -- Since `w = T³ u` with `u(0) = 1`, the difference has order at least nine.
  refine ⟨PowerSeries.C (W.b₄ ^ 2) * W.formalU ^ 3 * d ^ 2 * e, ?_, ?_⟩
  · rw [hroot, hN, W.formalW_eq_X_pow_mul_formalU]
    linear_combination (norm := (ring_nf; reduce_mod_char!))
  · dsimp [d, e]
    simp only [map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_formalU, PowerSeries.constantCoeff_invOfUnit,
      Units.val_one, inv_one, one_pow, mul_one]
    rw [PowerSeries.constantCoeff_eq,
      constantCoeff_subst_of_constantCoeff_zero hX (fun _ => PowerSeries.constantCoeff_X)]
    simp

private theorem exists_nsmulSeries_two_sub_formalInverse (hb : W.b₂ = 0) :
    ∃ s : PowerSeries R,
      (formalGroup W).nsmulSeries 2 = W.formalInverse + PowerSeries.X ^ 9 * s ∧
      PowerSeries.constantCoeff s = -(W.b₄ ^ 2) := by
  obtain ⟨r, hroot, hr⟩ := W.exists_formalThirdRoot_diagonal hb
  -- Negation preserves this degree-nine congruence, with linear coefficient `-1`.
  obtain ⟨s, hs, hsc⟩ := PowerSeries.exists_subst_add_X_pow_mul W.formalInverse
    PowerSeries.constantCoeff_X r (by decide : (9 : ℕ) ≠ 0)
  refine ⟨s, ?_, ?_⟩
  · rw [W.nsmulSeries_two_formalGroup, hroot, hs, PowerSeries.X_subst]
  · rw [← W.formalGroup_addInvX, (formalGroup W).coeff_one_addInvX, hr] at hsc
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, neg_one_mul] using hsc

/-- When `b₂ = 0` in characteristic three, the tripling series vanishes below degree nine,
with degree-nine coefficient `-b₄²`. Smoothness is unnecessary for this computation. -/
theorem coeff_nsmulSeries_three_formalGroup_of_char_three (hb : W.b₂ = 0) {n : ℕ}
    (hn : n ≤ 9) :
    PowerSeries.coeff n ((formalGroup W).nsmulSeries 3) =
      if n = 9 then -(W.b₄ ^ 2) else 0 := by
  obtain ⟨s, hs', hsc⟩ := W.exists_nsmulSeries_two_sub_formalInverse hb
  -- Adding `T` cancels the inverse parameter and retains that leading coefficient.
  have h := (formalGroup W).coeff_nsmulSeries_succ_of_eq_addInvX_add_X_pow_mul
    (by simpa only [formalGroup_addInvX] using hs') (by decide : (9 : ℕ) ≠ 0) hn
  simpa only [hsc] using h

end Ring

section Field

variable {K : Type*} [Field K] [CharP K 3] (W : WeierstrassCurve K) [W.IsElliptic]

/-- In characteristic three, an elliptic curve has formal-group height two exactly when
`b₂ = 0`. -/
theorem height_formalGroup_eq_two_iff_b₂_eq_zero_of_char_three :
    (formalGroup W).height 3 = 2 ↔ W.b₂ = 0 := by
  constructor
  · intro h
    by_contra hb
    have h' := W.height_formalGroup_eq_one_iff_b₂_ne_zero_of_char_three.mpr hb
    rw [h] at h'
    exact (by decide : (2 : ℕ∞) ≠ 1) h'
  · intro hb
    have hb₄ : W.b₄ ≠ 0 := by
      intro h
      have hΔ := W.isUnit_Δ.ne_zero
      rw [Δ_of_char_three, hb, h] at hΔ
      simp at hΔ
    apply (formalGroup W).height_eq_natCast_iff.mpr
    norm_num only [Nat.reducePow]
    rw [← Nat.cast_ofNat (R := ℕ∞), PowerSeries.order_eq_nat]
    constructor
    · simpa only [W.coeff_nsmulSeries_three_formalGroup_of_char_three hb le_rfl, ite_true,
        neg_ne_zero, ne_eq, sq_eq_zero_iff] using hb₄
    · intro i hi
      simpa [ne_of_lt hi] using
        W.coeff_nsmulSeries_three_formalGroup_of_char_three hb hi.le

/-- In characteristic three, an elliptic curve has formal-group height one or two. -/
theorem height_formalGroup_eq_one_or_eq_two_of_char_three :
    (formalGroup W).height 3 = 1 ∨ (formalGroup W).height 3 = 2 := by
  by_cases hb : W.b₂ = 0
  · exact Or.inr (W.height_formalGroup_eq_two_iff_b₂_eq_zero_of_char_three.mpr hb)
  · exact Or.inl (W.height_formalGroup_eq_one_iff_b₂_ne_zero_of_char_three.mpr hb)

/-- In characteristic three, an elliptic curve is supersingular exactly when its formal group
has height two. -/
theorem isSupersingular_iff_height_formalGroup_eq_two_of_char_three :
    W.IsSupersingular 3 ↔ (formalGroup W).height 3 = 2 := by
  rw [isSupersingular_iff_j_eq_zero_of_char_three, j_eq_zero_iff_of_char_three,
    height_formalGroup_eq_two_iff_b₂_eq_zero_of_char_three]

end Field

end WeierstrassCurve
