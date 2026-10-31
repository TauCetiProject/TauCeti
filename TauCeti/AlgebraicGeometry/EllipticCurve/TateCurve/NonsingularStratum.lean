/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Strata
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Ring.Ultra
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Surjectivity of the Tate uniformisation onto the nonsingular stratum

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. Modulo the maximal
ideal, the Tate curve `E_q : y² + xy = x³ + a₄(q) x + a₆(q)` is the nodal cubic `y² + xy = x³`,
and its points with `‖x‖ = 1` are the points whose reduction is a nonsingular point other than the
point at infinity. This file shows that every such point is the image of a parameter `u` on the
unit circle with `‖1 - u‖ = 1`. Together with the converse `norm_tateUniformizationX_eq_one` from
`TateCurve.Strata`, a point of `E_q(K)` with first coordinate `x` is the image of such a parameter
exactly when `‖x‖ = 1` (`exists_tateUniformization_eq_some_iff_norm_eq_one`).
Nothing here assumes a discrete value group or restricts the characteristic.

On the nodal cubic the parametrisation `u ↦ (u / (1 - u)², u² / (1 - u)³)` is inverted by
`(x, y) ↦ y / (x + y)`. For a point `(x, y)` of `E_q(K)` with `‖x‖ = 1` put `c = y / (x + y)`; then
`‖c‖ = ‖1 - c‖ = 1`. The parameter is the fixed point of

`u ↦ c - (1 - u)³ / u · ((1 - c) (Y(u) - u² / (1 - u)³) - c (X(u) - u / (1 - u)²))`

on the closed set `{u : ‖u‖ = ‖1 - u‖ = 1}`. This map is a contraction with constant `‖q‖`, because
the differences between the Tate coordinates and the nodal parametrisation are `‖q‖`-Lipschitz on
the unit circle (`norm_tateUniformizationX_sub_sub_le`, `norm_tateUniformizationY_sub_sub_le`).
At the fixed point `x Y(u) = y X(u)`, so `(x, y)` and `(X(u), Y(u))` lie on a common line through
the origin. Such a line meets `E_q(K)` in at most one point with first coordinate of norm one, so
the two points agree.

## Main results

* `TauCeti.norm_tateUniformizationX_sub_sub_le`, `TauCeti.norm_tateUniformizationY_sub_sub_le`:
  on the unit circle the differences between the Tate coordinates and the nodal parametrisation
  are Lipschitz with constant `‖q‖`.
* `TauCeti.exists_tateUniformizationX_eq_and_tateUniformizationY_eq`: every solution `(x, y)` of
  the Tate equation with `‖x‖ = 1` is `(X(u), Y(u))` for some `u` with `‖u‖ = ‖1 - u‖ = 1`.
* `TauCeti.exists_tateUniformization_eq_some_iff_norm_eq_one`: an affine point of `E_q(K)` is the
  image of a parameter with `‖u‖ = ‖1 - u‖ = 1` exactly when its first coordinate has norm one.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, V.3–V.4.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

namespace TauCeti

open WeierstrassCurve.Affine

variable {K : Type*} [NormedField K]

/-! ### Convergence of the one-sided series -/

private theorem negTerm_eq (t : K) :
    -t / (1 - t) ^ 3 = -(t ^ 2 / (1 - t) ^ 3 + t / (1 - t) ^ 2) := by
  rcases eq_or_ne (1 - t) 0 with h | h
  · simp [h]
  · field_simp
    ring

section Summable

variable [CompleteSpace K]

private theorem summable_xTerm_succ (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    Summable fun n : ℕ ↦ (q : K) ^ (n + 1) * u / (1 - (q : K) ^ (n + 1) * u) ^ 2 := by
  simpa only [Function.comp_def, zpow_natCast] using
    (summable_tateUniformizationX q hq u).comp_injective
      (i := fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ)) fun _ _ h ↦ by simpa using h

private theorem summable_yTerm_succ (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    Summable fun n : ℕ ↦ ((q : K) ^ (n + 1) * u) ^ 2 / (1 - (q : K) ^ (n + 1) * u) ^ 3 := by
  simpa only [Function.comp_def, zpow_natCast] using
    (summable_tateUniformizationY q hq u).comp_injective
      (i := fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ)) fun _ _ h ↦ by simpa using h

private theorem summable_negTerm_succ (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    Summable fun n : ℕ ↦ -((q : K) ^ (n + 1) * u) / (1 - (q : K) ^ (n + 1) * u) ^ 3 := by
  simpa only [negTerm_eq] using
    ((summable_yTerm_succ q hq u).add (summable_xTerm_succ q hq u)).neg

end Summable

variable [IsUltrametricDist K]

/-! ### Lipschitz estimates for the terms of the coordinate series -/

/-- A difference of the form `(t - t') P / ((1 - t)ᵏ (1 - t')ᵏ)` with `‖t‖, ‖t'‖ < 1` and
`‖P‖ ≤ 1` has norm at most `‖t - t'‖`. -/
private theorem norm_sub_le_of_eq_mul_div {t t' a a' P : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1)
    {k : ℕ} (h : a - a' = (t - t') * P / ((1 - t) ^ k * (1 - t') ^ k)) (hP : ‖P‖ ≤ 1) :
    ‖a - a'‖ ≤ ‖t - t'‖ := by
  rw [h, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hP

private theorem norm_xTerm_sub_le {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t / (1 - t) ^ 2 - t' / (1 - t') ^ 2‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  refine norm_sub_le_of_eq_mul_div ht ht' (P := 1 - t * t') (k := 2) (by field_simp; ring)
    (Subring.mem_unitClosedBall.mp ?_)
  have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
  have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
  apply_rules [sub_mem, mul_mem, one_mem]

private theorem norm_yTerm_sub_le {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t ^ 2 / (1 - t) ^ 3 - t' ^ 2 / (1 - t') ^ 3‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  refine norm_sub_le_of_eq_mul_div ht ht'
    (P := t + t' - t * t' - t * t' - t * t' + t ^ 2 * t' ^ 2) (k := 3) (by field_simp; ring)
    (Subring.mem_unitClosedBall.mp ?_)
  have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
  have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
  apply_rules [add_mem, sub_mem, mul_mem, pow_mem]

private theorem norm_negTerm_sub_le {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖-t / (1 - t) ^ 3 - -t' / (1 - t') ^ 3‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  refine norm_sub_le_of_eq_mul_div ht ht'
    (P := -(1 - t * t' - t * t' - t * t' + t * t' * (t + t'))) (k := 3) (by field_simp; ring)
    (Subring.mem_unitClosedBall.mp ?_)
  have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
  have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
  apply_rules [neg_mem, add_mem, sub_mem, mul_mem, one_mem]

/-! ### Lipschitz estimates for the Tate coordinates on the unit circle -/

variable [CompleteSpace K]

/-- **The first Tate coordinate is the nodal parametrisation up to a `‖q‖`-Lipschitz error.** On
the unit circle, `u ↦ X(u) - u / (1 - u)²` is Lipschitz with constant `‖q‖`. -/
theorem norm_tateUniformizationX_sub_sub_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (hu' : ‖(u' : K)‖ = 1) :
    ‖(tateUniformizationX q u - u / (1 - u) ^ 2) -
        (tateUniformizationX q u' - u' / (1 - u') ^ 2)‖ ≤ ‖(q : K)‖ * ‖(u : K) - u'‖ := by
  have e (a A B s a' A' B' : K) :
      a + A + B - 2 * s - a - (a' + A' + B' - 2 * s - a') = (A - A') + (B - B') := by ring
  have hs (v : Kˣ) := summable_xTerm_succ q hq v⁻¹
  simp only [Units.val_inv_eq_inv_val] at hs
  have hqw (w : K) (hw : ‖w‖ = 1) : ‖(q : K) * w‖ < 1 := by rwa [norm_mul, hw, mul_one]
  have hinv : ‖(q : K) * ((u : K)⁻¹ - (u' : K)⁻¹)‖ = ‖(q : K)‖ * ‖(u : K) - u'‖ := by
    rw [norm_mul]
    simpa [dist_eq_norm, hu, hu'] using dist_inv_inv₀ u.ne_zero u'.ne_zero
  rw [tateUniformizationX_eq_tsum_nat q hq u, tateUniformizationX_eq_tsum_nat q hq u', e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [← norm_mul]
    exact norm_tsum_sub_tsum_le_norm_mul (fun w ↦ w / (1 - w) ^ 2) (fun _ _ ↦ norm_xTerm_sub_le)
      hq.le (hqw _ hu) (hqw _ hu') (summable_xTerm_succ q hq u) (summable_xTerm_succ q hq u')
  · rw [← hinv]
    exact norm_tsum_sub_tsum_le_norm_mul (fun w ↦ w / (1 - w) ^ 2) (fun _ _ ↦ norm_xTerm_sub_le)
      hq.le
      (hqw _ (by rw [norm_inv, hu, inv_one])) (hqw _ (by rw [norm_inv, hu', inv_one])) (hs u)
      (hs u')

/-- **The second Tate coordinate is the nodal parametrisation up to a `‖q‖`-Lipschitz error.** On
the unit circle, `u ↦ Y(u) - u² / (1 - u)³` is Lipschitz with constant `‖q‖`. -/
theorem norm_tateUniformizationY_sub_sub_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (hu' : ‖(u' : K)‖ = 1) :
    ‖(tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3) -
        (tateUniformizationY q u' - (u' : K) ^ 2 / (1 - u') ^ 3)‖ ≤
      ‖(q : K)‖ * ‖(u : K) - u'‖ := by
  have e (a A B s a' A' B' : K) :
      a + A + B + s - a - (a' + A' + B' + s - a') = (A - A') + (B - B') := by ring
  have hs (v : Kˣ) := summable_negTerm_succ q hq v⁻¹
  simp only [Units.val_inv_eq_inv_val] at hs
  have hqw (w : K) (hw : ‖w‖ = 1) : ‖(q : K) * w‖ < 1 := by rwa [norm_mul, hw, mul_one]
  have hinv : ‖(q : K) * ((u : K)⁻¹ - (u' : K)⁻¹)‖ = ‖(q : K)‖ * ‖(u : K) - u'‖ := by
    rw [norm_mul]
    simpa [dist_eq_norm, hu, hu'] using dist_inv_inv₀ u.ne_zero u'.ne_zero
  rw [tateUniformizationY_eq_tsum_nat q hq u, tateUniformizationY_eq_tsum_nat q hq u', e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [← norm_mul]
    exact norm_tsum_sub_tsum_le_norm_mul (fun w ↦ w ^ 2 / (1 - w) ^ 3) (fun _ _ ↦ norm_yTerm_sub_le)
      hq.le (hqw _ hu) (hqw _ hu') (summable_yTerm_succ q hq u) (summable_yTerm_succ q hq u')
  · rw [← hinv]
    exact norm_tsum_sub_tsum_le_norm_mul (fun w ↦ -w / (1 - w) ^ 3) (fun _ _ ↦ norm_negTerm_sub_le)
      hq.le
      (hqw _ (by rw [norm_inv, hu, inv_one])) (hqw _ (by rw [norm_inv, hu', inv_one])) (hs u)
      (hs u')

/-! ### Solving for the parameter by a contraction -/

/-- The error term of the contraction: the combination `(1 - c) Y(u) - c X(u)` with the nodal
parametrisation subtracted from each coordinate. -/
private noncomputable def tateErr (q u : Kˣ) (c : K) : K :=
  (1 - c) * (tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3) -
    c * (tateUniformizationX q u - u / (1 - u) ^ 2)

private theorem norm_tateErr_le (q u : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) : ‖tateErr q u c‖ ≤ ‖(q : K)‖ := by
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_of_le_one_left (norm_nonneg _) hc'
      |>.trans (norm_tateUniformizationY_sub_le_of_norm_eq_one q u hq hu)
  · exact mul_le_of_le_one_left (norm_nonneg _) hc
      |>.trans (norm_tateUniformizationX_sub_le_of_norm_eq_one q u hq hu)

private theorem norm_tateErr_sub_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) (hu' : ‖(u' : K)‖ = 1) :
    ‖tateErr q u c - tateErr q u' c‖ ≤ ‖(q : K)‖ * ‖(u : K) - u'‖ := by
  have e : tateErr q u c - tateErr q u' c =
      (1 - c) * ((tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3) -
        (tateUniformizationY q u' - (u' : K) ^ 2 / (1 - u') ^ 3)) -
      c * ((tateUniformizationX q u - u / (1 - u) ^ 2) -
        (tateUniformizationX q u' - u' / (1 - u') ^ 2)) := by
    rw [tateErr, tateErr]
    ring
  rw [e]
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_of_le_one_left (norm_nonneg _) hc'
      |>.trans (norm_tateUniformizationY_sub_sub_le q u u' hq hu hu')
  · exact mul_le_of_le_one_left (norm_nonneg _) hc
      |>.trans (norm_tateUniformizationX_sub_sub_le q u u' hq hu hu')

omit [CompleteSpace K] in
/-- The factor `(1 - u)³ / u` of the contraction is `1`-Lipschitz on the unit circle. -/
private theorem norm_one_sub_pow_three_div_sub_le {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖(1 - v) ^ 3 / v - (1 - w) ^ 3 / w‖ ≤ ‖v - w‖ := by
  have h₀ : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have h₀' : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have e : (1 - v) ^ 3 / v - (1 - w) ^ 3 / w =
      (w - v) * (1 - v * w - v * w - v * w + v * w * (v + w)) / (v * w) := by
    field_simp
    ring
  have h₃ : v ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr hv.le
  have h₄ : w ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr hw.le
  have hP : 1 - v * w - v * w - v * w + v * w * (v + w) ∈ Subring.unitClosedBall K := by
    apply_rules [add_mem, sub_mem, mul_mem, one_mem]
  rw [e, norm_div, norm_mul, norm_mul, hv, hw, mul_one, div_one, norm_sub_rev]
  exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp hP)

/-- One step of the contraction, `u ↦ c - (1 - u)³ / u · tateErr q u c`. -/
private noncomputable def tateStep (q u : Kˣ) (c : K) : K :=
  c - (1 - (u : K)) ^ 3 / u * tateErr q u c

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_one_sub_pow_three_div {u : K} (hu : ‖u‖ = 1) (h : ‖1 - u‖ = 1) :
    ‖(1 - u) ^ 3 / u‖ = 1 := by
  rw [norm_div, norm_pow, hu, h, one_pow, div_one]

/-- The contraction moves every parameter of the stratum to within `‖q‖` of `c`. -/
private theorem norm_tateStep_sub_le (q u : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) (h : ‖1 - (u : K)‖ = 1) :
    ‖tateStep q u c - c‖ ≤ ‖(q : K)‖ := by
  rw [tateStep, sub_sub_cancel_left, norm_neg, norm_mul, norm_one_sub_pow_three_div hu h, one_mul]
  exact norm_tateErr_le q u hq hc hc' hu

/-- The contraction is `‖q‖`-Lipschitz on the stratum. -/
private theorem norm_tateStep_sub_tateStep_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K}
    (hc : ‖c‖ ≤ 1) (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) (hu' : ‖(u' : K)‖ = 1)
    (h' : ‖1 - (u' : K)‖ = 1) :
    ‖tateStep q u c - tateStep q u' c‖ ≤ ‖(q : K)‖ * ‖(u : K) - u'‖ := by
  have e : tateStep q u c - tateStep q u' c =
      (1 - (u' : K)) ^ 3 / u' * (tateErr q u' c - tateErr q u c) +
        ((1 - (u' : K)) ^ 3 / u' - (1 - (u : K)) ^ 3 / u) * tateErr q u c := by
    rw [tateStep, tateStep]
    ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
    rw [norm_mul, norm_sub_rev (u : K)]
  · rw [norm_one_sub_pow_three_div hu' h', one_mul]
    exact norm_tateErr_sub_le q u' u hq hc hc' hu' hu
  · rw [mul_comm]
    exact mul_le_mul (norm_tateErr_le q u hq hc hc' hu)
      (norm_one_sub_pow_three_div_sub_le hu' hu) (norm_nonneg _) (norm_nonneg _)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- At a fixed point of the contraction, `(1 - c) Y(u) = c X(u)`. -/
private theorem one_sub_mul_tateUniformizationY_eq_of_tateStep_eq (q u : Kˣ) {c : K}
    (h : 1 - (u : K) ≠ 0) (hu : tateStep q u c = u) :
    (1 - c) * tateUniformizationY q u = c * tateUniformizationX q u := by
  -- multiplying by `(1 - u)³ / u ≠ 0` turns the fixed-point equation into the claim
  have key : (1 - (u : K)) ^ 3 / u *
      ((1 - c) * tateUniformizationY q u - c * tateUniformizationX q u) =
      (c - tateStep q u c) + ((1 - c) * u - c * (1 - u)) := by
    rw [tateStep, tateErr]
    field_simp [u.ne_zero]
    ring
  rw [hu] at key
  have hm : (1 - (u : K)) ^ 3 / u ≠ 0 := div_ne_zero (pow_ne_zero _ h) u.ne_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp (key.trans (by ring))).resolve_left hm)

/-- **Solving for the parameter.** For `‖c‖ = ‖1 - c‖ = 1` there is a parameter `u` with
`‖u‖ = ‖1 - u‖ = 1` and `(1 - c) Y(u) = c X(u)`. It is the fixed point of the contraction
`tateStep q · c` of the complete set `{u : ‖u‖ = ‖1 - u‖ = 1}`. -/
private theorem exists_one_sub_mul_tateUniformizationY_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K}
    (hc : ‖c‖ = 1) (hc' : ‖1 - c‖ = 1) :
    ∃ u : Kˣ, ‖(u : K)‖ = 1 ∧ ‖1 - (u : K)‖ = 1 ∧
      (1 - c) * tateUniformizationY q u = c * tateUniformizationX q u := by
  set S : Set K := {u | ‖u‖ = 1 ∧ ‖1 - u‖ = 1}
  have hS : IsClosed S := (isClosed_eq continuous_norm continuous_const).inter
    (isClosed_eq (continuous_const.sub continuous_id).norm continuous_const)
  have : CompleteSpace S := hS.completeSpace_coe
  have : Nonempty S := ⟨⟨c, hc, hc'⟩⟩
  have hne (v : S) : (v : K) ≠ 0 := norm_ne_zero_iff.mp (by rw [v.2.1]; exact one_ne_zero)
  let U : S → Kˣ := fun v ↦ Units.mk0 v (hne v)
  have hU (v : S) : ‖((U v : Kˣ) : K)‖ = 1 ∧ ‖1 - ((U v : Kˣ) : K)‖ = 1 := v.2
  -- the step stays in `S`: it moves by less than `1` from `c ∈ S`
  have hstep (v : S) : tateStep q (U v) c ∈ S := by
    have h := (norm_tateStep_sub_le q _ hq hc.le hc'.le (hU v).1 (hU v).2).trans_lt hq
    refine ⟨?_, ?_⟩
    · rw [← hc]
      exact (IsUltrametricDist.norm_eq_of_norm_sub_lt_left (by rwa [norm_sub_rev, hc])).symm
    · rw [← hc']
      refine (IsUltrametricDist.norm_eq_of_norm_sub_lt_left ?_).symm
      rwa [sub_sub_sub_cancel_left, hc']
  have hF : ContractingWith ‖(q : K)‖₊ (fun v : S ↦ (⟨tateStep q (U v) c, hstep v⟩ : S)) := by
    refine ⟨by rwa [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one],
      LipschitzWith.of_dist_le_mul fun v w ↦ ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, coe_nnnorm]
    exact norm_tateStep_sub_tateStep_le q _ _ hq hc.le hc'.le (hU v).1 (hU w).1 (hU w).2
  set v := ContractingWith.fixedPoint _ hF
  have hv : tateStep q (U v) c = v := congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hF)
  exact ⟨U v, (hU v).1, (hU v).2, one_sub_mul_tateUniformizationY_eq_of_tateStep_eq q (U v)
    (norm_ne_zero_iff.mp (by rw [(hU v).2]; exact one_ne_zero)) hv⟩

/-! ### Points on a line through the origin -/

omit [CompleteSpace K] in
/-- On a curve `y² + xy = x³ + A₄x + A₆` with `‖A₄‖, ‖A₆‖ < 1`, a solution with `‖x‖ = 1` has
`‖y‖ = ‖x + y‖ = 1`. -/
private theorem norm_eq_one_of_equation {A₄ A₆ x y : K} (hA₄ : ‖A₄‖ < 1) (hA₆ : ‖A₆‖ < 1)
    (hx : ‖x‖ = 1) (h : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆) : ‖y‖ = 1 ∧ ‖x + y‖ = 1 := by
  have hr : ‖x ^ 3 + A₄ * x + A₆‖ = 1 := by
    have hx3 : ‖x ^ 3‖ = 1 := by rw [norm_pow, hx, one_pow]
    rw [← hx3, add_assoc]
    refine (IsUltrametricDist.norm_eq_of_norm_sub_lt_left ?_).symm
    rw [sub_add_cancel_left, norm_neg, hx3]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hA₆)
    rwa [norm_mul, hx, mul_one]
  have hp : ‖y‖ * ‖x + y‖ = 1 := by
    rw [← norm_mul, ← hr, ← h]
    ring_nf
  have hs : ‖x + y‖ ≤ max 1 ‖y‖ := hx ▸ IsUltrametricDist.norm_add_le_max x y
  rcases le_or_gt ‖y‖ 1 with hy | hy
  · have hs' : ‖x + y‖ ≤ 1 := hs.trans (max_le le_rfl hy)
    constructor <;> nlinarith [norm_nonneg y, norm_nonneg (x + y)]
  · have he : ‖x + y‖ = ‖y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hy.ne), hx,
        max_eq_right hy.le]
    rw [he] at hp
    nlinarith

omit [CompleteSpace K] in
/-- **A line through the origin meets the curve in at most one point with `‖x‖ = 1`.** If
`(x, y)` and `(X, Y)` solve `y² + xy = x³ + A₄x + A₆` with `‖A₄‖, ‖A₆‖ < 1`, both first coordinates
have norm one and `x Y = y X`, then the two points are equal. -/
private theorem eq_of_mul_eq_mul {A₄ A₆ x y X Y : K} (hA₄ : ‖A₄‖ < 1) (hA₆ : ‖A₆‖ < 1)
    (hx : ‖x‖ = 1) (hX : ‖X‖ = 1) (h₁ : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆)
    (h₂ : Y ^ 2 + X * Y = X ^ 3 + A₄ * X + A₆) (h : x * Y = y * X) : X = x ∧ Y = y := by
  have key : (x - X) * (x ^ 2 * X ^ 2 - (A₄ * x * X + A₆ * (x + X))) = 0 := by
    linear_combination x ^ 2 * h₂ - X ^ 2 * h₁ - (x * Y + y * X + x * X) * h
  have h₀ : ‖x ^ 2 * X ^ 2‖ = 1 := by rw [norm_mul, norm_pow, norm_pow, hx, hX]; simp
  have hne : x ^ 2 * X ^ 2 - (A₄ * x * X + A₆ * (x + X)) ≠ 0 := by
    rw [← norm_ne_zero_iff, ← (IsUltrametricDist.norm_eq_of_norm_sub_lt_left _), h₀]
    · exact one_ne_zero
    rw [sub_sub_cancel, h₀]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rwa [norm_mul, norm_mul, hx, hX, mul_one, mul_one]
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        ((IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hx, hX, max_self]))).trans_lt hA₆
  have hxX : X = x := (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)).symm
  refine ⟨hxX, ?_⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  rw [hxX, mul_comm y] at h
  exact mul_left_cancel₀ hx0 h

/-! ### Surjectivity onto the nonsingular stratum -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A parameter with `‖u‖ = ‖1 - u‖ = 1` is not a power of `q`. -/
private theorem notMem_zpowers_of_norm_one_sub_eq_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (h : ‖1 - (u : K)‖ = 1) : u ∉ Subgroup.zpowers q := by
  rintro ⟨n, rfl⟩
  rw [Units.val_zpow_eq_zpow_val, norm_zpow] at hu
  obtain rfl := (zpow_eq_one_iff_right₀ (norm_nonneg _) hq.ne).mp hu
  simp at h

/-- **Every solution of the Tate equation with `‖x‖ = 1` comes from the unit circle.** If `(x, y)`
satisfies `y² + xy = x³ + a₄(q) x + a₆(q)` and `‖x‖ = 1`, then `(x, y) = (X(u), Y(u))` for a
parameter `u` with `‖u‖ = ‖1 - u‖ = 1`. -/
theorem exists_tateUniformizationX_eq_and_tateUniformizationY_eq (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y : K} (h : (tateCurveAt q hq).toAffine.Equation x y)
    (hx : ‖x‖ = 1) :
    ∃ u : Kˣ, ‖(u : K)‖ = 1 ∧ ‖1 - (u : K)‖ = 1 ∧
      tateUniformizationX q u = x ∧ tateUniformizationY q u = y := by
  have hA₄ := (norm_tateCurveA₄_le (q : K) hq).trans_lt hq
  have hA₆ := (norm_tateCurveA₆_le (q : K) hq).trans_lt hq
  have heq {a b : K} (h : (tateCurveAt q hq).toAffine.Equation a b) :
      b ^ 2 + a * b = a ^ 3 + tateCurveA₄ (q : K) hq * a + tateCurveA₆ (q : K) hq := by
    rw [equation_iff] at h
    simp only [tateCurveAt_a₁, tateCurveAt_a₂, tateCurveAt_a₃, tateCurveAt_a₄,
      tateCurveAt_a₆] at h
    linear_combination h
  obtain ⟨-, hxy⟩ := norm_eq_one_of_equation hA₄ hA₆ hx (heq h)
  have hxy0 : x + y ≠ 0 := norm_ne_zero_iff.mp (by rw [hxy]; exact one_ne_zero)
  -- `c = y / (x + y)` is the parameter of `(x, y)` on the nodal cubic `y² + xy = x³`
  have hc₁ : y / (x + y) * (x + y) = y := div_mul_cancel₀ y hxy0
  have hc₂ : (1 - y / (x + y)) * (x + y) = x := by
    rw [sub_mul, one_mul, hc₁]
    ring
  have hc : ‖y / (x + y)‖ = 1 := by
    rw [norm_div, hxy, div_one]
    exact (norm_eq_one_of_equation hA₄ hA₆ hx (heq h)).1
  have hc' : ‖1 - y / (x + y)‖ = 1 := by
    have h := congrArg norm hc₂
    rwa [norm_mul, hxy, mul_one, hx] at h
  obtain ⟨u, hu, hu₁, hcu⟩ := exists_one_sub_mul_tateUniformizationY_eq q hq hc hc'
  have hcross : x * tateUniformizationY q u = y * tateUniformizationX q u := by
    linear_combination (x + y) * hcu - tateUniformizationY q u * hc₂ +
      tateUniformizationX q u * hc₁
  obtain ⟨hX, hY⟩ := eq_of_mul_eq_mul hA₄ hA₆ hx (norm_tateUniformizationX_eq_one q u hq hu hu₁)
    (heq h) (heq (equation_tateUniformizationX_tateUniformizationY_of_notMem_zpowers q u hq
      (notMem_zpowers_of_norm_one_sub_eq_one q u hq hu hu₁))) hcross
  exact ⟨u, hu, hu₁, hX, hY⟩

/-- **The Tate uniformisation is onto the nonsingular stratum.** An affine point `(x, y)` of
`E_q(K)` is the image of the class of a parameter `u` with `‖u‖ = ‖1 - u‖ = 1` exactly when
`‖x‖ = 1`. -/
theorem exists_tateUniformization_eq_some_iff_norm_eq_one (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x y : K} (h : (tateCurveAt q hq).toAffine.Nonsingular x y) :
    (∃ u : Kˣ, ‖(u : K)‖ = 1 ∧ ‖1 - (u : K)‖ = 1 ∧
      tateUniformization q hq (u : Kˣ ⧸ Subgroup.zpowers q) = .some x y h) ↔ ‖x‖ = 1 := by
  constructor
  · rintro ⟨u, hu, hu₁, hP⟩
    obtain ⟨-, hX, -⟩ := (tateUniformization_eq_some_iff q hq _ h).mp hP
    rw [← hX, tateQuotientCoordinates_mk]
    exact norm_tateUniformizationX_eq_one q u hq hu hu₁
  · intro hx
    obtain ⟨u, hu, hu₁, hX, hY⟩ :=
      exists_tateUniformizationX_eq_and_tateUniformizationY_eq q hq h.1 hx
    refine ⟨u, hu, hu₁, (tateUniformization_eq_some_iff q hq _ h).mpr ⟨?_, ?_, ?_⟩⟩
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact notMem_zpowers_of_norm_one_sub_eq_one q u hq hu hu₁
    · rw [tateQuotientCoordinates_mk, hX]
    · rw [tateQuotientCoordinates_mk, hY]

end TauCeti
