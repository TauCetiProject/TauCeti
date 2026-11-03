/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.NodalReduction
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
the unit circle (`norm_tateUniformizationX_sub_sub_le`, `norm_tateUniformizationY_sub_sub_le`
from `TateCurve.Strata`).
At the fixed point `x Y(u) = y X(u)`, so `(x, y)` and `(X(u), Y(u))` lie on a common line through
the origin. Such a line meets `E_q(K)` in at most one point with first coordinate of norm one
(`eq_and_eq_of_mul_eq_mul_of_equation` from `TateCurve.NodalReduction`), so the two points agree.

## Main results

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

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

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

/-- One step of the contraction, `u ↦ c - (1 - u)³ / u · tateErr q u c`. -/
private noncomputable def tateStep (q u : Kˣ) (c : K) : K :=
  c - (1 - (u : K)) ^ 3 / u * tateErr q u c

/-- The contraction moves every parameter of the stratum to within `‖q‖` of `c`. -/
private theorem norm_tateStep_sub_le (q u : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) (h : ‖1 - (u : K)‖ = 1) :
    ‖tateStep q u c - c‖ ≤ ‖(q : K)‖ := by
  rw [tateStep, sub_sub_cancel_left, norm_neg, norm_mul, norm_div, norm_pow, hu, h, one_pow,
    div_one, one_mul]
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
  · rw [norm_div, norm_pow, hu', h', one_pow, div_one, one_mul]
    exact norm_tateErr_sub_le q u' u hq hc hc' hu' hu
  · rw [mul_comm]
    exact mul_le_mul (norm_tateErr_le q u hq hc hc' hu)
      (norm_one_sub_cube_div_sub_one_sub_cube_div_le hu' hu) (norm_nonneg _) (norm_nonneg _)

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

/-! ### Surjectivity onto the nonsingular stratum -/

/-- **Every solution of the Tate equation with `‖x‖ = 1` comes from the unit circle.** If `(x, y)`
satisfies `y² + xy = x³ + a₄(q) x + a₆(q)` and `‖x‖ = 1`, then `(x, y) = (X(u), Y(u))` for a
parameter `u` with `‖u‖ = ‖1 - u‖ = 1`. -/
theorem exists_tateUniformizationX_eq_and_tateUniformizationY_eq (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y : K} (h : (tateCurveAt q hq).toAffine.Equation x y)
    (hx : ‖x‖ = 1) :
    ∃ u : Kˣ, ‖(u : K)‖ = 1 ∧ ‖1 - (u : K)‖ = 1 ∧
      tateUniformizationX q u = x ∧ tateUniformizationY q u = y := by
  have hA₄ := (norm_tateCurveA₄_le (q : K) hq).trans_lt hq
  have hA₆ := (norm_tateCurveA₆ (q : K) hq).trans_lt hq
  have heq {a b : K} (h : (tateCurveAt q hq).toAffine.Equation a b) :
      b ^ 2 + a * b = a ^ 3 + tateCurveA₄ (q : K) hq * a + tateCurveA₆ (q : K) hq := by
    rw [equation_iff] at h
    simp only [tateCurveAt_a₁, tateCurveAt_a₂, tateCurveAt_a₃, tateCurveAt_a₄,
      tateCurveAt_a₆] at h
    linear_combination h
  obtain ⟨-, hxy⟩ := norm_eq_one_and_norm_add_eq_one_of_equation hA₄ hA₆ hx (heq h)
  have hxy0 : x + y ≠ 0 := norm_ne_zero_iff.mp (by rw [hxy]; exact one_ne_zero)
  -- `c = y / (x + y)` is the parameter of `(x, y)` on the nodal cubic `y² + xy = x³`
  have hc₁ : y / (x + y) * (x + y) = y := div_mul_cancel₀ y hxy0
  have hc₂ : (1 - y / (x + y)) * (x + y) = x := by
    rw [sub_mul, one_mul, hc₁]
    ring
  have hc : ‖y / (x + y)‖ = 1 := by
    rw [norm_div, hxy, div_one]
    exact (norm_eq_one_and_norm_add_eq_one_of_equation hA₄ hA₆ hx (heq h)).1
  have hc' : ‖1 - y / (x + y)‖ = 1 := by
    have h := congrArg norm hc₂
    rwa [norm_mul, hxy, mul_one, hx] at h
  obtain ⟨u, hu, hu₁, hcu⟩ := exists_one_sub_mul_tateUniformizationY_eq q hq hc hc'
  have hcross : x * tateUniformizationY q u = y * tateUniformizationX q u := by
    linear_combination (x + y) * hcu - tateUniformizationY q u * hc₂ +
      tateUniformizationX q u * hc₁
  obtain ⟨hX, hY⟩ := eq_and_eq_of_mul_eq_mul_of_equation hA₄ hA₆ hx
    (norm_tateUniformizationX_eq_one q u hq hu hu₁) (heq h)
    (heq (equation_tateUniformizationX_tateUniformizationY_of_notMem_zpowers q u hq
      (notMem_zpowers_of_norm_eq_one hq hu (by rintro rfl; simp at hu₁)))) hcross
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
      exact notMem_zpowers_of_norm_eq_one hq hu (by rintro rfl; simp at hu₁)
    · rw [tateQuotientCoordinates_mk, hX]
    · rw [tateQuotientCoordinates_mk, hY]

end TauCeti
