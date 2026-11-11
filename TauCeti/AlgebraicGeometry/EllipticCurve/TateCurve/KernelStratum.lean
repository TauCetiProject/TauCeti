/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Strata
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# The Tate uniformisation is onto the kernel of reduction

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. The points of the
Tate curve `E_q : y² + xy = x³ + a₄(q) x + a₆(q)` whose first coordinate has norm above one are
the points with a pole modulo the maximal ideal, that is, the kernel of reduction. This file shows
that the Tate uniformisation `Kˣ / q^ℤ → E_q(K)` is onto them: every solution `(x, y)` of the Tate
equation with `‖x‖ > 1` is `(X(u), Y(u))` for a parameter `u ≠ 1` with `‖1 - u‖ < 1`. Together
with `TauCeti.one_lt_norm_tateQuotientCoordinates_fst_iff`, an affine point of `E_q(K)` is the
image of the class of a parameter in `1 + 𝔪` exactly when its first coordinate has norm above
one. Nothing assumes a discrete value group or restricts the characteristic.

## Main results

* `TauCeti.exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_one_lt_norm`: a solution
  `(x, y)` of the Tate equation with `‖x‖ > 1` is `(X(u), Y(u))` for some `u ≠ 1` with
  `‖1 - u‖ < 1`.
* `TauCeti.exists_tateUniformization_eq_some_iff_one_lt_norm`: an affine point of `E_q(K)` is the
  image of a parameter in `1 + 𝔪` exactly when its first coordinate has norm above one.

## Implementation notes

The nodal cubic `y² + xy = x³`, the reduction of `E_q`, is parametrised by
`u ↦ (u / (1 - u)², u² / (1 - u)³)`, with inverse `(x, y) ↦ y / (x + y)`. For a solution `(x, y)`
with `‖x‖ > 1`, the element `c = y / (x + y)` satisfies `‖1 - c‖ < 1`, and the parameter is the
fixed point of
`u ↦ c - (1 - u)³ / u · ((1 - c)(Y(u) - u² / (1 - u)³) - c (X(u) - u / (1 - u)²))`
on the ball `‖1 - u‖ < 1`, which is closed because the norm is ultrametric. This map is a
contraction with constant `‖q‖`, by the Lipschitz estimates
`TauCeti.norm_tateUniformizationX_sub_sub_le` and `TauCeti.norm_tateUniformizationY_sub_sub_le`.
At its fixed point `x Y(u) = y X(u)`, and a line through the origin meets the curve in at most
one point whose first coordinate has norm above one
(`TauCeti.eq_of_mul_eq_mul_of_one_lt_norm`).

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3–V.4.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Solving for the parameter by a contraction -/

/-- The error term of the contraction: the combination `(1 - c) Y(u) - c X(u)` with the nodal
parametrisation subtracted from each coordinate. -/
private noncomputable def kernelErr (q u : Kˣ) (c : K) : K :=
  (1 - c) * (tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3) -
    c * (tateUniformizationX q u - u / (1 - u) ^ 2)

private theorem norm_kernelErr_le (q u : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) : ‖kernelErr q u c‖ ≤ ‖(q : K)‖ := by
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_of_le_one_left (norm_nonneg _) hc'
      |>.trans (norm_tateUniformizationY_sub_le_of_norm_eq_one q u hq hu)
  · exact mul_le_of_le_one_left (norm_nonneg _) hc
      |>.trans (norm_tateUniformizationX_sub_le_of_norm_eq_one q u hq hu)

private theorem norm_kernelErr_sub_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖1 - c‖ ≤ 1) (hu : ‖(u : K)‖ = 1) (hu' : ‖(u' : K)‖ = 1) :
    ‖kernelErr q u c - kernelErr q u' c‖ ≤ ‖(q : K)‖ * ‖(u : K) - u'‖ := by
  have e : kernelErr q u c - kernelErr q u' c =
      (1 - c) * ((tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3) -
        (tateUniformizationY q u' - (u' : K) ^ 2 / (1 - u') ^ 3)) -
      c * ((tateUniformizationX q u - u / (1 - u) ^ 2) -
        (tateUniformizationX q u' - u' / (1 - u') ^ 2)) := by
    rw [kernelErr, kernelErr]
    ring
  rw [e]
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_of_le_one_left (norm_nonneg _) hc'
      |>.trans (norm_tateUniformizationY_sub_sub_le q u u' hq hu hu')
  · exact mul_le_of_le_one_left (norm_nonneg _) hc
      |>.trans (norm_tateUniformizationX_sub_sub_le q u u' hq hu hu')

/-- One step of the contraction, `u ↦ c - (1 - u)³ / u · kernelErr q u c`. -/
private noncomputable def kernelStep (q u : Kˣ) (c : K) : K :=
  c - (1 - (u : K)) ^ 3 / u * kernelErr q u c

/-- The contraction moves every parameter of the ball `‖1 - u‖ < 1` by less than one from `c`. -/
private theorem norm_kernelStep_sub_lt (q u : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K}
    (hc : ‖1 - c‖ < 1) (hu : ‖1 - (u : K)‖ < 1) : ‖kernelStep q u c - c‖ < 1 := by
  have hu₁ : ‖(u : K)‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hu
  have hc₁ : ‖c‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hc
  simpa [kernelStep, hu₁] using
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hu.le)).trans_lt
      ((norm_kernelErr_le q u hq hc₁.le hc.le hu₁).trans_lt hq)

/-- The contraction is `‖q‖`-Lipschitz on the ball `‖1 - u‖ < 1`. -/
private theorem norm_kernelStep_sub_kernelStep_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K}
    (hc : ‖1 - c‖ < 1) (hu : ‖1 - (u : K)‖ < 1) (hu' : ‖1 - (u' : K)‖ < 1) :
    ‖kernelStep q u c - kernelStep q u' c‖ ≤ ‖(q : K)‖ * ‖(u : K) - u'‖ := by
  have hu₁ : ‖(u : K)‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hu
  have hu₁' : ‖(u' : K)‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hu'
  have hc₁ : ‖c‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hc
  have e : kernelStep q u c - kernelStep q u' c =
      (1 - (u' : K)) ^ 3 / u' * (kernelErr q u' c - kernelErr q u c) +
        ((1 - (u' : K)) ^ 3 / u' - (1 - (u : K)) ^ 3 / u) * kernelErr q u c := by
    rw [kernelStep, kernelStep]
    ring
  have hg : ‖(1 - (u' : K)) ^ 3 / u'‖ ≤ 1 := by
    rw [norm_div, norm_pow, hu₁', div_one]
    exact pow_le_one₀ (norm_nonneg _) hu'.le
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
    rw [norm_mul, norm_sub_rev (u : K)]
  · exact mul_le_of_le_one_left (norm_nonneg _) hg
      |>.trans (norm_kernelErr_sub_le q u' u hq hc₁.le hc.le hu₁' hu₁)
  · rw [mul_comm]
    exact mul_le_mul (norm_kernelErr_le q u hq hc₁.le hc.le hu₁)
      (norm_one_sub_cube_div_sub_one_sub_cube_div_le hu₁' hu₁) (norm_nonneg _)
      (norm_nonneg _)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- At a fixed point `u ≠ 1` of the contraction, `(1 - c) Y(u) = c X(u)`. -/
private theorem one_sub_mul_tateUniformizationY_eq_of_kernelStep_eq (q u : Kˣ) {c : K}
    (h : 1 - (u : K) ≠ 0) (hu : kernelStep q u c = u) :
    (1 - c) * tateUniformizationY q u = c * tateUniformizationX q u := by
  -- multiplying by `(1 - u)³ / u ≠ 0` turns the fixed-point equation into the claim
  have key : (1 - (u : K)) ^ 3 / u *
      ((1 - c) * tateUniformizationY q u - c * tateUniformizationX q u) =
      (c - kernelStep q u c) + ((1 - c) * u - c * (1 - u)) := by
    rw [kernelStep, kernelErr]
    field_simp [u.ne_zero]
    ring
  rw [hu] at key
  have hm : (1 - (u : K)) ^ 3 / u ≠ 0 := div_ne_zero (pow_ne_zero _ h) u.ne_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp (key.trans (by ring))).resolve_left hm)

/-- **Solving for the parameter.** For `c ≠ 1` with `‖1 - c‖ < 1` there is a parameter `u ≠ 1`
with `‖1 - u‖ < 1` and `(1 - c) Y(u) = c X(u)`. It is the fixed point of the contraction
`kernelStep q · c` of the ball `‖1 - u‖ < 1`, which is closed since the norm is ultrametric. -/
private theorem exists_one_sub_mul_tateUniformizationY_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1) {c : K}
    (hc : ‖1 - c‖ < 1) (hc₁ : c ≠ 1) :
    ∃ u : Kˣ, (u : K) ≠ 1 ∧ ‖1 - (u : K)‖ < 1 ∧
      (1 - c) * tateUniformizationY q u = c * tateUniformizationX q u := by
  set S : Set K := Metric.ball 1 1
  have hmem {v : K} : v ∈ S ↔ ‖1 - v‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
  have : CompleteSpace S := (IsUltrametricDist.isClosed_ball (1 : K) 1).completeSpace_coe
  have : Nonempty S := ⟨⟨c, hmem.mpr hc⟩⟩
  have hne (v : S) : (v : K) ≠ 0 := fun h ↦ by
    have := hmem.mp v.2
    rw [h, sub_zero, norm_one] at this
    exact lt_irrefl _ this
  let U : S → Kˣ := fun v ↦ Units.mk0 v (hne v)
  have hU (v : S) : ‖1 - ((U v : Kˣ) : K)‖ < 1 := hmem.mp v.2
  -- the step stays in the ball: it moves by less than one from `c`, which lies in the ball
  have hstep (v : S) : kernelStep q (U v) c ∈ S := by
    refine hmem.mpr ?_
    rw [show 1 - kernelStep q (U v) c = (1 - c) + (c - kernelStep q (U v) c) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hc ?_)
    rw [norm_sub_rev]
    exact norm_kernelStep_sub_lt q _ hq hc (hU v)
  have hF : ContractingWith ‖(q : K)‖₊ (fun v : S ↦ (⟨kernelStep q (U v) c, hstep v⟩ : S)) := by
    refine ⟨by rwa [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one],
      LipschitzWith.of_dist_le_mul fun v w ↦ ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, coe_nnnorm]
    exact norm_kernelStep_sub_kernelStep_le q _ _ hq hc (hU v) (hU w)
  set v := ContractingWith.fixedPoint _ hF
  have hv : kernelStep q (U v) c = v :=
    congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hF)
  -- the fixed point is not `1`, where the step is the constant `c ≠ 1`
  have hv₁ : ((U v : Kˣ) : K) ≠ 1 := fun h ↦ by
    have hc' : kernelStep q (U v) c = c := by simp [kernelStep, h]
    exact hc₁ (hc'.symm.trans (hv.trans (by simpa [U] using h)))
  exact ⟨U v, hv₁, hU v, one_sub_mul_tateUniformizationY_eq_of_kernelStep_eq q (U v)
    (sub_ne_zero.mpr (Ne.symm hv₁)) hv⟩

/-! ### Surjectivity onto the kernel of reduction -/

/-- **Every solution of the Tate equation with a pole comes from `1 + 𝔪`.** If `(x, y)` satisfies
`y² + xy = x³ + a₄(q) x + a₆(q)` and `‖x‖ > 1`, then `(x, y) = (X(u), Y(u))` for a parameter
`u ≠ 1` with `‖1 - u‖ < 1`. -/
theorem exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_one_lt_norm (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y : K} (h : (tateCurveAt q hq).toAffine.Equation x y)
    (hx : 1 < ‖x‖) :
    ∃ u : Kˣ, u ≠ 1 ∧ ‖1 - (u : K)‖ < 1 ∧
      tateUniformizationX q u = x ∧ tateUniformizationY q u = y := by
  have hA₄ := (norm_tateCurveA₄_le (q : K) hq).trans hq.le
  have hA₆ := (norm_tateCurveA₆ (q : K) hq).trans_le hq.le
  have hxy := norm_lt_norm_add_of_equation hA₄ hA₆ hx ((tateCurveAt_equation_iff q hq).mp h)
  have hxy₀ : x + y ≠ 0 := norm_pos_iff.mp ((one_pos.trans hx).trans hxy)
  have hx₀ : x ≠ 0 := norm_pos_iff.mp (one_pos.trans hx)
  -- `c = y / (x + y)` is the parameter of `(x, y)` on the nodal cubic `y² + xy = x³`
  have hc₁ : y / (x + y) * (x + y) = y := div_mul_cancel₀ y hxy₀
  have hc₂ : (1 - y / (x + y)) * (x + y) = x := by
    rw [sub_mul, one_mul, hc₁]
    ring
  have hc : ‖1 - y / (x + y)‖ < 1 := by
    have h' := congrArg norm hc₂
    rw [norm_mul] at h'
    exact (mul_lt_iff_lt_one_left ((one_pos.trans hx).trans hxy)).mp (h' ▸ hxy)
  have hc1 : y / (x + y) ≠ 1 := fun h₁ ↦ by
    rw [h₁, sub_self, zero_mul] at hc₂
    exact hx₀ hc₂.symm
  obtain ⟨u, hu1, hu, hcu⟩ := exists_one_sub_mul_tateUniformizationY_eq q hq hc hc1
  have hcross : x * tateUniformizationY q u = y * tateUniformizationX q u := by
    linear_combination (x + y) * hcu - tateUniformizationY q u * hc₂ +
      tateUniformizationX q u * hc₁
  have hXu : 1 < ‖tateUniformizationX q u‖ := by
    rw [norm_tateUniformizationX_of_norm_one_sub_lt_one q u hq hu1 hu]
    have hd : 0 < ‖1 - (u : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu1))
    exact (one_lt_inv₀ (by positivity)).mpr (pow_lt_one₀ hd.le hu two_ne_zero)
  have hu₁ : ‖(u : K)‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hu
  have hnot : u ∉ Subgroup.zpowers q :=
    notMem_zpowers_of_norm_eq_one hq hu₁ fun h ↦ hu1 (by rw [h, Units.val_one])
  obtain ⟨hX, hY⟩ := eq_of_mul_eq_mul_of_one_lt_norm hA₄ hA₆ hx hXu
    ((tateCurveAt_equation_iff q hq).mp h) ((tateCurveAt_equation_iff q hq).mp
      (equation_tateUniformizationX_tateUniformizationY_of_notMem_zpowers q u hq hnot)) hcross
  exact ⟨u, fun h ↦ hu1 (by rw [h, Units.val_one]), hu, hX, hY⟩

/-- **The Tate uniformisation is onto the kernel of reduction.** An affine point `(x, y)` of
`E_q(K)` is the image of the class of a parameter `u` with `‖1 - u‖ < 1` exactly when
`‖x‖ > 1`. -/
theorem exists_tateUniformization_eq_some_iff_one_lt_norm (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x y : K} (h : (tateCurveAt q hq).toAffine.Nonsingular x y) :
    (∃ u : Kˣ, ‖1 - (u : K)‖ < 1 ∧
      tateUniformization q hq (u : Kˣ ⧸ Subgroup.zpowers q) = .some x y h) ↔ 1 < ‖x‖ := by
  constructor
  · rintro ⟨u, hu, hP⟩
    obtain ⟨hne, hX, -⟩ := (tateUniformization_eq_some_iff q hq _ h).mp hP
    rw [← hX]
    exact (one_lt_norm_tateQuotientCoordinates_fst_iff q hq hne).mpr ⟨u, rfl, hu⟩
  · intro hx
    obtain ⟨u, hu1, hu, hX, hY⟩ :=
      exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_one_lt_norm q hq h.1 hx
    have hu₁ : ‖(u : K)‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one hu
    refine ⟨u, hu, (tateUniformization_eq_some_iff q hq _ h).mpr ⟨?_, ?_, ?_⟩⟩
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact notMem_zpowers_of_norm_eq_one hq hu₁ hu1
    · rw [tateQuotientCoordinates_mk, hX]
    · rw [tateQuotientCoordinates_mk, hY]

end TauCeti
