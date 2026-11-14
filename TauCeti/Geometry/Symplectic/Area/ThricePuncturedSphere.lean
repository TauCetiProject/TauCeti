/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.HoledDisc
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate

/-!
# Symplectic area on truncated punctured spheres

Let `(V, ω)` be a symplectic vector space and let `u` be a `C²` map from the thrice-punctured
sphere `S = ℂ ∖ {0, 1}` to `V`. The truncation `S_R` (`TauCeti.ThricePuncturedSphere.truncation`)
is bounded by the three circles `±s = R` of the cylindrical ends, and in the end coordinates
`z = s + i t` of the end `q` the restriction of `u` to the circle `±s = R` is the loop
`ℓ_q(t) = u(φ_q(±R + i t))`, where `φ_q` is the end lift `Puncture.cylindricalEndLift`. This file
proves Stokes' formula for the symplectic area of `u` over `S_R`:

`∫_{S_R} u^*ω = a(ℓ_0) + a(ℓ_1) - a(ℓ_∞)`

for `R ≥ 1`, where `a` is the loop area `TauCeti.SymplecticForm.loopArea`, the integral of the
primitive `λₓ(v) = ½ ω(x, v)` of `ω` (`SymplecticForm.integral_fderiv_apply_truncation`). All
three loops run clockwise in the plane. This is the boundary orientation of `S_R` on the two
inner circles, about `0` and `1`, and the reverse of it on the outer circle, which gives the
signs of the ends: `+` on the input ends `0` and `1`, `-` on the output end `∞`.

The same holds on spheres with finitely many moving input ends, the domains of the associativity
family of the pair-of-pants product (see
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds`). An input end with center `c` and
nonzero scale `a` has the end lift `z ↦ c + a φ₀(z)`, and the output end at `∞` keeps the end lift
`φ_∞`. If the discs `‖w - cᵢ‖ < ‖aᵢ‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, then for `R ≥ 1` the end circles at `s = R` bound the disc
`‖w‖ ≤ 2 exp (2πR)` with the holes `‖w - cᵢ‖ < ‖aᵢ‖ exp (-2πR) / 2`, and the symplectic area of
`u` over it is `∑ i, a(ℓᵢ) - a(ℓ_∞)`
(`SymplecticForm.integral_fderiv_apply_closedBall_sdiff_iUnion_ball_eq_sum_loopArea_sub`).

Both truncations are discs with holes, so both formulas are instances of Stokes' formula on a disc
with holes, `TauCeti.SymplecticForm.integral_fderiv_apply_closedBall_sdiff_biUnion_ball`. No
extension of `u` across the punctures is needed. In the energy identities of the pair-of-pants
product and of its associativity family, adding the Hamiltonian terms turns these loop areas into
the Hamiltonian actions of the end loops; see
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.5.
-/

public section

open Set Metric MeasureTheory Complex Filter Topology
open scoped Real

namespace TauCeti.SymplecticForm

open ThricePuncturedSphere ThricePuncturedSphere.Puncture

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The loop of the end `q` along the circle `s = x` runs clockwise around the circle of radius
`‖b_q‖ exp (-2πx)` about the center `c_q` of the end, so its loop area is minus that of the
counterclockwise circle. -/
private theorem loopArea_cylindricalEndLift (ω : SymplecticForm V) (u : ℂ → V) (q : Puncture)
    (x : ℝ) :
    ω.loopArea (fun t ↦ u (q.cylindricalEndLift (x + t * I))) =
      -ω.loopArea (fun t ↦ u (circleMap q.endCenter
        (‖q.endScale‖ * Real.exp (-(2 * π * x))) (2 * π * t))) := by
  simp only [cylindricalEndLift_ofReal_add_ofReal_mul_I]
  exact ω.loopArea_comp_circleMap_sub_mul u _ _ _

variable [FiniteDimensional ℝ V]

/-- **Stokes' formula for symplectic area on the truncated thrice-punctured sphere.** Let `u` be
`C²` on `S = ℂ ∖ {0, 1}`. For `R ≥ 1` the symplectic area of `u` over the truncation `S_R` is the
signed sum of the loop areas of the restrictions of `u` to the three boundary circles `±s = R`,
parametrized by the end coordinates:

`∫_{S_R} u^*ω = ∑ q, ±a(t ↦ u(φ_q(±R + i t)))`,

with the sign `+` on the input ends `0` and `1` and `-` on the output end `∞`. -/
theorem integral_fderiv_apply_truncation (ω : SymplecticForm V) {u : ℂ → V}
    (hu : ContDiffOn ℝ 2 u {w : ℂ | w ≠ 0 ∧ w ≠ 1}) {R : ℝ} (hR : 1 ≤ R) :
    ∫ w in truncation R, ω (fderiv ℝ u w 1) (fderiv ℝ u w I) =
      ∑ q : Puncture, q.endSign *
        ω.loopArea (fun t ↦ u (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))) := by
  -- The radii of the boundary circles: `r` about `0` and `1`, and `ρ` about `0`.
  set r := Real.exp (-(2 * π * R)) / 2 with hr_def
  set ρ := 2 * Real.exp (2 * π * R) with hρ_def
  have hexp : 5 ≤ Real.exp (2 * π * R) := by
    have := Real.add_one_le_exp (2 * π * R)
    nlinarith [Real.two_le_pi]
  have hexp' : Real.exp (-(2 * π * R)) * Real.exp (2 * π * R) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hr₀ : 0 < r := by positivity
  have hr : r ≤ 1 / 10 := by nlinarith [Real.exp_pos (-(2 * π * R))]
  -- The truncation is the disc of radius `ρ` with the holes of radius `r` about `0` and `1`.
  have htrunc : truncation R =
      closedBall 0 ρ \ ⋃ q ∈ ({zero, one} : Finset Puncture), ball q.endCenter r := by
    rw [truncation_eq]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
      iUnion_iUnion_eq_left, endCenter_zero, endCenter_one, mem_inter_iff, mem_ofPred_eq,
      mem_closedBall, Set.mem_sdiff, mem_union, mem_ball, dist_eq_norm, sub_zero, not_or,
      not_lt]
    tauto
  have hloops : ∑ q : Puncture, q.endSign *
      ω.loopArea (fun t ↦ u (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))) =
        ω.loopArea (fun t ↦ u (circleMap 0 ρ (2 * π * t))) -
          ∑ q ∈ ({zero, one} : Finset Puncture),
            ω.loopArea (fun t ↦ u (circleMap q.endCenter r (2 * π * t))) := by
    have e₀ : ‖zero.endScale‖ * Real.exp (-(2 * π * (zero.endSign * R))) = r := by
      rw [hr_def, endScale_zero, endSign_zero, one_mul]
      norm_num
      ring
    have e₁ : ‖one.endScale‖ * Real.exp (-(2 * π * (one.endSign * R))) = r := by
      rw [hr_def, endScale_one, endSign_one, one_mul]
      norm_num
      ring
    have e₂ : ‖inf.endScale‖ * Real.exp (-(2 * π * (inf.endSign * R))) = ρ := by
      rw [hρ_def, endScale_inf, endSign_inf, neg_one_mul, mul_neg, neg_neg]
      norm_num
    simp only [loopArea_cylindricalEndLift]
    rw [sum_univ, e₀, e₁, e₂, Finset.sum_pair (by decide), endSign_zero, endSign_one,
      endSign_inf, endCenter_inf]
    ring
  rw [hloops, htrunc]
  refine ω.integral_fderiv_apply_closedBall_sdiff_biUnion_ball _ 0 (by positivity) _
    (fun _ _ ↦ hr₀) (fun q hq ↦ ?_) ?_ fun w hw ↦ ?_
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> norm_num <;> linarith
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.pairwise_insert,
      Set.pairwise_singleton, mem_singleton_iff, forall_eq, true_and, endCenter_zero,
      endCenter_one]
    intro _
    norm_num
    linarith
  · -- The holes contain the punctures `0` and `1`.
    simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
      iUnion_iUnion_eq_left, endCenter_zero, endCenter_one, Set.mem_sdiff, mem_union,
      not_or] at hw
    refine hu.contDiffAt ((isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun continuous_id continuous_const) |>.mem_nhds ⟨?_, ?_⟩)
    · rintro rfl
      exact hw.2.1 (mem_ball_self hr₀)
    · rintro rfl
      exact hw.2.2 (mem_ball_self hr₀)

/-- **Stokes' formula for symplectic area on a sphere with moving input ends.** Let the input ends
have centers `c i` and nonzero scales `a i`, so that the end lift of the input `i` is
`z ↦ c i + a i φ₀(z)` for the end lift `φ₀(z) = exp (-2πz) / 2` of the input end at `0` of the
pair of pants, with the discs `‖w - c i‖ < ‖a i‖ / 2` pairwise disjoint inside the disc
`‖w‖ ≤ 2 exp (2π)`, and let the output end at `∞` have the end lift `φ_∞`. For `R ≥ 1`, the
symplectic area of a map `u` which is `C²` at every point of the disc `‖w‖ ≤ 2 exp (2πR)` with the
holes `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2` removed is the sum of the loop areas of the input end
loops at `s = R`, minus the loop area of the output end loop at `s = -R`:

`∫ u^*ω = ∑ i, a(t ↦ u(c i + a i φ₀(R + i t))) - a(t ↦ u(φ_∞(-R + i t)))`. -/
theorem integral_fderiv_apply_closedBall_sdiff_iUnion_ball_eq_sum_loopArea_sub
    (ω : SymplecticForm V) {ι : Type*} [Fintype ι] {c a : ι → ℂ} (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℂ → V} {R : ℝ} (hR : 1 ≤ R)
    (hu : ∀ w ∈ closedBall 0 (2 * Real.exp (2 * π * R)) \
      ⋃ i, ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2), ContDiffAt ℝ 2 u w) :
    ∫ w in closedBall 0 (2 * Real.exp (2 * π * R)) \
        ⋃ i, ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2),
        ω (fderiv ℝ u w 1) (fderiv ℝ u w I) =
      ∑ i, ω.loopArea (fun t ↦ u (c i + a i * zero.cylindricalEndLift (R + t * I))) -
        ω.loopArea (fun t ↦ u (inf.cylindricalEndLift (-R + t * I))) := by
  have hexp : Real.exp (-(2 * π * R)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hexp' : Real.exp (2 * π) ≤ Real.exp (2 * π * R) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  -- The input end loops run clockwise around the holes, the output loop around the outer circle.
  have hin (i : ι) : ω.loopArea (fun t ↦ u (c i + a i * zero.cylindricalEndLift (R + t * I))) =
      -ω.loopArea (fun t ↦ u (circleMap (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2)
        (2 * π * t))) := by
    have hpt (t : ℝ) : c i + a i * zero.cylindricalEndLift (R + t * I) =
        circleMap (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2)
          (arg (a i) + arg zero.endScale - 2 * π * t) := by
      have h := norm_mul_exp_arg_mul_I (a i)
      rw [cylindricalEndLift_ofReal_add_ofReal_mul_I, circleMap, circleMap, endCenter_zero,
        norm_endScale (by decide), add_sub_assoc, ofReal_add, add_mul, Complex.exp_add]
      push_cast
      linear_combination (-(cexp (-(2 * ↑π * ↑R)) / 2 *
        cexp ((↑(arg zero.endScale) - 2 * ↑π * ↑t) * I))) * h
    simp only [hpt]
    exact ω.loopArea_comp_circleMap_sub_mul u _ _ _
  have hinf : ω.loopArea (fun t ↦ u (inf.cylindricalEndLift (-R + t * I))) =
      -ω.loopArea (fun t ↦ u (circleMap 0 (2 * Real.exp (2 * π * R)) (2 * π * t))) := by
    have h := ω.loopArea_cylindricalEndLift u inf (-R)
    simp only [ofReal_neg, endCenter_inf, endScale_inf, Complex.norm_ofNat, mul_neg,
      neg_neg] at h
    exact h
  have hD := ω.integral_fderiv_apply_closedBall_sdiff_biUnion_ball Finset.univ 0
    (ρ := 2 * Real.exp (2 * π * R)) (by positivity) c
    (r := fun i ↦ ‖a i‖ * Real.exp (-(2 * π * R)) / 2)
    (fun i _ ↦ by have := norm_pos_iff.2 (ha i); positivity)
    (fun i _ ↦ by
      rw [sub_zero]
      nlinarith [hout i, norm_nonneg (a i), Real.exp_pos (-(2 * π * R))])
    (fun i _ j _ hij ↦ by
      nlinarith [hsep hij, norm_nonneg (a i), norm_nonneg (a j), Real.exp_pos (-(2 * π * R))])
    (by simpa only [Finset.mem_univ, iUnion_true] using hu)
  simp only [Finset.mem_univ, iUnion_true] at hD
  rw [hD, hinf, Finset.sum_congr rfl fun i _ ↦ hin i, Finset.sum_neg_distrib]
  ring

end TauCeti.SymplecticForm
