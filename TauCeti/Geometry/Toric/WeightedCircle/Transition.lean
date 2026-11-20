/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Toric.WeightedCircle.Slice
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Symplectic.Complex.Polar
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The changes of slices of the weighted ellipsoid quotient are local symplectomorphisms

Let `a, b` be positive integers and `ε > 0`. The circle acts on `ℂ²` by the weighted rotations
`u • (z₁, z₂) = (u ^ a z₁, u ^ b z₂)` (`TauCeti.Toric.weightedRotation`) and preserves the
ellipsoid `E : a |z₁|² + b |z₂|² = 2 ε`. The orbit space `E / S¹` has two slice charts
(`TauCeti.Geometry.Toric.WeightedCircle.Slice`): the discs `b |w|² < 2 ε` over `z₁ ≠ 0` and
`a |u|² < 2 ε` over `z₂ ≠ 0`, with residual groups `ℤ / a` and `ℤ / b`, on which the standard
symplectic form of `ℂ²` restricts to the area forms `d(Re w) ∧ d(Im w)` and `d(Re u) ∧ d(Im u)`.
The change from the first slice to the second sends the orbit through the slice point over a
nonzero `w` to the orbit through the slice point over

`exp(-i a arg(w) / b) √((2 ε - b |w|²) / a)`

(`TauCeti.Toric.weightedSliceTransition`). It is only defined up to the residual group `ℤ / b`,
and the principal argument makes it jump across the negative real axis. This file shows that it is
a local symplectomorphism between the two slices: the two area forms agree on the overlap of the
charts, as they must for both to be the reduced symplectic form of `E / S¹` read in a slice.

For a nonzero `w₀`, the **branch near `w₀`** (`TauCeti.Toric.weightedSliceTransitionBranch`)
replaces `arg(w)` by `arg(w / w₀) + arg(w₀)`, an argument of `w` which is smooth off the ray
where `w / w₀` is a nonpositive real, in particular near `w₀`.

* **Branches are changes of slices.** The branch near `w₀` agrees with the change of slices at
  `w₀`, differs from it by an element of the residual group `ℤ / b` at every nonzero `w`
  (`TauCeti.Toric.exists_weightedSliceTransitionBranch_eq`), and the rotation by
  `exp(-i (arg(w / w₀) + arg(w₀)) / b)` carries the slice point over `w` to the slice point over its
  value
  (`weightedRotation_weightedSliceFst_eq_weightedSliceSnd_weightedSliceTransitionBranch`).
* **Branches are local symplectomorphisms.** Off that ray, on the open disc `b |w|² < 2 ε`, the
  branch is smooth (`TauCeti.Toric.contDiffAt_weightedSliceTransitionBranch`), its differential
  preserves the area form
  (`TauCeti.Toric.stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch`), and it is a
  local diffeomorphism (`TauCeti.Toric.isLocalDiffeomorphAt_weightedSliceTransitionBranch`).

The branch is `e^{iθ} r` for the angle `θ = -a (arg(w / w₀) + arg(w₀)) / b` and the radius
`r = √((2 ε - b |w|²) / a)`, so it pulls the area form back to `r dr ∧ dθ`
(`TauCeti.stdComplexSymplecticForm_fderiv_circleExp_mul_ofReal`). Here
`r dr = -(b / a) d(|w|² / 2)` and `dθ = -(a / b) dφ` for the angle `φ` of `w`, so
`r dr ∧ dθ = d(|w|² / 2) ∧ dφ`, which is the area form in polar coordinates
(`TauCeti.stdComplexSymplecticForm_apply_eq_polar`). The two weights cancel: the radius shrinks by
the factor `b / a` in `d(|w|²)` as the angle turns `a / b` times as fast. Since the residual
groups act by rotations, which preserve the area form (`TauCeti.stdComplexSymplecticForm_mul_mul`),
every choice of branch gives the same conclusion. The change from the second slice to the first is
the change of slices for the weights `(b, a)`, read through
`TauCeti.Toric.weightedSliceSnd_eq_swap`.

## Main results

* `TauCeti.Toric.weightedSliceTransitionBranch`: the branch near `w₀` of the change of slices.
* `TauCeti.Toric.exists_weightedSliceTransitionBranch_eq`: branches differ from the change of
  slices by the residual group `ℤ / b`.
* `weightedRotation_weightedSliceFst_eq_weightedSliceSnd_weightedSliceTransitionBranch`: every
  branch is a change of slices.
* `TauCeti.Toric.contDiffAt_weightedSliceTransitionBranch`,
  `TauCeti.Toric.stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch`,
  `TauCeti.Toric.isLocalDiffeomorphAt_weightedSliceTransitionBranch`: the branches are smooth local
  diffeomorphisms preserving the area form.
* `TauCeti.Toric.contDiffAt_weightedSliceTransition`,
  `TauCeti.Toric.stdComplexSymplecticForm_fderiv_weightedSliceTransition`,
  `TauCeti.Toric.isLocalDiffeomorphAt_weightedSliceTransition`: the same for the change of slices
  itself off the nonpositive real axis.

## References

* E. Lerman and S. Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. **349** (1997), 4201–4230, Section 1 (weighted projective
  spaces as symplectic orbifold quotients).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (reduction by circle actions with finite stabilizers).
-/

public section

noncomputable section

open Set Real Complex
open scoped InnerProductSpace Manifold

namespace TauCeti.Toric

variable {a b : ℕ} {ε : ℝ}

/-! ### Branches of the change of slices -/

variable (a b ε) in
/-- The **branch near `w₀` of the change of slices**,
`w ↦ exp(-i a (arg(w / w₀) + arg(w₀)) / b) √((2 ε - b |w|²) / a)`. -/
def weightedSliceTransitionBranch (w₀ w : ℂ) : ℂ :=
  (Circle.exp (-(a * (arg (w / w₀) + arg w₀) / b)) : ℂ) * ((√((2 * ε - b * ‖w‖ ^ 2) / a) : ℝ) : ℂ)

/-- The defining formula of the branch near `w₀` of the change of slices. -/
theorem weightedSliceTransitionBranch_apply (w₀ w : ℂ) :
    weightedSliceTransitionBranch a b ε w₀ w =
      (Circle.exp (-(a * (arg (w / w₀) + arg w₀) / b)) : ℂ) *
        ((√((2 * ε - b * ‖w‖ ^ 2) / a) : ℝ) : ℂ) :=
  (rfl)

/-- The branch at `1` is the change of slices `TauCeti.Toric.weightedSliceTransition`. -/
@[simp]
theorem weightedSliceTransitionBranch_one :
    weightedSliceTransitionBranch a b ε 1 = weightedSliceTransition a b ε := by
  funext w
  rw [weightedSliceTransitionBranch_apply, weightedSliceTransition_apply, div_one, arg_one,
    add_zero]

/-- Every branch agrees with the change of slices at its base point. -/
@[simp]
theorem weightedSliceTransitionBranch_self (w₀ : ℂ) :
    weightedSliceTransitionBranch a b ε w₀ w₀ = weightedSliceTransition a b ε w₀ := by
  rw [weightedSliceTransitionBranch_apply, weightedSliceTransition_apply]
  rcases eq_or_ne w₀ 0 with rfl | hw₀
  · rw [div_zero, arg_zero, add_zero]
  · rw [div_self hw₀, arg_one, zero_add]

/-- The branches of the change of slices have the norm `√((2 ε - b |w|²) / a)` of the first
coordinate of the slice point over `w`. -/
theorem norm_weightedSliceTransitionBranch (w₀ w : ℂ) :
    ‖weightedSliceTransitionBranch a b ε w₀ w‖ = √((2 * ε - b * ‖w‖ ^ 2) / a) := by
  rw [weightedSliceTransitionBranch_apply, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The argument of `w / w₀` plus that of `w₀` is the argument of `w` up to a multiple of `2π`. -/
private theorem exists_arg_div_add_arg_eq {w₀ w : ℂ} (hw₀ : w₀ ≠ 0) (hw : w ≠ 0) :
    ∃ m : ℤ, arg (w / w₀) + arg w₀ = arg w + 2 * π * m := by
  have h := arg_div_coe_angle hw hw₀
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by linarith⟩

/-- **Every branch is a change of slices.** For `w` in the closed disc `b |w|² ≤ 2 ε`, the circle
element `exp(-i (arg(w / w₀) + arg(w₀)) / b)` rotates the slice point over `w` onto the slice over
`z₂ ≠ 0`, at the point over the value at `w` of the branch near `w₀` of the change of slices. -/
theorem weightedRotation_weightedSliceFst_eq_weightedSliceSnd_weightedSliceTransitionBranch
    (ha : 0 < a) (hb : 0 < b) {w₀ w : ℂ} (hw₀ : w₀ ≠ 0) (hwε : b * ‖w‖ ^ 2 ≤ 2 * ε) :
    weightedRotation a b (Circle.exp (-((arg (w / w₀) + arg w₀) / b)))
        (weightedSliceFst a b ε w) =
      weightedSliceSnd a b ε (weightedSliceTransitionBranch a b ε w₀ w) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  refine Prod.ext ?_ ?_
  · rw [weightedRotation_fst, weightedSliceSnd_fst, weightedSliceTransitionBranch_apply,
      ← Circle.coe_pow, ← Circle.exp_natCast_mul, weightedSliceFst_fst]
    congr 3
    ring
  · have hs : (2 * ε - a * ‖weightedSliceTransitionBranch a b ε w₀ w‖ ^ 2) / b = ‖w‖ ^ 2 := by
      rw [norm_weightedSliceTransitionBranch, Real.sq_sqrt (div_nonneg (by linarith) ha'.le)]
      field_simp
      ring
    rw [weightedRotation_snd, weightedSliceSnd_snd, hs, Real.sqrt_sq (norm_nonneg _),
      weightedSliceFst_snd, ← Circle.coe_pow, ← Circle.exp_natCast_mul]
    rcases eq_or_ne w 0 with rfl | hw
    · rw [mul_zero, norm_zero, ofReal_zero]
    obtain ⟨m, hm⟩ := exists_arg_div_add_arg_eq hw₀ hw
    have hv : Circle.exp (b * -((arg (w / w₀) + arg w₀) / b)) = Circle.exp (-arg w) :=
      Circle.exp_eq_exp.2 ⟨-m, by rw [hm]; field_simp; push_cast; ring⟩
    rw [hv, Circle.exp_neg_arg_mul_self]

/-- The branches of the change of slices differ from it by the residual group `ℤ / b`: off the
origin, the value of the branch near `w₀` is `exp(-2π i a k / b)` times that of the change of slices
for some `k ∈ ℤ / b`. -/
theorem exists_weightedSliceTransitionBranch_eq [NeZero b] {w₀ w : ℂ} (hw₀ : w₀ ≠ 0)
    (hw : w ≠ 0) :
    ∃ k : ZMod b, weightedSliceTransitionBranch a b ε w₀ w =
      ((ZMod.toCircle (-k) ^ a : Circle) : ℂ) * weightedSliceTransition a b ε w := by
  obtain ⟨m, hm⟩ := exists_arg_div_add_arg_eq hw₀ hw
  have hm' : (arg (w / w₀) : ℂ) + arg w₀ = arg w + 2 * π * m := by exact_mod_cast hm
  refine ⟨m, ?_⟩
  rw [weightedSliceTransitionBranch_apply, weightedSliceTransition_apply, ← mul_assoc]
  congr 1
  rw [Circle.coe_pow, ← Int.cast_neg, ZMod.toCircle_intCast, Circle.coe_exp, Circle.coe_exp,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [hm']
  ring

/-! ### Smoothness and the area form -/

/-- **The branches are smooth.** The branch near `w₀` of the change of slices is smooth at every
point `w` of the open disc `b |w|² < 2 ε` off the ray where `w / w₀` is a nonpositive real. -/
theorem contDiffAt_weightedSliceTransitionBranch {w₀ w : ℂ} (hw : w / w₀ ∈ slitPlane)
    (hwε : b * ‖w‖ ^ 2 < 2 * ε) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (weightedSliceTransitionBranch a b ε w₀) w := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- For `a = 0` the radius `√(x / 0)` vanishes, so the branch is the zero function.
    have h0 : weightedSliceTransitionBranch 0 b ε w₀ = fun _ ↦ 0 := by
      funext y
      rw [weightedSliceTransitionBranch_apply, Nat.cast_zero, div_zero, Real.sqrt_zero,
        ofReal_zero, mul_zero]
    rw [h0]
    exact contDiffAt_const
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hθ : ContDiffAt ℝ n (fun y : ℂ ↦ -(a * (arg (y / w₀) + arg w₀) / b)) w :=
    ((contDiffAt_const.mul (((contDiffAt_arg hw).comp w (contDiffAt_id.div_const w₀)).add
      contDiffAt_const)).div_const _).neg
  have hr : ContDiffAt ℝ n (fun y : ℂ ↦ √((2 * ε - b * ‖y‖ ^ 2) / a)) w :=
    ((contDiffAt_const.sub (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)).div_const
      _).sqrt (div_pos (by linarith) ha').ne'
  rw [funext (weightedSliceTransitionBranch_apply (a := a) (b := b) (ε := ε) w₀)]
  simp only [Circle.coe_exp]
  exact ((ofRealCLM.contDiff.contDiffAt.comp w hθ).mul contDiffAt_const).cexp.mul
    (ofRealCLM.contDiff.contDiffAt.comp w hr)

/-- **The branches preserve the area form.** At every point `w` of the open disc `b |w|² < 2 ε` off
the ray where `w / w₀` is a nonpositive real, the differential of the branch near `w₀` of the
change of slices preserves the area form `d(Re w) ∧ d(Im w)`. -/
theorem stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch (ha : 0 < a) (hb : 0 < b)
    {w₀ w : ℂ} (hw : w / w₀ ∈ slitPlane) (hwε : b * ‖w‖ ^ 2 < 2 * ε) (v v' : ℂ) :
    stdComplexSymplecticForm (fderiv ℝ (weightedSliceTransitionBranch a b ε w₀) w v)
        (fderiv ℝ (weightedSliceTransitionBranch a b ε w₀) w v') =
      stdComplexSymplecticForm v v' := by
  obtain ⟨hw', hw₀⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hw)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  -- The branch is `e^{iθ} r` for the angle `θ` and the radius `r` below.
  have hθ : HasFDerivAt (fun y : ℂ ↦ -(a * (arg (y / w₀) + arg w₀) / b)) _ w :=
    (((((hasDerivAt_id w).div_const w₀).hasFDerivAt_arg hw).add_const (arg w₀)).const_mul
      (a : ℝ) |>.mul_const ((b : ℝ)⁻¹) |>.neg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simp only [id, div_eq_mul_inv, Pi.neg_apply])
  have hr : HasFDerivAt (fun y : ℂ ↦ √((2 * ε - b * ‖y‖ ^ 2) / a)) _ w :=
    (((((hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_mul (b : ℝ)).const_sub (2 * ε)).mul_const
      ((a : ℝ)⁻¹)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ div_eq_mul_inv _ _)).sqrt
      (div_pos (by linarith) ha').ne'
  have hfun : weightedSliceTransitionBranch a b ε w₀ = fun y ↦
      (Circle.exp (-(a * (arg (y / w₀) + arg w₀) / b)) : ℂ) *
        ((√((2 * ε - b * ‖y‖ ^ 2) / a) : ℝ) : ℂ) :=
    funext (weightedSliceTransitionBranch_apply w₀)
  rw [hfun, stdComplexSymplecticForm_fderiv_circleExp_mul_ofReal hθ hr,
    stdComplexSymplecticForm_apply_eq_polar hw']
  have hw₀w : 1 / w₀ / (id w / w₀) = 1 / w := by
    rw [id_eq]
    field_simp
  have hs : √((2 * ε - b * ‖w‖ ^ 2) / a) ≠ 0 :=
    (Real.sqrt_pos.2 (div_pos (by linarith) ha')).ne'
  simp only [smul_neg, neg_apply, smul_apply, coe_innerSL_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, imCLM_apply, hw₀w, mul_one_div, Nat.cast_ofNat]
  field_simp

/-- **The branches are local diffeomorphisms.** At every point `w` of the open disc
`b |w|² < 2 ε` off the ray where `w / w₀` is a nonpositive real, the branch near `w₀` of the
change of slices is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorphAt_weightedSliceTransitionBranch (ha : 0 < a) (hb : 0 < b) {w₀ w : ℂ}
    (hw : w / w₀ ∈ slitPlane) (hwε : b * ‖w‖ ^ 2 < 2 * ε) {n : WithTop ℕ∞} :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (weightedSliceTransitionBranch a b ε w₀) w := by
  -- The differential preserves the nondegenerate area form, so it is injective.
  have hinj : Function.Injective (fderiv ℝ (weightedSliceTransitionBranch a b ε w₀) w) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    have h := stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch ha hb hw hwε v (I * v)
    rw [hv] at h
    simp only [map_zero, LinearMap.zero_apply, stdComplexSymplecticForm_apply, mul_im, I_re,
      zero_mul, I_im, one_mul, zero_add, mul_re, zero_sub, mul_neg, sub_neg_eq_add] at h
    exact Complex.normSq_eq_zero.mp (by rw [Complex.normSq_apply]; linarith)
  let t : Set ℂ := {y | y / w₀ ∈ slitPlane ∧ b * ‖y‖ ^ 2 < 2 * ε}
  have ht : IsOpen t :=
    (isOpen_slitPlane.preimage (continuous_id.div_const w₀)).inter
      (isOpen_lt (continuous_const.mul (continuous_norm.pow 2)) continuous_const)
  -- The inverse function theorem gives the analytic case, which implies every other one.
  refine (isLocalDiffeomorphAt_of_fderiv_eq (n := ⊤) (t := t)
    (fun y hy ↦ (contDiffAt_weightedSliceTransitionBranch hy.1 hy.2).contDiffWithinAt) ht
    ⟨hw, hwε⟩ le_top (e := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv)
    (by ext; simp [LinearEquiv.coe_ofInjectiveEndo])).of_le le_top

/-! ### The change of slices -/

/-- **The change of slices is smooth** on the open disc `b |w|² < 2 ε` off the nonpositive real
axis. -/
theorem contDiffAt_weightedSliceTransition {w : ℂ} (hw : w ∈ slitPlane)
    (hwε : b * ‖w‖ ^ 2 < 2 * ε) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (weightedSliceTransition a b ε) w := by
  rw [← weightedSliceTransitionBranch_one]
  exact contDiffAt_weightedSliceTransitionBranch (by rwa [div_one]) hwε

/-- **The change of slices preserves the area form** on the open disc `b |w|² < 2 ε` off the
nonpositive real axis. -/
theorem stdComplexSymplecticForm_fderiv_weightedSliceTransition (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : w ∈ slitPlane) (hwε : b * ‖w‖ ^ 2 < 2 * ε) (v v' : ℂ) :
    stdComplexSymplecticForm (fderiv ℝ (weightedSliceTransition a b ε) w v)
        (fderiv ℝ (weightedSliceTransition a b ε) w v') =
      stdComplexSymplecticForm v v' := by
  rw [← weightedSliceTransitionBranch_one]
  exact stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch ha hb (by rwa [div_one])
    hwε v v'

/-- **The change of slices is a local diffeomorphism** on the open disc `b |w|² < 2 ε` off the
nonpositive real axis. -/
theorem isLocalDiffeomorphAt_weightedSliceTransition (ha : 0 < a) (hb : 0 < b) {w : ℂ}
    (hw : w ∈ slitPlane) (hwε : b * ‖w‖ ^ 2 < 2 * ε) {n : WithTop ℕ∞} :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (weightedSliceTransition a b ε) w := by
  rw [← weightedSliceTransitionBranch_one]
  exact isLocalDiffeomorphAt_weightedSliceTransitionBranch ha hb (by rwa [div_one]) hwε

end TauCeti.Toric
