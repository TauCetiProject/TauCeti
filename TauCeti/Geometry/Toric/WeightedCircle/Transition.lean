/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Toric.WeightedCircle.Slice
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Symplectic.Complex.Polar
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.LinearAlgebra.BilinearForm.Isometry

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
where `w / w₀` is a nonpositive real, in particular near `w₀`. The branch is again a change of
slices, and differs from `weightedSliceTransition` by the residual group `ℤ / b`
(`TauCeti.Geometry.Toric.WeightedCircle.Slice`).

**Branches are local symplectomorphisms.** Off that ray, on the open disc `b |w|² < 2 ε`, the
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

/-- The angle `θ = -a (arg(w / w₀) + arg(w₀)) / b` of the branch near `w₀` has differential
`v ↦ -(a / b) Im (v / w)` off the ray where `w / w₀` is a nonpositive real. -/
private theorem hasFDerivAt_weightedSliceTransitionBranch_angle {w₀ w : ℂ}
    (hw : w / w₀ ∈ slitPlane) :
    HasFDerivAt (fun y : ℂ ↦ -(a * (arg (y / w₀) + arg w₀) / b))
      (-(a / b : ℝ) • (imCLM ∘L ContinuousLinearMap.mul ℝ ℂ w⁻¹)) w := by
  obtain ⟨-, hw₀⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hw)
  refine (((((((hasDerivAt_id w).div_const w₀).hasFDerivAt_arg hw).add_const (arg w₀)).const_mul
    (a : ℝ)).mul_const (b : ℝ)⁻¹).neg.congr_of_eventuallyEq
    (.of_forall fun y ↦ by simp [div_eq_mul_inv])).congr_fderiv ?_
  rw [id_eq, div_div_div_cancel_right₀ hw₀]
  ext v
  simp
  field_simp
  ring

/-- The radius `r = √((2 ε - b |w|²) / a)` of the branches has differential
`v ↦ -(b / a) ⟪w, v⟫ / r` on the open disc `b |w|² < 2 ε`. -/
private theorem hasFDerivAt_weightedSliceTransitionBranch_radius (ha : 0 < a) {w : ℂ}
    (hwε : b * ‖w‖ ^ 2 < 2 * ε) :
    HasFDerivAt (fun y : ℂ ↦ √((2 * ε - b * ‖y‖ ^ 2) / a))
      ((-(b / a) / √((2 * ε - b * ‖w‖ ^ 2) / a)) • innerSL ℝ w) w := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  refine (((((hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_mul (b : ℝ)).const_sub
    (2 * ε)).mul_const (a : ℝ)⁻¹).congr_of_eventuallyEq
    (.of_forall fun y ↦ div_eq_mul_inv _ _)).sqrt (div_pos (by linarith) ha').ne'
    |>.congr_fderiv ?_
  ext v
  simp
  field_simp

/-- **The branches preserve the area form.** At every point `w` of the open disc `b |w|² < 2 ε` off
the ray where `w / w₀` is a nonpositive real, the differential of the branch near `w₀` of the
change of slices preserves the area form `d(Re w) ∧ d(Im w)`. -/
theorem stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch (ha : 0 < a) (hb : 0 < b)
    {w₀ w : ℂ} (hw : w / w₀ ∈ slitPlane) (hwε : b * ‖w‖ ^ 2 < 2 * ε) (v v' : ℂ) :
    stdComplexSymplecticForm (fderiv ℝ (weightedSliceTransitionBranch a b ε w₀) w v)
        (fderiv ℝ (weightedSliceTransitionBranch a b ε w₀) w v') =
      stdComplexSymplecticForm v v' := by
  obtain ⟨hw', -⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hw)
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- The branch is `e^{iθ} r` for the angle `θ` and the radius `r`.
  rw [funext (weightedSliceTransitionBranch_apply (a := a) (b := b) (ε := ε) w₀),
    stdComplexSymplecticForm_fderiv_circleExp_mul_ofReal
      (hasFDerivAt_weightedSliceTransitionBranch_angle hw)
      (hasFDerivAt_weightedSliceTransitionBranch_radius ha hwε),
    stdComplexSymplecticForm_apply_eq_polar hw']
  simp [div_im]
  field_simp
  ring

/-- **The branches are local diffeomorphisms.** At every point `w` of the open disc
`b |w|² < 2 ε` off the ray where `w / w₀` is a nonpositive real, the branch near `w₀` of the
change of slices is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorphAt_weightedSliceTransitionBranch (ha : 0 < a) (hb : 0 < b) {w₀ w : ℂ}
    (hw : w / w₀ ∈ slitPlane) (hwε : b * ‖w‖ ^ 2 < 2 * ε) {n : WithTop ℕ∞} :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (weightedSliceTransitionBranch a b ε w₀) w := by
  -- The differential preserves the nondegenerate area form, so it is injective.
  have hinj : Function.Injective (fderiv ℝ (weightedSliceTransitionBranch a b ε w₀) w) :=
    LinearMap.BilinForm.Isometry.injective (B := stdComplexSymplecticForm.toBilinForm)
      ⟨(fderiv ℝ _ w : ℂ →L[ℝ] ℂ).toLinearMap,
        stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch ha hb hw hwε⟩
      stdComplexSymplecticForm.nondegenerate.1
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
