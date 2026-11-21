/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Annulus.TwistBand
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Faces of the twist band and the directions of the momenta

Let `F = (X, Y)` be an area-preserving `C²` twist map of a strip `ℝ × J` over an open interval
`J ∋ 0`, mapping the line `y = 0` into itself, and let `S'` be its band generating function
(`TauCeti.stripBandGeneratingFunction`), with the convention `y = -∂₁ S'(x, X)`,
`Y = ∂₂ S'(x, X)`. In the generating-function proof of the Poincaré–Birkhoff theorem a chain of
such factors `F_k` is studied through the cyclic action `W = Σ_k S'_k(x_k, x_(k+1))`, whose
negative gradient moves the positions with velocities `dx_k/dt = y_k - Y_(k-1)`, the momenta being
`y_k = -∂₁ S'_k(x_k, x_(k+1))` and `Y_k = ∂₂ S'_k(x_k, x_(k+1))`. Along this flow the input
momentum of the factor `k` moves with velocity

`dy_k/dt = -d²S'_k((dx_k/dt, dx_(k+1)/dt), (1, 0))`.

The compact block of admissible configurations is cut out by `0 ≤ y_k ≤ 1`. This file computes
the direction of `dy_k/dt` on its faces, the configurations with `y_k = c` for a height `c ∈ J`
whose line `y = c` the factor maps into itself, `Y(x, c) = c`; for a lift of an annulus map these
are the two boundary circles `c = 0` and `c = 1`. There `Y_k = c` too, so
`dx_k/dt = c - Y_(k-1)` and `dx_(k+1)/dt = y_(k+1) - c`.

* On a preserved line `y = c`, `Y_x = 0`. With the area condition
  `X_x Y_y - X_y Y_x = 1` this gives `X_x Y_y = 1`, where `X_x = B'` is the derivative of the
  boundary graph `B(x) = X(x, c)`. By the Hessian formula of
  `TauCeti.fderiv_fderiv_stripBandGeneratingFunction_apply`, the differentials of the two momenta
  at a point `(x, B(x))` of the face are proportional: `B' dY = dy`
  (`TauCeti.deriv_mul_fderiv_fderiv_stripBandGeneratingFunction_apply_zero_one`). Applied to the
  direction `(1, 0)` this is the identity `S'_11 = -S'_12 B'` of the second derivatives.
* On the face the velocity of the momentum is
  `dy_k/dt = (B'(Y_(k-1) - c) + (y_(k+1) - c)) / X_y`
  (`TauCeti.neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face`).
  When the boundary graph is weakly increasing at `x`, `B' ≥ 0`, and the neighbouring momenta
  `Y_(k-1)` and `y_(k+1)` lie on the same side of `c` as the block, as they do at the lower face
  `c = 0` and at the upper face `c = 1` for momenta in `[0, 1]`, the numerator has a definite sign
  (`TauCeti.mul_neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face_nonneg`,
  `TauCeti.mul_neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face_nonpos`). So for a positive
  twist, `X_y > 0`, the momentum moves weakly into the block on both faces, and for a negative
  twist weakly out of it. If moreover `B' > 0`, it is stationary exactly when both neighbouring
  momenta equal `c`
  (`TauCeti.neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face_eq_zero_iff`).

The worked example at the end checks these signs on the negative twist
`(x, y) ↦ (x - (6y + 1) / 8, y)`: with neighbouring momenta `1 / 8` on the lower face and `7 / 8`
on the upper face, the momentum velocities are `-1 / 3` and `1 / 3`, both outward.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

open Set

namespace TauCeti

variable {F : ℝ × ℝ → ℝ × ℝ} {J : Set ℝ}

/-- Where `F = (X, Y)` is differentiable at `(x, c)`, the horizontal slice `s ↦ X(s, c)` has
derivative `X_x(x, c)` at `x`. -/
private theorem hasDerivAt_fst_slice_left {x c : ℝ} (hd : DifferentiableAt ℝ F (x, c)) :
    HasDerivAt (fun s ↦ (F (s, c)).1) (fderiv ℝ F (x, c) (1, 0)).1 x :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_slice_left hd)

/-- Where `F = (X, Y)` is differentiable at `(x, c)`, the horizontal slice `s ↦ Y(s, c)` has
derivative `Y_x(x, c)` at `x`. -/
private theorem hasDerivAt_snd_slice_left {x c : ℝ} (hd : DifferentiableAt ℝ F (x, c)) :
    HasDerivAt (fun s ↦ (F (s, c)).2) (fderiv ℝ F (x, c) (1, 0)).2 x :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_slice_left hd)

/-- **The momenta on a face of the band.** On a strip `ℝ × J` over an open interval `J`
containing `0`, let `F = (X, Y)` be `C²`, twist, preserve area and map the line `y = 0` into
itself, and let it map the line `y = c`, `c ∈ J`, into itself as well. At the point
`(x, B(x))` of the corresponding boundary graph `B(x) = X(x, c)`, the differentials of the input
momentum `y = -∂₁ S'` and of the output momentum `Y = ∂₂ S'` of the band generating function `S'`
are proportional, `B'(x) dY = dy`. In the direction `(1, 0)` this is `S'_11 = -S'_12 B'(x)`. -/
theorem deriv_mul_fderiv_fderiv_stripBandGeneratingFunction_apply_zero_one (hJ : IsOpen J)
    (hJc : J.OrdConnected) (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q)
    (hY : ∀ x, (F (x, 0)).2 = 0) (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c : ℝ} (hc : c ∈ J)
    (hface : ∀ s, (F (s, c)).2 = c) (x : ℝ) (v : ℝ × ℝ) :
    deriv (fun s ↦ (F (s, c)).1) x *
        fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F (x, c)) v (0, 1) =
      -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F (x, c)) v
        (1, 0) := by
  have hq : (x, c) ∈ Prod.snd ⁻¹' J := mem_preimage.2 hc
  have hd := (hF _ hq).differentiableAt two_ne_zero
  have hB := (hasDerivAt_fst_slice_left hd).deriv
  -- On the face `Y_x = 0`, so the area condition reads `X_x Y_y = 1`.
  have hXY : (fderiv ℝ F (x, c) (1, 0)).1 * (fderiv ℝ F (x, c) (0, 1)).2 = 1 := by
    have h : (fderiv ℝ F (x, c) (1, 0)).1 * (fderiv ℝ F (x, c) (0, 1)).2 -
        (fderiv ℝ F (x, c) (1, 0)).2 * (fderiv ℝ F (x, c) (0, 1)).1 = 1 := by
      have h := hdet _ hq
      rwa [ContinuousLinearMap.det, LinearMap.det_finTwoProd] at h
    -- `Y_x(x, c) = 0`, since `s ↦ Y(s, c)` is constant.
    have hYx := hasDerivAt_snd_slice_left hd
    rw [funext hface] at hYx
    rwa [← (hasDerivAt_const x c).unique hYx, zero_mul, sub_zero] at h
  have htw := htwist _ hq
  rw [hB, fderiv_fderiv_stripBandGeneratingFunction_apply hJ hJc h0 hF hY hdet htwist hq,
    fderiv_fderiv_stripBandGeneratingFunction_apply hJ hJc h0 hF hY hdet htwist hq]
  field_simp
  linear_combination v.2 * hXY

/-- **The velocity of the momentum on a face.** In the setting of
`TauCeti.fderiv_fderiv_stripBandGeneratingFunction_apply`, at the point `(x, B(x))` of the
boundary graph `B(x) = X(x, c)` of a height `c ∈ J`, the derivative of the input momentum
`y = -∂₁ S'` along `(c - a, b - c)` is `(B'(x) (a - c) + (b - c)) / X_y(x, c)`.

When the input momentum of a factor of a chain is `c` and its output momentum is `c` too, this is
the velocity of that input momentum under the negative gradient flow of the cyclic action, with
`a` the incoming momentum `Y_(k-1)` and `b` the next input momentum `y_(k+1)`. -/
theorem neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face (hJ : IsOpen J)
    (hJc : J.OrdConnected) (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q)
    (hY : ∀ x, (F (x, 0)).2 = 0) (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c : ℝ} (hc : c ∈ J)
    (x a b : ℝ) :
    -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F (x, c))
        (c - a, b - c) (1, 0) =
      (deriv (fun s ↦ (F (s, c)).1) x * (a - c) + (b - c)) / (fderiv ℝ F (x, c) (0, 1)).1 := by
  have hq : (x, c) ∈ Prod.snd ⁻¹' J := mem_preimage.2 hc
  have hd := (hF _ hq).differentiableAt two_ne_zero
  have hB := (hasDerivAt_fst_slice_left hd).deriv
  rw [hB, fderiv_fderiv_stripBandGeneratingFunction_apply hJ hJc h0 hF hY hdet htwist hq]
  ring

/-- **The momentum does not leave a lower face against the twist.** In the setting of
`TauCeti.neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face`, if the boundary graph is
weakly increasing at `x`, `0 ≤ B'(x)`, and both neighbouring momenta `a` and `b` are at least
`c`, then the velocity `dy/dt` of the momentum on the face satisfies `0 ≤ X_y dy/dt`. At the
lower face `c = 0` of the block `0 ≤ y ≤ 1`, the momentum moves weakly into the block for a positive
twist `X_y > 0` and weakly out of it for a negative twist. -/
theorem mul_neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face_nonneg (hJ : IsOpen J)
    (hJc : J.OrdConnected) (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q)
    (hY : ∀ x, (F (x, 0)).2 = 0) (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c : ℝ} (hc : c ∈ J) {x a b : ℝ}
    (hB : 0 ≤ deriv (fun s ↦ (F (s, c)).1) x) (ha : c ≤ a) (hb : c ≤ b) :
    0 ≤ (fderiv ℝ F (x, c) (0, 1)).1 *
      -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F (x, c))
        (c - a, b - c) (1, 0) := by
  have hq : (x, c) ∈ Prod.snd ⁻¹' J := mem_preimage.2 hc
  rw [neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face hJ hJc h0 hF hY hdet htwist hc,
    mul_div_cancel₀ _ (htwist _ hq)]
  have := mul_nonneg hB (sub_nonneg.2 ha)
  linarith

/-- **The momentum does not leave an upper face against the twist.** In the setting of
`TauCeti.neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face`, if the boundary graph is
weakly increasing at `x`, `0 ≤ B'(x)`, and both neighbouring momenta `a` and `b` are at most
`c`, then the velocity `dy/dt` of the momentum on the face satisfies `X_y dy/dt ≤ 0`. At the
upper face `c = 1` of the block `0 ≤ y ≤ 1`, the momentum moves weakly into the block for a positive
twist `X_y > 0` and weakly out of it for a negative twist. -/
theorem mul_neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face_nonpos (hJ : IsOpen J)
    (hJc : J.OrdConnected) (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q)
    (hY : ∀ x, (F (x, 0)).2 = 0) (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c : ℝ} (hc : c ∈ J) {x a b : ℝ}
    (hB : 0 ≤ deriv (fun s ↦ (F (s, c)).1) x) (ha : a ≤ c) (hb : b ≤ c) :
    (fderiv ℝ F (x, c) (0, 1)).1 *
      -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F (x, c))
        (c - a, b - c) (1, 0) ≤ 0 := by
  have hq : (x, c) ∈ Prod.snd ⁻¹' J := mem_preimage.2 hc
  rw [neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face hJ hJc h0 hF hY hdet htwist hc,
    mul_div_cancel₀ _ (htwist _ hq)]
  have := mul_nonpos_of_nonneg_of_nonpos hB (sub_nonpos.2 ha)
  linarith

/-- **Stationary momenta on a face.** In the setting of
`TauCeti.neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face`, if the boundary graph is
increasing, `B'(x) > 0`, and the neighbouring momenta `a` and `b` lie on the same side of `c`,
then the velocity of the momentum on the face vanishes exactly when `a = c` and `b = c`. -/
theorem neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face_eq_zero_iff (hJ : IsOpen J)
    (hJc : J.OrdConnected) (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q)
    (hY : ∀ x, (F (x, 0)).2 = 0) (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c : ℝ} (hc : c ∈ J) {x a b : ℝ}
    (hB : 0 < deriv (fun s ↦ (F (s, c)).1) x) (hab : c ≤ a ∧ c ≤ b ∨ a ≤ c ∧ b ≤ c) :
    -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F (x, c))
        (c - a, b - c) (1, 0) = 0 ↔ a = c ∧ b = c := by
  have hq : (x, c) ∈ Prod.snd ⁻¹' J := mem_preimage.2 hc
  rw [neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face hJ hJc h0 hF hY hdet htwist hc,
    div_eq_zero_iff, or_iff_left (htwist _ hq)]
  constructor
  · intro h
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h1 := mul_nonneg hB.le (sub_nonneg.2 ha)
      have h2 : deriv (fun s ↦ (F (s, c)).1) x * (a - c) = 0 := by linarith
      exact ⟨by simpa [hB.ne', sub_eq_zero] using h2, by linarith⟩
    · have h1 := mul_nonpos_of_nonneg_of_nonpos hB.le (sub_nonpos.2 ha)
      have h2 : deriv (fun s ↦ (F (s, c)).1) x * (a - c) = 0 := by linarith
      exact ⟨by simpa [hB.ne', sub_eq_zero] using h2, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-! ### A worked example

The negative twist `N(x, y) = (x - (6y + 1) / 8, y)`, the affine shear with `a = -1 / 8` and
`c = -3 / 4`, has `X_x = 1` and `X_y = -3 / 4` and preserves both lines `y = 0` and `y = 1`. On
the lower face, with both neighbouring momenta `1 / 8`, its momentum moves with velocity
`-1 / 3`, and on the upper face, with both neighbouring momenta `7 / 8`, with velocity `1 / 3`:
both point out of the block `0 ≤ y ≤ 1`, as they must for a negative twist. -/

example (x : ℝ) :
    -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction
        (fun q : ℝ × ℝ ↦ (q.1 + -(1 / 8) + -(3 / 4) * q.2, q.2)) univ))
        (stripTwistCoord (fun q : ℝ × ℝ ↦ (q.1 + -(1 / 8) + -(3 / 4) * q.2, q.2)) (x, 0))
        (0 - 1 / 8, 1 / 8 - 0) (1, 0) = -(1 / 3) ∧
    -fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction
        (fun q : ℝ × ℝ ↦ (q.1 + -(1 / 8) + -(3 / 4) * q.2, q.2)) univ))
        (stripTwistCoord (fun q : ℝ × ℝ ↦ (q.1 + -(1 / 8) + -(3 / 4) * q.2, q.2)) (x, 1))
        (1 - 7 / 8, 7 / 8 - 1) (1, 0) = 1 / 3 := by
  set N : ℝ × ℝ → ℝ × ℝ := fun q ↦ (q.1 + -(1 / 8) + -(3 / 4) * q.2, q.2)
  have hN (q : ℝ × ℝ) : HasFDerivAt N ((ContinuousLinearMap.fst ℝ ℝ ℝ +
      (-(3 / 4) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
    hasFDerivAt_affineShear _ _ q
  have hF (q : ℝ × ℝ) (_ : q ∈ Prod.snd ⁻¹' (univ : Set ℝ)) : ContDiffAt ℝ 2 N q := by
    fun_prop
  have hdet (q : ℝ × ℝ) (_ : q ∈ Prod.snd ⁻¹' (univ : Set ℝ)) : (fderiv ℝ N q).det = 1 := by
    rw [(hN q).fderiv, ContinuousLinearMap.det, LinearMap.det_finTwoProd]
    simp
  have htwist (q : ℝ × ℝ) (_ : q ∈ Prod.snd ⁻¹' (univ : Set ℝ)) :
      (fderiv ℝ N q (0, 1)).1 ≠ 0 := by
    simp [(hN q).fderiv]
  have hB (c : ℝ) : deriv (fun s ↦ (N (s, c)).1) x = 1 := by
    simp [N]
  have hface (c : ℝ) := neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face isOpen_univ
    ordConnected_univ (mem_univ 0) hF (fun _ ↦ rfl) hdet htwist (mem_univ c) x
  rw [hface, hface, hB, hB, (hN _).fderiv, (hN _).fderiv]
  norm_num

end TauCeti
