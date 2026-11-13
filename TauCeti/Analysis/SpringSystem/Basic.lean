/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The exact force and potential of a linear spring

A spring of stiffness `κ` and rest length `ℓ₀` joins two particles. Write `w` for the current
relative vector, the position of the second particle minus that of the first. The spring stores
the potential energy

`springPotential κ ℓ₀ w = (κ / 2) (‖w‖ - ℓ₀)²`

and pulls the first particle along the unit vector `w / ‖w‖` with the force

`springForce κ ℓ₀ w = κ (‖w‖ - ℓ₀) w / ‖w‖`,

so a stretched spring (`‖w‖ > ℓ₀`) draws the particles together and a compressed one pushes
them apart; the second particle feels the opposite force. These are the exact, nonlinear laws
of a Hookean spring. Finite spring systems, such as particles at the vertices of a polygon or a
polyhedron joined along its edges, are sums of such pair forces, and their normal modes come from
linearizing these laws at a rest configuration.

When the spring has zero length, `‖w‖ = 0`, the formula divides by `0`, and the force is then `0`
by Lean's convention; this degenerate configuration never arises near a rest configuration of
positive rest length.

## Main definitions

* `TauCeti.springPotential`: the potential energy `(κ / 2) (‖w‖ - ℓ₀)²`.
* `TauCeti.springForce`: the force `κ (‖w‖ - ℓ₀) w / ‖w‖` on the first particle.

## Main results

* `TauCeti.springPotential_eq_zero_iff`, `TauCeti.springForce_eq_zero_iff`: for `κ ≠ 0`, both
  vanish exactly at the rest length (the force also at zero length, `‖w‖ = 0`).
* `TauCeti.springForce_neg`, `TauCeti.springPotential_neg`: the second end feels the opposite
  force, and the energy does not depend on the orientation of the spring.
* `TauCeti.norm_springForce`: Hooke's law, `‖F‖ = |κ| |‖w‖ - ℓ₀|` away from zero length.
* `TauCeti.hasFDerivAt_springPotential`, `TauCeti.hasGradientAt_springPotential`: in an inner
  product space, away from `w = 0`, the force is the gradient of the potential in `w`.
* `TauCeti.hasFDerivAt_springForce`: away from `w = 0`, the derivative of the force, the stiffness
  of the spring.
* `TauCeti.hasFDerivAt_springForce_norm`, `TauCeti.hasFDerivAt_springForce_add_sub`: at rest, the
  force linearizes to `κ` times the orthogonal projection onto the rest direction, so two
  particles displaced by `uᵢ` and `uⱼ` feel `κ P_v (uⱼ - uᵢ)` to first order.
-/

public section

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The **potential energy of a spring** of stiffness `κ` and rest length `ℓ₀` whose two ends are
separated by the relative vector `w`: `(κ / 2) (‖w‖ - ℓ₀)²`. -/
noncomputable def springPotential (κ ℓ₀ : ℝ) (w : E) : ℝ :=
  κ / 2 * (‖w‖ - ℓ₀) ^ 2

theorem springPotential_def (κ ℓ₀ : ℝ) (w : E) :
    springPotential κ ℓ₀ w = κ / 2 * (‖w‖ - ℓ₀) ^ 2 :=
  (rfl)

/-- A spring of nonnegative stiffness stores nonnegative energy. -/
theorem springPotential_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (ℓ₀ : ℝ) (w : E) :
    0 ≤ springPotential κ ℓ₀ w := by
  rw [springPotential_def]
  positivity

/-- A spring of nonzero stiffness stores no energy exactly at its rest length. -/
theorem springPotential_eq_zero_iff {κ : ℝ} (hκ : κ ≠ 0) (ℓ₀ : ℝ) (w : E) :
    springPotential κ ℓ₀ w = 0 ↔ ‖w‖ = ℓ₀ := by
  simp [springPotential_def, hκ, sub_eq_zero]

/-- Reversing the spring, that is, exchanging its two ends, does not change its energy. -/
@[simp]
theorem springPotential_neg (κ ℓ₀ : ℝ) (w : E) :
    springPotential κ ℓ₀ (-w) = springPotential κ ℓ₀ w := by
  simp [springPotential_def]

variable [NormedSpace ℝ E]

/-- The **force of a spring** of stiffness `κ` and rest length `ℓ₀` on its first end, when the
second end sits at the relative vector `w` from it: `κ (‖w‖ - ℓ₀) w / ‖w‖`, directed along `w`
when the spring is stretched. The second end feels the opposite force. -/
noncomputable def springForce (κ ℓ₀ : ℝ) (w : E) : E :=
  (κ * (‖w‖ - ℓ₀) / ‖w‖) • w

theorem springForce_def (κ ℓ₀ : ℝ) (w : E) :
    springForce κ ℓ₀ w = (κ * (‖w‖ - ℓ₀) / ‖w‖) • w :=
  (rfl)

/-- **The second end feels the opposite force**: reversing the relative vector negates the
force. -/
@[simp]
theorem springForce_neg (κ ℓ₀ : ℝ) (w : E) : springForce κ ℓ₀ (-w) = -springForce κ ℓ₀ w := by
  simp [springForce_def]

/-- A spring of nonzero stiffness exerts no force exactly at its rest length, or when it has zero
length (where the direction `w / ‖w‖` is undefined and the force is `0` by convention). -/
theorem springForce_eq_zero_iff {κ : ℝ} (hκ : κ ≠ 0) (ℓ₀ : ℝ) (w : E) :
    springForce κ ℓ₀ w = 0 ↔ ‖w‖ = ℓ₀ ∨ ‖w‖ = 0 := by
  simp only [springForce_def, smul_eq_zero, div_eq_zero_iff, mul_eq_zero, hκ, false_or,
    sub_eq_zero]
  exact or_iff_left_of_imp fun h ↦ .inr (by rw [h, norm_zero])

/-- **Hooke's law.** Away from zero length, `‖w‖ ≠ 0`, the force of a spring has magnitude `|κ|`
times the deviation `|‖w‖ - ℓ₀|` of its length from the rest length. -/
theorem norm_springForce (κ ℓ₀ : ℝ) {w : E} (hw : ‖w‖ ≠ 0) :
    ‖springForce κ ℓ₀ w‖ = |κ| * |‖w‖ - ℓ₀| := by
  simp [springForce_def, norm_smul, hw]

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The force is the derivative of the potential.** Away from `w = 0`, the derivative of the
potential in the relative vector `w` is `v ↦ ⟪springForce κ ℓ₀ w, v⟫`. -/
theorem hasFDerivAt_springPotential (κ ℓ₀ : ℝ) {w : F} (hw : w ≠ 0) :
    HasFDerivAt (springPotential κ ℓ₀) (innerSL ℝ (springForce κ ℓ₀ w)) w := by
  have hn := hasFDerivAt_norm_of_ne hw
  rw [show springPotential κ ℓ₀ = fun x : F ↦ κ / 2 * (‖x‖ - ℓ₀) ^ 2 from
    funext (springPotential_def κ ℓ₀)]
  refine (((hn.sub_const ℓ₀).pow 2).const_mul (κ / 2)).congr_fderiv ?_
  ext v
  simp [springForce_def]
  field_simp

/-- **The force is the gradient of the potential**: away from `w = 0`, `springForce κ ℓ₀ w` is the
gradient of `springPotential κ ℓ₀` at the relative vector `w`. -/
theorem hasGradientAt_springPotential [CompleteSpace F] (κ ℓ₀ : ℝ) {w : F} (hw : w ≠ 0) :
    HasGradientAt (springPotential κ ℓ₀) (springForce κ ℓ₀ w) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hasFDerivAt_springPotential κ ℓ₀ hw using 1
  ext v
  simp

/-- **The stiffness of a spring.** Away from `w = 0`, the force is differentiable in the relative
vector `w`, with derivative `h ↦ (κ (‖w‖ - ℓ₀) / ‖w‖) h + (κ ℓ₀ ⟪w, h⟫ / ‖w‖³) w`: the tension
rescales the displacement `h`, and the change `⟪w, h⟫ / ‖w‖` of the length acts along `w`. -/
theorem hasFDerivAt_springForce (κ ℓ₀ : ℝ) {w : F} (hw : w ≠ 0) :
    HasFDerivAt (springForce κ ℓ₀)
      ((κ * (‖w‖ - ℓ₀) / ‖w‖) • ContinuousLinearMap.id ℝ F +
        ((κ * ℓ₀ / ‖w‖ ^ 3) • innerSL ℝ w).smulRight w) w := by
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hn := hasFDerivAt_norm_of_ne hw
  have hc : HasFDerivAt (fun x : F ↦ κ * (‖x‖ - ℓ₀) / ‖x‖)
      ((κ * ℓ₀ / ‖w‖ ^ 3) • innerSL ℝ w) w := by
    simp_rw [div_eq_mul_inv]
    refine (((hn.sub_const ℓ₀).const_mul κ).mul
      ((hasDerivAt_inv hw').comp_hasFDerivAt w hn)).congr_fderiv ?_
    ext h
    simp
    field_simp
    ring
  exact hc.smul (hasFDerivAt_id w)

/-- **The linearization of a spring at rest.** At a relative vector `v ≠ 0` of the rest length
`‖v‖`, the derivative of the force is `κ` times the orthogonal projection onto the line `ℝ ∙ v`:
to first order, only the stretching along the spring is felt. -/
theorem hasFDerivAt_springForce_norm (κ : ℝ) {v : F} (hv : v ≠ 0) :
    HasFDerivAt (springForce κ ‖v‖) (κ • (ℝ ∙ v).starProjection) v := by
  refine (hasFDerivAt_springForce κ ‖v‖ hv).congr_fderiv ?_
  ext h
  simp [Submodule.starProjection_singleton, smul_smul]
  field_simp

/-- **The linearized pair force.** Two particles joined by a spring of stiffness `κ` rest at the
relative vector `v ≠ 0`, at its rest length `‖v‖`. When they are displaced by `uᵢ` and `uⱼ`, the
force `springForce κ ‖v‖ (v + uⱼ - uᵢ)` on the first particle has derivative
`(uᵢ, uⱼ) ↦ κ P_v (uⱼ - uᵢ)` at `0`, where `P_v` is the orthogonal projection onto `ℝ ∙ v`. The
second particle feels the opposite force (`TauCeti.springForce_neg`). -/
theorem hasFDerivAt_springForce_add_sub (κ : ℝ) {v : F} (hv : v ≠ 0) :
    HasFDerivAt (fun u : F × F ↦ springForce κ ‖v‖ (v + u.2 - u.1))
      (κ • (ℝ ∙ v).starProjection ∘L
        (ContinuousLinearMap.snd ℝ F F - ContinuousLinearMap.fst ℝ F F)) 0 := by
  have hd : HasFDerivAt (fun u : F × F ↦ v + u.2 - u.1)
      (ContinuousLinearMap.snd ℝ F F - ContinuousLinearMap.fst ℝ F F) 0 :=
    (hasFDerivAt_snd.const_add v).sub hasFDerivAt_fst
  have hs : HasFDerivAt (springForce κ ‖v‖) (κ • (ℝ ∙ v).starProjection)
      (v + (0 : F × F).2 - (0 : F × F).1) := by
    simpa using hasFDerivAt_springForce_norm κ hv
  simpa [ContinuousLinearMap.smul_comp, smul_sub, Function.comp_def] using hs.comp (0 : F × F) hd

end InnerProductSpace

end TauCeti
