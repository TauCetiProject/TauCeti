/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

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

end TauCeti
