/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial

/-!
# Turning radii and the energy domain of the Kepler radial action

For an attractive Kepler potential with mass `m > 0` and angular momentum `ℓ ≠ 0`,
the effective potential has minimum energy `-m κ² / (2 ℓ²)`. At every negative energy
above this minimum there are exactly two positive turning radii. This file constructs
them, identifies the allowed radial interval, and applies the integral formula
`kepler_radialAction` on this energy domain. At the minimum the two radii coincide
at the circular radius `ℓ² / (m κ)` and the radial action is zero.

The radii are `(κ ∓ √(κ² + 2 E ℓ² / m)) / (-2 E)`. Statements about turning
points always retain positivity of the radius: the collision point is not in the
configuration space. These are statements about the reduced energy curve and its
action integral, not a construction of action-angle coordinates.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., §§8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Chapter 3.
-/

public section

noncomputable section

open Real Set

namespace TauCeti

/-- The pericentre radius of a bound Kepler orbit. Its physical domain is
`m > 0`, `κ > 0`, `ℓ ≠ 0` and `-m κ² / (2 ℓ²) ≤ E < 0`. -/
def keplerPeriapsisRadius (m κ ℓ E : ℝ) : ℝ :=
  (κ - √(κ ^ 2 + 2 * E * ℓ ^ 2 / m)) / (-2 * E)

/-- The apocentre radius of a bound Kepler orbit, on the same energy domain as
`keplerPeriapsisRadius`. At the circular energy the two radii agree. -/
def keplerApoapsisRadius (m κ ℓ E : ℝ) : ℝ :=
  (κ + √(κ ^ 2 + 2 * E * ℓ ^ 2 / m)) / (-2 * E)

/-- The explicit pericentre formula. -/
theorem keplerPeriapsisRadius_def (m κ ℓ E : ℝ) :
    keplerPeriapsisRadius m κ ℓ E =
      (κ - √(κ ^ 2 + 2 * E * ℓ ^ 2 / m)) / (-2 * E) := (rfl)

/-- The explicit apocentre formula. -/
theorem keplerApoapsisRadius_def (m κ ℓ E : ℝ) :
    keplerApoapsisRadius m κ ℓ E =
      (κ + √(κ ^ 2 + 2 * E * ℓ ^ 2 / m)) / (-2 * E) := (rfl)

variable {m κ ℓ E r : ℝ}

/-- Completing the square in the Kepler effective potential about its minimum energy. -/
theorem effectivePotential_kepler_sub_min (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hr : r ≠ 0) :
    effectivePotential m ℓ (fun r ↦ -κ / r) r + (m * κ ^ 2) / (2 * ℓ ^ 2) =
      (ℓ ^ 2 - m * κ * r) ^ 2 / (2 * m * ℓ ^ 2 * r ^ 2) := by
  rw [effectivePotential_apply]
  field_simp
  ring

/-- Every noncollision radius has effective energy at least the circular energy.
No sign assumption on `κ` is needed for the lower bound. -/
theorem effectivePotential_kepler_min_le (hm : 0 < m) (hℓ : ℓ ≠ 0) (hr : r ≠ 0) :
    -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ effectivePotential m ℓ (fun r ↦ -κ / r) r := by
  have h := effectivePotential_kepler_sub_min (κ := κ) hm.ne' hℓ hr
  have : 0 ≤ (ℓ ^ 2 - m * κ * r) ^ 2 / (2 * m * ℓ ^ 2 * r ^ 2) := by positivity
  rw [neg_div]
  linarith

/-- The square root in the turning-radius formulas is real on the bound-energy domain
and is strictly smaller than `κ`, excluding collision at either turning radius. -/
private theorem kepler_sqrt_discriminant_bounds (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) :
    0 ≤ κ ^ 2 + 2 * E * ℓ ^ 2 / m ∧ √(κ ^ 2 + 2 * E * ℓ ^ 2 / m) < κ := by
  have hℓ2 : 0 < ℓ ^ 2 := sq_pos_of_ne_zero hℓ
  have hbound := (div_le_iff₀ (by positivity : 0 < 2 * ℓ ^ 2)).1 hmin
  have hd : 0 ≤ κ ^ 2 + 2 * E * ℓ ^ 2 / m := by
    apply (nonneg_of_mul_nonneg_left ?_ hm)
    field_simp
    nlinarith
  refine ⟨hd, (sqrt_lt' hκ).2 ?_⟩
  have : 2 * E * ℓ ^ 2 / m < 0 := div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by linarith) hℓ2) hm
  linarith

/-- Both Kepler turning radii are positive and ordered on the closed bound-energy domain. -/
theorem kepler_turningRadii_pos_le (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) :
    0 < keplerPeriapsisRadius m κ ℓ E ∧
      keplerPeriapsisRadius m κ ℓ E ≤ keplerApoapsisRadius m κ ℓ E := by
  obtain ⟨-, hs⟩ := kepler_sqrt_discriminant_bounds hm hκ hℓ hmin hE
  rw [keplerPeriapsisRadius_def, keplerApoapsisRadius_def]
  refine ⟨div_pos (sub_pos.2 hs) (by linarith), ?_⟩
  exact (div_le_div_iff_of_pos_right (by linarith : 0 < -2 * E)).2
    (by linarith [sqrt_nonneg (κ ^ 2 + 2 * E * ℓ ^ 2 / m)])

/-- Above the circular energy the two turning radii are distinct. -/
theorem kepler_periapsisRadius_lt_apoapsisRadius (hm : 0 < m)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) < E) (hE : E < 0) (hℓ : ℓ ≠ 0) :
    keplerPeriapsisRadius m κ ℓ E < keplerApoapsisRadius m κ ℓ E := by
  rw [keplerPeriapsisRadius_def, keplerApoapsisRadius_def]
  have hbound := (div_lt_iff₀ (by positivity : 0 < 2 * ℓ ^ 2)).1 hmin
  have hd : 0 < κ ^ 2 + 2 * E * ℓ ^ 2 / m := by
    apply (pos_of_mul_pos_left ?_ hm.le)
    field_simp
    nlinarith
  exact (div_lt_div_iff_of_pos_right (by linarith : 0 < -2 * E)).2
    (by linarith [sqrt_pos.2 hd])

/-- The sum and product of the explicitly constructed Kepler turning radii. -/
private theorem kepler_turningRadii_vieta (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) :
    keplerPeriapsisRadius m κ ℓ E + keplerApoapsisRadius m κ ℓ E = -κ / E ∧
      keplerPeriapsisRadius m κ ℓ E * keplerApoapsisRadius m κ ℓ E =
        -(ℓ ^ 2) / (2 * m * E) := by
  have hs := sq_sqrt (kepler_sqrt_discriminant_bounds hm hκ hℓ hmin hE).1
  simp only [keplerPeriapsisRadius_def, keplerApoapsisRadius_def]
  generalize √(κ ^ 2 + 2 * E * ℓ ^ 2 / m) = s at hs ⊢
  constructor
  · ring
  · field_simp [hm.ne', hE.ne] at hs ⊢
    nlinarith [hs]

/-- Factoring the radial kinetic-energy polynomial by the two Kepler turning radii. -/
private theorem kepler_radialPolynomial_eq (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) (r : ℝ) :
    2 * m * E * r ^ 2 + 2 * m * κ * r - ℓ ^ 2 =
      (-2 * m * E) * (r - keplerPeriapsisRadius m κ ℓ E) *
        (keplerApoapsisRadius m κ ℓ E - r) := by
  obtain ⟨hsum, hprod⟩ := kepler_turningRadii_vieta hm hκ hℓ hmin hE
  have hsum' := (eq_div_iff hE.ne).1 hsum
  have hprod' := (eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hm.ne') hE.ne)).1 hprod
  linear_combination 2 * m * r * hsum' - hprod'

/-- The only positive turning points at a bound Kepler energy are its pericentre and apocentre. -/
theorem effectivePotential_kepler_eq_iff (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) (hr : 0 < r) :
    effectivePotential m ℓ (fun r ↦ -κ / r) r = E ↔
      r = keplerPeriapsisRadius m κ ℓ E ∨ r = keplerApoapsisRadius m κ ℓ E := by
  have hpoly : effectivePotential m ℓ (fun r ↦ -κ / r) r = E ↔
      2 * m * E * r ^ 2 + 2 * m * κ * r - ℓ ^ 2 = 0 := by
    rw [effectivePotential_apply]
    field_simp
    constructor <;> intro h <;> nlinarith [h]
  rw [hpoly, kepler_radialPolynomial_eq hm hκ hℓ hmin hE, mul_eq_zero, mul_eq_zero]
  simp only [mul_eq_zero, neg_eq_zero, OfNat.ofNat_ne_zero, hm.ne', hE.ne,
    or_self, false_or, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

/-- At a bound Kepler energy the allowed positive radii form precisely the closed
interval between the turning radii. -/
theorem effectivePotential_kepler_le_iff (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) (hr : 0 < r) :
    effectivePotential m ℓ (fun r ↦ -κ / r) r ≤ E ↔
      r ∈ Icc (keplerPeriapsisRadius m κ ℓ E) (keplerApoapsisRadius m κ ℓ E) := by
  have hpoly : effectivePotential m ℓ (fun r ↦ -κ / r) r ≤ E ↔
      0 ≤ 2 * m * E * r ^ 2 + 2 * m * κ * r - ℓ ^ 2 := by
    rw [effectivePotential_apply]
    have hden : 0 < 2 * m * r ^ 2 := by positivity
    constructor <;> intro h
    · have := (mul_le_mul_iff_left₀ hden).2 h
      field_simp at this
      nlinarith
    · apply (mul_le_mul_iff_left₀ hden).1
      field_simp
      nlinarith
  rw [hpoly, kepler_radialPolynomial_eq hm hκ hℓ hmin hE,
    mul_assoc, mul_nonneg_iff_of_pos_left
      (by nlinarith [mul_pos hm (neg_pos.2 hE)] : 0 < -2 * m * E)]
  have horder := (kepler_turningRadii_pos_le hm hκ hℓ hmin hE).2
  simpa only [← neg_sub r (keplerApoapsisRadius m κ ℓ E), mul_neg, neg_nonneg,
    mem_Icc] using sub_mul_sub_nonpos_iff r horder

/-- At the circular energy the pericentre is the circular radius. -/
@[simp]
theorem keplerPeriapsisRadius_circular (hm : m ≠ 0) (hκ : κ ≠ 0) (hℓ : ℓ ≠ 0) :
    keplerPeriapsisRadius m κ ℓ (-(m * κ ^ 2) / (2 * ℓ ^ 2)) = ℓ ^ 2 / (m * κ) := by
  have hd : κ ^ 2 + 2 * (-(m * κ ^ 2) / (2 * ℓ ^ 2)) * ℓ ^ 2 / m = 0 := by
    field_simp
    ring
  simp only [keplerPeriapsisRadius_def, hd, sqrt_zero, sub_zero]
  field_simp

/-- At the circular energy the apocentre is the circular radius too. -/
@[simp]
theorem keplerApoapsisRadius_circular (hm : m ≠ 0) (hκ : κ ≠ 0) (hℓ : ℓ ≠ 0) :
    keplerApoapsisRadius m κ ℓ (-(m * κ ^ 2) / (2 * ℓ ^ 2)) = ℓ ^ 2 / (m * κ) := by
  have hd : κ ^ 2 + 2 * (-(m * κ ^ 2) / (2 * ℓ ^ 2)) * ℓ ^ 2 / m = 0 := by
    field_simp
    ring
  simp only [keplerApoapsisRadius_def, hd, sqrt_zero, add_zero]
  field_simp

/-- The radial action formula on the entire bound-energy domain, including the circular
endpoint. The turning radii are constructed from energy and angular momentum. -/
theorem kepler_radialAction_turningRadii (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    (hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E) (hE : E < 0) :
    radialAction m (fun r ↦ -κ / r) ℓ E
        (keplerPeriapsisRadius m κ ℓ E) (keplerApoapsisRadius m κ ℓ E) =
      κ * √(m / (-2 * E)) - |ℓ| := by
  rcases hmin.eq_or_lt with rfl | hmin
  · rw [keplerPeriapsisRadius_circular hm.ne' hκ.ne' hℓ,
      keplerApoapsisRadius_circular hm.ne' hκ.ne' hℓ, radialAction_def,
      intervalIntegral.integral_same, mul_zero]
    have hdiv : m / (-2 * (-(m * κ ^ 2) / (2 * ℓ ^ 2))) = (ℓ / κ) ^ 2 := by
      field_simp
    rw [hdiv, sqrt_sq_eq_abs, abs_div, abs_of_pos hκ]
    field_simp
    ring
  obtain ⟨h₁, hle⟩ := kepler_turningRadii_pos_le hm hκ hℓ hmin.le hE
  have h₂ := h₁.trans_le hle
  have hturn (r : ℝ) (hr : 0 < r)
      (h : r = keplerPeriapsisRadius m κ ℓ E ∨ r = keplerApoapsisRadius m κ ℓ E) :
      2 * m * (E + κ / r) = ℓ ^ 2 / r ^ 2 := by
    have := (effectivePotential_kepler_eq_iff hm hκ hℓ hmin.le hE hr).2 h
    rw [effectivePotential_apply] at this
    field_simp at this ⊢
    nlinarith
  exact kepler_radialAction hm hℓ h₁
    (kepler_periapsisRadius_lt_apoapsisRadius hm hmin hE hℓ)
    (hturn _ h₁ (Or.inl rfl)) (hturn _ h₂ (Or.inr rfl))

end TauCeti
