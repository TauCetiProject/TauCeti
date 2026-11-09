/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Radial quadratures between simple turning points

A particle of mass `m > 0` with angular momentum `ℓ` in a central potential `U` moves radially in
the effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)` (`TauCeti.effectivePotential`). At energy
`E` its radial momentum satisfies `|p_r| = √(2 m (E - U_ℓ(r)))`
(`TauCeti.absRadialMomentum_eq_sqrt`), which vanishes at the turning points `U_ℓ(r) = E`. The
radial period and the apsidal angle (`TauCeti.radialPeriod`, `TauCeti.apsidalAngle`) are integrals
of `1 / |p_r|` between two turning points `r₁ < r₂`, so their integrands are in general unbounded at
both ends. This file proves that these quadratures converge and that they compute the time and the
polar angle of the actual motion.

**Convergence.** If `U_ℓ < E` on `(r₁, r₂)` and the turning points are *simple*, that is
`U_ℓ'(r₁) ≠ 0` and `U_ℓ'(r₂) ≠ 0`, then `2 m (E - U_ℓ)` dominates a positive multiple of
`(r - r₁) (r₂ - r)`, and `g / |p_r|` is interval integrable on `[r₁, r₂]` for every `g` continuous
there (`TauCeti.intervalIntegrable_div_absRadialMomentum`). In particular the integrands of the
radial period and of the apsidal angle are integrable.

**The quadratures along a motion.** Let `t ↦ (r(t), p_r(t))` be a radial motion of energy `E`: it
satisfies the first reduced Hamilton equation `r' = p_r / m` and
`p_r² / (2m) + U_ℓ(r) = E` (the reduced Hamiltonian `H_ℓ`, see
`TauCeti.centralForceHamiltonian_effectivePotential_apply`). On a time interval `[t₁, t₂]` on which
the particle moves outwards, `p_r > 0`, the substitution `x = r(t)` gives, for every function `h`,

`∫_{t₁}^{t₂} h(r(t)) dt = ∫_{r(t₁)}^{r(t₂)} m h(x) / |p_r(x)| dx`

(`TauCeti.integral_comp_eq_integral_mul_div_absRadialMomentum`), with the bounds exchanged for an
inward motion (`TauCeti.integral_comp_eq_integral_mul_div_absRadialMomentum_of_neg`). No
integrability needs to be assumed: the substitution is a change of variables for the Lebesgue
integral. Taking `h = 1`, the time to travel from `r(t₁)` to `r(t₂)` is
`t₂ - t₁ = ∫ m dx / |p_r|` (`TauCeti.sub_eq_integral_div_absRadialMomentum`), half the radial
period (`TauCeti.radialPeriod_eq_two_mul_sub`). The second Hamilton equation of polar canonical
coordinates is `θ' = ℓ / (m r²)` (`TauCeti.fderiv_polarCanonical_apply_eq_hamiltonianVectorField`),
and taking `h(x) = ℓ / (m x²)` shows that the polar angle swept while the radius moves from
`r(t₁)` to `r(t₂)` is the apsidal angle (`TauCeti.sub_eq_apsidalAngle`). A motion that moves out
from `r(t₁)` to `r(t₂)` and back to `r(t₁)` takes exactly one radial period
(`TauCeti.sub_eq_radialPeriod`).

## Main results

* `TauCeti.absRadialMomentum_eq_sqrt`: `|p_r| = √(2 m (E - U_ℓ(r)))`.
* `TauCeti.intervalIntegrable_div_absRadialMomentum`,
  `TauCeti.intervalIntegrable_div_sq_mul_absRadialMomentum`: convergence of the quadratures between
  simple turning points.
* `TauCeti.integral_comp_eq_integral_mul_div_absRadialMomentum` and
  `TauCeti.integral_comp_eq_integral_mul_div_absRadialMomentum_of_neg`: time integrals along an
  outward or inward radial motion as radial quadratures.
* `TauCeti.sub_eq_integral_div_absRadialMomentum`, `TauCeti.radialPeriod_eq_two_mul_sub`,
  `TauCeti.sub_eq_radialPeriod`: the radial period is the time of one radial oscillation.
* `TauCeti.sub_eq_apsidalAngle`: the apsidal angle is the polar angle swept between the turning
  points.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 2 and 8.
* L. D. Landau and E. M. Lifshitz, *Mechanics*, 3rd ed., Course of Theoretical Physics 1,
  Pergamon, 1976, Sections 11, 14 and 15.
-/

public section

open Real Set intervalIntegral MeasureTheory

namespace TauCeti

variable {m ℓ E r₁ r₂ : ℝ} {U : ℝ → ℝ}

/-- For `m ≠ 0`, the absolute radial momentum is `√(2 m (E - U_ℓ(r)))`, in terms of the effective
potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`. -/
theorem absRadialMomentum_eq_sqrt (hm : m ≠ 0) (r : ℝ) :
    absRadialMomentum m U ℓ E r = √(2 * m * (E - effectivePotential m ℓ U r)) := by
  rw [absRadialMomentum_def, effectivePotential_apply]
  congr 1
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  field_simp
  ring

/-! ### Convergence between simple turning points -/

/-- **Convergence of the radial quadratures.** Let `r₁ < r₂` be turning points of energy `E`,
`U_ℓ(r₁) = U_ℓ(r₂) = E`, with `U_ℓ < E` in between, and let them be *simple*: `U_ℓ` has nonzero
one-sided derivatives at `r₁` and `r₂`. Then `g / |p_r|` is interval integrable on `[r₁, r₂]` for
every `g` continuous there, although `1 / |p_r|` is unbounded at both turning points. -/
theorem intervalIntegrable_div_absRadialMomentum {V₁ V₂ : ℝ} (hm : 0 < m) (h₁₂ : r₁ < r₂)
    (hU : ContinuousOn (effectivePotential m ℓ U) (Icc r₁ r₂))
    (hE : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hr₁ : effectivePotential m ℓ U r₁ = E) (hr₂ : effectivePotential m ℓ U r₂ = E)
    (hV₁ : HasDerivWithinAt (effectivePotential m ℓ U) V₁ (Ici r₁) r₁) (hV₁₀ : V₁ ≠ 0)
    (hV₂ : HasDerivWithinAt (effectivePotential m ℓ U) V₂ (Iic r₂) r₂) (hV₂₀ : V₂ ≠ 0)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc r₁ r₂)) :
    IntervalIntegrable (fun r ↦ g r / absRadialMomentum m U ℓ E r) volume r₁ r₂ := by
  simp_rw [absRadialMomentum_eq_sqrt hm.ne']
  have h2m : 0 < 2 * m := by positivity
  exact intervalIntegrable_div_sqrt_of_hasDerivWithinAt h₁₂ hg
    (continuousOn_const.mul (continuousOn_const.sub hU))
    (fun r hr ↦ mul_pos h2m (sub_pos.2 (hE r hr))) (by rw [hr₁, sub_self, mul_zero])
    (by rw [hr₂, sub_self, mul_zero]) ((hV₁.const_sub E).const_mul (2 * m))
    (mul_ne_zero h2m.ne' (neg_ne_zero.2 hV₁₀)) ((hV₂.const_sub E).const_mul (2 * m))
    (mul_ne_zero h2m.ne' (neg_ne_zero.2 hV₂₀))

/-- **Convergence of the apsidal angle.** Between simple turning points `0 < r₁ < r₂`, the
integrand `ℓ / (r² |p_r|)` of the apsidal angle is interval integrable. -/
theorem intervalIntegrable_div_sq_mul_absRadialMomentum {V₁ V₂ : ℝ} (hm : 0 < m) (h₁ : 0 < r₁)
    (h₁₂ : r₁ < r₂) (hU : ContinuousOn (effectivePotential m ℓ U) (Icc r₁ r₂))
    (hE : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hr₁ : effectivePotential m ℓ U r₁ = E) (hr₂ : effectivePotential m ℓ U r₂ = E)
    (hV₁ : HasDerivWithinAt (effectivePotential m ℓ U) V₁ (Ici r₁) r₁) (hV₁₀ : V₁ ≠ 0)
    (hV₂ : HasDerivWithinAt (effectivePotential m ℓ U) V₂ (Iic r₂) r₂) (hV₂₀ : V₂ ≠ 0) :
    IntervalIntegrable (fun r ↦ ℓ / (r ^ 2 * absRadialMomentum m U ℓ E r)) volume r₁ r₂ := by
  simp_rw [← div_div]
  exact intervalIntegrable_div_absRadialMomentum hm h₁₂ hU hE hr₁ hr₂ hV₁ hV₁₀ hV₂ hV₂₀
    (continuousOn_const.div (continuousOn_id.pow 2) fun r hr ↦ pow_ne_zero 2 (h₁.trans_le hr.1).ne')

/-! ### The quadratures along a radial motion -/

variable {r p θ : ℝ → ℝ} {t₁ t₂ t₃ : ℝ}

/-- **Time integrals as radial quadratures.** Let `t ↦ (r(t), p_r(t))` be a radial motion of
energy `E` on `[t₁, t₂]`: `r` is continuous, `r' = p_r / m` and `p_r² / (2m) + U_ℓ(r) = E` on
`(t₁, t₂)`, and let it move outwards, `p_r > 0`. Then for every function `h`,
`∫_{t₁}^{t₂} h(r(t)) dt = ∫_{r(t₁)}^{r(t₂)} m h(x) / |p_r(x)| dx`. -/
theorem integral_comp_eq_integral_mul_div_absRadialMomentum (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hr : ContinuousOn r (Icc t₁ t₂)) (hr' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt r (p t / m) t)
    (hp : ∀ t ∈ Ioo t₁ t₂, 0 < p t)
    (hE : ∀ t ∈ Ioo t₁ t₂, p t ^ 2 / (2 * m) + effectivePotential m ℓ U (r t) = E)
    (h : ℝ → ℝ) :
    ∫ t in t₁..t₂, h (r t) = ∫ x in r t₁..r t₂, m * h x / absRadialMomentum m U ℓ E x := by
  -- The radius is strictly increasing, since `r' = p_r / m > 0`.
  have hmono : StrictMonoOn r (Icc t₁ t₂) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hr
      (by simpa only [interior_Icc] using fun t ht ↦ (hr' t ht).hasDerivWithinAt)
      (by simpa only [interior_Icc] using fun t ht ↦ div_pos (hp t ht) hm)
  have himage : r '' Ioo t₁ t₂ = Ioo (r t₁) (r t₂) := hr.image_Ioo_of_strictMonoOn ht hmono
  have hle : r t₁ ≤ r t₂ := hmono.monotoneOn (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
  rw [integral_of_le ht, integral_of_le hle, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo, ← himage, integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioo (fun t htt ↦ (hr' t htt).hasDerivWithinAt)
      (hmono.injOn.mono Ioo_subset_Icc_self)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t htt ↦ ?_
  have hpt := hp t htt
  have habs : absRadialMomentum m U ℓ E (r t) = p t := by
    rw [absRadialMomentum_eq_sqrt hm.ne', ← hE t htt, add_sub_cancel_right,
      mul_div_cancel₀ _ (by positivity), sqrt_sq hpt.le]
  rw [smul_eq_mul, habs, abs_of_pos (div_pos hpt hm)]
  field_simp

/-- **Time integrals along an inward radial motion.** For a radial motion of energy `E` on
`[t₁, t₂]` moving inwards, `p_r < 0`,
`∫_{t₁}^{t₂} h(r(t)) dt = ∫_{r(t₂)}^{r(t₁)} m h(x) / |p_r(x)| dx`. -/
theorem integral_comp_eq_integral_mul_div_absRadialMomentum_of_neg (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hr : ContinuousOn r (Icc t₁ t₂)) (hr' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt r (p t / m) t)
    (hp : ∀ t ∈ Ioo t₁ t₂, p t < 0)
    (hE : ∀ t ∈ Ioo t₁ t₂, p t ^ 2 / (2 * m) + effectivePotential m ℓ U (r t) = E)
    (h : ℝ → ℝ) :
    ∫ t in t₁..t₂, h (r t) = ∫ x in r t₂..r t₁, m * h x / absRadialMomentum m U ℓ E x := by
  -- Reverse time: `s ↦ (r(-s), -p_r(-s))` moves outwards on `[-t₂, -t₁]`.
  have hneg : ∀ s ∈ Ioo (-t₂) (-t₁), -s ∈ Ioo t₁ t₂ := fun s hs ↦
    ⟨lt_neg_of_lt_neg hs.2, neg_lt.1 hs.1⟩
  have key := integral_comp_eq_integral_mul_div_absRadialMomentum (r := fun s ↦ r (-s))
    (p := fun s ↦ -p (-s)) hm (neg_le_neg ht)
    (hr.comp continuousOn_neg fun s hs ↦ ⟨le_neg_of_le_neg hs.2, neg_le.1 hs.1⟩)
    (fun s hs ↦ by
      have := (hr' (-s) (hneg s hs)).comp s (hasDerivAt_neg s)
      rwa [mul_neg_one, ← neg_div] at this)
    (fun s hs ↦ neg_pos.2 (hp (-s) (hneg s hs)))
    (fun s hs ↦ by simpa using hE (-s) (hneg s hs)) h
  simp only [neg_neg] at key
  rw [← key, intervalIntegral.integral_comp_neg (fun t ↦ h (r t)), neg_neg, neg_neg]

/-- **The time between two radii.** Along an outward radial motion of energy `E` on `[t₁, t₂]`,
the elapsed time is the radial quadrature `t₂ - t₁ = ∫_{r(t₁)}^{r(t₂)} m dx / |p_r(x)|`. -/
theorem sub_eq_integral_div_absRadialMomentum (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hr : ContinuousOn r (Icc t₁ t₂)) (hr' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt r (p t / m) t)
    (hp : ∀ t ∈ Ioo t₁ t₂, 0 < p t)
    (hE : ∀ t ∈ Ioo t₁ t₂, p t ^ 2 / (2 * m) + effectivePotential m ℓ U (r t) = E) :
    t₂ - t₁ = ∫ x in r t₁..r t₂, m / absRadialMomentum m U ℓ E x := by
  simpa using integral_comp_eq_integral_mul_div_absRadialMomentum hm ht hr hr' hp hE fun _ ↦ 1

/-- **Half the radial period.** The radial period between `r(t₁)` and `r(t₂)` is twice the time
an outward radial motion of energy `E` takes to travel from `r(t₁)` to `r(t₂)`. -/
theorem radialPeriod_eq_two_mul_sub (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hr : ContinuousOn r (Icc t₁ t₂)) (hr' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt r (p t / m) t)
    (hp : ∀ t ∈ Ioo t₁ t₂, 0 < p t)
    (hE : ∀ t ∈ Ioo t₁ t₂, p t ^ 2 / (2 * m) + effectivePotential m ℓ U (r t) = E) :
    radialPeriod m U ℓ E (r t₁) (r t₂) = 2 * (t₂ - t₁) := by
  rw [radialPeriod_def, sub_eq_integral_div_absRadialMomentum hm ht hr hr' hp hE]

/-- **The radial period is the time of one radial oscillation.** Let a radial motion of energy
`E` move outwards from `r(t₁)` to `r(t₂)` on `[t₁, t₂]` and back inwards to `r(t₃) = r(t₁)` on
`[t₂, t₃]`. Then `t₃ - t₁` is the radial period between `r(t₁)` and `r(t₂)`. -/
theorem sub_eq_radialPeriod (hm : 0 < m) (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃)
    (hr : ContinuousOn r (Icc t₁ t₃)) (hr' : ∀ t ∈ Ioo t₁ t₃, HasDerivAt r (p t / m) t)
    (hp₁₂ : ∀ t ∈ Ioo t₁ t₂, 0 < p t) (hp₂₃ : ∀ t ∈ Ioo t₂ t₃, p t < 0)
    (hE : ∀ t ∈ Ioo t₁ t₃, p t ^ 2 / (2 * m) + effectivePotential m ℓ U (r t) = E)
    (hr₃ : r t₃ = r t₁) :
    t₃ - t₁ = radialPeriod m U ℓ E (r t₁) (r t₂) := by
  have hsub₁ : Ioo t₁ t₂ ⊆ Ioo t₁ t₃ := Ioo_subset_Ioo_right h₂₃
  have hsub₂ : Ioo t₂ t₃ ⊆ Ioo t₁ t₃ := Ioo_subset_Ioo_left h₁₂
  have hout := sub_eq_integral_div_absRadialMomentum hm h₁₂
    (hr.mono (Icc_subset_Icc_right h₂₃)) (fun t ht ↦ hr' t (hsub₁ ht)) hp₁₂
    (fun t ht ↦ hE t (hsub₁ ht))
  have hin := integral_comp_eq_integral_mul_div_absRadialMomentum_of_neg hm h₂₃
    (hr.mono (Icc_subset_Icc_left h₁₂)) (fun t ht ↦ hr' t (hsub₂ ht)) hp₂₃
    (fun t ht ↦ hE t (hsub₂ ht)) fun _ ↦ 1
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, hr₃, ← hout] at hin
  rw [radialPeriod_def, ← hout]
  linarith

/-- **The apsidal angle is the polar angle swept.** Along an outward radial motion of energy `E`
on `[t₁, t₂]` starting at `r(t₁) > 0`, let the polar angle `θ` satisfy `θ' = ℓ / (m r²)`. Then the
angle swept, `θ(t₂) - θ(t₁)`, is the apsidal angle between `r(t₁)` and `r(t₂)`. -/
theorem sub_eq_apsidalAngle (hm : 0 < m) (ht : t₁ ≤ t₂) (hr₁ : 0 < r t₁)
    (hr : ContinuousOn r (Icc t₁ t₂)) (hr' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt r (p t / m) t)
    (hp : ∀ t ∈ Ioo t₁ t₂, 0 < p t)
    (hE : ∀ t ∈ Ioo t₁ t₂, p t ^ 2 / (2 * m) + effectivePotential m ℓ U (r t) = E)
    (hθ : ContinuousOn θ (Icc t₁ t₂)) (hθ' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt θ (ℓ / (m * r t ^ 2)) t) :
    θ t₂ - θ t₁ = apsidalAngle m U ℓ E (r t₁) (r t₂) := by
  -- The radius is strictly increasing, since `r' = p_r / m > 0`.
  have hmono : StrictMonoOn r (Icc t₁ t₂) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hr
      (by simpa only [interior_Icc] using fun t ht ↦ (hr' t ht).hasDerivWithinAt)
      (by simpa only [interior_Icc] using fun t ht ↦ div_pos (hp t ht) hm)
  have hpos : ∀ t ∈ Icc t₁ t₂, r t ≠ 0 := fun t htt ↦
    (hr₁.trans_le (hmono.monotoneOn (left_mem_Icc.2 ht) htt htt.1)).ne'
  have hint : IntervalIntegrable (fun t ↦ ℓ / (m * r t ^ 2)) volume t₁ t₂ :=
    (continuousOn_const.div (continuousOn_const.mul (hr.pow 2)) fun t htt ↦
      mul_ne_zero hm.ne' (pow_ne_zero 2 (hpos t htt))).intervalIntegrable_of_Icc ht
  rw [← integral_eq_sub_of_hasDerivAt_of_le ht hθ hθ' hint,
    integral_comp_eq_integral_mul_div_absRadialMomentum hm ht hr hr' hp hE
      fun x ↦ ℓ / (m * x ^ 2), apsidalAngle_def]
  refine integral_congr fun x _ ↦ ?_
  rw [← mul_div_assoc, mul_div_mul_left _ _ hm.ne', div_div]

end TauCeti
