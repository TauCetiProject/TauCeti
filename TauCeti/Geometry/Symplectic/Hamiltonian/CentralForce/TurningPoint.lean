/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction
import TauCeti.MeasureTheory.Function.Jacobian.OneDim

/-!
# Radial motion between simple turning points

A particle of mass `m > 0` with angular momentum `ℓ` in a central potential `U` moves radially
according to the reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)` on the half-line `r > 0`,
with effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)` (`TauCeti.effectivePotential`). At energy
`E` the absolute radial momentum is `|p_r| = √(2 m (E - U_ℓ(r)))`
(`TauCeti.absRadialMomentum_eq_abs`), and the classical quadratures between two radii `r₁ < r₂`
are the radial period `TauCeti.radialPeriod`, twice `∫ m dr / |p_r| = ∫ dr / √((2 / m) (E - U_ℓ))`,
and the apsidal angle `TauCeti.apsidalAngle`, `∫ ℓ dr / (r² |p_r|)`.

This file treats an arbitrary potential, rather than the closed forms for the Kepler problem and the
isotropic oscillator in `TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction`.

* **Convergence.** The integrands are unbounded at turning points, where `U_ℓ(rᵢ) = E`. At *simple*
  turning points, `U_ℓ'(rᵢ) ≠ 0`, with `U_ℓ < E` in between, the radicand `2 m (E - U_ℓ)` dominates
  a multiple of `(r - r₁) (r₂ - r)`, and both quadratures converge
  (`TauCeti.intervalIntegrable_div_absRadialMomentum`,
  `TauCeti.intervalIntegrable_div_sq_mul_absRadialMomentum`).
* **Time and angle.** Along an integral curve `(r(t), p_r(t))` of the reduced Hamiltonian vector
  field with energy `E`, suppose the radius moves from one of `r₁`, `r₂` to the other during
  `[t₁, t₂]` and stays strictly between them meanwhile, where `U_ℓ < E`. The energy is conserved and
  `p_r` does not vanish, so `r` is monotone and `dt = m dr / |p_r|`. Hence the elapsed time is the
  quadrature, `t₂ - t₁ = ∫_{r₁}^{r₂} m dr / |p_r|`
  (`TauCeti.sub_eq_integral_div_absRadialMomentum`). If moreover `θ' = ℓ / (m r²)`, the polar
  Hamilton equation of the angle (`TauCeti.hasDerivAt_polarCanonical_comp`), the angle swept is the
  apsidal angle (`TauCeti.sub_eq_apsidalAngle`). These identities need no hypothesis on the
  derivative of `U_ℓ` at `r₁` and `r₂`.
* **The radial period.** For a full radial oscillation, from one turning radius to the other and
  back, the elapsed time is the radial period, twice the time integral between the turning points
  (`TauCeti.sub_eq_radialPeriod`), and the angle swept is twice the apsidal angle
  (`TauCeti.sub_eq_two_mul_apsidalAngle`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 4 and 8.
* L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., Pergamon, 1976, Sections 11 and 14.
-/

public section

open Real Set intervalIntegral MeasureTheory

namespace TauCeti

variable {m ℓ E r₁ r₂ : ℝ} {U : ℝ → ℝ}

/-- For a nonzero mass, the absolute radial momentum is `√(2 m (E - U_ℓ(r)))`. -/
theorem absRadialMomentum_eq_sqrt (hm : m ≠ 0) (r : ℝ) :
    absRadialMomentum m U ℓ E r = √(2 * m * (E - effectivePotential m ℓ U r)) := by
  rw [absRadialMomentum_def, effectivePotential_apply]
  congr 1
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · field_simp
    ring

/-- On the level `E` of the reduced Hamiltonian, the absolute radial momentum at a radius `r > 0`
is `|p_r|`. -/
theorem absRadialMomentum_eq_abs (hm : m ≠ 0) {r p : ℝ} (hr : 0 < r)
    (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (r, p) = E) :
    absRadialMomentum m U ℓ E r = |p| := by
  rw [centralForceHamiltonian_effectivePotential_apply hr.le] at hE
  rw [absRadialMomentum_def, ← sqrt_sq_eq_abs, ← hE]
  congr 1
  field_simp
  ring

/-! ### Convergence of the quadratures at simple turning points -/

section Convergence

variable {d₁ d₂ : ℝ}

/-- **The time quadrature converges at simple turning points.** Let `0 < r₁ < r₂` be turning
points of energy `E`, `U_ℓ(r₁) = U_ℓ(r₂) = E`, with `U_ℓ < E` in between, at which the effective
potential has nonzero one-sided derivatives. Then `r ↦ m / |p_r|` is interval integrable on
`[r₁, r₂]`, although it is unbounded at both turning points. -/
theorem intervalIntegrable_div_absRadialMomentum (hm : 0 < m) (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hU : ContinuousOn U (Icc r₁ r₂)) (hE₁ : effectivePotential m ℓ U r₁ = E)
    (hE₂ : effectivePotential m ℓ U r₂ = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hd₁ : HasDerivWithinAt (effectivePotential m ℓ U) d₁ (Ici r₁) r₁) (hd₁0 : d₁ ≠ 0)
    (hd₂ : HasDerivWithinAt (effectivePotential m ℓ U) d₂ (Iic r₂) r₂) (hd₂0 : d₂ ≠ 0) :
    IntervalIntegrable (fun r ↦ m / absRadialMomentum m U ℓ E r) volume r₁ r₂ := by
  have hcont : ContinuousOn (fun r ↦ 2 * m * (E - effectivePotential m ℓ U r)) (Icc r₁ r₂) := by
    refine continuousOn_const.mul (continuousOn_const.sub ?_)
    rw [show effectivePotential m ℓ U = fun r ↦ ℓ ^ 2 / (2 * m * r ^ 2) + U r from
      funext (effectivePotential_apply m ℓ U)]
    refine ContinuousOn.add ?_ hU
    exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
      fun r hr ↦ by have := hr₁.trans_le hr.1; positivity
  have h := intervalIntegrable_one_div_sqrt_of_hasDerivWithinAt h₁₂ hcont
    (fun r hr ↦ mul_pos (by positivity) (sub_pos.2 (hlt r hr)))
    (by rw [hE₁, sub_self, mul_zero]) (by rw [hE₂, sub_self, mul_zero])
    ((hd₁.const_sub E).const_mul (2 * m)) (by simp [hm.ne', hd₁0])
    ((hd₂.const_sub E).const_mul (2 * m)) (by simp [hm.ne', hd₂0])
  convert h.const_mul m using 2 with r
  rw [absRadialMomentum_eq_sqrt hm.ne', mul_one_div]

/-- **The angle quadrature converges at simple turning points.** Under the hypotheses of
`TauCeti.intervalIntegrable_div_absRadialMomentum`, `r ↦ ℓ / (r² |p_r|)` is interval integrable on
`[r₁, r₂]`. -/
theorem intervalIntegrable_div_sq_mul_absRadialMomentum (hm : 0 < m) (hr₁ : 0 < r₁)
    (h₁₂ : r₁ < r₂) (hU : ContinuousOn U (Icc r₁ r₂)) (hE₁ : effectivePotential m ℓ U r₁ = E)
    (hE₂ : effectivePotential m ℓ U r₂ = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hd₁ : HasDerivWithinAt (effectivePotential m ℓ U) d₁ (Ici r₁) r₁) (hd₁0 : d₁ ≠ 0)
    (hd₂ : HasDerivWithinAt (effectivePotential m ℓ U) d₂ (Iic r₂) r₂) (hd₂0 : d₂ ≠ 0) :
    IntervalIntegrable (fun r ↦ ℓ / (r ^ 2 * absRadialMomentum m U ℓ E r)) volume r₁ r₂ := by
  have h := (intervalIntegrable_div_absRadialMomentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₁0 hd₂
    hd₂0).continuousOn_mul (g := fun r ↦ ℓ / (m * r ^ 2)) <| by
      rw [uIcc_of_le h₁₂.le]
      exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
        fun r hr ↦ by have := hr₁.trans_le hr.1; positivity
  convert h using 2 with r
  rw [div_mul_div_comm, mul_assoc, mul_comm ℓ m, mul_div_mul_left _ _ hm.ne']

end Convergence

/-! ### Time and angle along the radial motion -/

section Motion

variable {γ : ℝ → ℝ × ℝ} {t₁ t₂ : ℝ}

/-- The hypotheses shared by the time and angle formulas along one leg of the radial motion give
the change of variables from time to radius with `|p_r| = |p_r|(r)`, and `r₁ ≤ r₂`. -/
private theorem leg_data (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hγ : ∀ t ∈ Icc t₁ t₂, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ∈ Icc t₁ t₂, 0 < (γ t).1) (hU : ∀ t ∈ Icc t₁ t₂, DifferentiableAt ℝ U (γ t).1)
    (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₁) = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hends : (γ t₁).1 = r₁ ∧ (γ t₂).1 = r₂ ∨ (γ t₁).1 = r₂ ∧ (γ t₂).1 = r₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo r₁ r₂) :
    r₁ ≤ r₂ ∧ (∀ t ∈ Ioo t₁ t₂, absRadialMomentum m U ℓ E (γ t).1 = |(γ t).2| ∧ (γ t).2 ≠ 0) ∧
      ∀ g : ℝ → ℝ, ∫ r in Ioo r₁ r₂, g r = ∫ t in Ioo t₁ t₂, |(γ t).2| / m * g (γ t).1 := by
  have hIoo : Ioo t₁ t₂ ⊆ Icc t₁ t₂ := Ioo_subset_Icc_self
  have hEt := centralForceHamiltonian_effectivePotential_eq_of_hasDerivAt hγ hr hU
  -- On the level `E`, `p_r² / (2m) = E - U_ℓ(r) > 0` strictly between the radii.
  have hp (t : ℝ) (htI : t ∈ Ioo t₁ t₂) :
      absRadialMomentum m U ℓ E (γ t).1 = |(γ t).2| ∧ (γ t).2 ≠ 0 := by
    have hEt' : centralForceHamiltonian m (effectivePotential m ℓ U) ((γ t).1, (γ t).2) = E :=
      (hEt t (hIoo htI)).trans hE
    refine ⟨absRadialMomentum_eq_abs hm.ne' (hr t (hIoo htI)) hEt', fun h0 ↦ ?_⟩
    have hlt' := hlt _ (hmem t htI)
    rw [centralForceHamiltonian_effectivePotential_apply (hr t (hIoo htI)).le, h0,
      add_assoc] at hEt'
    rw [effectivePotential_apply] at hlt'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      zero_add] at hEt'
    linarith
  have hrc : ContinuousOn (fun t ↦ (γ t).1) (Icc t₁ t₂) :=
    fun t ht ↦ (hγ t ht).continuousAt.fst.continuousWithinAt
  have himage : (fun t ↦ (γ t).1) '' Ioo t₁ t₂ = Ioo r₁ r₂ := by
    have hmaps : MapsTo (fun t ↦ (γ t).1) (Ioo t₁ t₂) (Ioo r₁ r₂) := hmem
    refine hmaps.image_subset.antisymm ?_
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₁, h₂] using intermediate_value_Ioo ht hrc
    · simpa only [h₁, h₂] using intermediate_value_Ioo' ht hrc
  have h₁₂ : r₁ ≤ r₂ := by
    rcases ht.eq_or_lt with rfl | ht'
    · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
    · obtain ⟨h₁, h₂⟩ := hmem _ ⟨left_lt_add_div_two.2 ht', add_div_two_lt_right.2 ht'⟩
      exact (h₁.trans h₂).le
  refine ⟨h₁₂, hp, fun g ↦ ?_⟩
  rw [← himage, integral_image_eq_integral_abs_deriv_smul_of_ne_zero (convex_Ioo t₁ t₂)
    (fun t htI ↦ (hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential
      (hγ t (hIoo htI)) (hr t (hIoo htI)) (hU t (hIoo htI))).hasDerivWithinAt)
    (fun t htI ↦ div_ne_zero (hp t htI).2 hm.ne') g]
  simp only [smul_eq_mul, abs_div, abs_of_pos hm]

/-- **The time between turning radii is the radial quadrature.** Let `(r(t), p_r(t))` be an
integral curve on `[t₁, t₂]`, in the half-line `r > 0`, of the Hamiltonian vector field of the
reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`, with energy `E`. Suppose the radius moves
from one of `r₁`, `r₂` to the other and stays strictly between them, where `U_ℓ < E`. Then the
elapsed time is

`t₂ - t₁ = ∫_{r₁}^{r₂} m dr / |p_r| = ∫_{r₁}^{r₂} dr / √((2 / m) (E - U_ℓ(r)))`. -/
theorem sub_eq_integral_div_absRadialMomentum (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hγ : ∀ t ∈ Icc t₁ t₂, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ∈ Icc t₁ t₂, 0 < (γ t).1) (hU : ∀ t ∈ Icc t₁ t₂, DifferentiableAt ℝ U (γ t).1)
    (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₁) = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hends : (γ t₁).1 = r₁ ∧ (γ t₂).1 = r₂ ∨ (γ t₁).1 = r₂ ∧ (γ t₂).1 = r₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo r₁ r₂) :
    t₂ - t₁ = ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r := by
  obtain ⟨h₁₂, hp, hcov⟩ := leg_data hm ht hγ hr hU hE hlt hends hmem
  rw [integral_of_le h₁₂, integral_Ioc_eq_integral_Ioo, hcov,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ ↦ (1 : ℝ)) fun t htI ↦ ?_,
    setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le ht]
  rw [(hp t htI).1]
  field_simp [abs_ne_zero.2 (hp t htI).2]

/-- **The angle swept between turning radii is the apsidal angle.** Under the hypotheses of
`TauCeti.sub_eq_integral_div_absRadialMomentum`, let `θ` satisfy the polar Hamilton equation
`θ' = ℓ / (m r²)`. Then the angle swept while the radius moves between `r₁` and `r₂` is

`θ(t₂) - θ(t₁) = ∫_{r₁}^{r₂} ℓ dr / (r² |p_r|)`. -/
theorem sub_eq_apsidalAngle (hm : 0 < m) (ht : t₁ ≤ t₂)
    (hγ : ∀ t ∈ Icc t₁ t₂, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ∈ Icc t₁ t₂, 0 < (γ t).1) (hU : ∀ t ∈ Icc t₁ t₂, DifferentiableAt ℝ U (γ t).1)
    (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₁) = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hends : (γ t₁).1 = r₁ ∧ (γ t₂).1 = r₂ ∨ (γ t₁).1 = r₂ ∧ (γ t₂).1 = r₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo r₁ r₂) {θ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc t₁ t₂, HasDerivAt θ (ℓ / (m * (γ t).1 ^ 2)) t) :
    θ t₂ - θ t₁ = apsidalAngle m U ℓ E r₁ r₂ := by
  obtain ⟨h₁₂, hp, hcov⟩ := leg_data hm ht hγ hr hU hE hlt hends hmem
  have hcont : ContinuousOn (fun t ↦ ℓ / (m * (γ t).1 ^ 2)) (Icc t₁ t₂) := fun t ht ↦
    (continuousAt_const.div (continuousAt_const.mul ((hγ t ht).continuousAt.fst.pow 2))
      (mul_ne_zero hm.ne' (pow_ne_zero 2 (hr t ht).ne'))).continuousWithinAt
  rw [← integral_eq_sub_of_hasDerivAt (by rwa [uIcc_of_le ht])
      (hcont.intervalIntegrable_of_Icc ht), apsidalAngle_def, integral_of_le h₁₂,
    integral_Ioc_eq_integral_Ioo, hcov, integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t htI ↦ ?_
  have hr' := hr t (Ioo_subset_Icc_self htI)
  rw [(hp t htI).1]
  field_simp [abs_ne_zero.2 (hp t htI).2]

/-- **A full radial oscillation lasts one radial period.** Let `(r(t), p_r(t))` be an integral curve
on `[t₁, t₃]`, in the half-line `r > 0`, of the Hamiltonian vector field of the reduced Hamiltonian,
with energy `E`. Suppose the radius moves from one of `r₁`, `r₂` to the other during `[t₁, t₂]`
and back during `[t₂, t₃]`, staying strictly between them, where `U_ℓ < E`, except at these
times. Then `t₃ - t₁` is the radial period, twice the time integral between the turning radii. -/
theorem sub_eq_radialPeriod (hm : 0 < m) {t₃ : ℝ} (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : ∀ t ∈ Icc t₁ t₃, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ∈ Icc t₁ t₃, 0 < (γ t).1) (hU : ∀ t ∈ Icc t₁ t₃, DifferentiableAt ℝ U (γ t).1)
    (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₁) = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hends : (γ t₁).1 = r₁ ∧ (γ t₂).1 = r₂ ∨ (γ t₁).1 = r₂ ∧ (γ t₂).1 = r₁)
    (h₃ : (γ t₃).1 = (γ t₁).1) (hmem₁₂ : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo r₁ r₂)
    (hmem₂₃ : ∀ t ∈ Ioo t₂ t₃, (γ t).1 ∈ Ioo r₁ r₂) :
    t₃ - t₁ = radialPeriod m U ℓ E r₁ r₂ := by
  have hsub₁ : Icc t₁ t₂ ⊆ Icc t₁ t₃ := Icc_subset_Icc_right ht₂₃
  have hsub₂ : Icc t₂ t₃ ⊆ Icc t₁ t₃ := Icc_subset_Icc_left ht₁₂
  have hE₂ := (centralForceHamiltonian_effectivePotential_eq_of_hasDerivAt hγ hr hU t₂
    ⟨ht₁₂, ht₂₃⟩).trans hE
  have h₁ := sub_eq_integral_div_absRadialMomentum hm ht₁₂ (fun t ht ↦ hγ t (hsub₁ ht))
    (fun t ht ↦ hr t (hsub₁ ht)) (fun t ht ↦ hU t (hsub₁ ht)) hE hlt hends hmem₁₂
  have h₂ := sub_eq_integral_div_absRadialMomentum hm ht₂₃ (fun t ht ↦ hγ t (hsub₂ ht))
    (fun t ht ↦ hr t (hsub₂ ht)) (fun t ht ↦ hU t (hsub₂ ht)) hE₂ hlt
    (by rw [h₃]; tauto) hmem₂₃
  rw [radialPeriod_def]
  linarith

/-- **The angle swept in a full radial oscillation is twice the apsidal angle.** Under the
hypotheses of `TauCeti.sub_eq_radialPeriod`, if `θ' = ℓ / (m r²)` on `[t₁, t₃]`, then
`θ(t₃) - θ(t₁) = 2 Δθ`, where `Δθ` is the apsidal angle. -/
theorem sub_eq_two_mul_apsidalAngle (hm : 0 < m) {t₃ : ℝ} (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : ∀ t ∈ Icc t₁ t₃, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ∈ Icc t₁ t₃, 0 < (γ t).1) (hU : ∀ t ∈ Icc t₁ t₃, DifferentiableAt ℝ U (γ t).1)
    (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₁) = E)
    (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
    (hends : (γ t₁).1 = r₁ ∧ (γ t₂).1 = r₂ ∨ (γ t₁).1 = r₂ ∧ (γ t₂).1 = r₁)
    (h₃ : (γ t₃).1 = (γ t₁).1) (hmem₁₂ : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo r₁ r₂)
    (hmem₂₃ : ∀ t ∈ Ioo t₂ t₃, (γ t).1 ∈ Ioo r₁ r₂) {θ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc t₁ t₃, HasDerivAt θ (ℓ / (m * (γ t).1 ^ 2)) t) :
    θ t₃ - θ t₁ = 2 * apsidalAngle m U ℓ E r₁ r₂ := by
  have hsub₁ : Icc t₁ t₂ ⊆ Icc t₁ t₃ := Icc_subset_Icc_right ht₂₃
  have hsub₂ : Icc t₂ t₃ ⊆ Icc t₁ t₃ := Icc_subset_Icc_left ht₁₂
  have hE₂ := (centralForceHamiltonian_effectivePotential_eq_of_hasDerivAt hγ hr hU t₂
    ⟨ht₁₂, ht₂₃⟩).trans hE
  have h₁ := sub_eq_apsidalAngle hm ht₁₂ (fun t ht ↦ hγ t (hsub₁ ht))
    (fun t ht ↦ hr t (hsub₁ ht)) (fun t ht ↦ hU t (hsub₁ ht)) hE hlt hends hmem₁₂
    fun t ht ↦ hθ t (hsub₁ ht)
  have h₂ := sub_eq_apsidalAngle hm ht₂₃ (fun t ht ↦ hγ t (hsub₂ ht))
    (fun t ht ↦ hr t (hsub₂ ht)) (fun t ht ↦ hU t (hsub₂ ht)) hE₂ hlt
    (by rw [h₃]; tauto) hmem₂₃ fun t ht ↦ hθ t (hsub₂ ht)
  linarith

end Motion

end TauCeti
