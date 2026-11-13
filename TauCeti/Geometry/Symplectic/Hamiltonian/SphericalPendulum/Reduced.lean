/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.RotationAngle
public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard
import TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic
import TauCeti.MeasureTheory.Function.Jacobian.OneDim
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The reduced spherical pendulum: period and rotation integrals

In cylindrical coordinates `(z, φ)` on the unit sphere, with conjugate momenta `(p_z, j)`, the
energy of the spherical pendulum is

`H(z, φ, p_z, j) = (1 - z²) p_z² / 2 + V_j(z)`,  `V_j(z) = j² / (2 (1 - z²)) + z`,

where `V_j` is the effective potential `TauCeti.sphericalPendulumEffectivePotential`. It does not
depend on the azimuth `φ`, so the vertical angular momentum `j` is conserved, and for fixed `j`
the height obeys Hamilton's equations of the **reduced Hamiltonian**
`H_j(z, p_z) = (1 - z²) p_z² / 2 + V_j(z)` (`TauCeti.sphericalPendulumReducedHamiltonian`) on
`(-1, 1) × ℝ` with the standard form `dz ∧ dp_z`, and the azimuth obeys `φ' = ∂H / ∂j`. This
cylindrical reduction of the flow on `T*S²` is informal motivation here: the file proves
`∂_j H_j = j / (1 - z²)` (`TauCeti.hasDerivAt_sphericalPendulumReducedHamiltonian_left`), and the
azimuth formulas below take `φ' = j / (1 - z²)` as a hypothesis on `φ : ℝ → ℝ`. The vertical
momentum of the pendulum is `p₃ = z' = (1 - z²) p_z`, so at a point of the phase space away from
the poles `H_J(q₃, p₃ / (1 - q₃²))` is the energy
(`TauCeti.sphericalPendulumReducedHamiltonian_eq_fst_sphericalPendulumEnergyMomentum`).

Along a motion of energy `h` the height velocity satisfies `z'² = 2 (h - z) (1 - z²) - j²`
(`TauCeti.sq_one_sub_fst_sq_mul_snd_eq_of_sphericalPendulumReducedHamiltonian_eq`). Integrating
`dt = dz / |z'|` between turning heights `z₁ < z₂`, where the radicand vanishes or the height
reverses, gives the classical quadratures. The **period** of the height is

`T(h, j) = 2 ∫ dz / √(2 (h - z) (1 - z²) - j²)`

(`TauCeti.sphericalPendulumPeriod`), with the same convention as the rotation angle
`Θ(h, j) = 2 ∫ j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`
(`TauCeti.sphericalPendulumRotationAngle`): the integral runs over `(-1, 1)` and the integrand
vanishes where the radicand is not positive.

* **Convergence.** At simple turning points, where the radicand has a nonzero derivative, both
  quadratures between the turning heights converge
  (`TauCeti.intervalIntegrable_one_div_sqrt_sphericalPendulum`,
  `TauCeti.intervalIntegrable_div_mul_sqrt_sphericalPendulum`).
* **One leg.** Along an integral curve of the reduced Hamiltonian vector field whose height runs
  from one of `z₁`, `z₂` to the other, staying strictly between them where the radicand is
  positive, the elapsed time is `∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`, and an azimuth `φ`
  with `φ' = j / (1 - z²)` sweeps `∫_{z₁}^{z₂} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`
  (`TauCeti.sub_eq_integral_one_div_sqrt_of_sphericalPendulum`,
  `TauCeti.sub_eq_integral_div_mul_sqrt_of_sphericalPendulum`).
* **A full oscillation.** If moreover `z₁` and `z₂` bound the heights at which the radicand is
  positive, a full oscillation of the height, up and back down, lasts `T(h, j)` and turns such an
  azimuth by `Θ(h, j)` (`TauCeti.sub_eq_sphericalPendulumPeriod`,
  `TauCeti.sub_eq_sphericalPendulumRotationAngle`).

So after one period of the height the motion returns to its initial height and vertical momentum,
rotated about the vertical axis by the rotation angle `Θ(h, j)`; the rotation number
`Θ(h, j) / (2π)` enters the Hamiltonian monodromy of the pendulum. The reduced coordinates are
singular at the poles, so the motions considered here stay in `-1 < z < 1`. The angular momentum
vanishes at the poles (`TauCeti.snd_sphericalPendulumEnergyMomentum_eq_zero_of_sq_eq_one`), so
for `j ≠ 0` the fibre `F⁻¹(h, j)` contains no pole.

The change of variables from time to height along one leg is the shared quadrature
`MeasureTheory.sub_eq_integral_div_of_mapsTo`, which follows the radial pattern of
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.TurningPoint`
(`TauCeti.sub_eq_integral_div_absRadialMomentum`, `TauCeti.sub_eq_apsidalAngle`); convergence at
simple turning points reuses `TauCeti.intervalIntegrable_one_div_sqrt_of_hasDerivWithinAt`, as
`TauCeti.intervalIntegrable_div_absRadialMomentum` does.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
* L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., Pergamon, 1976, Section 14, Problem 1.
-/

public section

open Real Set MeasureTheory intervalIntegral

namespace TauCeti

/-! ### The reduced Hamiltonian -/

/-- The **reduced Hamiltonian** `H_j(z, p_z) = (1 - z²) p_z² / 2 + V_j(z)` of the spherical
pendulum at vertical angular momentum `j`, on the phase space `ℝ × ℝ` of heights `z` and conjugate
momenta `p_z`. It is the energy of the pendulum in cylindrical coordinates; it is meaningful for
`-1 < z < 1`. -/
noncomputable def sphericalPendulumReducedHamiltonian (j : ℝ) (x : ℝ × ℝ) : ℝ :=
  (1 - x.1 ^ 2) * x.2 ^ 2 / 2 + sphericalPendulumEffectivePotential j x.1

theorem sphericalPendulumReducedHamiltonian_def (j : ℝ) (x : ℝ × ℝ) :
    sphericalPendulumReducedHamiltonian j x =
      (1 - x.1 ^ 2) * x.2 ^ 2 / 2 + sphericalPendulumEffectivePotential j x.1 :=
  (rfl)

@[simp]
theorem sphericalPendulumReducedHamiltonian_apply (j z p : ℝ) :
    sphericalPendulumReducedHamiltonian j (z, p) =
      (1 - z ^ 2) * p ^ 2 / 2 + sphericalPendulumEffectivePotential j z :=
  (rfl)

/-- The reduced Hamiltonian is even in the angular momentum. -/
@[simp]
theorem sphericalPendulumReducedHamiltonian_neg_left (j : ℝ) (x : ℝ × ℝ) :
    sphericalPendulumReducedHamiltonian (-j) x = sphericalPendulumReducedHamiltonian j x := by
  simp only [sphericalPendulumReducedHamiltonian_def, sphericalPendulumEffectivePotential_neg_left]

/-- At a point `(q, p)` of the phase space away from the poles, the reduced Hamiltonian at the
vertical angular momentum `J(q, p)`, evaluated at the height `q₃` and the momentum
`p_z = p₃ / (1 - q₃²)` conjugate to it, is the energy `H(q, p)`. -/
theorem sphericalPendulumReducedHamiltonian_eq_fst_sphericalPendulumEnergyMomentum
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hz : x.1 2 ^ 2 < 1) :
    sphericalPendulumReducedHamiltonian (sphericalPendulumEnergyMomentum x).2
        (x.1 2, x.2 2 / (1 - x.1 2 ^ 2)) =
      (sphericalPendulumEnergyMomentum x).1 := by
  have hz' : 1 - x.1 2 ^ 2 ≠ 0 := (sub_pos.2 hz).ne'
  rw [fst_sphericalPendulumEnergyMomentum_eq hx hz, sphericalPendulumReducedHamiltonian_def]
  field_simp
  ring

/-- The derivative `∂_j H_j` of the reduced Hamiltonian in the angular momentum is
`j / (1 - z²)`. Away from the poles (`z² < 1`) this is the angular velocity `φ' = ∂H / ∂j` of the
azimuth. At `z = ±1` the formula still holds, but only through the convention `a / 0 = 0`: both
`H_j` and `j / (1 - z²)` are singular there, and the identity then reads `0 = 0`. -/
theorem hasDerivAt_sphericalPendulumReducedHamiltonian_left (j : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun j ↦ sphericalPendulumReducedHamiltonian j x) (j / (1 - x.1 ^ 2)) j := by
  simp only [sphericalPendulumReducedHamiltonian_def, sphericalPendulumEffectivePotential_def]
  have h := (((hasDerivAt_pow 2 j).div_const (2 * (1 - x.1 ^ 2))).add_const x.1).const_add
    ((1 - x.1 ^ 2) * x.2 ^ 2 / 2)
  convert h using 1
  rcases eq_or_ne (1 - x.1 ^ 2) 0 with h0 | h0
  · simp [h0]
  · field_simp
    ring

/-- Away from the poles, the effective potential `V_j(z) = j² / (2 (1 - z²)) + z` has derivative
`V_j'(z) = j² z / (1 - z²)² + 1`. -/
theorem hasDerivAt_sphericalPendulumEffectivePotential (j : ℝ) {z : ℝ} (hz : z ^ 2 ≠ 1) :
    HasDerivAt (sphericalPendulumEffectivePotential j) (j ^ 2 * z / (1 - z ^ 2) ^ 2 + 1) z := by
  have hz' : 1 - z ^ 2 ≠ 0 := sub_ne_zero.2 hz.symm
  rw [funext (sphericalPendulumEffectivePotential_def j)]
  refine (((hasDerivAt_const z (j ^ 2)).fun_div (((hasDerivAt_pow 2 z).const_sub 1).const_mul 2)
    (mul_ne_zero two_ne_zero hz')).fun_add (hasDerivAt_id' z)).congr_deriv ?_
  field_simp
  ring

/-- The derivative of the reduced Hamiltonian away from the poles, as partial gradients:
`∂_z H_j = 1 + j² z / (1 - z²)² - z p_z²` and `∂_{p_z} H_j = (1 - z²) p_z`. -/
theorem hasFDerivAt_sphericalPendulumReducedHamiltonian (j : ℝ) {x : ℝ × ℝ} (hz : x.1 ^ 2 ≠ 1) :
    HasFDerivAt (sphericalPendulumReducedHamiltonian j)
      ((innerSL ℝ (1 + j ^ 2 * x.1 / (1 - x.1 ^ 2) ^ 2 - x.1 * x.2 ^ 2)).coprod
        (innerSL ℝ ((1 - x.1 ^ 2) * x.2))) x := by
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (p := x)
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (p := x)
  have h := ((((hasFDerivAt_const (1 : ℝ) x).sub (hfst.pow 2)).mul (hsnd.pow 2)).mul_const
    (2⁻¹ : ℝ)).add ((hasDerivAt_sphericalPendulumEffectivePotential j hz).comp_hasFDerivAt x hfst)
  have hH : sphericalPendulumReducedHamiltonian j =
      fun y ↦ (1 - y.1 ^ 2) * y.2 ^ 2 * 2⁻¹ + sphericalPendulumEffectivePotential j y.1 := by
    funext y
    rw [sphericalPendulumReducedHamiltonian_def, div_eq_mul_inv]
  rw [hH]
  refine h.congr_fderiv ?_
  ext <;> simp [RCLike.inner_apply] <;> ring

/-- **Hamilton's equations of the reduced pendulum.** Away from the poles, the Hamiltonian vector
field of `H_j` at `(z, p_z)` is `((1 - z²) p_z, z p_z² - j² z / (1 - z²)² - 1)`. -/
theorem stdSymplecticForm_hamiltonianVectorField_sphericalPendulumReducedHamiltonian (j : ℝ)
    {x : ℝ × ℝ} (hz : x.1 ^ 2 ≠ 1) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField (sphericalPendulumReducedHamiltonian j) x =
      ((1 - x.1 ^ 2) * x.2, x.1 * x.2 ^ 2 - j ^ 2 * x.1 / (1 - x.1 ^ 2) ^ 2 - 1) := by
  rw [stdSymplecticForm_hamiltonianVectorField
    (hasFDerivAt_sphericalPendulumReducedHamiltonian j hz)]
  ext
  · rfl
  · simp only [neg_sub]
    ring

variable {j h z₁ z₂ : ℝ}

/-! ### The period of the height -/

/-- The **period** `T(h, j) = 2 ∫ dz / √(2 (h - z) (1 - z²) - j²)` of the height of the spherical
pendulum at energy `h` and vertical angular momentum `j`. As for the rotation angle
`TauCeti.sphericalPendulumRotationAngle`, the integral runs over `(-1, 1)`, but the integrand
vanishes at every height `z` with `2 (h - z) (1 - z²) ≤ j²`, so for a regular value it is twice the
integral between the two turning points of the height. -/
noncomputable def sphericalPendulumPeriod (h j : ℝ) : ℝ :=
  2 * ∫ z in (-1)..1, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)

theorem sphericalPendulumPeriod_def (h j : ℝ) :
    sphericalPendulumPeriod h j = 2 * ∫ z in (-1)..1, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) :=
  (rfl)

/-- The period is even in the angular momentum. -/
@[simp]
theorem sphericalPendulumPeriod_neg_right (h j : ℝ) :
    sphericalPendulumPeriod h (-j) = sphericalPendulumPeriod h j := by
  simp only [sphericalPendulumPeriod_def, neg_sq]

/-- The period is nonnegative. -/
theorem sphericalPendulumPeriod_nonneg (h j : ℝ) : 0 ≤ sphericalPendulumPeriod h j :=
  mul_nonneg zero_le_two (intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ by positivity)

/-- **The period between turning heights.** If `-1 ≤ z₁ ≤ z₂ ≤ 1` and the radicand
`2 (h - z) (1 - z²) - j²` is not positive at the heights in `(-1, 1)` outside `(z₁, z₂)`, then
`T(h, j) = 2 ∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`. -/
theorem sphericalPendulumPeriod_eq_integral (hz₁ : -1 ≤ z₁) (h₁₂ : z₁ ≤ z₂) (hz₂ : z₂ ≤ 1)
    (hout : ∀ z ∈ Ioo (-1) 1, z ∉ Ioo z₁ z₂ → 2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0) :
    sphericalPendulumPeriod h j =
      2 * ∫ z in z₁..z₂, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
  rw [sphericalPendulumPeriod_def,
    TauCeti.intervalIntegral.integral_eq_integral_of_forall_notMem_eq_zero hz₁ h₁₂ hz₂
      fun z hz hz' ↦ by rw [sqrt_eq_zero'.2 (hout z hz hz'), div_zero]]

/-- **The rotation angle between turning heights.** Under the hypotheses of
`TauCeti.sphericalPendulumPeriod_eq_integral`,
`Θ(h, j) = 2 ∫_{z₁}^{z₂} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`. -/
theorem sphericalPendulumRotationAngle_eq_integral (hz₁ : -1 ≤ z₁) (h₁₂ : z₁ ≤ z₂) (hz₂ : z₂ ≤ 1)
    (hout : ∀ z ∈ Ioo (-1) 1, z ∉ Ioo z₁ z₂ → 2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0) :
    sphericalPendulumRotationAngle h j =
      2 * ∫ z in z₁..z₂, j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) := by
  rw [sphericalPendulumRotationAngle_def,
    TauCeti.intervalIntegral.integral_eq_integral_of_forall_notMem_eq_zero hz₁ h₁₂ hz₂
      fun z hz hz' ↦ by rw [sqrt_eq_zero'.2 (hout z hz hz'), mul_zero, div_zero]]

/-! ### Convergence at simple turning points -/

/-- **The time quadrature converges at simple turning points.** Let `z₁ < z₂` with
`2 (h - z) (1 - z²) > j²` in between, and suppose that each `zᵢ` at which the radicand
`P(z) = 2 (h - z) (1 - z²) - j²` vanishes is a simple zero, `P'(zᵢ) = 6 zᵢ² - 4 h zᵢ - 2 ≠ 0`.
Then `z ↦ 1 / √P(z)` is interval integrable on `[z₁, z₂]`, although it is unbounded at a turning
point. -/
theorem intervalIntegrable_one_div_sqrt_sphericalPendulum (h₁₂ : z₁ < z₂)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hd₁ : 2 * (h - z₁) * (1 - z₁ ^ 2) - j ^ 2 = 0 → 6 * z₁ ^ 2 - 4 * h * z₁ - 2 ≠ 0)
    (hd₂ : 2 * (h - z₂) * (1 - z₂ ^ 2) - j ^ 2 = 0 → 6 * z₂ ^ 2 - 4 * h * z₂ - 2 ≠ 0) :
    IntervalIntegrable (fun z ↦ 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) volume z₁ z₂ := by
  have hP (z : ℝ) : HasDerivAt (fun z ↦ 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
      (6 * z ^ 2 - 4 * h * z - 2) z := by
    simpa only [one_mul, mul_one] using
      (hasDerivAt_two_mul_sub_mul_mul_one_sub_sq h 1 z).sub_const (j ^ 2)
  refine intervalIntegrable_one_div_sqrt_of_hasDerivWithinAt h₁₂
    (fun z _ ↦ (hP z).continuousAt.continuousWithinAt) hlt (fun h0 ↦ ?_) (fun h0 ↦ ?_)
  · exact ⟨_, hd₁ h0, (hP z₁).hasDerivWithinAt⟩
  · exact ⟨_, hd₂ h0, (hP z₂).hasDerivWithinAt⟩

/-- **The period is positive.** If `-1 ≤ z₁ < z₂ ≤ 1` bound the heights in `(-1, 1)` at which the
radicand `2 (h - z) (1 - z²) - j²` is positive, which are all of `(z₁, z₂)`, and the turning points
are simple, then `0 < T(h, j)`. -/
theorem sphericalPendulumPeriod_pos (hz₁ : -1 ≤ z₁) (h₁₂ : z₁ < z₂) (hz₂ : z₂ ≤ 1)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hout : ∀ z ∈ Ioo (-1) 1, z ∉ Ioo z₁ z₂ → 2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0)
    (hd₁ : 2 * (h - z₁) * (1 - z₁ ^ 2) - j ^ 2 = 0 → 6 * z₁ ^ 2 - 4 * h * z₁ - 2 ≠ 0)
    (hd₂ : 2 * (h - z₂) * (1 - z₂ ^ 2) - j ^ 2 = 0 → 6 * z₂ ^ 2 - 4 * h * z₂ - 2 ≠ 0) :
    0 < sphericalPendulumPeriod h j := by
  rw [sphericalPendulumPeriod_eq_integral hz₁ h₁₂.le hz₂ hout]
  exact mul_pos two_pos <| intervalIntegral_pos_of_pos_on
    (intervalIntegrable_one_div_sqrt_sphericalPendulum h₁₂ hlt hd₁ hd₂)
    (fun z hz ↦ one_div_pos.2 (sqrt_pos.2 (hlt z hz))) h₁₂

/-- **The angle quadrature converges at simple turning points.** Under the hypotheses of
`TauCeti.intervalIntegrable_one_div_sqrt_sphericalPendulum`, the integrand
`z ↦ j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` of the rotation angle is interval integrable on
`[z₁, z₂]`. For `j ≠ 0` the radicand is `-j² < 0` at the poles, so `[z₁, z₂]` avoids them; for
`j = 0` the integrand vanishes. -/
theorem intervalIntegrable_div_mul_sqrt_sphericalPendulum (h₁₂ : z₁ < z₂)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hd₁ : 2 * (h - z₁) * (1 - z₁ ^ 2) - j ^ 2 = 0 → 6 * z₁ ^ 2 - 4 * h * z₁ - 2 ≠ 0)
    (hd₂ : 2 * (h - z₂) * (1 - z₂ ^ 2) - j ^ 2 = 0 → 6 * z₂ ^ 2 - 4 * h * z₂ - 2 ≠ 0) :
    IntervalIntegrable (fun z ↦ j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))
      volume z₁ z₂ := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  -- The radicand is nonnegative on `[z₁, z₂]`, the closure of `(z₁, z₂)`, but `-j² < 0` at
  -- the poles.
  have hnn : Icc z₁ z₂ ⊆ {z | 0 ≤ 2 * (h - z) * (1 - z ^ 2) - j ^ 2} := by
    rw [← closure_Ioo h₁₂.ne]
    exact closure_minimal (fun z hz ↦ (hlt z hz).le)
      (isClosed_le continuous_const (by fun_prop))
  have hpos {z : ℝ} (hz : z ∈ Icc z₁ z₂) : 1 - z ^ 2 ≠ 0 := fun h0 ↦ by
    have := hnn hz
    rw [mem_ofPred_eq, h0, mul_zero, zero_sub, neg_nonneg] at this
    exact hj (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg j)))
  have h := (intervalIntegrable_one_div_sqrt_sphericalPendulum h₁₂ hlt hd₁ hd₂).continuousOn_mul
    (g := fun z ↦ j / (1 - z ^ 2)) <| by
      rw [uIcc_of_le h₁₂.le]
      exact continuousOn_const.div (continuousOn_const.sub (continuousOn_id.pow 2))
        fun z hz ↦ hpos hz
  convert h using 2 with z
  rw [div_mul_div_comm, mul_one]

/-! ### The motion of the height -/

section Motion

variable {t₁ t₂ : ℝ} {γ : ℝ → ℝ × ℝ}

/-- **Energy conservation for the reduced pendulum.** The reduced Hamiltonian is constant along an
integral curve, on a preconnected set of times, of its Hamiltonian vector field that stays away
from the poles. -/
theorem sphericalPendulumReducedHamiltonian_eq_of_hasDerivWithinAt {s : Set ℝ}
    (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivWithinAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) s t)
    (hz : ∀ t ∈ s, (γ t).1 ^ 2 ≠ 1) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    sphericalPendulumReducedHamiltonian j (γ t) = sphericalPendulumReducedHamiltonian j (γ t₀) :=
  (stdSymplecticForm (V := ℝ)).apply_eq_of_hasDerivWithinAt_hamiltonianVectorField hs hγ
    (fun s hs ↦ (hasFDerivAt_sphericalPendulumReducedHamiltonian j (hz s hs)).differentiableAt)
    ht₀ ht

/-- **The height velocity.** Along an integral curve of the reduced Hamiltonian vector field away
from the poles, the height has derivative `z' = (1 - z²) p_z`, the vertical momentum `p₃` of the
pendulum. -/
theorem hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_sphericalPendulumReducedHamiltonian
    {t : ℝ} (hγ : HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t) (hz : (γ t).1 ^ 2 ≠ 1) :
    HasDerivAt (fun s ↦ (γ s).1) ((1 - (γ t).1 ^ 2) * (γ t).2) t := by
  rw [stdSymplecticForm_hamiltonianVectorField_sphericalPendulumReducedHamiltonian j hz] at hγ
  exact hγ.fst

/-- On the level `h` of the reduced Hamiltonian, away from the poles, the square of the height
velocity is the radicand: `((1 - z²) p_z)² = 2 (h - z) (1 - z²) - j²`. -/
theorem sq_one_sub_fst_sq_mul_snd_eq_of_sphericalPendulumReducedHamiltonian_eq {x : ℝ × ℝ}
    (hz : x.1 ^ 2 ≠ 1) (hE : sphericalPendulumReducedHamiltonian j x = h) :
    ((1 - x.1 ^ 2) * x.2) ^ 2 = 2 * (h - x.1) * (1 - x.1 ^ 2) - j ^ 2 := by
  have hz' : 1 - x.1 ^ 2 ≠ 0 := sub_ne_zero.2 hz.symm
  rw [← hE, sphericalPendulumReducedHamiltonian_def, sphericalPendulumEffectivePotential_def]
  field_simp
  ring

/-- The hypotheses shared by the time and azimuth formulas along one leg of the height: the height
is continuous, with derivative `z' = (1 - z²) p_z` on `(t₁, t₂)`, where
`|z'| = √(2 (h - z) (1 - z²) - j²)` and `z' ≠ 0`. -/
private theorem leg_data (ht : t₁ ≤ t₂)
    (hγ : ∀ t ∈ Icc t₁ t₂, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t)
    (hz : ∀ t ∈ Icc t₁ t₂, (γ t).1 ^ 2 < 1)
    (hE : sphericalPendulumReducedHamiltonian j (γ t₁) = h)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hmem : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo z₁ z₂) :
    ContinuousOn (fun t ↦ (γ t).1) (Icc t₁ t₂) ∧
      ∀ t ∈ Ioo t₁ t₂, HasDerivAt (fun s ↦ (γ s).1) ((1 - (γ t).1 ^ 2) * (γ t).2) t ∧
        (1 - (γ t).1 ^ 2) * (γ t).2 ≠ 0 ∧
        |(1 - (γ t).1 ^ 2) * (γ t).2| = √(2 * (h - (γ t).1) * (1 - (γ t).1 ^ 2) - j ^ 2) := by
  refine ⟨fun t ht ↦ (hγ t ht).continuousAt.fst.continuousWithinAt, fun t htI ↦ ?_⟩
  have htc : t ∈ Icc t₁ t₂ := Ioo_subset_Icc_self htI
  -- On the level `h`, `z'² = 2 (h - z) (1 - z²) - j²`, which is positive strictly between the
  -- turning heights.
  have hsq := sq_one_sub_fst_sq_mul_snd_eq_of_sphericalPendulumReducedHamiltonian_eq
    (hz t htc).ne <| (sphericalPendulumReducedHamiltonian_eq_of_hasDerivWithinAt isPreconnected_Icc
      (fun s hs ↦ (hγ s hs).hasDerivWithinAt) (fun s hs ↦ (hz s hs).ne) (left_mem_Icc.2 ht)
      htc).trans hE
  refine ⟨hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_sphericalPendulumReducedHamiltonian
    (hγ t htc) (hz t htc).ne, fun h0 ↦ ?_, by rw [← hsq, sqrt_sq_eq_abs]⟩
  have := hlt _ (hmem t htI)
  rw [← hsq, h0] at this
  simp at this

/-- **The time between turning heights.** Let `(z(t), p_z(t))` be an integral curve on `[t₁, t₂]`,
away from the poles, of the Hamiltonian vector field of the reduced Hamiltonian `H_j`, with energy
`h`. Suppose the height moves from one of `z₁`, `z₂` to the other and stays strictly between
them, where `2 (h - z) (1 - z²) > j²`. Then the elapsed time is

`t₂ - t₁ = ∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`. -/
theorem sub_eq_integral_one_div_sqrt_of_sphericalPendulum (ht : t₁ ≤ t₂)
    (hγ : ∀ t ∈ Icc t₁ t₂, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t)
    (hz : ∀ t ∈ Icc t₁ t₂, (γ t).1 ^ 2 < 1)
    (hE : sphericalPendulumReducedHamiltonian j (γ t₁) = h)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (γ t₁).1 = z₁ ∧ (γ t₂).1 = z₂ ∨ (γ t₁).1 = z₂ ∧ (γ t₂).1 = z₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo z₁ z₂) :
    t₂ - t₁ = ∫ z in z₁..z₂, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
  obtain ⟨hc, hleg⟩ := leg_data ht hγ hz hE hlt hmem
  exact sub_eq_integral_div_of_mapsTo (φ := id) (ω := fun _ ↦ 1) ht hc
    (fun t ht ↦ (hleg t ht).1) (fun t ht ↦ (hleg t ht).2.1) hends hmem
    (fun t ht ↦ (hleg t ht).2.2) (fun t _ ↦ hasDerivAt_id t) continuousOn_const

/-- **The azimuth swept between turning heights.** Under the hypotheses of
`TauCeti.sub_eq_integral_one_div_sqrt_of_sphericalPendulum`, let the azimuth `φ` satisfy its
Hamilton equation `φ' = ∂H / ∂j = j / (1 - z²)`. Then the azimuth swept while the height moves
between `z₁` and `z₂` is

`φ(t₂) - φ(t₁) = ∫_{z₁}^{z₂} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`. -/
theorem sub_eq_integral_div_mul_sqrt_of_sphericalPendulum (ht : t₁ ≤ t₂)
    (hγ : ∀ t ∈ Icc t₁ t₂, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t)
    (hz : ∀ t ∈ Icc t₁ t₂, (γ t).1 ^ 2 < 1)
    (hE : sphericalPendulumReducedHamiltonian j (γ t₁) = h)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (γ t₁).1 = z₁ ∧ (γ t₂).1 = z₂ ∨ (γ t₁).1 = z₂ ∧ (γ t₂).1 = z₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo z₁ z₂) {φ : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc t₁ t₂, HasDerivAt φ (j / (1 - (γ t).1 ^ 2)) t) :
    φ t₂ - φ t₁ =
      ∫ z in z₁..z₂, j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) := by
  obtain ⟨hc, hleg⟩ := leg_data ht hγ hz hE hlt hmem
  simp_rw [← div_div]
  exact sub_eq_integral_div_of_mapsTo (ω := fun z ↦ j / (1 - z ^ 2)) ht hc
    (fun t ht ↦ (hleg t ht).1) (fun t ht ↦ (hleg t ht).2.1) hends hmem
    (fun t ht ↦ (hleg t ht).2.2) hφ fun t ht ↦
      (continuousAt_const.div (continuousAt_const.sub ((hγ t ht).continuousAt.fst.pow 2))
        (sub_pos.2 (hz t ht)).ne').continuousWithinAt

/-- The hypotheses shared by the period and rotation formulas for a full oscillation: the two
legs' time intervals, the energy at the turning time and the bounds `-1 ≤ z₁ ≤ z₂ ≤ 1`. -/
private theorem full_data {t₃ : ℝ} (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : ∀ t ∈ Icc t₁ t₃, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t)
    (hz : ∀ t ∈ Icc t₁ t₃, (γ t).1 ^ 2 < 1)
    (hE : sphericalPendulumReducedHamiltonian j (γ t₁) = h)
    (hends : (γ t₁).1 = z₁ ∧ (γ t₂).1 = z₂ ∨ (γ t₁).1 = z₂ ∧ (γ t₂).1 = z₁)
    (hmem₁₂ : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo z₁ z₂) :
    Icc t₁ t₂ ⊆ Icc t₁ t₃ ∧ Icc t₂ t₃ ⊆ Icc t₁ t₃ ∧
      sphericalPendulumReducedHamiltonian j (γ t₂) = h ∧ -1 ≤ z₁ ∧ z₁ ≤ z₂ ∧ z₂ ≤ 1 := by
  have hsub₁ : Icc t₁ t₂ ⊆ Icc t₁ t₃ := Icc_subset_Icc_right ht₂₃
  have hsub₂ : Icc t₂ t₃ ⊆ Icc t₁ t₃ := Icc_subset_Icc_left ht₁₂
  have h₁₃ : t₁ ≤ t₃ := ht₁₂.trans ht₂₃
  have hE₂ := (sphericalPendulumReducedHamiltonian_eq_of_hasDerivWithinAt isPreconnected_Icc
    (fun s hs ↦ (hγ s hs).hasDerivWithinAt) (fun s hs ↦ (hz s hs).ne) (left_mem_Icc.2 h₁₃)
    ⟨ht₁₂, ht₂₃⟩).trans hE
  have h₁₂ : z₁ ≤ z₂ := by
    rcases ht₁₂.eq_or_lt with rfl | ht'
    · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
    · obtain ⟨h₁, h₂⟩ := hmem₁₂ _ ⟨left_lt_add_div_two.2 ht', add_div_two_lt_right.2 ht'⟩
      exact (h₁.trans h₂).le
  -- The turning heights are values of the height, which stays in `(-1, 1)`.
  have hb₁ : (γ t₁).1 ^ 2 < 1 := hz t₁ ⟨le_rfl, h₁₃⟩
  have hb₂ : (γ t₂).1 ^ 2 < 1 := hz t₂ ⟨ht₁₂, ht₂₃⟩
  refine ⟨hsub₁, hsub₂, hE₂, ?_⟩
  rcases hends with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁] at hb₁ <;> rw [e₂] at hb₂ <;>
    exact ⟨by nlinarith, h₁₂, by nlinarith⟩
/-- **A full oscillation of the height lasts one period.** Let `(z(t), p_z(t))` be an integral curve
on `[t₁, t₃]`, away from the poles, of the Hamiltonian vector field of the reduced Hamiltonian
`H_j`, with energy `h`. Let `z₁ ≤ z₂` bound the heights in `(-1, 1)` at which the radicand
`2 (h - z) (1 - z²) - j²` is positive, which are all of `(z₁, z₂)`. Suppose the height moves from
one of `z₁`, `z₂` to the other during `[t₁, t₂]` and back during `[t₂, t₃]`, staying strictly
between them except at these times. Then `t₃ - t₁ = T(h, j)`. -/
theorem sub_eq_sphericalPendulumPeriod {t₃ : ℝ} (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : ∀ t ∈ Icc t₁ t₃, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t)
    (hz : ∀ t ∈ Icc t₁ t₃, (γ t).1 ^ 2 < 1)
    (hE : sphericalPendulumReducedHamiltonian j (γ t₁) = h)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hout : ∀ z ∈ Ioo (-1) 1, z ∉ Ioo z₁ z₂ → 2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0)
    (hends : (γ t₁).1 = z₁ ∧ (γ t₂).1 = z₂ ∨ (γ t₁).1 = z₂ ∧ (γ t₂).1 = z₁)
    (h₃ : (γ t₃).1 = (γ t₁).1) (hmem₁₂ : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo z₁ z₂)
    (hmem₂₃ : ∀ t ∈ Ioo t₂ t₃, (γ t).1 ∈ Ioo z₁ z₂) :
    t₃ - t₁ = sphericalPendulumPeriod h j := by
  obtain ⟨hsub₁, hsub₂, hE₂, hz₁, h₁₂, hz₂⟩ :=
    full_data ht₁₂ ht₂₃ hγ hz hE hends hmem₁₂
  have e₁ := sub_eq_integral_one_div_sqrt_of_sphericalPendulum ht₁₂
    (fun t ht ↦ hγ t (hsub₁ ht)) (fun t ht ↦ hz t (hsub₁ ht)) hE hlt hends hmem₁₂
  have e₂ := sub_eq_integral_one_div_sqrt_of_sphericalPendulum ht₂₃
    (fun t ht ↦ hγ t (hsub₂ ht)) (fun t ht ↦ hz t (hsub₂ ht)) hE₂ hlt
    (by rw [h₃]; tauto) hmem₂₃
  rw [sphericalPendulumPeriod_eq_integral hz₁ h₁₂ hz₂ hout]
  linarith

/-- **A full oscillation of the height turns the azimuth by the rotation angle.** Under the
hypotheses of `TauCeti.sub_eq_sphericalPendulumPeriod`, if the azimuth satisfies
`φ' = j / (1 - z²)` on `[t₁, t₃]`, then `φ(t₃) - φ(t₁) = Θ(h, j)`. -/
theorem sub_eq_sphericalPendulumRotationAngle {t₃ : ℝ} (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : ∀ t ∈ Icc t₁ t₃, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (sphericalPendulumReducedHamiltonian j) (γ t)) t)
    (hz : ∀ t ∈ Icc t₁ t₃, (γ t).1 ^ 2 < 1)
    (hE : sphericalPendulumReducedHamiltonian j (γ t₁) = h)
    (hlt : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hout : ∀ z ∈ Ioo (-1) 1, z ∉ Ioo z₁ z₂ → 2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0)
    (hends : (γ t₁).1 = z₁ ∧ (γ t₂).1 = z₂ ∨ (γ t₁).1 = z₂ ∧ (γ t₂).1 = z₁)
    (h₃ : (γ t₃).1 = (γ t₁).1) (hmem₁₂ : ∀ t ∈ Ioo t₁ t₂, (γ t).1 ∈ Ioo z₁ z₂)
    (hmem₂₃ : ∀ t ∈ Ioo t₂ t₃, (γ t).1 ∈ Ioo z₁ z₂) {φ : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc t₁ t₃, HasDerivAt φ (j / (1 - (γ t).1 ^ 2)) t) :
    φ t₃ - φ t₁ = sphericalPendulumRotationAngle h j := by
  obtain ⟨hsub₁, hsub₂, hE₂, hz₁, h₁₂, hz₂⟩ :=
    full_data ht₁₂ ht₂₃ hγ hz hE hends hmem₁₂
  have e₁ := sub_eq_integral_div_mul_sqrt_of_sphericalPendulum ht₁₂
    (fun t ht ↦ hγ t (hsub₁ ht)) (fun t ht ↦ hz t (hsub₁ ht)) hE hlt hends hmem₁₂
    fun t ht ↦ hφ t (hsub₁ ht)
  have e₂ := sub_eq_integral_div_mul_sqrt_of_sphericalPendulum ht₂₃
    (fun t ht ↦ hγ t (hsub₂ ht)) (fun t ht ↦ hz t (hsub₂ ht)) hE₂ hlt
    (by rw [h₃]; tauto) hmem₂₃ fun t ht ↦ hφ t (hsub₂ ht)
  rw [sphericalPendulumRotationAngle_eq_integral hz₁ h₁₂ hz₂ hout]
  linarith

end Motion

end TauCeti
