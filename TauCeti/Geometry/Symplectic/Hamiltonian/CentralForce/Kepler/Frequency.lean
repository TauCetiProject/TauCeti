/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Signed Kepler frequencies in action variables

The energy of an attractive Kepler orbit, expressed in its radial action `I_r` and signed
angular action `I_θ = ℓ`, is `H = -m κ² / (2 (I_r + |I_θ|)²)`. This file differentiates that
function on the two components `I_θ ≠ 0`. Its radial derivative is
`Ω_r = m κ² / (I_r + |I_θ|)³`, and its angular derivative is `sign(I_θ) Ω_r`.
In particular the frequencies have equal magnitudes, with signed resonance `1 : ±1`.

The comparison with `radialAction` uses the evaluated Kepler quadrature, rather than a new
choice of action. The derivatives also agree with `2π / radialPeriod` and
`2 * apsidalAngle / radialPeriod`; the latter includes both halves of the radial oscillation.
The frequency statements concern derivatives of this energy function;
they do not construct action-angle charts on the original phase space.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer,
  1989, Sections 8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, third edition, Addison-Wesley,
  2002, Section 10.8.
-/

public noncomputable section

open Real
open scoped ContDiff

namespace TauCeti

/-- The Kepler energy as a function of the radial action and the **signed** angular action.
Its physical action domain has `0 ≤ I.1` and `I.2 ≠ 0`; the formula extends wherever
`I.1 + |I.2| ≠ 0`. -/
def keplerActionHamiltonian (m κ : ℝ) (I : ℝ × ℝ) : ℝ :=
  -(m * κ ^ 2) / (2 * (I.1 + |I.2|) ^ 2)

/-- The formula for the Kepler Hamiltonian in action variables. -/
theorem keplerActionHamiltonian_def (m κ : ℝ) (I : ℝ × ℝ) :
    keplerActionHamiltonian m κ I = -(m * κ ^ 2) / (2 * (I.1 + |I.2|) ^ 2) := (rfl)

/-- The action Hamiltonian is smooth away from zero angular action and zero total action. -/
theorem contDiffAt_keplerActionHamiltonian (m κ : ℝ) {I : ℝ × ℝ} {k : ℕ∞}
    (hℓ : I.2 ≠ 0) (hI : I.1 + |I.2| ≠ 0) :
    ContDiffAt ℝ k (keplerActionHamiltonian m κ) I := by
  convert! (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ × ℝ ↦ -(m * κ ^ 2)) I).div
    (contDiffAt_const.mul ((contDiffAt_fst.add (contDiffAt_snd.abs hℓ)).pow 2))
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hI)) using 1

/-- The radial action derivative is `m κ² / (I_r + |ℓ|)³`, including when `ℓ = 0`. -/
theorem hasDerivAt_keplerActionHamiltonian_fst (m κ ℓ : ℝ) {J : ℝ}
    (hJ : J + |ℓ| ≠ 0) :
    HasDerivAt (fun r ↦ keplerActionHamiltonian m κ (r, ℓ))
      (m * κ ^ 2 / (J + |ℓ|) ^ 3) J := by
  unfold keplerActionHamiltonian
  convert (hasDerivAt_const J (-(m * κ ^ 2))).fun_div
    ((((hasDerivAt_id J).add_const |ℓ|).fun_pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hJ)) using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The full differential of the Kepler energy in action variables. The angular coefficient
retains the sign factor from the angular action. No positivity of the parameters is needed
for this analytic identity. -/
theorem hasFDerivAt_keplerActionHamiltonian (m κ : ℝ) {I : ℝ × ℝ}
    (hℓ : I.2 ≠ 0) (hI : I.1 + |I.2| ≠ 0) :
    HasFDerivAt (keplerActionHamiltonian m κ)
      ((m * κ ^ 2 / (I.1 + |I.2|) ^ 3) •
        (ContinuousLinearMap.fst ℝ ℝ ℝ +
          (SignType.sign I.2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) I := by
  have hs : HasDerivAt (fun s : ℝ ↦ -(m * κ ^ 2) / (2 * s ^ 2))
      (m * κ ^ 2 / (I.1 + |I.2|) ^ 3) (I.1 + |I.2|) := by
    simpa only [keplerActionHamiltonian_def, abs_zero, add_zero] using
      hasDerivAt_keplerActionHamiltonian_fst m κ 0 (by simpa using hI)
  convert! hs.comp_hasFDerivAt I
    ((hasFDerivAt_fst).fun_add ((hasFDerivAt_snd).abs hℓ)) using 1

/-- The angular action derivative is `sign(ℓ)` times the radial frequency formula. -/
theorem hasDerivAt_keplerActionHamiltonian_snd (m κ J : ℝ) {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (hJ : J + |ℓ| ≠ 0) :
    HasDerivAt (fun l ↦ keplerActionHamiltonian m κ (J, l))
      ((SignType.sign ℓ : ℝ) * (m * κ ^ 2 / (J + |ℓ|) ^ 3)) ℓ := by
  have h := (hasFDerivAt_keplerActionHamiltonian m κ (I := (J, ℓ)) hℓ hJ).comp_hasDerivAt ℓ
    ((hasDerivAt_const ℓ J).prodMk (hasDerivAt_id ℓ))
  simpa [Function.comp_def, mul_comm] using h

/-- The radial frequency is strictly positive for positive mass, nonzero coupling, and
positive total action. -/
theorem deriv_keplerActionHamiltonian_fst_pos {m κ J ℓ : ℝ}
    (hm : 0 < m) (hκ : κ ≠ 0) (hJ : 0 < J + |ℓ|) :
    0 < deriv (fun r ↦ keplerActionHamiltonian m κ (r, ℓ)) J := by
  rw [(hasDerivAt_keplerActionHamiltonian_fst m κ ℓ hJ.ne').deriv]
  positivity

/-- The signed Kepler resonance: `Ω_θ = sign(ℓ) Ω_r`. -/
theorem deriv_keplerActionHamiltonian_snd_eq_sign_mul (m κ J : ℝ) {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (hJ : J + |ℓ| ≠ 0) :
    deriv (fun l ↦ keplerActionHamiltonian m κ (J, l)) ℓ =
      (SignType.sign ℓ : ℝ) * deriv (fun r ↦ keplerActionHamiltonian m κ (r, ℓ)) J := by
  rw [(hasDerivAt_keplerActionHamiltonian_snd m κ J hℓ hJ).deriv,
    (hasDerivAt_keplerActionHamiltonian_fst m κ ℓ hJ).deriv]

/-- The two Kepler action frequencies have equal absolute values, including on the
negative-angular-momentum component. -/
theorem abs_deriv_keplerActionHamiltonian_snd (m κ J : ℝ) {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (hJ : J + |ℓ| ≠ 0) :
    |deriv (fun l ↦ keplerActionHamiltonian m κ (J, l)) ℓ| =
      |deriv (fun r ↦ keplerActionHamiltonian m κ (r, ℓ)) J| := by
  rw [deriv_keplerActionHamiltonian_snd_eq_sign_mul m κ J hℓ hJ, abs_mul]
  rcases hℓ.lt_or_gt with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- The radial action frequency agrees with the angular frequency `2π / T_r` of the
radial oscillation, where `T_r` is the actual Kepler period quadrature. -/
theorem deriv_keplerActionHamiltonian_fst_eq_div_radialPeriod {m κ ℓ E r₁ r₂ : ℝ}
    (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    deriv (fun J ↦ keplerActionHamiltonian m κ (J, ℓ))
        (radialAction m (fun r ↦ -κ / r) ℓ E r₁ r₂) =
      2 * π / radialPeriod m (fun r ↦ -κ / r) ℓ E r₁ r₂ := by
  have hE := kepler_energy_neg hm hℓ h₁ hlt hr₁ hr₂
  have hκ := kepler_kappa_pos hm hℓ h₁ hlt hr₁ hr₂
  have ha : 0 < (r₁ + r₂) / 2 := by linarith
  have hb : 0 < √(m / κ) := sqrt_pos.2 (div_pos hm hκ)
  have hc : 0 < √((r₁ + r₂) / 2) := sqrt_pos.2 ha
  have htotal : 0 < radialAction m (fun r ↦ -κ / r) ℓ E r₁ r₂ + |ℓ| := by
    rw [kepler_radialAction hm hℓ h₁ hlt hr₁ hr₂, sub_add_cancel]
    exact mul_pos hκ (sqrt_pos.2 (div_pos hm (by linarith)))
  have hs : √(m / (-2 * E)) = √(m / κ) * √((r₁ + r₂) / 2) := by
    rw [← sqrt_mul (div_nonneg hm.le hκ.le)]
    congr 1
    rw [kepler_kappa_eq hm.ne' h₁.ne' (h₁.trans hlt).ne' hlt.ne hr₁ hr₂]
    field_simp [hE.ne, ne_of_gt (by linarith : 0 < r₁ + r₂)]
  rw [(hasDerivAt_keplerActionHamiltonian_fst m κ ℓ htotal.ne').deriv,
    kepler_radialAction hm hℓ h₁ hlt hr₁ hr₂, sub_add_cancel,
    kepler_radialPeriod hm hℓ h₁ hlt hr₁ hr₂, rpow_div_two_eq_sqrt 3 ha.le,
    hs]
  have hb2 := sq_sqrt (div_pos hm hκ).le
  field_simp at hb2 ⊢
  rw [hb2]
  norm_num [rpow_natCast]

/-- The signed angular action frequency is the total polar angle swept in one radial
period divided by that period. `apsidalAngle` describes only half of the oscillation. -/
theorem deriv_keplerActionHamiltonian_snd_eq_div_radialPeriod {m κ ℓ E r₁ r₂ : ℝ}
    (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    deriv (fun l ↦ keplerActionHamiltonian m κ
        (radialAction m (fun r ↦ -κ / r) ℓ E r₁ r₂, l)) ℓ =
      2 * apsidalAngle m (fun r ↦ -κ / r) ℓ E r₁ r₂ /
        radialPeriod m (fun r ↦ -κ / r) ℓ E r₁ r₂ := by
  have hE := kepler_energy_neg hm hℓ h₁ hlt hr₁ hr₂
  have hκ := kepler_kappa_pos hm hℓ h₁ hlt hr₁ hr₂
  have htotal : radialAction m (fun r ↦ -κ / r) ℓ E r₁ r₂ + |ℓ| ≠ 0 := by
    rw [kepler_radialAction hm hℓ h₁ hlt hr₁ hr₂, sub_add_cancel]
    exact ne_of_gt (mul_pos hκ (sqrt_pos.2 (div_pos hm (by linarith))))
  rw [deriv_keplerActionHamiltonian_snd_eq_sign_mul m κ _ hℓ htotal,
    deriv_keplerActionHamiltonian_fst_eq_div_radialPeriod hm hℓ h₁ hlt hr₁ hr₂,
    kepler_apsidalAngle hm hℓ h₁ hlt hr₁ hr₂]
  ring

end TauCeti
