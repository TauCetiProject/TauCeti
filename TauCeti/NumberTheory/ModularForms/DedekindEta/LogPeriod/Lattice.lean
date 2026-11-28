/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
public import TauCeti.NumberTheory.ModularForms.DedekindEta.LogPeriod.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Covolume

/-!
# The logarithmic period through the area and the discriminant

If the lattice `Λ` of a period pair is `c (ℤ τ + ℤ)`, the logarithmic period
`log (4 π Im τ |η(τ)|⁴)` of `ℤ τ + ℤ` is `log (A / π) + log |Δ(Λ)| / 6`, where `A` is the covolume
of `Λ` and `Δ(Λ) = g₂³ - 27 g₃²` the discriminant of its Weierstrass curve
(`UpperHalfPlane.logPeriod_eq_of_lattice_eq`).
-/

public section

open scoped Real UpperHalfPlane

namespace UpperHalfPlane

/-- **The logarithmic period through the area and the discriminant.** If the lattice of `L` is
`c (ℤ τ + ℤ)`, then `log (4 π Im τ |η(τ)|⁴) = log (A / π) + log |Δ| / 6`, where `A` is the covolume
of the lattice and `Δ = g₂³ - 27 g₃²` the discriminant of its Weierstrass curve. -/
theorem logPeriod_eq_of_lattice_eq {L : PeriodPair} {c : ℂˣ} {τ : ℍ}
    (h : L.lattice = (c • τ.periodPair).lattice) :
    logPeriod τ = Real.log (ZLattice.covolume L.lattice / π) +
      Real.log ‖L.weierstrassCurve.Δ‖ / 6 := by
  have hc : 0 < ‖(c : ℂ)‖ := norm_pos_iff.2 c.ne_zero
  have hη : 0 < ‖ModularForm.eta (τ : ℂ)‖ := norm_pos_iff.2 (ModularForm.eta_ne_zero τ.im_pos)
  have hA : ZLattice.covolume L.lattice = ‖(c : ℂ)‖ ^ 2 * τ.im := by
    rw [← covolume_lattice_periodPair, ← PeriodPair.covolume_lattice_smul]
    -- The two covolumes are those of the submodules identified by `h`.
    congr 1
  have hΔ : ‖L.weierstrassCurve.Δ‖ = (‖(c : ℂ)‖⁻¹ ^ 2 * (4 * π ^ 2) *
      ‖ModularForm.eta (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [PeriodPair.weierstrassCurve_eq_of_lattice_eq h, PeriodPair.weierstrassCurve_smul,
      WeierstrassCurve.variableChange_Δ, weierstrassCurve_Δ_periodPair,
      ModularForm.discriminant]
    simp only [norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [logPeriod_def, hA, hΔ, Real.log_pow, Nat.cast_ofNat,
    mul_div_cancel_left₀ _ (by norm_num : (6 : ℝ) ≠ 0),
    ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp

end UpperHalfPlane
