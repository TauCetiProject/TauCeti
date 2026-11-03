/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TateGauge.UnitBall
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Unit-ball Tate gauges on the p-adic numbers

For every prime `p`, the gauge of `ℤ_[p]` with unit `p` and base `p` is the p-adic norm.
With unit `p²` and the same base it instead takes values `1` and `p⁻¹` at `p` and `p²`,
respectively, so is not multiplicative. These results distinguish a norm from its discrete
rounding, at every prime including two.
-/

public section

namespace Padic

open TauCeti Huber

private noncomputable def primeUniformizer (p : ℕ) [hp : Fact p.Prime] :
    NormedRing.PseudoUniformizer ℚ_[p] where
  unit := Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero)
  norm_mul := norm_mul _
  norm_pos := by
    simpa only [Units.val_mk0] using
      (norm_pos_iff.mpr (by exact_mod_cast hp.out.ne_zero) : 0 < ‖(p : ℚ_[p])‖)
  norm_lt_one := Padic.norm_p_lt_one

variable {p : ℕ} [hp : Fact p.Prime]

/-- The gauge for the usual prime generator recovers the norm, also at zero. -/
@[simp]
theorem tateGauge_subring_eq_norm (x : ℚ_[p]) :
    tateGauge (PadicInt.subring p) (Units.mk0 (p : ℚ_[p])
      (by exact_mod_cast hp.out.ne_zero)) p x = ‖x‖ := by
  have hball : PadicInt.subring p = Subring.unitClosedBall ℚ_[p] := by
    ext y
    simp [PadicInt.mem_subring_iff]
  have hdiscrete : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖((primeUniformizer p).unit : ℚ_[p])‖ ^ n = ‖x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    · exact Or.inr ⟨x.valuation, by
        simpa [primeUniformizer, Padic.norm_p] using (Padic.norm_eq_zpow_neg_valuation hx).symm⟩
  simpa [primeUniformizer, Padic.norm_p, ← hball] using
    (tateGauge_unitClosedBall_eq_norm_iff (primeUniformizer p) x).2 hdiscrete

/-- With generator `p²` and base `p`, the gauge takes values `1` and `p⁻¹` at `p` and `p²`,
respectively, and is not multiplicative. -/
theorem tateGauge_subring_sq_values_and_not_mul :
    let g := tateGauge (PadicInt.subring p)
      ((Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero)) ^ 2) (p : ℝ)
    g p = 1 ∧ g ((p : ℚ_[p]) ^ 2) = (p : ℝ)⁻¹ ∧
      ¬ ∀ x y : ℚ_[p], g (x * y) = g x * g y := by
  let ϖ := primeUniformizer p
  have hu : ϖ.unit = Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero) := (rfl)
  have hball : PadicInt.subring p = Subring.unitClosedBall ℚ_[p] := by
    ext y
    simp [PadicInt.mem_subring_iff]
  have hc₀ : 0 < ‖(ϖ.unit : ℚ_[p])‖ := ϖ.norm_pos
  have hc₁ : ‖(ϖ.unit : ℚ_[p])‖ < 1 := ϖ.norm_lt_one
  have hround : zpowCeil (‖(ϖ.unit : ℚ_[p])‖ ^ 2) ‖(ϖ.unit : ℚ_[p])‖ = 1 := by
    simpa using (zpowCeil_eq_zpow_iff (pow_pos hc₀ 2)
      (pow_lt_one₀ hc₀.le hc₁ (by omega)) 0).2
        ⟨by simpa [pow_two] using mul_lt_mul_of_pos_left hc₁ hc₀, hc₁.le⟩
  have hp₁ : 1 < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hgp : tateGauge (PadicInt.subring p) (ϖ.unit ^ 2) p p = 1 := by
    have h := tateGauge_unitClosedBall_eq_rpow (ϖ.pow 2 (by omega)) hp₁ (ϖ.unit : ℚ_[p])
    simp only [NormedRing.PseudoUniformizer.pow_unit, Units.val_pow_eq_pow_val, norm_pow,
      hround, Real.one_rpow] at h
    simpa only [← hball, hu, Units.val_mk0] using h
  have hgp₂ : tateGauge (PadicInt.subring p) (ϖ.unit ^ 2) p ((p : ℚ_[p]) ^ 2) =
      (p : ℝ)⁻¹ := by
    have hone : tateGauge (PadicInt.subring p) (ϖ.unit ^ 2) p 1 = 1 := by
      have h := tateGauge_unitClosedBall_eq_rpow (ϖ.pow 2 (by omega)) hp₁ (1 : ℚ_[p])
      rw [norm_one, zpowCeil_one (ϖ.pow 2 (by omega)).norm_pos
        (ϖ.pow 2 (by omega)).norm_lt_one, Real.one_rpow] at h
      simpa only [← hball, NormedRing.PseudoUniformizer.pow_unit] using h
    have h := tateGauge_zpow_mul (A₀ := PadicInt.subring p)
      (ϖ := ϖ.unit ^ 2) (zero_lt_one.trans hp₁) 1 (1 : ℚ_[p])
    rw [hone] at h
    simpa [ϖ, primeUniformizer] using h
  refine ⟨hgp, hgp₂, fun h ↦ ?_⟩
  have hpp := h p p
  rw [← hu, ← pow_two, hgp₂, hgp, one_mul] at hpp
  exact (inv_lt_one_of_one_lt₀ hp₁).ne hpp

end Padic
