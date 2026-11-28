/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Basic

import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs
import TauCeti.Analysis.ODE.Complex.RegularSingularPoint

/-!
# Fundamental pair of solutions at a regular singularity

For `w''(z) + f(z) w'(z) + g(z) w(z) = 0` at a regular singularity `z₀` where
`(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and `(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`,
`TauCeti.exists_regularSingular_fundamental_pair` packages the canonical solutions of
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Basic` and the Abel–Liouville Wronskian
nonvanishing theorems `TauCeti.regularSingular_wronskian_ne_zero` and
`TauCeti.regularSingular_log_wronskian_ne_zero` from
`TauCeti.Analysis.ODE.Complex.RegularSingularPoint` into an unconditional fundamental pair of
`TauCeti.LinearEquation.IsSolution` solutions on `TauCeti.regularSingularSlitDisc z₀ r`.

## References
* NIST DLMF §2.7(ii), 2.7.1–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex

namespace TauCeti

/-- **Existence of a fundamental pair of `LinearEquation` solutions at every regular singularity**:
on `regularSingularSlitDisc z₀ r`, `regularSingularEquation hf hg` always possesses two solutions
with nowhere-vanishing Wronskian. -/
theorem exists_regularSingular_fundamental_pair {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z)) :
    ∃ w₁ w₂ : ℂ → ℂ,
      (regularSingularEquation hf hg).IsSolution w₁ ∧
      (regularSingularEquation hf hg).IsSolution w₂ ∧
      ∀ z ∈ regularSingularSlitDisc z₀ r,
        w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  obtain ⟨α₁, α₂, hre, hfact⟩ := exists_indicialPoly_roots (fs 0) (gs 0)
  have hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0 :=
    fun _ hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs
  have hw₁ := (regularSingularCoeff_solution hf hg (by simp [hfact]) hres₁).2
  by_cases hnat : ∃ N : ℕ, α₁ - α₂ = N
  · obtain ⟨N, hN⟩ := hnat
    have hw₂ := (regularSingular_second_solution hf hg hfact hN).2
    have hα₁ : α₁ = α₂ + N := by linear_combination hN
    subst hα₁
    refine ⟨_, _, hw₁, hw₂, fun z hz => ?_⟩
    obtain ⟨hzs, hzb⟩ := mem_regularSingularSlitDisc.mp hz
    exact regularSingular_log_wronskian_ne_zero
      (a := regularSingularCoeff fs gs (α₂ + N))
      (b := regularSingularSecondCoeff fs gs α₂ N)
      (c := regularSingularLogMultiplier fs gs α₂ N)
      hf hg hfact rfl
      (fun s hs => indicialPoly_mul_regularSingularCoeff hs (hres₁ s hs))
      (fun s hs => by
        have hrec := regularSingularSecondCoeff_rec hfact s
        rw [regularSingularLogForcing_of_lt _ _ _ hs, mul_zero, add_zero] at hrec
        linear_combination hrec)
      (fun s => by
        have hrec := regularSingularSecondCoeff_rec hfact (s + N)
        rw [show α₂ + ((s + N : ℕ) : ℂ) = (α₂ + N) + s by push_cast; ring] at hrec
        linear_combination hrec)
      (by simp) (fun hN0 => by simp [hN0])
      (fun hN0 => by
        simp [regularSingularSecondCoeff_zero_of_pos fs gs α₂ (Nat.pos_of_ne_zero hN0)])
      (regularSingularSolution_eq fs gs z₀ (α₂ + N))
      (by
        funext w
        simp only [regularSingularSecondSolution_apply, regularSingularSolution_apply, mul_assoc])
      hzs hzb
  · have hnat' := not_exists.mp hnat
    have hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0 := fun s hs =>
      (indicialPoly_add_nat_ne_zero_iff hfact).mpr ⟨by omega, hnat' s⟩
    refine ⟨_, _, hw₁, (regularSingularCoeff_solution hf hg (by simp [hfact]) hres₂).2,
      fun z hz => ?_⟩
    obtain ⟨hzs, hzb⟩ := mem_regularSingularSlitDisc.mp hz
    exact regularSingular_wronskian_ne_zero hf hg hfact (fun h0 => hnat' 0 (by simp [h0]))
      (fun s hs => indicialPoly_mul_regularSingularCoeff hs (hres₁ s hs))
      (fun s hs => indicialPoly_mul_regularSingularCoeff hs (hres₂ s hs))
      (by simp) (by simp)
      (regularSingularSolution_eq fs gs z₀ α₁)
      (regularSingularSolution_eq fs gs z₀ α₂)
      hzs hzb

end TauCeti
