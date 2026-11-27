/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Basic
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.ODE.Complex.RegularSingularPoint

/-!
# Abel–Liouville Wronskian and fundamental pair at a regular singularity

For `w''(z) + f(z) w'(z) + g(z) w(z) = 0` at a regular singularity `z₀` where
`(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and `(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`:
* Using `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`, the weighted Wronskian
  `(z - z₀)^{fs 0} exp(H(z - z₀)) (w₁ w₂' - w₁' w₂)` is constant on
  `{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}` (`TauCeti.cpow_mul_exp_mul_wronskian_eq`).
* Explicit Abel–Liouville formulas (`TauCeti.wronskian_regularSingular_eq`,
  `TauCeti.wronskian_regularSingular_second_eq`), nonvanishing
  (`TauCeti.wronskian_regularSingular_ne_zero`, `TauCeti.wronskian_regularSingular_second_ne_zero`),
  and fundamental pair existence (`TauCeti.exists_regularSingular_fundamental_pair` for
  `TauCeti.regularSingularEquation`).

## References
* NIST DLMF §2.7(ii), 2.7.1–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Finset Metric Set
open scoped Topology

namespace TauCeti

private theorem tsum_ite_zero_div_eq_tsum_succ (fs : ℕ → ℂ) (u : ℂ) :
    (∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s) =
      ∑' s : ℕ, fs (s + 1) / (s + 1) * u ^ (s + 1) := by
  by_cases h : Summable fun s : ℕ => fs (s + 1) / (s + 1) * u ^ (s + 1)
  · have h' : Summable fun s : ℕ => (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s :=
      (summable_nat_add_iff 1).mp (by simpa using h)
    rw [h'.tsum_eq_zero_add]
    simp
  · rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable]
    exact fun hs => h (by simpa using (summable_nat_add_iff 1).mpr hs)

/-- **Abel–Liouville Wronskian constancy at a regular singularity**: for any two holomorphic
solutions `w₁`, `w₂` of `w'' + f w' + g w = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`,
where `(z - z₀) f(z) = ∑ fs s * (z - z₀)^s` on `0 < ‖z - z₀‖ < r`, the weighted Wronskian
`(z - z₀)^{fs 0} exp(H(z - z₀)) (w₁ w₂' - w₁' w₂)` is constant on the slit punctured disc, where
`H(u) = ∑' s, (if s = 0 then 0 else fs s / s) * u ^ s`. -/
theorem cpow_mul_exp_mul_wronskian_eq {z₀ : ℂ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ} {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hw₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hw₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) :
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    let F : ℂ → ℂ := fun z =>
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)
    ∀ z₁ z₂, z₁ ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} →
      z₂ ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} → F z₁ = F z₂ := by
  intro H F z₁ z₂ hz₁ hz₂
  obtain ⟨C, hC⟩ := exists_wronskian_eq_of_regularSingular hf hw₁ hw₂ hsol₁ hsol₂
  have hval : ∀ z ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}, F z = C := by
    intro z ⟨hzs, hzb⟩
    dsimp only [F, H]
    rw [hC z hzs hzb, tsum_ite_zero_div_eq_tsum_succ]
    have hpow : (z - z₀) ^ fs 0 * (z - z₀) ^ (-fs 0) = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero hzs), add_neg_cancel, Complex.cpow_zero]
    have hexp : cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) *
        cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc
      (z - z₀) ^ fs 0 * cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) *
          (C * (z - z₀) ^ (-fs 0) *
            cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)))
        = C * ((z - z₀) ^ fs 0 * (z - z₀) ^ (-fs 0)) *
            (cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) *
              cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1))) := by ring
      _ = C := by rw [hpow, hexp, mul_one, mul_one]
  exact (hval z₁ hz₁).trans (hval z₂ hz₂).symm

/-- **Abel–Liouville Wronskian formula** for two pure-series solutions
`regularSingularSolution fs gs z₀ α₁` and `regularSingularSolution fs gs z₀ α₂` attached to
indicial roots `α₁`, `α₂` satisfying the positive-shift conditions `Q(α₁ + s) ≠ 0` and
`Q(α₂ + s) ≠ 0` for all `s ≥ 1`:
`w₁ z * deriv w₂ z - deriv w₁ z * w₂ z = (α₂ - α₁) * (z - z₀)^{-fs 0} * exp(-H(z - z₀))` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, where `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`. Equal roots
`α₁ = α₂` are allowed (giving Wronskian `0`). -/
theorem wronskian_regularSingular_eq {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSolution fs gs z₀ α₂
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z =
        (α₂ - α₁) * (z - z₀) ^ (-fs 0) * cexp (-H (z - z₀)) := by
  intro w₁ w₂ H z hzs hzb
  have hw := regularSingular_wronskian hf hg
    (fun α => by simpa [indicialPoly_def] using hfact α)
    (fun s hs => by
      simpa [indicialPoly_def] using indicialPoly_mul_regularSingularCoeff hs (hres₁ s hs))
    (fun s hs => by
      simpa [indicialPoly_def] using indicialPoly_mul_regularSingularCoeff hs (hres₂ s hs))
    (regularSingularSolution_eq fs gs z₀ α₁) (regularSingularSolution_eq fs gs z₀ α₂) hzs hzb
  dsimp only [w₁, w₂, H]
  rw [hw, tsum_ite_zero_div_eq_tsum_succ, regularSingularCoeff_zero, regularSingularCoeff_zero]
  ring

/-- For two distinct indicial roots `α₁ ≠ α₂` that are both non-resonant (`Q(αᵢ + s) ≠ 0` for all
`s ≥ 1`), the two canonical series solutions attached to `α₁` and `α₂` have nowhere-vanishing
Wronskian on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_ne_zero {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0)
    (hne : α₁ ≠ α₂) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSolution fs gs z₀ α₂
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  intro w₁ w₂ z hzs hzb
  rw [wronskian_regularSingular_eq hf hg hfact hres₁ hres₂ z hzs hzb]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hne.symm)
    (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.slitPlane_ne_zero hzs)))) (Complex.exp_ne_zero _)

/-- **Abel–Liouville Wronskian formula** in the resonant/logarithmic case `α₁ - α₂ = N ∈ ℕ`:
`w₁ z * deriv w₂ z - deriv w₁ z * w₂ z` equals
`(if N = 0 then 1 else -N) * (z - z₀)^{-fs 0} * exp(-H(z - z₀))` on the slit punctured disc,
where `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`. -/
theorem wronskian_regularSingular_second_eq {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSecondSolution fs gs z₀ α₂ N
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z =
        (if N = 0 then (1 : ℂ) else -(N : ℂ)) * (z - z₀) ^ (-fs 0) * cexp (-H (z - z₀)) := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  intro w₁ w₂ H z hzs hzb
  have hw := regularSingular_log_wronskian
    (a := regularSingularCoeff fs gs (α₂ + N))
    (b := regularSingularSecondCoeff fs gs α₂ N)
    (c := regularSingularLogMultiplier fs gs α₂ N)
    (w₁ := w₁) (w₂ := w₂)
    hf hg (fun α => by simpa [indicialPoly_def] using hfact α) rfl
    (fun s hs => by
      simpa [indicialPoly_def] using
        indicialPoly_mul_regularSingularCoeff hs
          (indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs))
    (fun s hs => by
      have hrec := regularSingularSecondCoeff_rec hfact s
      rw [regularSingularLogForcing_of_lt _ _ _ hs, mul_zero, add_zero] at hrec
      simp only [indicialPoly_def] at hrec
      linear_combination hrec)
    (fun s => by
      have hrec := regularSingularSecondCoeff_rec hfact (s + N)
      rw [regularSingularLogForcing_of_le _ _ _ (Nat.le_add_left N s), Nat.add_sub_cancel] at hrec
      simp only [indicialPoly_def] at hrec
      push_cast at hrec
      rw [Finset.sum_range_succ, Nat.sub_self]
      linear_combination hrec)
    (regularSingularSolution_eq fs gs z₀ (α₂ + N))
    (by
      funext w
      simp only [w₂, regularSingularSecondSolution_apply, regularSingularSolution_apply, mul_assoc])
    hzs hzb
  dsimp only [w₁, w₂, H]
  rw [hw, tsum_ite_zero_div_eq_tsum_succ, regularSingularCoeff_zero]
  rcases eq_or_ne N 0 with rfl | hN0
  · simp [regularSingularLogMultiplier_zero]
  · simp [hN0, zero_pow hN0,
      regularSingularSecondCoeff_zero_of_pos fs gs α₂ (Nat.pos_of_ne_zero hN0)]

/-- When `α₁ - α₂ = N ∈ ℕ`, the primary series solution `w₁` and the second solution `w₂` have
nowhere-vanishing Wronskian on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_second_ne_zero {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSecondSolution fs gs z₀ α₂ N
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  intro w₁ w₂ z hzs hzb
  rw [wronskian_regularSingular_second_eq hf hg hfact hdiff z hzs hzb]
  refine mul_ne_zero (mul_ne_zero ?_
    (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.slitPlane_ne_zero hzs)))) (Complex.exp_ne_zero _)
  split_ifs with hN0
  · exact one_ne_zero
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hN0)

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
    exact ⟨_, _, hw₁, (regularSingular_second_solution hf hg hfact hN).2, fun z hz =>
      let h := mem_regularSingularSlitDisc.mp hz
      wronskian_regularSingular_second_ne_zero hf hg hfact hN z h.1 h.2⟩
  · have hnat' := not_exists.mp hnat
    have hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0 := fun s hs =>
      (indicialPoly_add_nat_ne_zero_iff hfact).mpr ⟨by omega, hnat' s⟩
    exact ⟨_, _, hw₁, (regularSingularCoeff_solution hf hg (by simp [hfact]) hres₂).2, fun z hz =>
      let h := mem_regularSingularSlitDisc.mp hz
      wronskian_regularSingular_ne_zero hf hg hfact hres₁ hres₂
        (fun h0 => hnat' 0 (by simp [h0])) z h.1 h.2⟩

end TauCeti
