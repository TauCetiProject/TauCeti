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
# Wronskians and fundamental pairs of solutions at a regular singularity

For `w''(z) + f(z) w'(z) + g(z) w(z) = 0` at a regular singularity `z₀` where
`(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and `(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`:
* `TauCeti.wronskian_regularSingular_eq` and `TauCeti.wronskian_regularSingular_ne_zero`:
  Abel–Liouville Wronskian formula and nonvanishing for the canonical non-resonant Frobenius pair
  `TauCeti.regularSingularSolution`.
* `TauCeti.wronskian_regularSingular_second_eq` and
  `TauCeti.wronskian_regularSingular_second_ne_zero`: Abel–Liouville Wronskian formula and
  nonvanishing for `TauCeti.regularSingularSolution` and `TauCeti.regularSingularSecondSolution`
  when `α₁ - α₂ = N ∈ ℕ`.
* `TauCeti.exists_regularSingular_fundamental_pair`: unconditional fundamental pair of
  `TauCeti.LinearEquation.IsSolution` solutions on `TauCeti.regularSingularSlitDisc z₀ r`.
* `TauCeti.eulerCauchy_two_neg_one_example`: worked Euler–Cauchy example `w'' - 2 z⁻² w = 0`
  computing the indicial roots `2` and `-1`, canonical coefficients, zero log multiplier,
  solutions `z²` and `z⁻¹`, and constant Wronskian `-3`.

## References
* NIST DLMF §2.7(ii), 2.7.1–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Finset

namespace TauCeti

/-- **Abel–Liouville Wronskian formula** for two canonical Frobenius solutions
`regularSingularSolution fs gs z₀ α₁` and `regularSingularSolution fs gs z₀ α₂` attached to
indicial roots `α₁`, `α₂` satisfying the non-resonance conditions `Q(α₁ + s) ≠ 0` and
`Q(α₂ + s) ≠ 0` for all `s ≥ 1`: on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`,
`w₁ z * deriv w₂ z - deriv w₁ z * w₂ z` equals
`(α₂ - α₁) * (z - z₀)^{-fs 0} * cexp (-∑' s, fs (s + 1) / (s + 1) * (z - z₀)^{s + 1})`. -/
theorem wronskian_regularSingular_eq {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    regularSingularSolution fs gs z₀ α₁ z * deriv (regularSingularSolution fs gs z₀ α₂) z -
        deriv (regularSingularSolution fs gs z₀ α₁) z * regularSingularSolution fs gs z₀ α₂ z =
      (α₂ - α₁) * (z - z₀) ^ (-fs 0) *
        cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  have hw := regularSingular_wronskian hf hg hfact
    (fun s hs => indicialPoly_mul_regularSingularCoeff hs (hres₁ s hs))
    (fun s hs => indicialPoly_mul_regularSingularCoeff hs (hres₂ s hs))
    (regularSingularSolution_eq fs gs z₀ α₁) (regularSingularSolution_eq fs gs z₀ α₂) hzs hzb
  simpa using hw

/-- For two distinct non-resonant indicial roots `α₁ ≠ α₂` (`Q(αᵢ + s) ≠ 0` for all `s ≥ 1`), the
canonical Frobenius solutions `regularSingularSolution fs gs z₀ α₁` and
`regularSingularSolution fs gs z₀ α₂` have nowhere-vanishing Wronskian on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_ne_zero {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0)
    (hne : α₁ ≠ α₂) {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    regularSingularSolution fs gs z₀ α₁ z * deriv (regularSingularSolution fs gs z₀ α₂) z -
        deriv (regularSingularSolution fs gs z₀ α₁) z * regularSingularSolution fs gs z₀ α₂ z ≠
      0 := by
  rw [wronskian_regularSingular_eq hf hg hfact hres₁ hres₂ hzs hzb]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hne.symm)
    (cpow_ne_zero_iff.mpr (.inl (slitPlane_ne_zero hzs)))) (Complex.exp_ne_zero _)

/-- **Abel–Liouville Wronskian formula** in the resonant/logarithmic case `α₁ - α₂ = N ∈ ℕ`:
for `w₁ = regularSingularSolution fs gs z₀ α₁` and
`w₂ = regularSingularSecondSolution fs gs z₀ α₂ N`, `w₁ z * deriv w₂ z - deriv w₁ z * w₂ z` equals
`(if N = 0 then 1 else -(N : ℂ)) * (z - z₀)^{-fs 0} *`
`cexp (-∑' s, fs (s + 1) / (s + 1) * (z - z₀)^{s + 1})` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_second_eq {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    regularSingularSolution fs gs z₀ α₁ z *
          deriv (regularSingularSecondSolution fs gs z₀ α₂ N) z -
        deriv (regularSingularSolution fs gs z₀ α₁) z *
          regularSingularSecondSolution fs gs z₀ α₂ N z =
      (if N = 0 then (1 : ℂ) else -(N : ℂ)) * (z - z₀) ^ (-fs 0) *
        cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨hb, hc⟩ := (forall_regularSingularLogForcing_rec_iff rfl).mp
    (regularSingularSecondCoeff_rec hfact)
  have hw := regularSingular_log_wronskian
    (a := regularSingularCoeff fs gs (α₂ + N))
    (b := regularSingularSecondCoeff fs gs α₂ N)
    (c := regularSingularLogMultiplier fs gs α₂ N)
    (w₁ := regularSingularSolution fs gs z₀ (α₂ + N))
    (w₂ := regularSingularSecondSolution fs gs z₀ α₂ N)
    hf hg hfact rfl
    (fun s hs => indicialPoly_mul_regularSingularCoeff hs
      (indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs))
    hb hc
    (regularSingularSolution_eq fs gs z₀ (α₂ + N))
    (by
      funext w
      simp only [regularSingularSecondSolution_apply, regularSingularSolution_apply, mul_assoc])
    hzs hzb
  rw [hw, regularSingularCoeff_zero]
  rcases eq_or_ne N 0 with rfl | hN0
  · simp [regularSingularLogMultiplier_zero]
  · simp [hN0, zero_pow hN0,
      regularSingularSecondCoeff_zero_of_pos fs gs α₂ (Nat.pos_of_ne_zero hN0)]

/-- When `α₁ - α₂ = N ∈ ℕ`, the canonical primary solution `regularSingularSolution fs gs z₀ α₁`
and second solution `regularSingularSecondSolution fs gs z₀ α₂ N` have nowhere-vanishing Wronskian
on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_second_ne_zero {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    regularSingularSolution fs gs z₀ α₁ z *
          deriv (regularSingularSecondSolution fs gs z₀ α₂ N) z -
        deriv (regularSingularSolution fs gs z₀ α₁) z *
          regularSingularSecondSolution fs gs z₀ α₂ N z ≠
      0 := by
  rw [wronskian_regularSingular_second_eq hf hg hfact hdiff hzs hzb]
  refine mul_ne_zero (mul_ne_zero ?_ (cpow_ne_zero_iff.mpr (.inl (slitPlane_ne_zero hzs))))
    (Complex.exp_ne_zero _)
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
    refine ⟨_, _, hw₁, (regularSingular_second_solution hf hg hfact hN).2, fun z hz => ?_⟩
    obtain ⟨hzs, hzb⟩ := mem_regularSingularSlitDisc.mp hz
    exact wronskian_regularSingular_second_ne_zero hf hg hfact hN hzs hzb
  · have hnat' := not_exists.mp hnat
    have hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0 := fun s hs =>
      (indicialPoly_add_nat_ne_zero_iff hfact).mpr ⟨by omega, hnat' s⟩
    refine ⟨_, _, hw₁, (regularSingularCoeff_solution hf hg (by simp [hfact]) hres₂).2,
      fun z hz => ?_⟩
    obtain ⟨hzs, hzb⟩ := mem_regularSingularSlitDisc.mp hz
    exact wronskian_regularSingular_ne_zero hf hg hfact hres₁ hres₂
      (fun h0 => hnat' 0 (by simp [h0])) hzs hzb

/-- **Worked Euler–Cauchy example**: for `w'' - 2 z⁻² w = 0` at `z₀ = 0` (`fs = 0`,
`gs = Pi.single 0 (-2)`), the indicial polynomial factors as `(α - 2)(α + 1)` (`α₁ = 2`,
`α₂ = -1`, `N = 3`), all higher series coefficients vanish, the logarithmic multiplier is `0`,
the canonical solutions simplify to `z²` and `z⁻¹`, both solve the ODE on `Complex.slitPlane`, and
their Wronskian equals `-3`. -/
theorem eulerCauchy_two_neg_one_example :
    (∀ α : ℂ, indicialPoly ((0 : ℕ → ℂ) 0) ((Pi.single 0 (-2 : ℂ) : ℕ → ℂ) 0) α =
        (α - 2) * (α - (-1))) ∧
      (∀ s : ℕ, 1 ≤ s → regularSingularCoeff 0 (Pi.single 0 (-2 : ℂ)) 2 s = 0) ∧
      regularSingularLogMultiplier 0 (Pi.single 0 (-2 : ℂ)) (-1) 3 = 0 ∧
      (∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff 0 (Pi.single 0 (-2 : ℂ)) (-1) 3 s = 0) ∧
      regularSingularSolution 0 (Pi.single 0 (-2 : ℂ)) 0 2 = (fun z : ℂ => z ^ 2) ∧
      regularSingularSecondSolution 0 (Pi.single 0 (-2 : ℂ)) 0 (-1) 3 = (fun z : ℂ => z⁻¹) ∧
      (∀ z ∈ slitPlane,
        deriv (deriv fun w : ℂ => w ^ 2) z + 0 * deriv (fun w : ℂ => w ^ 2) z +
          (-2 / z ^ 2) * z ^ 2 = 0) ∧
      (∀ z ∈ slitPlane,
        deriv (deriv fun w : ℂ => w⁻¹) z + 0 * deriv (fun w : ℂ => w⁻¹) z +
          (-2 / z ^ 2) * z⁻¹ = 0) ∧
      ∀ z ∈ slitPlane,
        z ^ 2 * deriv (fun w : ℂ => w⁻¹) z - deriv (fun w : ℂ => w ^ 2) z * z⁻¹ = -3 := by
  have hfact : ∀ α : ℂ,
      indicialPoly ((0 : ℕ → ℂ) 0) ((Pi.single 0 (-2 : ℂ) : ℕ → ℂ) 0) α = (α - 2) * (α - (-1)) :=
    fun α => by simp only [indicialPoly_def, Pi.zero_apply, Pi.single_eq_same]; ring
  have hconv0 (σ : ℂ) (d : ℕ → ℂ) (m : ℕ) :
      (∑ k ∈ range m, ((σ + (k : ℂ)) * (0 : ℕ → ℂ) (m - k) +
        (Pi.single 0 (-2 : ℂ) : ℕ → ℂ) (m - k)) * d k) = 0 :=
    sum_eq_zero fun k hk => by
      have hmk : m - k ≠ 0 := by have := mem_range.mp hk; omega
      simp [Pi.single_eq_of_ne hmk]
  have ha_zero : ∀ s : ℕ, 1 ≤ s → regularSingularCoeff 0 (Pi.single 0 (-2 : ℂ)) 2 s = 0 :=
    fun s hs => by
      rw [regularSingularCoeff_of_ne_zero _ _ 2 (by omega), hconv0, mul_zero]
  have hbc := eq_regularSingularSecondCoeff_of_rec
    (fs := (0 : ℕ → ℂ)) (gs := Pi.single 0 (-2 : ℂ))
    (b' := fun s => if s = 0 then (1 : ℂ) else 0) (α₂ := -1) (c' := 0) (N := 3)
    (fun α => by rw [hfact]; ring)
    (by simp) (by simp) (fun _ => rfl) fun s => by
      rcases eq_or_ne s 0 with rfl | hs0
      · norm_num [indicialPoly_def]
      · simp only [hs0, ↓reduceIte, mul_zero, zero_add, zero_mul, add_zero]
        exact hconv0 (-1) _ s
  have hc_zero : regularSingularLogMultiplier 0 (Pi.single 0 (-2 : ℂ)) (-1) 3 = 0 := hbc.2.symm
  have hb_zero :
      ∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff 0 (Pi.single 0 (-2 : ℂ)) (-1) 3 s = 0 :=
    fun s hs => by rw [← hbc.1]; simp [show s ≠ 0 by omega]
  have hw₁ : regularSingularSolution 0 (Pi.single 0 (-2 : ℂ)) 0 2 = fun z : ℂ => z ^ 2 := by
    funext z
    rw [regularSingularSolution_apply, sub_zero,
      tsum_eq_single 0 fun s hs => by simp [ha_zero s (Nat.pos_of_ne_zero hs)],
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
    simp
  have hw₂ : regularSingularSecondSolution 0 (Pi.single 0 (-2 : ℂ)) 0 (-1) 3 =
      fun z : ℂ => z⁻¹ := by
    funext z
    rw [regularSingularSecondSolution_apply, sub_zero, hc_zero, zero_mul, zero_mul, add_zero,
      tsum_eq_single 0 fun s hs => by simp [hb_zero s (Nat.pos_of_ne_zero hs)]]
    simp [cpow_neg_one]
  have hode (r : ℝ) :
      (∀ y, 0 < ‖y - (0 : ℂ)‖ → ‖y - 0‖ < r →
        HasSum (fun s => (0 : ℕ → ℂ) s * (y - 0) ^ s) ((y - 0) * (0 : ℂ → ℂ) y)) ∧
      (∀ y, 0 < ‖y - (0 : ℂ)‖ → ‖y - 0‖ < r →
        HasSum (fun s => (Pi.single 0 (-2 : ℂ) : ℕ → ℂ) s * (y - 0) ^ s)
          ((y - 0) ^ 2 * (-2 / y ^ 2))) := by
    refine ⟨fun y _ _ => by simp [hasSum_zero], fun y hy _ => ?_⟩
    have hy0 : y ≠ 0 := by simpa using hy
    have hsing : HasSum (fun s : ℕ => (Pi.single 0 (-2 : ℂ) : ℕ → ℂ) s * (y - 0) ^ s) (-2) := by
      convert hasSum_single (0 : ℕ)
        (f := fun s : ℕ => (Pi.single 0 (-2 : ℂ) : ℕ → ℂ) s * (y - 0) ^ s)
        (fun s hs => by simp [Pi.single_eq_of_ne hs]) using 1
      simp
    convert hsing using 1
    simp only [sub_zero]
    field_simp [hy0]
  refine ⟨hfact, ha_zero, hc_zero, hb_zero, hw₁, hw₂,
    fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨hf, hg⟩ := hode (‖z‖ + 1)
    have hsol := (isSolution_regularSingularEquation_iff hf hg _).mp
      (regularSingularCoeff_solution hf hg (by norm_num [indicialPoly_def])
        (fun _ hs => indicialPoly_add_nat_ne_zero_of_re_le (α₁ := 2) (α₂ := -1)
          hfact (by norm_num) hs)).2
    simpa only [hw₁, Pi.zero_apply] using
      hsol.2 z (mem_regularSingularSlitDisc.mpr ⟨by simpa using hz, by simp⟩)
  · obtain ⟨hf, hg⟩ := hode (‖z‖ + 1)
    have hsol := (isSolution_regularSingularEquation_iff hf hg _).mp
      (regularSingular_second_solution hf hg hfact (by norm_num : (2 : ℂ) - (-1) = (3 : ℕ))).2
    simpa only [hw₂, Pi.zero_apply] using
      hsol.2 z (mem_regularSingularSlitDisc.mpr ⟨by simpa using hz, by simp⟩)
  · obtain ⟨hf, hg⟩ := hode (‖z‖ + 1)
    have hW := wronskian_regularSingular_second_eq hf hg hfact
      (by norm_num : (2 : ℂ) - (-1) = (3 : ℕ)) (by simpa using hz) (by simp)
    rw [hw₁, hw₂] at hW
    norm_num at hW
    simpa using hW

end TauCeti
