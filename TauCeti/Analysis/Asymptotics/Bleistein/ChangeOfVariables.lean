/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Bleistein.Coordinate
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Bleistein's integral change of variables

Given the canonical coordinate `TauCeti.bleisteinCoord` from
`TauCeti.Analysis.Asymptotics.Bleistein.Coordinate`, this file defines the transformed amplitude
`TauCeti.bleisteinAmplitude` (DLMF 2.3.30) and proves Bleistein's change-of-variables formula
(DLMF 2.3.29) for Laplace-type integrals
`∫ t in (0, k), (exp (-x * p t) * t ^ (lam - 1)) • q t`
with an interior critical point `t = α` coalescing with the algebraic endpoint `t = 0`.

At `w = 0` (`t = 0`), the factor `t / w` in `((t / w) ^ (lam - 1) * dt/dw) • q t` has a removable
singularity resolved by its limit `(deriv (bleisteinCoord p α) 0)⁻¹ > 0`. With this extension,
`bleisteinAmplitude` is continuous across both `w = 0` and `w = bleisteinOffset p α` (even when
`α ≤ 0` or `α = 0`), is nonzero at `w = bleisteinOffset p α` whenever `q α ≠ 0`, and transforms the
original integral on `(0, k)` or `(0, ∞)` into
`exp (-x * p 0) • ∫ w in (0, κ), (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w`
with equivalence of `IntegrableOn` (absolute convergence).

## Main definitions

* `TauCeti.bleisteinAmplitude`: the transformed amplitude `f(α, w)` of DLMF 2.3.30.

## Main results

* `TauCeti.continuousOn_bleisteinAmplitude`: continuity of `bleisteinAmplitude` across both `w = 0`
  and `w = bleisteinOffset p α`.
* `TauCeti.bleisteinAmplitude_bleisteinOffset_ne_zero`: nonvanishing at `w = bleisteinOffset p α`
  when `q α ≠ 0`.
* `TauCeti.integrableOn_bleisteinAmplitude_iff`,
  `TauCeti.integrableOn_bleisteinAmplitude_Ioo_iff_Ioi`,
  `TauCeti.integrableOn_bleisteinAmplitude_Ioi_iff_Ioi`: equivalence of absolute convergence.
* `TauCeti.integral_bleisteinCoord_eq`, `TauCeti.integral_bleisteinCoord_Ioo_eq_Ioo`,
  `TauCeti.integral_bleisteinCoord_Ioo_eq_Ioi`, `TauCeti.integral_bleisteinCoord_Ioi_eq_Ioo`,
  `TauCeti.integral_bleisteinCoord_Ioi_eq_Ioi`: Bleistein's integral change of variables
  (DLMF 2.3.29) for finite and infinite upper limits.

## References

* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. **19** (1966), 353–370.
* NIST Digital Library of Mathematical Functions, §2.3(v), <https://dlmf.nist.gov/2.3.v>.
-/

public section

open Filter Set MeasureTheory Function
open scoped ContDiff Topology

namespace TauCeti

/-! ### Transformed amplitude `bleisteinAmplitude` (DLMF 2.3.30) -/

/-- The transformed amplitude `f(α, w) = ((t / w) ^ (lam - 1) * dt/dw) • q t` of DLMF 2.3.30,
where `t = Set.invFunOn (bleisteinCoord p α) s w`. At `w = 0`, the removable singularity of
`t / w` is resolved by its limit `(deriv (bleisteinCoord p α) 0)⁻¹`, making `bleisteinAmplitude`
continuous across both `w = 0` and `w = a(α)`. -/
noncomputable def bleisteinAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) : E :=
  let t := invFunOn (bleisteinCoord p α) s w
  ((if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹ else t / w) ^ (lam - 1) /
      deriv (bleisteinCoord p α) t) •
    q t

section Amplitude
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unfolding identity for `bleisteinAmplitude`. -/
theorem bleisteinAmplitude_def (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p q lam α s w =
      (((if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
          else invFunOn (bleisteinCoord p α) s w / w) ^ (lam - 1)) /
        deriv (bleisteinCoord p α) (invFunOn (bleisteinCoord p α) s w)) •
      q (invFunOn (bleisteinCoord p α) s w) :=
  (rfl)

/-- For `w ≠ 0` (in particular on `(0, ∞)`), `bleisteinAmplitude` simplifies directly to
`((t / w) ^ (lam - 1) / deriv (bleisteinCoord p α) t) • q t`. -/
theorem bleisteinAmplitude_of_ne_zero (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ)
    {w : ℝ} (hw : w ≠ 0) :
    bleisteinAmplitude p q lam α s w =
      (((invFunOn (bleisteinCoord p α) s w / w) ^ (lam - 1)) /
        deriv (bleisteinCoord p α) (invFunOn (bleisteinCoord p α) s w)) •
      q (invFunOn (bleisteinCoord p α) s w) := by
  simp [bleisteinAmplitude, hw]

/-- `bleisteinAmplitude` does not depend on the ambient inversion domain once it contains the
preimage set: if `s₁ ⊆ s₂` and `bleisteinCoord p α` is injective on `s₂`, the two amplitudes
coincide on `bleisteinCoord p α '' s₁`. -/
theorem bleisteinAmplitude_congr_set {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s₁ s₂ : Set ℝ}
    (hsub : s₁ ⊆ s₂) (hinj : InjOn (bleisteinCoord p α) s₂)
    {w : ℝ} (hw : w ∈ bleisteinCoord p α '' s₁) :
    bleisteinAmplitude p q lam α s₁ w = bleisteinAmplitude p q lam α s₂ w := by
  rcases hw with ⟨t, ht₁, rfl⟩
  have h₁ : invFunOn (bleisteinCoord p α) s₁ (bleisteinCoord p α t) = t :=
    (hinj.mono hsub).leftInvOn_invFunOn ht₁
  have h₂ : invFunOn (bleisteinCoord p α) s₂ (bleisteinCoord p α t) = t :=
    hinj.leftInvOn_invFunOn (hsub ht₁)
  simp only [bleisteinAmplitude_def, h₁, h₂]

/-- Evaluation of `bleisteinAmplitude` at `w = bleisteinCoord p α t` when `w ≠ 0`. -/
theorem bleisteinAmplitude_bleisteinCoord {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinCoord p α) s) {t : ℝ} (ht : t ∈ s)
    (hw : bleisteinCoord p α t ≠ 0) :
    bleisteinAmplitude p q lam α s (bleisteinCoord p α t) =
      (((t / bleisteinCoord p α t) ^ (lam - 1)) / deriv (bleisteinCoord p α) t) • q t := by
  rw [bleisteinAmplitude_of_ne_zero p q lam α s hw, hinj.leftInvOn_invFunOn ht]

/-- Explicit formula of DLMF 2.3.30 away from `t = α` and `w = 0`:
`f(α, w) = ((t / w) ^ (lam - 1) * (w - a) / deriv p t) • q t`. -/
theorem bleisteinAmplitude_bleisteinCoord_of_ne {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ}
    {s : Set ℝ} (hinj : InjOn (bleisteinCoord p α) s) {t : ℝ} (ht : t ∈ s) (htα : t ≠ α)
    (hw : bleisteinCoord p α t ≠ 0) (hpt : p α < p t) (hp : DifferentiableAt ℝ p t) :
    bleisteinAmplitude p q lam α s (bleisteinCoord p α t) =
      ((t / bleisteinCoord p α t) ^ (lam - 1) *
        (bleisteinCoord p α t - bleisteinOffset p α) / deriv p t) • q t := by
  rw [bleisteinAmplitude_bleisteinCoord hinj ht hw, deriv_bleisteinCoord_of_ne htα hpt hp,
    div_div_eq_mul_div]

/-- Positivity of the desingularized ratio `w ↦ if w = 0 then (w' 0)⁻¹ else t(w) / w` throughout
`bleisteinCoord p α '' U`. -/
private lemma bleisteinRatio_pos {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (h0 : 0 ∈ U) (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t)
    {w : ℝ} (hw_mem : w ∈ bleisteinCoord p α '' U) :
    0 < (if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
      else invFunOn (bleisteinCoord p α) U w / w) := by
  rcases hw_mem with ⟨t, ht, rfl⟩
  by_cases hw0 : bleisteinCoord p α t = 0
  · simp [hw0, inv_pos, hw' 0 h0]
  · simp only [hw0, ↓reduceIte, hmono.injOn.leftInvOn_invFunOn ht]
    have ht0 : t ≠ 0 := by rintro rfl; exact hw0 (bleisteinCoord_zero p α)
    rcases ht0.lt_or_gt with hlt | hgt
    · exact div_pos_of_neg_of_neg hlt (bleisteinCoord_neg hmono h0 ht hlt)
    · exact div_pos hgt (bleisteinCoord_pos hmono h0 ht hgt)

/-- Continuity of the desingularized ratio `w ↦ if w = 0 then (w' 0)⁻¹ else t(w) / w` across
`w = 0` on `bleisteinCoord p α '' U`. -/
private lemma continuousOn_bleisteinRatio {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t) :
    ContinuousOn
      (fun w ↦ if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
        else invFunOn (bleisteinCoord p α) U w / w)
      (bleisteinCoord p α '' U) := by
  have hinj : InjOn (bleisteinCoord p α) U := hmono.injOn
  have hw'_ne : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0 := fun t ht ↦ (hw' t ht).ne'
  have hopen_img : IsOpen (bleisteinCoord p α '' U) := isOpen_image_bleisteinCoord hU hw hw'_ne
  intro w hw_mem
  by_cases hw0 : w = 0
  · subst hw0
    have hd0 : HasStrictDerivAt (invFunOn (bleisteinCoord p α) U)
        (deriv (bleisteinCoord p α) 0)⁻¹ 0 := by
      simpa [bleisteinCoord_zero] using
        hasStrictDerivAt_invFunOn_bleisteinCoord hU hw hinj hw'_ne h0
    have hinv0 : invFunOn (bleisteinCoord p α) U 0 = 0 := by
      simpa [bleisteinCoord_zero] using hinj.leftInvOn_invFunOn h0
    have hlim : Tendsto
        (fun w ↦ if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
          else invFunOn (bleisteinCoord p α) U w / w)
        (𝓝[≠] 0) (𝓝 (deriv (bleisteinCoord p α) 0)⁻¹) := by
      refine (hasDerivAt_iff_tendsto_slope.mp hd0.hasDerivAt).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
      simp [slope_def_field, hinv0, hu]
    exact (continuousAt_iff_punctured_nhds.mpr (by simpa using hlim)).continuousWithinAt
  · have hmem_ne : (bleisteinCoord p α '' U) \ {0} ∈ 𝓝 w :=
      (hopen_img.sdiff isClosed_singleton).mem_nhds ⟨hw_mem, hw0⟩
    have hcont_inv : ContinuousAt (invFunOn (bleisteinCoord p α) U) w :=
      (continuousOn_invFunOn_bleisteinCoord hU hw hinj hw'_ne).continuousAt
        (hopen_img.mem_nhds hw_mem)
    have hquot : ContinuousAt (fun u ↦ invFunOn (bleisteinCoord p α) U u / u) w :=
      hcont_inv.div continuousAt_id hw0
    refine (hquot.congr ?_).continuousWithinAt
    filter_upwards [hmem_ne] with u hu
    simp [mem_singleton_iff.not.mp hu.2]

/-- Continuity of `bleisteinAmplitude p q lam α U` across the entire image `bleisteinCoord p α '' U`
(including both `w = 0` and `w = a(α)`). -/
theorem continuousOn_bleisteinAmplitude {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t)
    (hq : ContinuousOn q U) :
    ContinuousOn (bleisteinAmplitude p q lam α U) (bleisteinCoord p α '' U) := by
  have hratio_cont := continuousOn_bleisteinRatio hU h0 hw hmono hw'
  have hinj : InjOn (bleisteinCoord p α) U := hmono.injOn
  have hw'_ne : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0 := fun t ht ↦ (hw' t ht).ne'
  have hmaps : MapsTo (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' U) U := by
    rintro _ ⟨t, ht, rfl⟩; rwa [hinj.leftInvOn_invFunOn ht]
  have hinv_cont : ContinuousOn (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' U) :=
    continuousOn_invFunOn_bleisteinCoord hU hw hinj hw'_ne
  have hrpow : ContinuousOn
      (fun w ↦ (if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
        else invFunOn (bleisteinCoord p α) U w / w) ^ (lam - 1))
      (bleisteinCoord p α '' U) :=
    hratio_cont.rpow_const fun _ hw_mem ↦ Or.inl (bleisteinRatio_pos h0 hmono hw' hw_mem).ne'
  have hscalar : ContinuousOn
      (fun w ↦ ((if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
          else invFunOn (bleisteinCoord p α) U w / w) ^ (lam - 1)) /
        deriv (bleisteinCoord p α) (invFunOn (bleisteinCoord p α) U w))
      (bleisteinCoord p α '' U) :=
    hrpow.div ((hw.continuousOn_deriv_of_isOpen hU le_rfl).comp hinv_cont hmaps)
      fun _ hw_mem ↦ hw'_ne _ (hmaps hw_mem)
  exact hscalar.smul (hq.comp hinv_cont hmaps)

/-- Nonvanishing of `bleisteinAmplitude` at the critical value `w = bleisteinOffset p α` whenever
`q α ≠ 0` (covering `α < 0`, `α = 0`, and `α > 0`). -/
theorem bleisteinAmplitude_bleisteinOffset_ne_zero {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ}
    {U : Set ℝ} (h0 : 0 ∈ U) (hα : α ∈ U) (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t) (hqα : q α ≠ 0) :
    bleisteinAmplitude p q lam α U (bleisteinOffset p α) ≠ 0 := by
  have hpos := bleisteinRatio_pos h0 hmono hw' ⟨α, hα, bleisteinCoord_self p α⟩
  have hinv : invFunOn (bleisteinCoord p α) U (bleisteinOffset p α) = α := by
    simpa [bleisteinCoord_self] using hmono.injOn.leftInvOn_invFunOn hα
  rw [bleisteinAmplitude_def, hinv]
  have hpos' : 0 < (if bleisteinOffset p α = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
      else α / bleisteinOffset p α) := by simpa [hinv] using hpos
  exact smul_ne_zero (div_pos (Real.rpow_pos_of_pos hpos' _) (hw' α hα)).ne' hqα

/-! ### Integral change of variables (DLMF 2.3.29) -/

/-- Pointwise Jacobian cancellation on `U ∩ (0, ∞)`: pulling back the normal-form integrand
`exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) • bleisteinAmplitude p q lam α U w` with the
Jacobian factor `|deriv (bleisteinCoord p α) t|` recovers
`exp (-x * (p t - p 0)) * t ^ (lam - 1) • q t`. -/
private lemma abs_deriv_bleisteinCoord_smul_eq {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U : Set ℝ}
    (h0 : 0 ∈ U) (hp0 : p α ≤ p 0) (hpmin : ∀ t ∈ U, p α ≤ p t)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t)
    {t : ℝ} (htU : t ∈ U) (ht0 : 0 < t) :
    |deriv (bleisteinCoord p α) t| •
      ((Real.exp (-x * (bleisteinCoord p α t ^ 2 / 2 -
            bleisteinOffset p α * bleisteinCoord p α t)) *
          bleisteinCoord p α t ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U (bleisteinCoord p α t)) =
      (Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t := by
  have hwt_pos : 0 < bleisteinCoord p α t := bleisteinCoord_pos hmono h0 htU ht0
  have hdw_pos : 0 < deriv (bleisteinCoord p α) t := hw' t htU
  rw [bleisteinAmplitude_bleisteinCoord hmono.injOn htU hwt_pos.ne',
    half_sq_bleisteinCoord_sub_mul hp0 (hpmin t htU), abs_of_pos hdw_pos, smul_smul, smul_smul]
  congr 1
  have hrpow : bleisteinCoord p α t ^ (lam - 1) * (t / bleisteinCoord p α t) ^ (lam - 1) =
      t ^ (lam - 1) := by
    rw [← Real.mul_rpow hwt_pos.le (div_pos ht0 hwt_pos).le, mul_div_cancel₀ _ hwt_pos.ne']
  calc
    deriv (bleisteinCoord p α) t *
        (Real.exp (-x * (p t - p 0)) * bleisteinCoord p α t ^ (lam - 1)) *
        ((t / bleisteinCoord p α t) ^ (lam - 1) / deriv (bleisteinCoord p α) t)
      = Real.exp (-x * (p t - p 0)) *
          (bleisteinCoord p α t ^ (lam - 1) * (t / bleisteinCoord p α t) ^ (lam - 1)) *
          (deriv (bleisteinCoord p α) t / deriv (bleisteinCoord p α) t) := by ring
    _ = Real.exp (-x * (p t - p 0)) * t ^ (lam - 1) := by
        rw [hrpow, div_self hdw_pos.ne', mul_one]

/-- Equivalence of absolute convergence (`IntegrableOn`) between the original integral on a
measurable set `s ⊆ U ∩ (0, ∞)` and the transformed Bleistein integral on `bleisteinCoord p α '' s`
(DLMF 2.3.29). -/
theorem integrableOn_bleisteinAmplitude_iff {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U s : Set ℝ}
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (hU : IsOpen U) (h0 : 0 ∈ U) (hp0 : p α ≤ p 0) (hpmin : ∀ t ∈ U, p α ≤ p t)
    (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (bleisteinCoord p α '' s) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  have hd : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord p α) (deriv (bleisteinCoord p α) t) s t :=
    fun t ht ↦ ((hw.contDiffAt (hU.mem_nhds (hsU ht))).differentiableAt one_ne_zero).hasDerivAt
      |>.hasDerivWithinAt
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd (hmono.injOn.mono hsU)]
  have hcongr : IntegrableOn
      (fun t ↦ |deriv (bleisteinCoord p α) t| •
        ((Real.exp (-x * (bleisteinCoord p α t ^ 2 / 2 -
              bleisteinOffset p α * bleisteinCoord p α t)) *
            bleisteinCoord p α t ^ (lam - 1)) •
          bleisteinAmplitude p q lam α U (bleisteinCoord p α t))) s ↔
      IntegrableOn (fun t ↦ (Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t) s :=
    integrableOn_congr_fun
      (fun t ht ↦ abs_deriv_bleisteinCoord_smul_eq h0 hp0 hpmin hmono hw' (hsU ht) (hs0 t ht)) hs
  rw [hcongr]
  have hscale : (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      fun t ↦ Real.exp (-x * p 0) • ((Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t) := by
    ext t
    rw [smul_smul, ← mul_assoc, ← Real.exp_add]
    exact congrArg (fun r ↦ (Real.exp r * t ^ (lam - 1)) • q t) (by ring)
  rw [hscale]
  exact (integrable_smul_iff (Real.exp_ne_zero (-x * p 0)) _).symm

/-- General measurable-set form of Bleistein's change of variables (DLMF 2.3.29): for any
measurable `s ⊆ U ∩ (0, ∞)`,
`∫ t in s, (exp (-x * p t) * t ^ (lam - 1)) • q t` equals
`exp (-x * p 0) • ∫ w in bleisteinCoord p α '' s,
  (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w`. -/
theorem integral_bleisteinCoord_eq {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U s : Set ℝ}
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (hU : IsOpen U) (h0 : 0 ∈ U) (hp0 : p α ≤ p 0) (hpmin : ∀ t ∈ U, p α ≤ p t)
    (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t) :
    (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in bleisteinCoord p α '' s,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hd : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord p α) (deriv (bleisteinCoord p α) t) s t :=
    fun t ht ↦ ((hw.contDiffAt (hU.mem_nhds (hsU ht))).differentiableAt one_ne_zero).hasDerivAt
      |>.hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul hs hd (hmono.injOn.mono hsU)]
  have hcongr :
      (∫ t in s, |deriv (bleisteinCoord p α) t| •
        ((Real.exp (-x * (bleisteinCoord p α t ^ 2 / 2 -
              bleisteinOffset p α * bleisteinCoord p α t)) *
            bleisteinCoord p α t ^ (lam - 1)) •
          bleisteinAmplitude p q lam α U (bleisteinCoord p α t))) =
      ∫ t in s, (Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t :=
    setIntegral_congr_fun hs fun t ht ↦
      abs_deriv_bleisteinCoord_smul_eq h0 hp0 hpmin hmono hw' (hsU ht) (hs0 t ht)
  rw [hcongr, ← integral_smul]
  refine setIntegral_congr_fun hs fun t _ ↦ ?_
  rw [smul_smul, ← mul_assoc, ← Real.exp_add]
  exact congrArg (fun r ↦ (Real.exp r * t ^ (lam - 1)) • q t) (by ring)

/-- Equivalence of `IntegrableOn` under derivative-sign hypotheses on an open convex domain `U`. -/
theorem integrableOn_bleisteinAmplitude_of_deriv_sign {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ}
    {U s : Set ℝ} (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (hU : IsOpen U) (hconv : Convex ℝ U) (h0 : 0 ∈ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (bleisteinCoord p α '' s) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  have hpmin : ∀ t ∈ U, p α ≤ p t := fun t ht ↦
    (eq_or_ne t α).elim (fun h ↦ h ▸ le_rfl) fun hne ↦
      (lt_of_injOn_bleisteinCoord hmono.injOn hα ht hne).le
  exact integrableOn_bleisteinAmplitude_iff hs hsU hs0 hU h0 (hpmin 0 h0) hpmin
    (contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright) hmono
    (fun _ ht ↦ deriv_bleisteinCoord_pos_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright ht)

/-- Bleistein's change of variables on `s ⊆ U ∩ (0, ∞)` under derivative-sign hypotheses on an
open convex domain `U`. -/
theorem integral_bleisteinCoord_of_deriv_sign {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ}
    {U s : Set ℝ} (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (hU : IsOpen U) (hconv : Convex ℝ U) (h0 : 0 ∈ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in bleisteinCoord p α '' s,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  have hpmin : ∀ t ∈ U, p α ≤ p t := fun t ht ↦
    (eq_or_ne t α).elim (fun h ↦ h ▸ le_rfl) fun hne ↦
      (lt_of_injOn_bleisteinCoord hmono.injOn hα ht hne).le
  exact integral_bleisteinCoord_eq hs hsU hs0 hU h0 (hpmin 0 h0) hpmin
    (contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright) hmono
    (fun _ ht ↦ deriv_bleisteinCoord_pos_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright ht)

/-- Equivalence of `IntegrableOn` on `(0, k)` and `(0, ∞)` when `p t → +∞` as `t → k⁻`
(`κ = +∞`). -/
theorem integrableOn_bleisteinAmplitude_Ioo_iff_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x k : ℝ}
    {U : Set ℝ} (hk : 0 < k) (hαk : α < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p (𝓝[<] k) atTop) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (Ioi 0) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioo 0 k) := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  rw [← integrableOn_bleisteinAmplitude_of_deriv_sign measurableSet_Ioo
      (Ioo_subset_Ico_self.trans hIco) (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp'0
      hp'' hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioi hk (hw.continuousOn.mono hIco) (hmono.mono hIco)
      (tendsto_bleisteinCoord_nhdsLT_atTop hαk htend)]

/-- Equivalence of `IntegrableOn` on `(0, ∞)` and `(0, ∞)` when `p t → +∞` as `t → +∞`
(`κ = +∞`). -/
theorem integrableOn_bleisteinAmplitude_Ioi_iff_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ}
    {U : Set ℝ} (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p atTop atTop) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (Ioi 0) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioi 0) := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  rw [← integrableOn_bleisteinAmplitude_of_deriv_sign measurableSet_Ioi
      (Ioi_subset_Ici_self.trans hIci) (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp'0
      hp'' hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioi (hw.continuousOn.mono hIci) (hmono.mono hIci)
      (tendsto_bleisteinCoord_atTop_atTop htend)]

/-- Bleistein's change of variables on `(0, k)` with finite upper limit `κ = lim_{t → k⁻} w(α, t)`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioo_eq_Ioo {p : ℝ → ℝ} {q : ℝ → E} {lam α x k κ : ℝ} {U : Set ℝ}
    (hk : 0 < k) (hIco : Ico 0 k ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) (𝓝[<] k) (𝓝 κ)) :
    (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioo 0 κ,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioo (Ioo_subset_Ico_self.trans hIco)
      (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp'0 hp'' hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioo hk (hw.continuousOn.mono hIco) (hmono.mono hIco) htend]

/-- Bleistein's change of variables on `(0, k)` when `p t → +∞` as `t → k⁻`, so `κ = +∞`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioo_eq_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x k : ℝ} {U : Set ℝ}
    (hk : 0 < k) (hαk : α < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p (𝓝[<] k) atTop) :
    (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioi 0,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioo (Ioo_subset_Ico_self.trans hIco)
      (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp'0 hp'' hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioi hk (hw.continuousOn.mono hIco) (hmono.mono hIco)
      (tendsto_bleisteinCoord_nhdsLT_atTop hαk htend)]

/-- Bleistein's change of variables on `(0, ∞)` with finite upper limit `κ = lim_{t → +∞} w(α, t)`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioi_eq_Ioo {p : ℝ → ℝ} {q : ℝ → E} {lam α x κ : ℝ} {U : Set ℝ}
    (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) atTop (𝓝 κ)) :
    (∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioo 0 κ,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioi (Ioi_subset_Ici_self.trans hIci)
      (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp'0 hp'' hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioo (hw.continuousOn.mono hIci) (hmono.mono hIci) htend]

/-- Bleistein's change of variables on `(0, ∞)` when `p t → +∞` as `t → +∞`, so `κ = +∞`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioi_eq_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U : Set ℝ}
    (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p atTop atTop) :
    (∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioi 0,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioi (Ioi_subset_Ici_self.trans hIci)
      (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp'0 hp'' hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioi (hw.continuousOn.mono hIci) (hmono.mono hIci)
      (tendsto_bleisteinCoord_atTop_atTop htend)]

end Amplitude

end TauCeti
