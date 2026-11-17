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
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Calculus.InverseFunctionTheorem

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
`bleisteinAmplitude` is continuous on `bleisteinCoord p α '' s` for any `s ⊆ U` on which `q` is
continuous (covering `w = 0` when `0 ∈ s`, and `w = bleisteinOffset p α` whenever `α ∈ s`,
including `α ≤ 0`), is nonzero at `w = bleisteinOffset p α` whenever `q α ≠ 0`, and transforms the
original integral on `(0, k)` or `(0, ∞)` into
`exp (-x * p 0) • ∫ w in (0, κ), (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w`
with equivalence of `IntegrableOn` (absolute convergence).

## Main definitions

* `TauCeti.bleisteinAmplitude`: the transformed amplitude `f(α, w)` of DLMF 2.3.30.

## Main results

* `TauCeti.bleisteinAmplitude_zero`, `TauCeti.bleisteinAmplitude_zero_of_injOn`,
  `TauCeti.bleisteinAmplitude_bleisteinOffset`,
  `TauCeti.bleisteinAmplitude_bleisteinOffset_of_ne_zero`: evaluation of `bleisteinAmplitude` at
  `w = 0` and at the critical point image `w = bleisteinOffset p α`.
* `TauCeti.continuousOn_bleisteinAmplitude`: continuity of `bleisteinAmplitude` on
  `bleisteinCoord p α '' s` for `s ⊆ U` (covering `w = 0` when `0 ∈ s`, and
  `w = bleisteinOffset p α` whenever `α ∈ s`).
* `TauCeti.bleisteinAmplitude_bleisteinOffset_ne_zero`: nonvanishing at `w = bleisteinOffset p α`
  when `q α ≠ 0`.
* `TauCeti.integrableOn_bleisteinAmplitude_iff`,
  `TauCeti.integrableOn_bleisteinAmplitude_iff_of_deriv_sign`,
  `TauCeti.integrableOn_bleisteinAmplitude_Ioo_iff_Ioo`,
  `TauCeti.integrableOn_bleisteinAmplitude_Ioi_iff_Ioo`,
  `TauCeti.integrableOn_bleisteinAmplitude_Ioo_iff_Ioi`,
  `TauCeti.integrableOn_bleisteinAmplitude_Ioi_iff_Ioi`: equivalence of absolute convergence.
* `TauCeti.integral_bleisteinCoord_eq`, `TauCeti.integral_bleisteinCoord_of_deriv_sign`,
  `TauCeti.integral_bleisteinCoord_Ioo_eq_Ioo`, `TauCeti.integral_bleisteinCoord_Ioo_eq_Ioi`,
  `TauCeti.integral_bleisteinCoord_Ioi_eq_Ioo`, `TauCeti.integral_bleisteinCoord_Ioi_eq_Ioi`:
  Bleistein's integral change of variables (DLMF 2.3.29) for finite and infinite upper limits.

## References

* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. **19** (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §9.4.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted A K Peters,
  1997. Chapter 9, §10.
* NIST Digital Library of Mathematical Functions, §2.3(v), <https://dlmf.nist.gov/2.3.v>.
-/

public section

open Filter Set MeasureTheory Function
open scoped ContDiff Topology

namespace TauCeti

/-! ### Transformed amplitude `bleisteinAmplitude` (DLMF 2.3.30) -/

/-- The transformed amplitude `f(α, w) = ((t / w) ^ (lam - 1) * dt/dw) • q t` of DLMF 2.3.30,
where `t = Function.invFunOn (bleisteinCoord p α) s w`. At `w = 0`, the removable singularity of
`t / w` is resolved by its limit `(deriv (bleisteinCoord p α) 0)⁻¹`, making `bleisteinAmplitude`
continuous across `w = 0` (and across `w = a(α)` whenever `α ∈ s`). -/
noncomputable def bleisteinAmplitude {E : Type*} [SMul ℝ E]
    (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) : E :=
  let t := invFunOn (bleisteinCoord p α) s w
  ((if w = 0 then (deriv (bleisteinCoord p α) 0)⁻¹ else t / w) ^ (lam - 1) /
      deriv (bleisteinCoord p α) t) •
    q t

section Amplitude
variable {E : Type*} [SMul ℝ E]

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

/-- Value of `bleisteinAmplitude` at the removable singularity `w = 0`. -/
theorem bleisteinAmplitude_zero (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) :
    bleisteinAmplitude p q lam α s 0 =
      (((deriv (bleisteinCoord p α) 0)⁻¹ ^ (lam - 1)) /
        deriv (bleisteinCoord p α) (invFunOn (bleisteinCoord p α) s 0)) •
      q (invFunOn (bleisteinCoord p α) s 0) := by
  simp [bleisteinAmplitude]

/-- Value of `bleisteinAmplitude` at `w = 0` when `0 ∈ s` and `bleisteinCoord p α` is injective
on `s`. -/
theorem bleisteinAmplitude_zero_of_injOn {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinCoord p α) s) (h0 : 0 ∈ s) :
    bleisteinAmplitude p q lam α s 0 =
      (((deriv (bleisteinCoord p α) 0)⁻¹ ^ (lam - 1)) / deriv (bleisteinCoord p α) 0) • q 0 := by
  have hinv : invFunOn (bleisteinCoord p α) s 0 = 0 := by
    simpa [bleisteinCoord_zero] using hinj.leftInvOn_invFunOn h0
  rw [bleisteinAmplitude_zero, hinv]

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

/-- Evaluation of `bleisteinAmplitude` at the critical point image `w = bleisteinOffset p α`. -/
theorem bleisteinAmplitude_bleisteinOffset {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinCoord p α) s) (hα : α ∈ s) :
    bleisteinAmplitude p q lam α s (bleisteinOffset p α) =
      (((if bleisteinOffset p α = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
          else α / bleisteinOffset p α) ^ (lam - 1)) /
        deriv (bleisteinCoord p α) α) • q α := by
  have hinv : invFunOn (bleisteinCoord p α) s (bleisteinOffset p α) = α := by
    simpa [bleisteinCoord_self] using hinj.leftInvOn_invFunOn hα
  rw [bleisteinAmplitude_def, hinv]

/-- Explicit leading coefficient `φ₀ = ((α / a) ^ (lam - 1) / √(p'' α)) • q α` of DLMF 2.3.32
at `w = bleisteinOffset p α` when `bleisteinOffset p α ≠ 0`. -/
theorem bleisteinAmplitude_bleisteinOffset_of_ne_zero {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ}
    {s : Set ℝ} (hinj : InjOn (bleisteinCoord p α) s) (hα : α ∈ s)
    (ha : bleisteinOffset p α ≠ 0)
    (hp : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hp'0 : deriv p α = 0)
    (hp' : DifferentiableAt ℝ (deriv p) α) :
    bleisteinAmplitude p q lam α s (bleisteinOffset p α) =
      (((α / bleisteinOffset p α) ^ (lam - 1)) / Real.sqrt (deriv (deriv p) α)) • q α := by
  rw [bleisteinAmplitude_bleisteinOffset hinj hα, deriv_bleisteinCoord_self hp hp'0 hp']
  simp [ha]

end Amplitude

/-- `bleisteinAmplitude` vanishes when the amplitude `q` is identically zero. -/
@[simp]
theorem bleisteinAmplitude_zero_fun {E : Type*} [Zero E] [SMulZeroClass ℝ E]
    (p : ℝ → ℝ) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p (0 : ℝ → E) lam α s w = 0 := by
  simp [bleisteinAmplitude]

/-- Additivity of `bleisteinAmplitude` in the amplitude `q`. -/
theorem bleisteinAmplitude_add {E : Type*} [AddZeroClass E] [DistribSMul ℝ E]
    (p : ℝ → ℝ) (q₁ q₂ : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p (q₁ + q₂) lam α s w =
      bleisteinAmplitude p q₁ lam α s w + bleisteinAmplitude p q₂ lam α s w := by
  simp [bleisteinAmplitude, smul_add]

/-- Homogeneity of `bleisteinAmplitude` in the amplitude `q`. -/
theorem bleisteinAmplitude_smul {𝕜 E : Type*} [SMul ℝ E] [SMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    (p : ℝ → ℝ) (c : 𝕜) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p (c • q) lam α s w = c • bleisteinAmplitude p q lam α s w := by
  simp [bleisteinAmplitude, smul_comm]

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
  have hstrict : ∀ t ∈ U,
      HasStrictDerivAt (bleisteinCoord p α) (deriv (bleisteinCoord p α) t) t :=
    fun t ht ↦ (hw.contDiffAt (hU.mem_nhds ht)).hasStrictDerivAt_deriv one_ne_zero
  have hw'_ne : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0 := fun t ht ↦ (hw' t ht).ne'
  have hopen_img : IsOpen (bleisteinCoord p α '' U) :=
    isOpen_image_of_hasStrictDerivAt hU hstrict hw'_ne
  have hinv_cont : ContinuousOn (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' U) :=
    continuousOn_invFunOn_of_hasStrictDerivAt hU hinj hstrict hw'_ne
  have hd0 : HasStrictDerivAt (invFunOn (bleisteinCoord p α) U)
      (deriv (bleisteinCoord p α) 0)⁻¹ 0 := by
    simpa [bleisteinCoord_zero] using
      (hstrict 0 h0).invFunOn (hw'_ne 0 h0) (hU.mem_nhds h0) hinj
  have hinv0 : invFunOn (bleisteinCoord p α) U 0 = 0 := by
    simpa [bleisteinCoord_zero] using hinj.leftInvOn_invFunOn h0
  have hdslope : ContinuousOn (dslope (invFunOn (bleisteinCoord p α) U) 0)
      (bleisteinCoord p α '' U) :=
    (continuousOn_dslope (hopen_img.mem_nhds ⟨0, h0, bleisteinCoord_zero p α⟩)).mpr
      ⟨hinv_cont, hd0.hasDerivAt.differentiableAt⟩
  refine hdslope.congr fun w _ ↦ ?_
  by_cases hw0 : w = 0
  · simp [hw0, dslope_same, hd0.hasDerivAt.deriv]
  · simp [hw0, dslope_of_ne _ hw0, slope_def_field, hinv0]

/-- Continuity of `bleisteinAmplitude p q lam α U` on `bleisteinCoord p α '' s` for `s ⊆ U`
(including `w = 0` when `0 ∈ s`, and `w = a(α)` whenever `α ∈ s`). -/
theorem continuousOn_bleisteinAmplitude {E : Type*} [TopologicalSpace E] [SMul ℝ E]
    [ContinuousSMul ℝ E] {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {U s : Set ℝ}
    (hsU : s ⊆ U) (hU : IsOpen U) (h0 : 0 ∈ U) (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinCoord p α) t)
    (hq : ContinuousOn q s) :
    ContinuousOn (bleisteinAmplitude p q lam α U) (bleisteinCoord p α '' s) := by
  have hratio_cont := continuousOn_bleisteinRatio hU h0 hw hmono hw'
  have hinj : InjOn (bleisteinCoord p α) U := hmono.injOn
  have hstrict : ∀ t ∈ U,
      HasStrictDerivAt (bleisteinCoord p α) (deriv (bleisteinCoord p α) t) t :=
    fun t ht ↦ (hw.contDiffAt (hU.mem_nhds ht)).hasStrictDerivAt_deriv one_ne_zero
  have hw'_ne : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0 := fun t ht ↦ (hw' t ht).ne'
  have hmapsU : MapsTo (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' U) U := by
    rintro _ ⟨t, ht, rfl⟩; rwa [hinj.leftInvOn_invFunOn ht]
  have hmaps : MapsTo (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' s) s := by
    rintro _ ⟨t, ht, rfl⟩; rwa [hinj.leftInvOn_invFunOn (hsU ht)]
  have hinv_cont : ContinuousOn (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' U) :=
    continuousOn_invFunOn_of_hasStrictDerivAt hU hinj hstrict hw'_ne
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
    hrpow.div ((hw.continuousOn_deriv_of_isOpen hU le_rfl).comp hinv_cont hmapsU)
      fun _ hw_mem ↦ hw'_ne _ (hmapsU hw_mem)
  have hsub : bleisteinCoord p α '' s ⊆ bleisteinCoord p α '' U := image_mono hsU
  exact (hscalar.mono hsub).smul (hq.comp (hinv_cont.mono hsub) hmaps)

/-- Nonvanishing of `bleisteinAmplitude` at the critical value `w = bleisteinOffset p α` whenever
`q α ≠ 0` (covering `α < 0`, `α = 0`, and `α > 0`). -/
theorem bleisteinAmplitude_bleisteinOffset_ne_zero {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {U : Set ℝ}
    (h0 : 0 ∈ U) (hα : α ∈ U) (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw'α : 0 < deriv (bleisteinCoord p α) α) (hqα : q α ≠ 0) :
    bleisteinAmplitude p q lam α U (bleisteinOffset p α) ≠ 0 := by
  rw [bleisteinAmplitude_bleisteinOffset hmono.injOn hα]
  have hpos : 0 < (if bleisteinOffset p α = 0 then (deriv (bleisteinCoord p α) 0)⁻¹
      else α / bleisteinOffset p α) := by
    split_ifs with ha
    · have hα0 : α = 0 :=
        hmono.injOn hα h0 (by rw [bleisteinCoord_self, bleisteinCoord_zero, ha])
      exact inv_pos.mpr (hα0 ▸ hw'α)
    · have hα0 : α ≠ 0 := by rintro rfl; exact ha (bleisteinOffset_zero p)
      rcases hα0.lt_or_gt with hlt | hgt
      · exact div_pos_of_neg_of_neg hlt
          (by simpa [bleisteinCoord_self] using bleisteinCoord_neg hmono h0 hα hlt)
      · exact div_pos hgt
          (by simpa [bleisteinCoord_self] using bleisteinCoord_pos hmono h0 hα hgt)
  exact smul_ne_zero (div_pos (Real.rpow_pos_of_pos hpos _) hw'α).ne' hqα

/-! ### Integral change of variables (DLMF 2.3.29) -/

section Integral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real function with strictly positive derivative on `s` has `HasDerivWithinAt` at every point
of `s`. -/
private lemma hasDerivWithinAt_of_deriv_pos {f : ℝ → ℝ} {s : Set ℝ}
    (hf' : ∀ t ∈ s, 0 < deriv f t) :
    ∀ t ∈ s, HasDerivWithinAt f (deriv f t) s t :=
  fun t ht ↦ (differentiableAt_of_deriv_ne_zero (hf' t ht).ne').hasDerivAt.hasDerivWithinAt

/-- Pointwise Jacobian cancellation on `U ∩ (0, ∞)`: pulling back the normal-form integrand
`exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) • bleisteinAmplitude p q lam α U w` with the
Jacobian factor `|deriv (bleisteinCoord p α) t|` recovers
`exp (-x * (p t - p 0)) * t ^ (lam - 1) • q t`. -/
private lemma abs_deriv_bleisteinCoord_smul_eq {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U : Set ℝ}
    (h0 : 0 ∈ U) (hp0 : p α ≤ p 0) (hmono : StrictMonoOn (bleisteinCoord p α) U)
    {t : ℝ} (htU : t ∈ U) (ht0 : 0 < t) (hpt : p α ≤ p t)
    (hdw : 0 < deriv (bleisteinCoord p α) t) :
    |deriv (bleisteinCoord p α) t| •
      ((Real.exp (-x * (bleisteinCoord p α t ^ 2 / 2 -
            bleisteinOffset p α * bleisteinCoord p α t)) *
          bleisteinCoord p α t ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U (bleisteinCoord p α t)) =
      (Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t := by
  have hwt_pos : 0 < bleisteinCoord p α t := bleisteinCoord_pos hmono h0 htU ht0
  rw [bleisteinAmplitude_bleisteinCoord hmono.injOn htU hwt_pos.ne',
    half_sq_bleisteinCoord_sub_mul hp0 hpt, abs_of_pos hdw, smul_smul, smul_smul]
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
        rw [hrpow, div_self hdw.ne', mul_one]

/-- Equivalence of absolute convergence (`IntegrableOn`) between the original integral on a
measurable set `s ⊆ U ∩ (0, ∞)` and the transformed Bleistein integral on `bleisteinCoord p α '' s`
(DLMF 2.3.29). -/
theorem integrableOn_bleisteinAmplitude_iff {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U s : Set ℝ}
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (h0 : 0 ∈ U) (hp0 : p α ≤ p 0) (hpmin : ∀ t ∈ s, p α ≤ p t)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ s, 0 < deriv (bleisteinCoord p α) t) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (bleisteinCoord p α '' s) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs (hasDerivWithinAt_of_deriv_pos hw')
    (hmono.injOn.mono hsU)]
  have hcongr : IntegrableOn
      (fun t ↦ |deriv (bleisteinCoord p α) t| •
        ((Real.exp (-x * (bleisteinCoord p α t ^ 2 / 2 -
              bleisteinOffset p α * bleisteinCoord p α t)) *
            bleisteinCoord p α t ^ (lam - 1)) •
          bleisteinAmplitude p q lam α U (bleisteinCoord p α t))) s ↔
      IntegrableOn (fun t ↦ (Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t) s :=
    integrableOn_congr_fun
      (fun t ht ↦ abs_deriv_bleisteinCoord_smul_eq h0 hp0 hmono (hsU ht) (hs0 t ht) (hpmin t ht)
        (hw' t ht)) hs
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
    (h0 : 0 ∈ U) (hp0 : p α ≤ p 0) (hpmin : ∀ t ∈ s, p α ≤ p t)
    (hmono : StrictMonoOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ s, 0 < deriv (bleisteinCoord p α) t) :
    (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in bleisteinCoord p α '' s,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  rw [integral_image_eq_integral_abs_deriv_smul hs (hasDerivWithinAt_of_deriv_pos hw')
    (hmono.injOn.mono hsU)]
  have hcongr :
      (∫ t in s, |deriv (bleisteinCoord p α) t| •
        ((Real.exp (-x * (bleisteinCoord p α t ^ 2 / 2 -
              bleisteinOffset p α * bleisteinCoord p α t)) *
            bleisteinCoord p α t ^ (lam - 1)) •
          bleisteinAmplitude p q lam α U (bleisteinCoord p α t))) =
      ∫ t in s, (Real.exp (-x * (p t - p 0)) * t ^ (lam - 1)) • q t :=
    setIntegral_congr_fun hs fun t ht ↦
      abs_deriv_bleisteinCoord_smul_eq h0 hp0 hmono (hsU ht) (hs0 t ht) (hpmin t ht) (hw' t ht)
  rw [hcongr, ← integral_smul]
  refine setIntegral_congr_fun hs fun t _ ↦ ?_
  rw [smul_smul, ← mul_assoc, ← Real.exp_add]
  exact congrArg (fun r ↦ (Real.exp r * t ^ (lam - 1)) • q t) (by ring)

/-- Equivalence of `IntegrableOn` under derivative-sign hypotheses on an open convex domain `U`. -/
theorem integrableOn_bleisteinAmplitude_iff_of_deriv_sign {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ}
    {U s : Set ℝ} (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (hU : IsOpen U) (hconv : Convex ℝ U) (h0 : 0 ∈ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (bleisteinCoord p α '' s) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp.continuousOn hpleft hpright
  exact integrableOn_bleisteinAmplitude_iff hs hsU hs0 h0
    (le_of_injOn_bleisteinCoord hmono.injOn hα h0)
    (fun _ ht ↦ le_of_injOn_bleisteinCoord hmono.injOn hα (hsU ht)) hmono
    (fun _ ht ↦ deriv_bleisteinCoord_pos_of_deriv_sign hU hconv hα hp hp'' hpleft hpright (hsU ht))

/-- Bleistein's change of variables on `s ⊆ U ∩ (0, ∞)` under derivative-sign hypotheses on an
open convex domain `U`. -/
theorem integral_bleisteinCoord_of_deriv_sign {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ}
    {U s : Set ℝ} (hs : MeasurableSet s) (hsU : s ⊆ U) (hs0 : ∀ t ∈ s, 0 < t)
    (hU : IsOpen U) (hconv : Convex ℝ U) (h0 : 0 ∈ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in bleisteinCoord p α '' s,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp.continuousOn hpleft hpright
  exact integral_bleisteinCoord_eq hs hsU hs0 h0
    (le_of_injOn_bleisteinCoord hmono.injOn hα h0)
    (fun _ ht ↦ le_of_injOn_bleisteinCoord hmono.injOn hα (hsU ht)) hmono
    (fun _ ht ↦ deriv_bleisteinCoord_pos_of_deriv_sign hU hconv hα hp hp'' hpleft hpright (hsU ht))

/-- Equivalence of `IntegrableOn` on `(0, κ)` and `(0, k)` with finite upper limit
`κ = lim_{t → k⁻} w(α, t)`. -/
theorem integrableOn_bleisteinAmplitude_Ioo_iff_Ioo {p : ℝ → ℝ} {q : ℝ → E} {lam α x k κ : ℝ}
    {U : Set ℝ} (hk : 0 < k) (hIco : Ico 0 k ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hα : α ∈ U) (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) (𝓝[<] k) (𝓝 κ)) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (Ioo 0 κ) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioo 0 k) := by
  rw [← integrableOn_bleisteinAmplitude_iff_of_deriv_sign measurableSet_Ioo
    (Ioo_subset_Ico_self.trans hIco) (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp''
    hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioo_of_deriv_sign hk hIco hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Equivalence of `IntegrableOn` on `(0, ∞)` and `(0, k)` when `p t → +∞` as `t → k⁻`
(`κ = +∞`). -/
theorem integrableOn_bleisteinAmplitude_Ioi_iff_Ioo {p : ℝ → ℝ} {q : ℝ → E} {lam α x k : ℝ}
    {U : Set ℝ} (hk : 0 < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p (𝓝[<] k) atTop) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (Ioi 0) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioo 0 k) := by
  rw [← integrableOn_bleisteinAmplitude_iff_of_deriv_sign measurableSet_Ioo
    (Ioo_subset_Ico_self.trans hIco) (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp''
    hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioi_of_deriv_sign hk hIco hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Equivalence of `IntegrableOn` on `(0, κ)` and `(0, ∞)` with finite upper limit
`κ = lim_{t → +∞} w(α, t)`. -/
theorem integrableOn_bleisteinAmplitude_Ioo_iff_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x κ : ℝ}
    {U : Set ℝ} (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) atTop (𝓝 κ)) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (Ioo 0 κ) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioi 0) := by
  rw [← integrableOn_bleisteinAmplitude_iff_of_deriv_sign measurableSet_Ioi
    (Ioi_subset_Ici_self.trans hIci) (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp''
    hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioo_of_deriv_sign hIci hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Equivalence of `IntegrableOn` on `(0, ∞)` and `(0, ∞)` when `p t → +∞` as `t → +∞`
(`κ = +∞`). -/
theorem integrableOn_bleisteinAmplitude_Ioi_iff_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ}
    {U : Set ℝ} (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p atTop atTop) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α U w)
      (Ioi 0) ↔
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioi 0) := by
  rw [← integrableOn_bleisteinAmplitude_iff_of_deriv_sign measurableSet_Ioi
    (Ioi_subset_Ici_self.trans hIci) (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp''
    hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioi_of_deriv_sign hIci hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Bleistein's change of variables on `(0, k)` with finite upper limit `κ = lim_{t → k⁻} w(α, t)`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioo_eq_Ioo {p : ℝ → ℝ} {q : ℝ → E} {lam α x k κ : ℝ} {U : Set ℝ}
    (hk : 0 < k) (hIco : Ico 0 k ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) (𝓝[<] k) (𝓝 κ)) :
    (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioo 0 κ,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioo (Ioo_subset_Ico_self.trans hIco)
    (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp'' hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioo_of_deriv_sign hk hIco hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Bleistein's change of variables on `(0, k)` when `p t → +∞` as `t → k⁻`, so `κ = +∞`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioo_eq_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x k : ℝ} {U : Set ℝ}
    (hk : 0 < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p (𝓝[<] k) atTop) :
    (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioi 0,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioo (Ioo_subset_Ico_self.trans hIco)
    (fun _ ht ↦ ht.1) hU hconv (hIco ⟨le_rfl, hk⟩) hα hp hp'' hpleft hpright,
    image_bleisteinCoord_Ioo_eq_Ioi_of_deriv_sign hk hIco hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Bleistein's change of variables on `(0, ∞)` with finite upper limit `κ = lim_{t → +∞} w(α, t)`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioi_eq_Ioo {p : ℝ → ℝ} {q : ℝ → E} {lam α x κ : ℝ} {U : Set ℝ}
    (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) atTop (𝓝 κ)) :
    (∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioo 0 κ,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioi (Ioi_subset_Ici_self.trans hIci)
    (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp'' hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioo_of_deriv_sign hIci hconv hα hp.continuousOn hpleft hpright
      htend]

/-- Bleistein's change of variables on `(0, ∞)` when `p t → +∞` as `t → +∞`, so `κ = +∞`
(DLMF 2.3.29). -/
theorem integral_bleisteinCoord_Ioi_eq_Ioi {p : ℝ → ℝ} {q : ℝ → E} {lam α x : ℝ} {U : Set ℝ}
    (hIci : Ici 0 ⊆ U) (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : DifferentiableOn ℝ p U) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p atTop atTop) :
    (∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * p 0) •
        ∫ w in Ioi 0,
          (Real.exp (-x * (w ^ 2 / 2 - bleisteinOffset p α * w)) * w ^ (lam - 1)) •
            bleisteinAmplitude p q lam α U w := by
  rw [integral_bleisteinCoord_of_deriv_sign measurableSet_Ioi (Ioi_subset_Ici_self.trans hIci)
    (fun _ ht ↦ ht) hU hconv (hIci self_mem_Ici) hα hp hp'' hpleft hpright,
    image_bleisteinCoord_Ioi_eq_Ioi_of_deriv_sign hIci hconv hα hp.continuousOn hpleft hpright
      htend]

end Integral

end TauCeti
