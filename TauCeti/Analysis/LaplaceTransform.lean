/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate

/-!
# The one-sided Laplace transform

For `f : ℝ → E`, a complex parameter `s` and `z : E`, `TauCeti.HasLaplace f s z` says that the
ordinary one-sided Laplace integral

`∫₀^∞ e^(-st) • f t dt`

converges absolutely and equals `z`. The integral is a Bochner integral for Lebesgue measure
restricted to `(0, ∞)`; an optional measure argument replaces this default.

Integrability is part of the predicate. The Bochner integral of a non-integrable function is `0`,
so the bare equation `∫ e^(-st) • f t = z` cannot certify convergence:
`TauCeti.not_hasLaplace_one_zero` records that the constant `1` has no transform at `s = 0`,
although its totalised integral there is `0`.

This is the ordinary transform of `f`, not the Laplace–Stieltjes transform `∫ e^(-st) df(t)`:
the constant `1` has transform `1 / s` (`TauCeti.hasLaplace_one`), and `t ↦ t ^ k` has transform
`k! / s ^ (k + 1)` (`TauCeti.hasLaplace_pow`). These are the transforms of the counting functions
and of the model terms in Tauberian theorems of Ikehara–Delange type.

## Main results

* `TauCeti.HasLaplace`: convergence and value of the one-sided Laplace transform.
* `TauCeti.HasLaplace.unique`: the value is unique.
* `TauCeti.HasLaplace.congr_ae`: the predicate depends on `f` only up to almost-everywhere
  equality.
* `TauCeti.HasLaplace.add`, `TauCeti.HasLaplace.neg`, `TauCeti.HasLaplace.sub`,
  `TauCeti.HasLaplace.const_smul`: linearity.
* `TauCeti.HasLaplace.comp_mul_left`: a positive dilation `t ↦ c t` of the input rescales the
  parameter and the value.
* `TauCeti.hasLaplace_pow`, `TauCeti.hasLaplace_one`: the transforms of `t ^ k` and of `1` on
  `0 < Re s`, from the Gamma integral with a complex rate.

## References

The predicate, its argument order, its default measure and its scalar-action hypotheses follow
Dennj Osele, *The Laplace transform* (2026), declarations `LaplaceConvergent`, `laplace` and
`HasLaplace` of `Mathlib/Analysis/LaplaceTransform.lean` at commit
`90482cd37e85e423459de2ed103cea2f4d98cb20` of <https://github.com/dennj/mathlib4>
(Apache 2.0); the additivity, scaling and dilation proofs are adapted from that file. The
convergence hypothesis on the ordinary Laplace integral is that of H. Delange,
*Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71** (1954), 213–242,
p. 213.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section SMul

variable [SMul ℂ E]

/-- `HasLaplace f s z μ`: the Laplace integral `∫ e^(-st) • f t ∂μ` converges absolutely and
equals `z`. With the default measure, Lebesgue measure restricted to `(0, ∞)`, this is the
ordinary one-sided Laplace transform `∫₀^∞ e^(-st) • f t dt`. Integrability is part of the
predicate, because the Bochner integral of a non-integrable function is `0`. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (z : E) (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
    ∫ t, Complex.exp (-s * t) • f t ∂μ = z

/-- Unfolding `HasLaplace`: integrability of the Laplace integrand and the value of its
integral. -/
theorem hasLaplace_iff {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace f s z μ ↔ Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
      ∫ t, Complex.exp (-s * t) • f t ∂μ = z :=
  Iff.rfl

/-- An integrable Laplace integrand has, as its transform, its integral. -/
theorem _root_.MeasureTheory.Integrable.hasLaplace {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ) :
    HasLaplace f s (∫ t, Complex.exp (-s * t) • f t ∂μ) μ :=
  ⟨hf, rfl⟩

namespace HasLaplace

variable {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}

/-- The Laplace integrand of a function with a Laplace transform is integrable. -/
theorem integrable (hf : HasLaplace f s z μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  hf.1

/-- The Laplace integral of a function with transform `z` equals `z`. -/
theorem integral_eq (hf : HasLaplace f s z μ) : ∫ t, Complex.exp (-s * t) • f t ∂μ = z :=
  hf.2

/-- The Laplace transform of a function at a given parameter is unique. -/
theorem unique (hz : HasLaplace f s z μ) (hw : HasLaplace f s w μ) : z = w :=
  hz.integral_eq.symm.trans hw.integral_eq

/-- Functions that agree almost everywhere have the same Laplace transforms. -/
theorem congr_ae (hf : HasLaplace f s z μ) (hfg : f =ᵐ[μ] g) : HasLaplace g s z μ := by
  have h : (fun t : ℝ ↦ Complex.exp (-s * t) • f t) =ᵐ[μ]
      fun t ↦ Complex.exp (-s * t) • g t := hfg.mono fun t ht ↦ by simp only [ht]
  exact ⟨hf.integrable.congr h, (integral_congr_ae h).symm.trans hf.integral_eq⟩

end HasLaplace

theorem hasLaplace_congr_ae {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} (hfg : f =ᵐ[μ] g) :
    HasLaplace f s z μ ↔ HasLaplace g s z μ :=
  ⟨fun hf ↦ hf.congr_ae hfg, fun hg ↦ hg.congr_ae hfg.symm⟩

/-- **Positive dilation.** If `f` has transform `z` at `s / c`, then `t ↦ f (c t)` has
transform `c⁻¹ • z` at `s`, for `0 < c`. -/
theorem HasLaplace.comp_mul_left {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ}
    (hf : HasLaplace f (s / c) z) (hc : 0 < c) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s (c⁻¹ • z) := by
  set g : ℝ → E := fun u ↦ Complex.exp (-(s / c) * u) • f u
  have h : EqOn (fun t : ℝ ↦ Complex.exp (-s * t) • f (c * t)) (fun t ↦ g (c * t)) (Ioi 0) :=
    fun t _ ↦ by
      simp only [g, Complex.ofReal_mul]
      congr 2
      field_simp [Complex.ofReal_ne_zero.mpr hc.ne']
  refine ⟨?_, ?_⟩
  · rw [← IntegrableOn, integrableOn_congr_fun h measurableSet_Ioi,
      integrableOn_Ioi_comp_mul_left_iff g 0 hc, mul_zero]
    exact hf.integrable
  · rw [setIntegral_congr_fun measurableSet_Ioi h, integral_comp_mul_left_Ioi g 0 hc, mul_zero,
      hf.integral_eq]

end SMul

/-- The zero function has Laplace transform `0` at every parameter and for every measure. -/
@[simp]
theorem hasLaplace_zero [SMulZeroClass ℂ E] (s : ℂ) (μ : Measure ℝ) :
    HasLaplace (fun _ : ℝ ↦ (0 : E)) s 0 μ :=
  ⟨by simp, by simp⟩

namespace HasLaplace

variable [DistribSMul ℂ E] {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}

/-- The Laplace transform is additive. -/
theorem add (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (fun t ↦ f t + g t) s (z + w) μ := by
  refine ⟨(hf.integrable.add hg.integrable).congr (ae_of_all _ fun t ↦ (smul_add _ _ _).symm),
    ?_⟩
  simp only [smul_add]
  rw [integral_add hf.integrable hg.integrable, hf.integral_eq, hg.integral_eq]

/-- The Laplace transform commutes with negation. -/
theorem neg (hf : HasLaplace f s z μ) : HasLaplace (fun t ↦ -f t) s (-z) μ := by
  refine ⟨hf.integrable.neg.congr (ae_of_all _ fun t ↦ (smul_neg _ _).symm), ?_⟩
  simp only [smul_neg]
  rw [integral_neg, hf.integral_eq]

/-- The Laplace transform commutes with subtraction. -/
theorem sub (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (fun t ↦ f t - g t) s (z - w) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end HasLaplace

/-- The Laplace transform commutes with multiplication by a constant from any normed ring acting
boundedly on `E` and commuting with the real and complex actions, in particular `ℂ` when `E` is a
complex normed space. -/
theorem HasLaplace.const_smul [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass ℝ R E]
    [SMulCommClass ℂ R E] (hf : HasLaplace f s z μ) (c : R) :
    HasLaplace (fun t ↦ c • f t) s (c • z) μ := by
  have h : (fun t : ℝ ↦ Complex.exp (-s * t) • c • f t) =
      fun t : ℝ ↦ c • Complex.exp (-s * t) • f t := funext fun t ↦ smul_comm _ _ _
  refine ⟨?_, ?_⟩
  · rw [h]
    exact hf.integrable.smul c
  · rw [h, hf.integrable.integral_smul c, hf.integral_eq]

/-- The constant `1` has no Laplace transform at `s = 0`: its Laplace integrand there is the
constant `1`, which is not integrable on `(0, ∞)`. The totalised integral is `0`, so the
integrability in `HasLaplace` is essential. -/
theorem not_hasLaplace_one_zero (z : ℂ) : ¬HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) 0 z := by
  intro h
  have h1 := h.integrable
  simp only [neg_zero, zero_mul, Complex.exp_zero, smul_eq_mul, mul_one] at h1
  rw [integrable_const_iff] at h1
  rcases h1 with h1 | h1
  · exact one_ne_zero h1
  · have := h1.measure_univ_lt_top
    simp [Real.volume_Ioi] at this

/-- The Laplace transform of `t ↦ t ^ k` is `k! / s ^ (k + 1)` on `0 < Re s`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s (k.factorial / s ^ (k + 1)) := by
  have hk : 0 < ((k : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have h : (fun t : ℝ ↦ Complex.exp (-s * t) • (t : ℂ) ^ k) =
      fun t : ℝ ↦ (t : ℂ) ^ ((k : ℂ) + 1 - 1) * Complex.exp (-(s * t)) := by
    ext t
    rw [add_sub_cancel_right, Complex.cpow_natCast, smul_eq_mul, mul_comm, neg_mul]
  refine ⟨?_, ?_⟩
  · rw [h]
    exact Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hk hs
  · rw [h, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hk hs,
      Complex.Gamma_nat_eq_factorial, Complex.cpow_neg, div_eq_mul_inv]
    norm_cast

/-- The Laplace transform of the constant `1` is `1 / s` on `0 < Re s`. -/
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) : HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) s (1 / s) := by
  simpa using hasLaplace_pow 0 hs

end TauCeti
