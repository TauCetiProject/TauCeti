/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Topology.Instances.Real.TSupport

/-!
# Mellin decay on vertical strips

A function of class `C^N` on the positive half-line whose positive closed support
`tsupport f ∩ Ioi 0` is compact
has Mellin transform of size `O((1 + |Im s|)⁻ᴺ)`, uniformly as `Re s` ranges over any
compact set. The Mellin transform integrates only over the positive half-line, so negative-side
support need not be bounded or separated from zero. In particular, smooth functions with compact
positive support separated from zero have decay of every finite order on vertical strips.
This decay is used in absolutely convergent explicit formulas.

A locally integrable function on the positive half-line with compact positive closed support is
Mellin convergent at every exponent, and its Mellin transform is entire. For a `C¹` such function
the Mellin transform divided by `s` is integrable on every vertical line `Re s = σ ≠ 0`, which is
what Mellin inversion of the Mellin transform `mellin f s / s` of the upper tail
`∫_{(x,∞)} f(y) dy/y` requires.

Mellin transforms on vertical lines are Fourier transforms in the logarithmic coordinate.
The estimate holds for complex normed-space targets without assuming completeness.

The finite-order statement is motivated by the `C¹` bump estimate
[MellinOfPsi in PNT+](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a6eae76b4b06abf85b456a5491ff7a983879b9c8/PrimeNumberTheoremAnd/MellinCalculus.lean#L398).
-/

public noncomputable section

open Set MeasureTheory
open scoped FourierTransform

namespace TauCeti

section ComplexSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private lemma contDiff_weighted_log (N : ℕ) {f : ℝ → F} (hf : ContDiffOn ℝ N f (Ioi 0)) :
    ContDiff ℝ N (fun p : ℝ × ℝ ↦
      (Real.exp (-p.1 * p.2) : ℂ) • f (Real.exp (-p.2))) := by
  have he : ContDiff ℝ N (fun p : ℝ × ℝ ↦ (Real.exp (-p.1 * p.2) : ℂ)) := by
    have hr : ContDiff ℝ N (fun p : ℝ × ℝ ↦ Real.exp (-p.1 * p.2)) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp hr
  exact he.smul (hf.comp_contDiff (by fun_prop) (fun _ ↦ Real.exp_pos _))

end ComplexSpace

section Support

variable {F : Type*} [Zero F] [SMulZeroClass ℂ F]

private lemma compact_log_support {f : ℝ → F} (hc : IsCompact (tsupport f ∩ Ioi 0)) :
    ∃ S : Set ℝ, IsCompact S ∧ ∀ σ : ℝ,
      tsupport (fun u ↦ (Real.exp (-σ * u) : ℂ) • f (Real.exp (-u))) ⊆ S := by
  let S : Set ℝ := (fun x ↦ -Real.log x) '' (tsupport f ∩ Ioi 0)
  have hS : IsCompact S := hc.image_of_continuousOn
    (Real.continuousOn_log.neg.mono fun x hx ↦ ne_of_gt hx.2)
  refine ⟨S, hS, fun σ ↦ closure_minimal ?_ hS.isClosed⟩
  intro u hu
  have hn : f (Real.exp (-u)) ≠ 0 := by
    intro h
    exact hu (by simp [h])
  refine ⟨Real.exp (-u), ⟨subset_closure hn, Real.exp_pos _⟩, ?_⟩
  simp

end Support

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma angular_mellin_bound (f : ℝ → E) (s : ℂ) (N : ℕ) {B : ℝ}
    (hB : (1 + ‖(2 * Real.pi)⁻¹ * s.im‖) ^ N *
      ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u)))
        ((2 * Real.pi)⁻¹ * s.im)‖ ≤ B) :
    (1 + |s.im|) ^ N * ‖mellin f s‖ ≤ (2 * Real.pi) ^ N * B := by
  let w : ℝ := (2 * Real.pi)⁻¹ * s.im
  have hw : |s.im| = (2 * Real.pi) * ‖w‖ := by
    dsimp [w]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hscale : 1 + |s.im| ≤ (2 * Real.pi) * (1 + ‖w‖) := by
    rw [hw]
    nlinarith [Real.two_le_pi]
  simp_rw [mellin_eq_fourier, div_eq_mul_inv, mul_comm s.im, ← Complex.coe_smul]
  calc
    _ ≤ ((2 * Real.pi) * (1 + ‖w‖)) ^ N *
        ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) w‖ := by
      gcongr
    _ = (2 * Real.pi) ^ N * ((1 + ‖w‖) ^ N *
        ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) w‖) := by rw [mul_pow]; ring
    _ ≤ (2 * Real.pi) ^ N * B := mul_le_mul_of_nonneg_left hB (by positivity)

end Scaling

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma weighted_log_family_data {N : ℕ} {f : ℝ → E}
    (hf : ContDiffOn ℝ N f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0))
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ S : Set ℝ, IsCompact S ∧ ∃ C > 0,
      (∀ σ : ℝ, tsupport (fun u ↦ (Real.exp (-σ * u) : ℂ) • f (Real.exp (-u))) ⊆ S) ∧
      (∀ σ ∈ K, ∀ n ≤ N, ∀ u,
        ‖iteratedFDeriv ℝ n (fun v ↦ (Real.exp (-σ * v) : ℂ) • f (Real.exp (-v))) u‖ ≤ C) := by
  obtain ⟨S, hS, hsupp⟩ := compact_log_support hc
  have hH := contDiff_weighted_log N hf
  obtain ⟨D, hD, hbound⟩ := hH.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    isOpen_univ (hK.prod hS) (subset_univ _)
  refine ⟨S, hS, D + 1, by positivity, hsupp, fun σ hσ n hn u ↦ ?_⟩
  by_cases hu : u ∈ S
  · exact (hH.contDiffAt.norm_iteratedFDeriv_prod_right_le n (by exact_mod_cast hn)).trans
      ((hbound n hn (σ, u) ⟨hσ, hu⟩).trans (le_add_of_nonneg_right zero_le_one))
  · have hz : iteratedFDeriv ℝ n (fun v ↦
        (Real.exp (-σ * v) : ℂ) • f (Real.exp (-v))) u = 0 := by
      apply Function.notMem_support.mp
      intro hm
      exact hu (hsupp σ (support_iteratedFDeriv_subset n hm))
    rw [hz, norm_zero]
    positivity

end Family

section Endpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If a function is `C^N` on the positive half-line and its positive closed support is compact,
its Mellin transform decays
with order `N` in the imaginary direction, uniformly over any compact set of real parts.
No restriction on the negative-side values or regularity is required. -/
theorem exists_one_add_abs_im_pow_mul_norm_mellin_le {N : ℕ} {f : ℝ → E}
    (hf : ContDiffOn ℝ N f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0))
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ K → (1 + |s.im|) ^ N * ‖mellin f s‖ ≤ C := by
  obtain ⟨S, hS, D, hD, hsupp, hbound⟩ := weighted_log_family_data hf hc hK
  let C : ℝ := (2 * Real.pi) ^ N * (2 ^ N * (D * volume.real S))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1 + C, add_pos_of_pos_of_nonneg zero_lt_one hC, fun s hs ↦ ?_⟩
  let w : ℝ := (2 * Real.pi)⁻¹ * s.im
  have hg : ContDiff ℝ N (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) := by
    have ht : ContDiff ℝ N (fun u : ℝ ↦ (s.re, u)) :=
      contDiff_const.prodMk contDiff_id
    exact (contDiff_weighted_log N hf).comp ht
  have hfinite : volume S ≠ ⊤ := hS.measure_lt_top.ne
  have hfour : (1 + ‖w‖) ^ N *
      ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) w‖ ≤
        2 ^ N * (D * volume.real S) :=
    TauCeti.one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset hg hfinite
      (hsupp s.re) (hbound s.re hs) w
  exact (angular_mellin_bound f s N hfour).trans (by dsimp [C]; linarith)

end Endpoint

section CompactPositiveSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function locally integrable on `(0, ∞)` whose positive closed support `tsupport f ∩ Ioi 0`
is compact is Mellin convergent at every exponent. -/
theorem mellinConvergent_of_isCompact_tsupport {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0)) (s : ℂ) :
    MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hf
    ((eventuallyEq_zero_atTop_of_isCompact_tsupport_inter_Ioi hc).trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)
    ((eventuallyEq_zero_nhdsGT_of_isCompact_tsupport_inter_Ioi hc).trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)

/-- The Mellin transform of a function locally integrable on `(0, ∞)` with compact positive closed
support is entire. -/
theorem differentiable_mellin_of_isCompact_tsupport {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0)) :
    Differentiable ℂ (mellin f) := fun s ↦
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hf
    ((eventuallyEq_zero_atTop_of_isCompact_tsupport_inter_Ioi hc).trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)
    ((eventuallyEq_zero_nhdsGT_of_isCompact_tsupport_inter_Ioi hc).trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)

/-- For a `C¹` function on `(0, ∞)` with compact positive closed support, `s ↦ mellin f s / s` is
integrable on every vertical line `Re s = σ` with `σ ≠ 0`: the transform decays like `|Im s|⁻¹`
and `1 / s` supplies a second factor `|Im s|⁻¹`. -/
theorem verticalIntegrable_mellin_div {f : ℝ → ℂ} (hf : ContDiffOn ℝ 1 f (Ioi 0))
    (hc : IsCompact (tsupport f ∩ Ioi 0)) {σ : ℝ} (hσ : σ ≠ 0) :
    Complex.VerticalIntegrable (fun s ↦ mellin f s / s) σ := by
  obtain ⟨C, hC0, hC⟩ := exists_one_add_abs_im_pow_mul_norm_mellin_le hf hc
    (isCompact_singleton (x := σ))
  have hσ0 : 0 < |σ| := abs_pos.mpr hσ
  have hs0 (t : ℝ) : (σ : ℂ) + t * Complex.I ≠ 0 := fun h ↦
    hσ (by simpa using congrArg Complex.re h)
  let K : ℝ := C * (1 + |σ|) / |σ|
  refine ((integrable_inv_one_add_sq.const_mul K).mono' ?_ (Filter.Eventually.of_forall
    fun t ↦ ?_))
  · exact ((differentiable_mellin_of_isCompact_tsupport
      (hf.continuousOn.locallyIntegrableOn measurableSet_Ioi) hc).continuous.comp
      (by fun_prop)).div (by fun_prop) hs0 |>.aestronglyMeasurable
  · set s : ℂ := (σ : ℂ) + t * Complex.I
    have hm : (1 + |t|) * ‖mellin f s‖ ≤ C := by simpa [s] using hC s (by simp [s])
    have hre : |σ| ≤ ‖s‖ := by simpa [s] using Complex.abs_re_le_norm s
    have him : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
    have hsn : 0 < ‖s‖ := hσ0.trans_le hre
    have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have hlin : (1 + |t|) * |σ| ≤ ‖s‖ * (1 + |σ|) := by nlinarith [abs_nonneg σ]
    have key : ‖mellin f s‖ * (1 + t ^ 2) ≤ K * ‖s‖ := calc
      ‖mellin f s‖ * (1 + t ^ 2) ≤ ‖mellin f s‖ * (1 + |t|) ^ 2 := by gcongr
      _ = ((1 + |t|) * ‖mellin f s‖) * (1 + |t|) := by ring
      _ ≤ C * (1 + |t|) := by gcongr
      _ ≤ K * ‖s‖ := by
        rw [show K * ‖s‖ = C * (‖s‖ * (1 + |σ|)) / |σ| by ring, le_div_iff₀ hσ0, mul_assoc]
        gcongr
    rw [norm_div, div_le_iff₀ hsn, mul_right_comm, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    exact key

end CompactPositiveSupport

end TauCeti
