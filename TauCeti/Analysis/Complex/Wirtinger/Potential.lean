/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.CauchyKernel
import TauCeti.Analysis.Complex.Pompeiu.Parameter
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Local solutions of the inhomogeneous Cauchy–Riemann equation

The Cauchy transform gives a right inverse for `bar∂` on compactly supported `Cⁿ`
functions into a complex Banach space, for `n ≥ 1`. Cutting off the source inside an
open disc gives a solution on any smaller closed disc, hence near any specified point of an open
domain, with the same regularity.
This supplies integrating factors for scalar Cauchy–Riemann equations.

The construction uses the right-inverse identity in `TauCeti.Analysis.Complex.Pompeiu.Basic`,
where the transform normalized by `(2π)⁻¹` inverts `2 bar∂`.

The same construction works for families. Cut off a family `f`, jointly `C^n` on `s ×ˢ U` for an
open set `U ⊆ ℂ`, by a fixed smooth function of the plane variable which equals `1` near a
compact set `K ⊆ U`. Its normalized transform (`TauCeti.Analysis.Complex.Pompeiu.Parameter`) is
a family `u`, jointly `C^n` on `s ×ˢ univ`, with `bar∂ (u p) = f p` near `K` for every parameter
`p ∈ s`. The cutoff does not depend on the parameter, so `s` need not be shrunk, and `u` is
holomorphic in those parameters in which `f` is. This is the one-variable step of the
`bar∂`-Poincaré lemma on polydiscs, which solves in one conjugate variable while keeping smooth
dependence on some of the other variables and holomorphic dependence on the rest.

## Main results

* `TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq`: a local solution of
  `bar∂ g = f` near a point of the domain of `f`.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_param`: local
  solutions of `bar∂ u = f` depending smoothly on parameters.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param`:
  local solutions depending smoothly on some parameters and holomorphically on the others.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I, Theorem 1.2.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  §§1–2 (the `bar∂`-Poincaré lemma in one and in several variables, where the solution depends
  holomorphically on the remaining variables).
-/

public noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Real Convolution ContDiff

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  {n : ℕ∞}

/-- A compactly supported `Cⁿ` source, for `n ≥ 1`, has a global `Cⁿ` `bar∂` primitive. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport {f : ℂ → W}
    (hn : 1 ≤ n) (hf : ContDiff ℝ n f) (hfc : HasCompactSupport f) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z, conjWirtingerDeriv g z 1 = f z := by
  let T := fun w ↦ (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
  have hT : ContDiff ℝ n T := by
    have hc : ContDiff ℝ n (fun w ↦ ∫ z, (w - z)⁻¹ • f z) := by
      convert hfc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
        Complex.locallyIntegrable_inv hf using 1
      funext w
      simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    exact hc.const_smul _
  refine ⟨fun w ↦ (2 : ℂ) • T w, hT.const_smul _, fun z ↦ ?_⟩
  have he := hfc.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul
    (hf.of_le (by exact_mod_cast hn)) z
  rw [conjWirtingerDeriv_apply, fderiv_fun_const_smul (hT.differentiable (by exact_mod_cast
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))) z) (2 : ℂ)]
  simp only [smul_apply, smul_eq_mul, mul_one]
  rw [smul_comm I (2 : ℂ), ← smul_add, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  exact he

/-- A `Cⁿ` source on an open disc `ball c R`, for `n ≥ 1`, admits a global `Cⁿ` function whose
`bar∂` agrees with the source on any smaller closed disc `closedBall c r`, `0 < r < R`. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq_on_closedBall {f : ℂ → W} {c : ℂ}
    {r R : ℝ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (Metric.ball c R)) (hr : 0 < r) (hrR : r < R) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z ∈ Metric.closedBall c r, conjWirtingerDeriv g z 1 = f z := by
  let χ : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  have hs : tsupport χ ⊆ Metric.ball c R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  have hcut : ContDiff ℝ n (fun w ↦ χ w • f w) := by
    apply contDiff_iff_contDiffAt.mpr
    intro w
    by_cases hw : w ∈ tsupport χ
    · exact (χ.contDiff (n := n)).contDiffAt.smul
        ((hf w (hs hw)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hw)))
    · apply (contDiffAt_const (c := (0 : W))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
      simp [hy]
  obtain ⟨g, hg, heq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport
    hn hcut χ.hasCompactSupport.smul_right
  exact ⟨g, hg, fun z hz ↦ by rw [heq, χ.one_of_mem_closedBall hz, one_smul]⟩

/-- A `Cⁿ` source on an open domain, for `n ≥ 1`, admits a global `Cⁿ` function whose
`bar∂` agrees with the source near any specified point of the domain. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq {f : ℂ → W} {U : Set ℂ}
    (hn : 1 ≤ n) (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) {z : ℂ} (hz : z ∈ U) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ᶠ w in 𝓝 z, conjWirtingerDeriv g w 1 = f w := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  obtain ⟨g, hg, heq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq_on_closedBall hn
    (hf.mono hsub) (half_pos hr) (half_lt_self hr)
  exact ⟨g, hg, eventually_of_mem (Metric.closedBall_mem_nhds z (half_pos hr)) heq⟩

/-! ### Local solutions of `bar∂ u = f` with parameters -/

section LocalSolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {P : Type*} {χ : ℂ → ℝ}
  {U K : Set ℂ}

/-- The family `f` cut off by `χ` in the plane variable and divided by `π`, so that its Cauchy
transform `cutoffTransform χ f` solves `bar∂ u = χ f`. -/
private noncomputable def cutoffFamily (χ : ℂ → ℝ) (f : P → ℂ → F) (p : P) (z : ℂ) : F :=
  ((π : ℂ)⁻¹ * χ z) • f p z

/-- The Cauchy transform `w ↦ ∫ (w - z)⁻¹ • π⁻¹ χ z f p z` of the cut-off family. -/
private noncomputable def cutoffTransform (χ : ℂ → ℝ) (f : P → ℂ → F) (p : P) (w : ℂ) : F :=
  ∫ z, (w - z)⁻¹ • cutoffFamily χ f p z

/-- The cut-off family vanishes off the support of `χ`. -/
private theorem cutoffFamily_eq_zero (f : P → ℂ → F) (p : P) {z : ℂ} (hz : z ∉ tsupport χ) :
    cutoffFamily χ f p z = 0 := by
  simp [cutoffFamily, image_eq_zero_of_notMem_tsupport hz]

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The cut-off family is jointly `Cⁿ` in the parameter and the point, over the whole plane. -/
private theorem contDiffOn_cutoffFamily {f : P → ℂ → F} {s : Set P} (hs : IsOpen s)
    (hU : IsOpen U) (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) :
    ContDiffOn ℝ n ↿(cutoffFamily χ f) (s ×ˢ univ) := by
  rintro ⟨p, z⟩ ⟨hp, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hz : z ∈ tsupport χ
  · have hc : ContDiff ℝ n fun x : P × ℂ ↦ (π : ℂ)⁻¹ * (χ x.2 : ℂ) :=
      contDiff_const.mul (ofRealCLM.contDiff.comp (hχ.comp contDiff_snd))
    exact hc.contDiffAt.smul (hf.contDiffAt ((hs.prod hU).mem_nhds (mk_mem_prod hp (hχU hz))))
  · -- Off the support of `χ`, the family vanishes near `(p, z)`.
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_univ.prod (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (mk_mem_prod (mem_univ p) hz)] with x hx
    exact cutoffFamily_eq_zero f x.1 hx.2

/-- The cut-off transform is jointly `Cⁿ` in the parameter and the point. -/
private theorem contDiffOn_cutoffTransform {f : P → ℂ → F} {s : Set P} (hs : IsOpen s)
    (hU : IsOpen U) (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) :
    ContDiffOn ℝ n ↿(cutoffTransform χ f) (s ×ˢ univ) :=
  contDiffOn_integral_sub_inv_smul_with_param hs hχc.isCompact
    (fun p _ _ hz ↦ cutoffFamily_eq_zero f p hz) (contDiffOn_cutoffFamily hs hU hχ hχU hf)

variable [CompleteSpace F]

/-- The cut-off transform solves `bar∂ u = χ f`. -/
private theorem conjWirtingerDeriv_cutoffTransform {f : P → ℂ → F} {s : Set P} (hn : 1 ≤ n)
    (hs : IsOpen s) (hU : IsOpen U) (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) {p : P} (hp : p ∈ s) (w : ℂ) :
    conjWirtingerDeriv (cutoffTransform χ f p) w 1 = (χ w : ℂ) • f p w := by
  have hg : ContDiff ℝ 1 (cutoffFamily χ f p) :=
    ((contDiffOn_cutoffFamily hs hU hχ hχU hf).comp_contDiff (contDiff_const.prodMk contDiff_id)
      fun z ↦ mk_mem_prod hp (mem_univ z)).of_le (by exact_mod_cast hn)
  have hc : HasCompactSupport (cutoffFamily χ f p) :=
    .intro hχc.isCompact fun z hz ↦ cutoffFamily_eq_zero f p hz
  unfold cutoffTransform
  rw [hc.conjWirtingerDeriv_integral_sub_inv_smul_apply_one hg, cutoffFamily, smul_smul,
    ← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

/-- The cut-off transform of a family holomorphic in a complex parameter is holomorphic in that
parameter. -/
private theorem differentiableAt_cutoffTransform {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℂ Q] {f : Q → ℂ → F} {s : Set Q} (hn : 1 ≤ n) (hs : IsOpen s) (hU : IsOpen U)
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U))
    (hfq : ∀ q ∈ s, ∀ z ∈ U, DifferentiableAt ℂ (fun q ↦ f q z) q) {q : Q} (hq : q ∈ s)
    (w : ℂ) :
    DifferentiableAt ℂ (fun q ↦ cutoffTransform χ f q w) q := by
  refine differentiableAt_integral_sub_inv_smul_with_param hs hχc.isCompact
    (fun q _ _ hz ↦ cutoffFamily_eq_zero f q hz)
    ((contDiffOn_cutoffFamily hs hU hχ hχU hf).of_le (by exact_mod_cast hn)) hq (fun z ↦ ?_) w
  by_cases hz : z ∈ tsupport χ
  · exact (hfq q hq z (hχU hz)).const_smul _
  · exact (differentiableAt_const (0 : F)).congr_of_eventuallyEq
      (.of_forall fun q ↦ cutoffFamily_eq_zero f q hz)

/-- **Local solutions of `bar∂ u = f` with smooth parameters.** Let `f` be a family of maps
`ℂ → F` which is jointly `Cⁿ`, `1 ≤ n`, on `s ×ˢ U` for an open set `s` of parameters and an
open set `U ⊆ ℂ`, and let `K ⊆ U` be compact. Then some family `u`, jointly `Cⁿ` on `s ×ˢ univ`,
satisfies `bar∂ (u p) = f p` near `K` for every `p ∈ s`, on a neighbourhood of `K` independent
of `p`. No shrinking of the parameter domain is needed. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_param {f : P → ℂ → F}
    {s : Set P} (hn : 1 ≤ n) (hs : IsOpen s) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) :
    ∃ u : P → ℂ → F, ContDiffOn ℝ n ↿u (s ×ˢ univ) ∧
      ∀ᶠ z in 𝓝ˢ K, ∀ p ∈ s, conjWirtingerDeriv (u p) z 1 = f p z := by
  obtain ⟨χ, hχ, -, hχK, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  have hχn : ContDiff ℝ n χ := hχ.of_le (by exact_mod_cast le_top)
  refine ⟨cutoffTransform χ f, contDiffOn_cutoffTransform hs hU hχn hχc hχU hf, ?_⟩
  filter_upwards [isOpen_interior.mem_nhdsSet.mpr hχK] with z hz p hp
  have hz1 : χ z = 1 := interior_subset hz
  simp [conjWirtingerDeriv_cutoffTransform hn hs hU hχn hχc hχU hf hp, hz1]

/-- **Local solutions of `bar∂ u = f` with smooth and holomorphic parameters.** Let `f` be a
family of maps `ℂ → F` indexed by `P × Q`, for a real normed space `P` and a complex normed space
`Q`, which is jointly `Cⁿ`, `1 ≤ n`, on `s ×ˢ U` for an open set `s ⊆ P × Q` and an open set
`U ⊆ ℂ`, and holomorphic in `q ∈ Q` at every point of `s ×ˢ U`. Let `K ⊆ U` be compact. Then some
family `u`, jointly `Cⁿ` on `s ×ˢ univ`, satisfies `bar∂ (u x) = f x` near `K` for every `x ∈ s`,
on a neighbourhood of `K` independent of `x`, and is holomorphic in `q` on `s` at every point of
the plane. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {f : P × Q → ℂ → F} {s : Set (P × Q)}
    (hn : 1 ≤ n) (hs : IsOpen s) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U))
    (hfq : ∀ x ∈ s, ∀ z ∈ U, DifferentiableAt ℂ (fun q ↦ f (x.1, q) z) x.2) :
    ∃ u : P × Q → ℂ → F, ContDiffOn ℝ n ↿u (s ×ˢ univ) ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ x ∈ s, conjWirtingerDeriv (u x) z 1 = f x z) ∧
      ∀ x ∈ s, ∀ w, DifferentiableAt ℂ (fun q ↦ u (x.1, q) w) x.2 := by
  obtain ⟨χ, hχ, -, hχK, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  have hχn : ContDiff ℝ n χ := hχ.of_le (by exact_mod_cast le_top)
  refine ⟨cutoffTransform χ f, contDiffOn_cutoffTransform hs hU hχn hχc hχU hf, ?_, ?_⟩
  · filter_upwards [isOpen_interior.mem_nhdsSet.mpr hχK] with z hz x hx
    have hz1 : χ z = 1 := interior_subset hz
    simp [conjWirtingerDeriv_cutoffTransform hn hs hU hχn hχc hχU hf hx, hz1]
  · -- Freeze the smooth parameter `p` and apply the holomorphic statement to the slice.
    rintro ⟨p, q⟩ hx w
    have hι : ContDiff ℝ n fun y : Q × ℂ ↦ ((p, y.1), y.2) :=
      (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
    exact differentiableAt_cutoffTransform (f := fun q z ↦ f (p, q) z) hn
      (hs.preimage (Continuous.prodMk_right p)) hU hχn hχc hχU
      (hf.comp hι.contDiffOn fun y hy ↦ mk_mem_prod hy.1 hy.2)
      (fun q hq z hz ↦ hfq (p, q) hq z hz) hx w

end LocalSolution

end TauCeti
