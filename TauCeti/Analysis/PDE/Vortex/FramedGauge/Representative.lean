/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries

/-!
# Sobolev representatives of smooth framed vortices

The framed degree-`m` plane vortex fields of the Sobolev model form the affine space
`A_m^s = x_ref + H^s(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), centered at a smooth
reference pair equal to `(-i m dθ, (z / |z|)^m)` outside a disc. A smooth vortex with the
degree-`m` end framing `α (z / |z|)^(-m) → 1` need not lie in `A_m^s`: its phase may approach the
winding phase only like `1 / |z|`, which is not square integrable. This file shows that every
such vortex is carried into `A_m^s`, for every order `s` at once, by a smooth framed gauge
transformation (`TauCeti.Vortex.exists_framedGaugeGroup_forall_smul_mem_framedFieldSpace`). Since
two fields of `A_m^k`, `k ≥ 2`, related by a smooth framed gauge are related by an element of
the Sobolev gauge group `G_(k+1)` (`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`),
the smooth framed gauge orbits of smooth framed vortices are thereby compared with the
`G_(k+1)`-orbits of vortices in `A_m^k`.

The gauge is the one making the section `|α|` times the winding phase outside a compact set
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). For such an end-normalized
vortex, the end trivialization by the inverse winding phase has the positive real section `|α|`,
and the holomorphicity rows of the vortex equation then determine its connection from
`ℓ = log |α|²`. Outside a large disc,

`x - x_ref = (-∂_t ℓ / 2, ∂_s ℓ / 2, x_ref,₂ (exp (ℓ / 2) - 1), x_ref,₃ (exp (ℓ / 2) - 1))`

in the coordinates `x = (b₁, b₂, p, q)` with `a = i (b₁ ds + b₂ dt)`, `α = 2 (p + i q)`. A cutoff
`v` of `ℓ` vanishing near the zeros of `α` solves `Δv = (exp v - 1) / 4 + g` with `g` smooth and
compactly supported, by the scalar equation `Δ log |α|² = (|α|² - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`). It is bounded and square integrable,
since `|v| ≤ 2 (1 - |α|²)` and the modulus defect is integrable
(`TauCeti.Vortex.integrable_one_sub_normSq`). Elliptic regularity for this semilinear equation
(`TemperedDistribution.mem_realSobolevFunctions_of_laplacian_eq_mul_exp_sub_one_add`) puts `v`
in every `H^s`, and then each coordinate of `x - x_ref` lies in `H^s`: the connection part as a
derivative of `v`, and the section part because `H^s(ℂ)` is closed under `w ↦ exp (w / 2) - 1`
for `s > 1` and under multiplication by the reference coefficients, which have bounded
derivatives.

## Main results

* `TauCeti.Vortex.mem_framedFieldSpace_of_eventually_sectionValue_eq`: a smooth vortex with
  `|α| → 1` whose section is `|α|` times the winding phase outside a compact set lies in `A_m^s`
  for every `s`.
* `TauCeti.Vortex.exists_framedGaugeGroup_forall_smul_mem_framedFieldSpace`: every smooth framed
  degree-`m` vortex has a smooth framed gauge transform lying in `A_m^s` for every `s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory TemperedDistribution
open scoped Topology ContDiff Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- **The end trivialization of an end-normalized vortex.** At a point `z` outside the cutoff
disc, near which the section of `x` is `|α|` times the winding phase, and at which `α ≠ 0` and
the vortex equation holds, the difference between `x` and the reference field is determined by
`ℓ = log |α|²`: its connection part is `(-∂_t ℓ / 2, ∂_s ℓ / 2)`, and its section part is the
reference section times `|α| - 1`. -/
private theorem sub_referenceField_apply_eq (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2) (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z)
    (hsol : equation x z = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0) :
    x z 0 - referenceField f m z 0 =
        -fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I / 2 ∧
      x z 1 - referenceField f m z 1 =
        fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 / 2 ∧
      x z 2 - referenceField f m z 2 = referenceField f m z 2 * (‖sectionValue x z‖ - 1) ∧
      x z 3 - referenceField f m z 3 = referenceField f m z 3 * (‖sectionValue x z‖ - 1) := by
  have hz₀ := ne_zero_of_rOut_le_norm_sq f hrOut
  set u : ℂ → Circle := (windingPhase m)⁻¹
  have hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z := by
    simp only [u, Pi.inv_apply, Circle.coe_inv_eq_conj]
    exact conjCLE.contDiff.contDiffAt.comp z (contDiffAt_windingPhase m hz₀)
  have hud := hu.differentiableAt (by norm_num)
  set y := gaugeTransform u x
  have hsoly : equation y z = 0 := (equation_gaugeTransform_eq_zero_iff hu hx).2 hsol
  have hRe (x' : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) : (sectionValue x' w).re = 2 * x' w 2 := by
    simp [sectionValue_apply]
  have hIm (x' : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) : (sectionValue x' w).im = 2 * x' w 3 := by
    simp [sectionValue_apply]
  -- The end trivialization `y` has the real section `|α|` near `z`.
  have hsec : ∀ᶠ w in 𝓝 z, sectionValue y w = ‖sectionValue x w‖ :=
    hphase.mono fun w hw ↦ sectionValue_gaugeTransform_inv_windingPhase hw
  have hy3 : (fun w ↦ y w 3) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := hsec.mono fun w hw ↦ by
    have h := congrArg Complex.im hw
    rw [hIm, ofReal_im] at h
    linarith
  have hy2 : y z 2 = ‖sectionValue x z‖ / 2 := by
    have h := congrArg Complex.re hsec.self_of_nhds
    rw [hRe, ofReal_re] at h
    linarith
  have hy3z : y z 3 = 0 := hy3.self_of_nhds
  have hdy3 : fderiv ℝ (fun w ↦ y w 3) z = 0 := by rw [hy3.fderiv_eq, fderiv_const_apply]
  have hre : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).re) z := reCLM.differentiableAt.comp z hud
  have him : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).im) z := imCLM.differentiableAt.comp z hud
  have hp : DifferentiableAt ℝ (fun w ↦ y w 2) z := by
    simp only [y, gaugeTransform_apply]
    exact (hre.mul (hx 2)).sub (him.mul (hx 3))
  have hq : DifferentiableAt ℝ (fun w ↦ y w 3) z := by
    simp only [y, gaugeTransform_apply]
    exact (him.mul (hx 2)).add (hre.mul (hx 3))
  have hnorm : ‖sectionValue x z‖ ≠ 0 := norm_ne_zero_iff.2 hα
  have hαy : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0 := by
    rw [hy2, hy3z]
    positivity
  -- `log |α|²` is gauge invariant.
  have hℓ : (fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))) =
      fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by
    ext w
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue, sectionValue_gaugeTransform, norm_mul,
      Circle.norm_coe, one_mul]
  have h₁ : equation y z 1 = 0 := by rw [hsoly]; rfl
  have h₂ : equation y z 2 = 0 := by rw [hsoly]; rfl
  have hd1 := fderiv_log_normSq_apply_one hp hq hαy h₁ h₂
  have hdI := fderiv_log_normSq_apply_I hp hq hαy h₁ h₂
  rw [hℓ, hdy3, hy3z] at hd1 hdI
  simp only [zero_apply, mul_zero, zero_mul, neg_zero, zero_div, zero_add,
    zero_sub] at hd1 hdI
  -- The reference field in the end trivialization is the vacuum.
  have href := gaugeTransform_inv_windingPhase_referenceField f m hrOut
  have href0 : referenceField f m z 0 - gaugeForm u z 1 = 0 := by
    simpa [gaugeTransform_apply, vacuumField_apply, -gaugeForm_apply] using
      congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v 0) href
  have href1 : referenceField f m z 1 - gaugeForm u z I = 0 := by
    simpa [gaugeTransform_apply, vacuumField_apply, -gaugeForm_apply] using
      congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v 1) href
  have hy0 : y z 0 = x z 0 - gaugeForm u z 1 := by simp [y, gaugeTransform_apply]
  have hy1 : y z 1 = x z 1 - gaugeForm u z I := by simp [y, gaugeTransform_apply]
  -- The section coordinates.
  have hsx := hphase.self_of_nhds
  have hrs : referenceSection f m z = windingPhase m z := by
    rw [referenceSection_eq_phase f m hrOut, coe_windingPhase m hz₀]
  have hx2 : x z 2 = ‖sectionValue x z‖ * (windingPhase m z : ℂ).re / 2 := by
    have h := congrArg Complex.re hsx
    rw [hRe, re_ofReal_mul] at h
    linarith
  have hx3 : x z 3 = ‖sectionValue x z‖ * (windingPhase m z : ℂ).im / 2 := by
    have h := congrArg Complex.im hsx
    rw [hIm, im_ofReal_mul] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdI]
    linarith
  · rw [hd1]
    linarith
  · simp only [referenceField_apply, Fin.isValue, Matrix.cons_val, hrs, hx2]
    ring
  · simp only [referenceField_apply, Fin.isValue, Matrix.cons_val, hrs, hx3]
    ring

/-- **A Sobolev cutoff of `log |α|²`.** Let `x` be a smooth plane vortex with `|α| → 1` at
infinity, and let `R ≥ 0` be such that `|α|² > 1 / 2` outside the disc of radius `R`. Then some
smooth function `v` lying in every `H^s` agrees with `ℓ = log |α|²` near every point outside the
disc of radius `R + 2`. -/
private theorem exists_forall_mem_realSobolevFunctions_eventuallyEq_log_normSq
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ z : ℂ, R < ‖z‖ → 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧ (∀ s, v ∈ realSobolevFunctions ℂ s 2) ∧
      ∀ z : ℂ, R + 2 < ‖z‖ → v =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hxd (i : Fin 4) (z : ℂ) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    (hxi i).differentiable (by simp) z
  set n : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  set ℓ : ℂ → ℝ := fun z ↦ Real.log (n z)
  have hn : ContDiff ℝ ∞ n := contDiff_const.mul (((hxi 2).pow 2).add ((hxi 3).pow 2))
  have hn1 (z : ℂ) : n z ≤ 1 :=
    normSq_le_one_of_tendsto ((hxi 0).differentiable (by simp)) ((hxi 1).differentiable (by simp))
      ((hxi 2).of_le (by norm_cast)) ((hxi 3).of_le (by norm_cast)) hsol hlim z
  have hn0 (z : ℂ) : 0 ≤ n z := by positivity
  -- The cutoff `v = (1 - b) ℓ` of `ℓ = log |α|²`, vanishing on the disc of radius `R + 1`.
  let b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  set v : ℂ → ℝ := fun z ↦ (1 - b z) * ℓ z
  have hvnear (z : ℂ) (hz : ‖z‖ < R + 1) : v =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    simp [v, b.one_of_mem_closedBall (ball_subset_closedBall hw)]
  have hvfar (z : ℂ) (hz : R + 2 < ‖z‖) : v =ᶠ[𝓝 z] ℓ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    have hb : b w = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact le_of_lt hw)
    simp [v, hb]
  have hℓ (z : ℂ) (hz : R < ‖z‖) : ContDiffAt ℝ ∞ ℓ z :=
    hn.contDiffAt.log (by linarith [(hR z hz)])
  have hv : ContDiff ℝ ∞ v := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : ‖z‖ < R + 1
    · exact contDiffAt_const.congr_of_eventuallyEq (hvnear z hz)
    · exact ((contDiff_const.sub b.contDiff).contDiffAt).mul (hℓ z (by linarith))
  -- `|v| ≤ 2 (1 - |α|²)`.
  have hvbound (z : ℂ) : |v z| ≤ 2 * (1 - n z) := by
    by_cases hz : ‖z‖ < R + 1
    · rw [(hvnear z hz).self_of_nhds, abs_zero]
      linarith [hn1 z]
    · have hnz := (hR z (by linarith))
      have hlog : |ℓ z| ≤ 2 * (1 - n z) := by
        have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 (by linarith : 0 < n z))
        rw [Real.log_inv] at h1
        rw [abs_of_nonpos (Real.log_nonpos (hn0 z) (hn1 z))]
        have h2 : (n z)⁻¹ - 1 ≤ 2 * (1 - n z) := by
          rw [inv_eq_one_div, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
          nlinarith [hn1 z]
        linarith
      have hb0 := b.nonneg (x := z)
      have hb1 := b.le_one (x := z)
      calc |v z| = |1 - b z| * |ℓ z| := abs_mul _ _
        _ ≤ 1 * (2 * (1 - n z)) := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
        _ = 2 * (1 - n z) := one_mul _
  -- `v` is bounded and square integrable, since `1 - |α|²` is integrable and at most one.
  have hdef : MemLp (fun z ↦ 1 - n z) 2 volume := by
    have hc : Continuous fun z ↦ 1 - n z := continuous_const.sub hn.continuous
    refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 ?_
    refine (integrable_one_sub_normSq volume ((hxi 0).differentiable (by simp))
      ((hxi 1).differentiable (by simp)) ((hxi 2).of_le (by norm_cast))
      ((hxi 3).of_le (by norm_cast)) hsol hlim).mono (hc.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by linarith [hn1 z])]
    nlinarith [hn1 z, hn0 z]
  have hv2 : MemLp v 2 volume :=
    (hdef.const_mul 2).of_le hv.continuous.aestronglyMeasurable (Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * (1 - n z) by linarith [hn1 z])]
      exact hvbound z)
  have hvC (z : ℂ) : |v z| ≤ 2 := (hvbound z).trans (by linarith [hn0 z])
  -- `v` solves `Δv = (exp v - 1) / 4 + g` with `g` smooth and compactly supported.
  set g : ℂ → ℝ := fun z ↦ Δ v z - 1 / 4 * (Real.exp (v z) - 1) with hg_def
  have hgc : ContDiff ℝ ∞ g :=
    (hv.laplacian (m := ∞) (by simp)).sub
      (contDiff_const.mul ((Real.contDiff_exp.comp hv).sub contDiff_const))
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (R + 2)) fun z hz ↦ ?_
    have hz' : R + 2 < ‖z‖ := by simpa using hz
    have hnz := (hR z (by linarith))
    have hΔ : Δ v z = (n z - 1) / 4 := by
      rw [(InnerProductSpace.laplacian_congr_nhds (hvfar z hz')).eq_of_nhds]
      exact laplacian_log_normSq_of_equation_eq_zero (hxd 0 z) (hxd 1 z)
        ((hxi 2).contDiffAt.of_le (by norm_cast)) ((hxi 3).contDiffAt.of_le (by norm_cast))
        (by linarith) (Eventually.of_forall hsol)
    have hvz : v z = ℓ z := (hvfar z hz').self_of_nhds
    simp only [g, hΔ, hvz, ℓ, Real.exp_log (by linarith : 0 < n z)]
    ring
  have hvS : ∀ s, v ∈ realSobolevFunctions ℂ s 2 :=
    mem_realSobolevFunctions_of_laplacian_eq_mul_exp_sub_one_add (c := 1 / 4)
      (by rw [Complex.finrank_real_complex]; norm_num) (hv.of_le (by norm_cast)) hv2 hvC
      (mem_realSobolevFunctions_of_hasCompactSupport hgc hgs) fun z ↦ by rw [hg_def]; ring
  exact ⟨v, hv, hvS, hvfar⟩

/-- **End-normalized vortices lie in every Sobolev field space.** Let `x` be a smooth plane
vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then `x` lies in the affine space `A_m^s` of framed degree-`m` fields for
every order `s`: `x - x_ref ∈ H^s`. -/
theorem mem_framedFieldSpace_of_eventually_sectionValue_eq (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (s : ℝ) : x ∈ framedFieldSpace f m s := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hxd (i : Fin 4) (z : ℂ) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    (hxi i).differentiable (by simp) z
  -- A radius beyond which the section is end-normalized, `|α|² > 1 / 2`, and the reference
  -- field is the winding pair.
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, R < ‖z‖ →
      (∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) ∧
        1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧ f.rOut ≤ ‖z‖ ^ 2 := by
    have H := hphase.and ((hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))).and
      (tendsto_norm_cocompact_atTop.eventually_gt_atTop (max 1 f.rOut)))
    obtain ⟨R₀, -, hR₀⟩ :=
      hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ H)
    refine ⟨max R₀ 0, le_max_right _ _, fun z hz ↦ ⟨?_, (hR₀ (show R₀ ≤ ‖z‖ by
      linarith [le_max_left R₀ 0])).2.1, rOut_le_norm_sq f (hR₀ (show R₀ ≤ ‖z‖ by
      linarith [le_max_left R₀ 0])).2.2⟩⟩
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact (hR₀ (show R₀ ≤ ‖w‖ by linarith [le_max_left R₀ 0, show max R₀ 0 < ‖w‖ from hw])).1
  obtain ⟨v, hv, hvS, hvfar⟩ := exists_forall_mem_realSobolevFunctions_eventuallyEq_log_normSq
    hx hsol hlim hR0 fun z hz ↦ (hR z hz).2.1
  -- Outside the disc of radius `R + 2`, `x - x_ref` is read off from `v`.
  have hfar (z : ℂ) (hz : R + 2 < ‖z‖) :
      x z 0 - referenceField f m z 0 = -fderiv ℝ v z I / 2 ∧
        x z 1 - referenceField f m z 1 = fderiv ℝ v z 1 / 2 ∧
        x z 2 - referenceField f m z 2 = referenceField f m z 2 * (Real.exp (v z / 2) - 1) ∧
        x z 3 - referenceField f m z 3 = referenceField f m z 3 * (Real.exp (v z / 2) - 1) := by
    obtain ⟨hph, hnz, hrOut⟩ := hR z (by linarith)
    have hα : sectionValue x z ≠ 0 := fun h ↦ by
      have := sq_norm_sectionValue x z
      rw [h, norm_zero] at this
      linarith
    have hexp : Real.exp (v z / 2) = ‖sectionValue x z‖ := by
      rw [(hvfar z hz).self_of_nhds]
      simp only [← sq_norm_sectionValue, Real.log_pow]
      rw [Nat.cast_ofNat, mul_div_cancel_left₀ _ two_ne_zero,
        Real.exp_log (norm_pos_iff.2 hα)]
    have hd := (hvfar z hz).fderiv_eq (𝕜 := ℝ)
    obtain ⟨h0, h1, h2, h3⟩ := sub_referenceField_apply_eq f hrOut (fun i ↦ hxd i z) (hsol z)
      hph hα
    exact ⟨by rw [hd]; exact h0, by rw [hd]; exact h1, by rw [hexp]; exact h2,
      by rw [hexp]; exact h3⟩
  -- A coordinate of `x - x_ref` lies in `H^s` once it agrees far out with a smooth function in
  -- every `H^s`.
  have key (i : Fin 4) (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F)
      (hFs : ∀ s, F ∈ realSobolevFunctions ℂ s 2)
      (hFeq : ∀ z, R + 2 < ‖z‖ → x z i - referenceField f m z i = F z) :
      (fun z ↦ (x - referenceField f m) z i) ∈ realSobolevFunctions ℂ s 2 := by
    set D : ℂ → ℝ := fun z ↦ x z i - referenceField f m z i - F z
    have hD : ContDiff ℝ ∞ D :=
      ((hxi i).sub (contDiff_euclidean.1 (contDiff_referenceField f m) i)).sub hF
    have hDc : HasCompactSupport D :=
      HasCompactSupport.intro (isCompact_closedBall 0 (R + 2)) fun z hz ↦ by
        simp only [D, hFeq z (by simpa using hz), sub_self]
    have h := add_mem (mem_realSobolevFunctions_of_hasCompactSupport hD hDc s) (hFs s)
    convert h using 1
    ext z
    simp [D]
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_cast)
  have hdv (u : ℂ) : ContDiff ℝ ∞ fun z ↦ fderiv ℝ v z u :=
    (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdvS (u : ℂ) (s : ℝ) : (fun z ↦ fderiv ℝ v z u) ∈ realSobolevFunctions ℂ s 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (le_max_left s 0)
      (fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (le_max_right s 0) hv1
        (hvS _) u)
  have hexpS (i : Fin 4) (s : ℝ) : (fun z ↦ referenceField f m z i * (Real.exp (v z / 2) - 1)) ∈
      realSobolevFunctions ℂ s 2 := by
    obtain ⟨k, hk⟩ := exists_nat_ge (max s 2)
    have hk2 : (Module.finrank ℝ ℂ : ℝ) < 2 * k := by
      rw [Complex.finrank_real_complex]
      push_cast
      linarith [le_max_right s 2]
    have he : (fun z ↦ Real.exp (v z / 2) - 1) ∈ realSobolevFunctions ℂ k 2 := by
      simpa only [one_div_mul_eq_div] using
        exp_mul_sub_one_mem_realSobolevFunctions hk2 (hvS k) (1 / 2)
    exact realSobolevFunctions_mono (by norm_num) (by norm_num) ((le_max_left s 2).trans hk)
      (mul_mem_realSobolevFunctions_of_bounded_derivatives (by norm_num) (by norm_num) k
        (contDiff_euclidean.1 (contDiff_referenceField f m) i)
        (fun j _ ↦ exists_norm_iteratedFDeriv_referenceField_apply_le f m i j) he)
  have hexpC (i : Fin 4) :
      ContDiff ℝ ∞ (fun z ↦ referenceField f m z i * (Real.exp (v z / 2) - 1)) :=
    (contDiff_euclidean.1 (contDiff_referenceField f m) i).mul
      ((Real.contDiff_exp.comp (hv.div_const 2)).sub contDiff_const)
  rw [mem_framedFieldSpace, mem_sobolevFields]
  intro i
  fin_cases i
  · exact key 0 (fun z ↦ -fderiv ℝ v z I / 2) ((hdv I).neg.div_const 2)
      (fun s ↦ by
        convert Submodule.smul_mem _ (-(1 / 2) : ℝ) (hdvS I s) using 1
        ext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring)
      fun z hz ↦ (hfar z hz).1
  · exact key 1 (fun z ↦ fderiv ℝ v z 1 / 2) ((hdv 1).div_const 2)
      (fun s ↦ by
        convert Submodule.smul_mem _ (1 / 2 : ℝ) (hdvS 1 s) using 1
        ext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring)
      fun z hz ↦ (hfar z hz).2.1
  · exact key 2 _ (hexpC 2) (hexpS 2) fun z hz ↦ (hfar z hz).2.2.1
  · exact key 3 _ (hexpC 3) (hexpS 3) fun z hz ↦ (hfar z hz).2.2.2

/-- **Every smooth framed vortex has a representative in every Sobolev field space.** A smooth
plane vortex with the degree-`m` end framing `α (z / |z|)^(-m) → 1` is carried by a smooth framed
gauge transformation into the affine space `A_m^s` of framed degree-`m` fields, for every order
`s` at once. The gauge makes the section `|α|` times the winding phase outside a compact set. -/
theorem exists_framedGaugeGroup_forall_smul_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ∀ s, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  refine ⟨u, fun s ↦ ?_⟩
  have huc := ((mem_framedGaugeGroup _).1 u.property).1
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim : Tendsto (fun z ↦ 4 * ((u • x) z 2 ^ 2 + (u • x) z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    refine (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ ?_
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue, framedGaugeGroup_smul,
      sectionValue_gaugeTransform, norm_mul, Circle.norm_coe, one_mul]
  exact mem_framedFieldSpace_of_eventually_sectionValue_eq f (contDiff_gaugeTransform huc hx)
    hsol' hlim hu s

end TauCeti.Vortex
