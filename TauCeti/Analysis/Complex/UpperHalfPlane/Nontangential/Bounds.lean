/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential
import Mathlib.Analysis.Normed.Group.Indicator

/-!
# Weak and strong type bounds for the nontangential maximal function of Poisson integrals

The nontangential maximal function of the Poisson integral of `|g| dx` is dominated by a multiple
of the Hardy–Littlewood maximal function of `g`
(`TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le`), so the maximal
inequalities on `ℝ` transfer to it:

* **Strong type.** For `1 < p`, `∫ (M^α_h P[|g| dx]) ^ p ≤ C ^ p K_p ∫ |g| ^ p`, where
  `C = max 2 (1 + 2 α ^ 2)` (`3` for `α = 1`) and `K_p = maximalFunctionConst 1 p` is the constant
  of the strong type bound for the maximal function on `ℝ`.
* **Weak type.** `t |{M^α_h P[|g| dx] > t}| ≤ 4 C ∫ |g|`.

For `g ∈ L¹(Π)`, where `Π = dx / (1 + x ^ 2)` is the Poisson measure, the maximal function need not
be finite, and the bound is localised:

* **Localisation.** For `|x| ≤ R` and `z` in the cone `Γ_1(x) = {|Re z - x| < Im z < 1}`,
  `P[|g| dx](z) ≤ 3 M(g 1_{[-R-2, R+2]})(x) + (2 (R + 2) ^ 2 / π) ‖g‖_{L¹(Π)}`.
* **Local weak type.** There is `C_R`, depending only on `R`, with
  `t |{x ∈ [-R, R] : M_1 P[|g| dx](x) > t}| ≤ C_R ‖g‖_{L¹(Π)}`.

## Main results

* `TauCeti.lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le`: the
  strong type bound.
* `TauCeti.mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le`: the
  weak type bound.
* `TauCeti.nontangentialMaximalFunction_one_one_upperHalfPlanePoissonLIntegral_le`: the
  localisation for functions in `L¹(Π)`.
* `TauCeti.exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le`:
  the local weak type bound for functions in `L¹(Π)`.

Each of these has a counterpart, named with `upperHalfPlanePoissonIntegral` in place of
`upperHalfPlanePoissonLIntegral`, for the Poisson integral `P[‖g‖ dx]`, whose norm is at most the
extended Poisson integral on the closed upper half-plane.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §4.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286
  (2022), Lemmas 5 and 6 and Corollary 1.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory Set

open scoped Real ENNReal

/-- The nontangential maximal function of the Poisson integral is at most that of the extended
Poisson integral. -/
private theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_lIntegral (α : ℝ)
    (h : ℝ≥0∞) (ν : Measure ℝ) (x : ℝ) :
    nontangentialMaximalFunction α h (upperHalfPlanePoissonIntegral ν) x ≤
      nontangentialMaximalFunction α h (upperHalfPlanePoissonLIntegral ν) x :=
  nontangentialMaximalFunction_mono_fun fun z hz => by
    simpa using enorm_upperHalfPlanePoissonIntegral_le ν (mem_nontangentialCone.1 hz).1.le

section Global

variable {F : Type*} [ENorm F]

/-- **The strong type bound for the nontangential maximal function.** For `1 < p`,
`∫ (M^α_h P[|g| dx]) ^ p ≤ C ^ p K_p ∫ |g| ^ p` with `C = max 2 (1 + 2 α ^ 2)` and `K_p` the
constant of the strong type bound for the Hardy–Littlewood maximal function on `ℝ`. -/
theorem lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le (α : ℝ)
    (h : ℝ≥0∞) {g : ℝ → F} (hg : AEMeasurable (fun x => ‖g x‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, nontangentialMaximalFunction α h
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ^ p ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) ^ p * maximalFunctionConst 1 p *
        ∫⁻ x, ‖g x‖ₑ ^ p := by
  set C := ENNReal.ofReal (max 2 (1 + 2 * α ^ 2))
  have hp0 : 0 ≤ p := by linarith
  calc ∫⁻ x, nontangentialMaximalFunction α h
          (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ^ p
      ≤ ∫⁻ x, C ^ p * maximalFunction volume g x ^ p := lintegral_mono fun x => by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact ENNReal.rpow_le_rpow
          (nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α h g x) hp0
    _ = C ^ p * ∫⁻ x, maximalFunction volume g x ^ p :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top)
    _ ≤ C ^ p * (maximalFunctionConst 1 p * ∫⁻ x, ‖g x‖ₑ ^ p) := by
        gcongr
        simpa using lintegral_rpow_maximalFunction_le volume hg hp
    _ = C ^ p * maximalFunctionConst 1 p * ∫⁻ x, ‖g x‖ₑ ^ p := (mul_assoc _ _ _).symm

/-- **The strong type bound for the nontangential maximal function.** For `1 < p`,
`∫ (M^α_h P[‖g‖ dx]) ^ p ≤ C ^ p K_p ∫ |g| ^ p` with `C = max 2 (1 + 2 α ^ 2)` and `K_p` the
constant of the strong type bound for the Hardy–Littlewood maximal function on `ℝ`. -/
theorem lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le (α : ℝ)
    (h : ℝ≥0∞) {g : ℝ → F} (hg : AEMeasurable (fun x => ‖g x‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, nontangentialMaximalFunction α h
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ^ p ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) ^ p * maximalFunctionConst 1 p *
        ∫⁻ x, ‖g x‖ₑ ^ p :=
  (lintegral_mono fun x => ENNReal.rpow_le_rpow
    (nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_lIntegral α h _ x)
    (by linarith)).trans
    (lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α h hg hp)

/-- **The strong type bound for aperture one.** For `1 < p`,
`∫ (M_h P[|g| dx]) ^ p ≤ 3 ^ p K_p ∫ |g| ^ p`. -/
theorem lintegral_rpow_nontangentialMaximalFunction_one_upperHalfPlanePoissonLIntegral_le
    (h : ℝ≥0∞) {g : ℝ → F} (hg : AEMeasurable (fun x => ‖g x‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, nontangentialMaximalFunction 1 h
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ^ p ≤
      3 ^ p * maximalFunctionConst 1 p * ∫⁻ x, ‖g x‖ₑ ^ p := by
  have h3 : ENNReal.ofReal (max 2 (1 + 2 * (1 : ℝ) ^ 2)) = 3 := by norm_num
  simpa only [h3] using
    lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le 1 h hg hp

/-- **The strong type bound for aperture one.** For `1 < p`,
`∫ (M_h P[‖g‖ dx]) ^ p ≤ 3 ^ p K_p ∫ |g| ^ p`. -/
theorem lintegral_rpow_nontangentialMaximalFunction_one_upperHalfPlanePoissonIntegral_le
    (h : ℝ≥0∞) {g : ℝ → F} (hg : AEMeasurable (fun x => ‖g x‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, nontangentialMaximalFunction 1 h
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ^ p ≤
      3 ^ p * maximalFunctionConst 1 p * ∫⁻ x, ‖g x‖ₑ ^ p := by
  have h3 : ENNReal.ofReal (max 2 (1 + 2 * (1 : ℝ) ^ 2)) = 3 := by norm_num
  simpa only [h3] using
    lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le 1 h hg hp

/-- **The weak type bound for the nontangential maximal function.**
`t |{M^α_h P[|g| dx] > t}| ≤ 4 C ∫ |g|` with `C = max 2 (1 + 2 α ^ 2)`. -/
theorem mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le (α : ℝ)
    (h : ℝ≥0∞) (g : ℝ → F) (t : ℝ≥0∞) :
    t * volume {x | t < nontangentialMaximalFunction α h
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x} ≤
      4 * ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * ∫⁻ x, ‖g x‖ₑ := by
  set C := ENNReal.ofReal (max 2 (1 + 2 * α ^ 2))
  have hC0 : C ≠ 0 := by
    simp only [C, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_max_of_lt_left two_pos
  have hCt : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hsub : {x | t < nontangentialMaximalFunction α h
      (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x} ⊆
      {x | t / C < maximalFunction volume g x} := fun x hx =>
    ENNReal.div_lt_of_lt_mul' <| hx.trans_le <|
      nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α h g x
  calc t * volume {x | t < nontangentialMaximalFunction α h
          (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x}
      ≤ C * (t / C * volume {x | t / C < maximalFunction volume g x}) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel hC0 hCt]
        gcongr
    _ ≤ C * (4 * ∫⁻ x, ‖g x‖ₑ) := by
        refine mul_le_mul' le_rfl ?_
        simpa using mul_measure_lt_maximalFunction_le volume g (t / C)
    _ = 4 * C * ∫⁻ x, ‖g x‖ₑ := by ring

/-- **The weak type bound for the nontangential maximal function.**
`t |{M^α_h P[‖g‖ dx] > t}| ≤ 4 C ∫ |g|` with `C = max 2 (1 + 2 α ^ 2)`. -/
theorem mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le (α : ℝ)
    (h : ℝ≥0∞) (g : ℝ → F) (t : ℝ≥0∞) :
    t * volume {x | t < nontangentialMaximalFunction α h
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x} ≤
      4 * ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * ∫⁻ x, ‖g x‖ₑ :=
  (mul_le_mul' le_rfl (measure_mono <| ofPred_subset_ofPred.2 fun x hx => hx.trans_le
    (nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_lIntegral α h _ x))).trans
    (mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α h g t)

end Global

section Local

/-- Away from `[-R - 2, R + 2]`, the Poisson kernel with pole in the cone `Γ_1(x)` over a point
`|x| ≤ R` is dominated by the density of the Poisson measure:
`P(z, s) ≤ 2 (R + 2) ^ 2 / π · (1 + s ^ 2)⁻¹`. -/
theorem upperHalfPlanePoissonKernel_le_of_mem_nontangentialCone_one {R x : ℝ} (hx : |x| ≤ R)
    {z : ℂ} (hz : z ∈ nontangentialCone 1 1 x) {s : ℝ} (hs : R + 2 ≤ |s|) :
    upperHalfPlanePoissonKernel z s ≤ 2 * (R + 2) ^ 2 / π * (1 + s ^ 2)⁻¹ := by
  obtain ⟨hy, hcone, hy1⟩ := mem_nontangentialCone.1 hz
  rw [one_mul] at hcone
  rw [ENNReal.ofReal_lt_one] at hy1
  rw [upperHalfPlanePoissonKernel_eq, normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, neg_mul_neg]
  set y := z.im
  set a := z.re
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  -- `|s - a| ≥ |s| - (R + 1) ≥ |s| / (R + 2)`.
  have ha : |a| ≤ R + 1 := by
    have := abs_sub_abs_le_abs_sub a x
    linarith
  have hsa : |s| / (R + 2) ≤ |s - a| := by
    have h1 : |s| - |a| ≤ |s - a| := abs_sub_abs_le_abs_sub s a
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hs1 : 1 ≤ s ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have hsa2 : s ^ 2 ≤ (R + 2) ^ 2 * (s - a) ^ 2 := by
    have h0 : 0 ≤ |s| / (R + 2) := div_nonneg (abs_nonneg _) (by linarith)
    have := mul_le_mul hsa hsa h0 (abs_nonneg _)
    rw [← sq, ← sq, div_pow, sq_abs, sq_abs, div_le_iff₀ (by nlinarith)] at this
    linarith
  have hpos : 0 < (s - a) * (s - a) + y * y :=
    add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_pos hy hy)
  rw [div_le_iff₀ (mul_pos Real.pi_pos hpos)]
  calc y ≤ 1 := hy1.le
    _ ≤ 2 * (R + 2) ^ 2 / π * (1 + s ^ 2)⁻¹ * (π * ((s - a) * (s - a) + y * y)) := by
      rw [show 2 * (R + 2) ^ 2 / π * (1 + s ^ 2)⁻¹ * (π * ((s - a) * (s - a) + y * y)) =
        2 * (R + 2) ^ 2 * ((s - a) * (s - a) + y * y) / (1 + s ^ 2) by
          field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg y, sq_nonneg (R + 2)]

variable {F : Type*} [TopologicalSpace F] [ESeminormedAddMonoid F]

/-- **Localisation of the Poisson integral of a function in `L¹(Π)`.** For `|x| ≤ R` and `z` in the
cone `Γ_1(x)`, `P[|g| dx](z) ≤ 3 M(g 1_{[-R-2, R+2]})(x) + 2 (R + 2) ^ 2 / π · ∫ |g| dΠ`, where
`Π = dx / (1 + x ^ 2)` is the Poisson measure. -/
theorem upperHalfPlanePoissonLIntegral_le_of_mem_nontangentialCone_one {g : ℝ → F}
    (hg : AEMeasurable (fun s => ‖g s‖ₑ)) {R x : ℝ} (hx : |x| ≤ R) {z : ℂ}
    (hz : z ∈ nontangentialCone 1 1 x) :
    upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ) z ≤
      3 * maximalFunction volume ((Icc (-(R + 2)) (R + 2)).indicator g) x +
        ENNReal.ofReal (2 * (R + 2) ^ 2 / π) *
          ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure := by
  set S := Icc (-(R + 2)) (R + 2)
  set k : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (upperHalfPlanePoissonKernel z s)
  have hk : Measurable k := (measurable_upperHalfPlanePoissonKernel z).ennreal_ofReal
  have hd : Measurable fun s : ℝ => ENNReal.ofReal (1 + s ^ 2)⁻¹ := by fun_prop
  -- Split the integral over `S` and its complement.
  rw [upperHalfPlanePoissonLIntegral_def,
    ← lintegral_add_compl _ (measurableSet_Icc : MeasurableSet S)]
  gcongr
  · -- On `S`: the Poisson integral of the truncated function, bounded on the cone.
    rw [restrict_withDensity measurableSet_Icc, ← withDensity_indicator measurableSet_Icc,
      ← upperHalfPlanePoissonLIntegral_def]
    have hind : (S.indicator fun s => ‖g s‖ₑ) = fun s => ‖S.indicator g s‖ₑ := by
      funext s
      exact (eNorm_indicator_eq_indicator_eNorm g s).symm
    rw [hind]
    calc upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖S.indicator g s‖ₑ) z
        ≤ nontangentialMaximalFunction 1 1
            (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖S.indicator g s‖ₑ))
            x := by
          simpa using le_nontangentialMaximalFunction (u := upperHalfPlanePoissonLIntegral
            (volume.withDensity fun s => ‖S.indicator g s‖ₑ)) hz
      _ ≤ 3 * maximalFunction volume (S.indicator g) x :=
          nontangentialMaximalFunction_one_upperHalfPlanePoissonLIntegral_le 1 _ x
  · -- Off `S`: the kernel is dominated by the density of the Poisson measure.
    rw [upperHalfPlanePoissonMeasure_eq_withDensity,
      lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable hg,
      restrict_withDensity measurableSet_Icc.compl,
      lintegral_withDensity_eq_lintegral_mul₀ hg.restrict hk.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_le_lintegral _ _).trans' (setLIntegral_mono' measurableSet_Icc.compl
      fun s hs => ?_)
    have hs' : R + 2 ≤ |s| := by
      have hR : 0 ≤ R := (abs_nonneg x).trans hx
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp only [Pi.mul_apply, k]
    rw [mul_comm (‖g s‖ₑ), ← mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (upperHalfPlanePoissonKernel_le_of_mem_nontangentialCone_one hx hz hs')

/-- **Localisation of the nontangential maximal function.** For `g ∈ L¹(Π)` and `|x| ≤ R`,
`M_1 P[|g| dx](x) ≤ 3 M(g 1_{[-R-2, R+2]})(x) + 2 (R + 2) ^ 2 / π · ∫ |g| dΠ`, where `M_1` is the
nontangential maximal function over cones `Γ_1(x)` of aperture and height one. -/
theorem nontangentialMaximalFunction_one_one_upperHalfPlanePoissonLIntegral_le {g : ℝ → F}
    (hg : AEMeasurable (fun s => ‖g s‖ₑ)) {R x : ℝ} (hx : |x| ≤ R) :
    nontangentialMaximalFunction 1 1
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      3 * maximalFunction volume ((Icc (-(R + 2)) (R + 2)).indicator g) x +
        ENNReal.ofReal (2 * (R + 2) ^ 2 / π) *
          ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure :=
  nontangentialMaximalFunction_le_iff.2 fun _ hz => by
    simpa using upperHalfPlanePoissonLIntegral_le_of_mem_nontangentialCone_one hg hx hz

/-- **Localisation of the nontangential maximal function.** For `g ∈ L¹(Π)` and `|x| ≤ R`,
`M_1 P[‖g‖ dx](x) ≤ 3 M(g 1_{[-R-2, R+2]})(x) + 2 (R + 2) ^ 2 / π · ∫ |g| dΠ`, where `M_1` is the
nontangential maximal function over cones `Γ_1(x)` of aperture and height one. -/
theorem nontangentialMaximalFunction_one_one_upperHalfPlanePoissonIntegral_le {g : ℝ → F}
    (hg : AEMeasurable (fun s => ‖g s‖ₑ)) {R x : ℝ} (hx : |x| ≤ R) :
    nontangentialMaximalFunction 1 1
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      3 * maximalFunction volume ((Icc (-(R + 2)) (R + 2)).indicator g) x +
        ENNReal.ofReal (2 * (R + 2) ^ 2 / π) *
          ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_lIntegral 1 1 _ x).trans
    (nontangentialMaximalFunction_one_one_upperHalfPlanePoissonLIntegral_le hg hx)

/-- A point of `[-R, R]` where `M_1 P[|g| dx] > t` has `M(g 1_{[-R-2, R+2]}) > t / 2 / 3` or
`2 (R + 2) ^ 2 / π · ∫ |g| dΠ > t / 2`. -/
private theorem lt_maximalFunction_or_lt_of_lt {g : ℝ → F} (hg : AEMeasurable (fun s => ‖g s‖ₑ))
    {R x : ℝ} (hxR : x ∈ Icc (-R) R) {t : ℝ≥0∞}
    (hx : t < nontangentialMaximalFunction 1 1
      (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x) :
    t / 2 / 3 < maximalFunction volume ((Icc (-(R + 2)) (R + 2)).indicator g) x ∨
      t / 2 < ENNReal.ofReal (2 * (R + 2) ^ 2 / π) *
        ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure := by
  have hle := nontangentialMaximalFunction_one_one_upperHalfPlanePoissonLIntegral_le hg
    (abs_le.2 hxR)
  by_contra hAB
  rw [not_or, not_lt, not_lt] at hAB
  have h1 : 3 * maximalFunction volume ((Icc (-(R + 2)) (R + 2)).indicator g) x ≤ t / 2 := by
    calc _ ≤ 3 * (t / 2 / 3) := by gcongr; exact hAB.1
      _ = t / 2 := ENNReal.mul_div_cancel (by simp) (by simp)
  have := hx.trans_le (hle.trans (add_le_add h1 hAB.2))
  rw [ENNReal.add_halves] at this
  exact lt_irrefl _ this

/-- **The local weak type bound for functions in `L¹(Π)`.** For `R` there is a constant `C_R`,
depending only on `R`, such that `t |{x ∈ [-R, R] : M_1 P[|g| dx](x) > t}| ≤ C_R ∫ |g| dΠ` for
every `g` with `‖g‖ₑ` a.e.-measurable and every `t`. -/
theorem exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le
    (R : ℝ) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : ℝ → F, AEMeasurable (fun s => ‖g s‖ₑ) → ∀ t : ℝ≥0∞,
      t * volume {x ∈ Icc (-R) R | t < nontangentialMaximalFunction 1 1
          (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x} ≤
        C * ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure := by
  set c := ENNReal.ofReal (2 * (R + 2) ^ 2 / π)
  set d := ENNReal.ofReal (1 + (R + 2) ^ 2)
  refine ⟨24 * d + 2 * c * volume (Icc (-R) R),
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      measure_Icc_lt_top.ne⟩, fun g hg t => ?_⟩
  set S := Icc (-(R + 2)) (R + 2)
  set N := ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure
  set A := {x | t / 2 / 3 < maximalFunction volume (S.indicator g) x}
  set B := {x ∈ Icc (-R) R | t / 2 < c * N}
  have hsub : {x ∈ Icc (-R) R | t < nontangentialMaximalFunction 1 1
      (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x} ⊆ A ∪ B :=
    fun x ⟨hxR, hx⟩ => (lt_maximalFunction_or_lt_of_lt hg hxR hx).imp id fun h => ⟨hxR, h⟩
  have hA : t * volume A ≤ 24 * d * N := by
    have hw := mul_measure_lt_maximalFunction_le volume (S.indicator g) (t / 2 / 3)
    simp only [Module.finrank_self, pow_one] at hw
    calc t * volume A = 2 * (3 * (t / 2 / 3 * volume A)) := by
          rw [← mul_assoc 3, ENNReal.mul_div_cancel (by simp) (by simp), ← mul_assoc,
            ENNReal.mul_div_cancel (by simp) (by simp)]
      _ ≤ 2 * (3 * (4 * (d * N))) := by
          refine mul_le_mul' le_rfl (mul_le_mul' le_rfl (hw.trans (mul_le_mul' le_rfl ?_)))
          simp_rw [eNorm_indicator_eq_indicator_eNorm]
          rw [lintegral_indicator measurableSet_Icc]
          exact setLIntegral_Icc_le_mul_lintegral_upperHalfPlanePoissonMeasure _ (R + 2)
      _ = 24 * d * N := by ring
  have hB : t * volume B ≤ 2 * c * volume (Icc (-R) R) * N := by
    by_cases hcN : t / 2 < c * N
    · have ht : t ≤ 2 * (c * N) := by
        calc t = 2 * (t / 2) := (ENNReal.mul_div_cancel (by simp) (by simp)).symm
          _ ≤ 2 * (c * N) := by gcongr
      calc t * volume B ≤ 2 * (c * N) * volume (Icc (-R) R) :=
            mul_le_mul' ht (measure_mono fun x hx => hx.1)
        _ = 2 * c * volume (Icc (-R) R) * N := by ring
    · have : B = ∅ := eq_empty_of_forall_notMem fun x hx => hcN hx.2
      simp [this]
  calc t * volume {x ∈ Icc (-R) R | t < nontangentialMaximalFunction 1 1
          (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x}
      ≤ t * (volume A + volume B) :=
        mul_le_mul' le_rfl ((measure_mono hsub).trans (measure_union_le _ _))
    _ = t * volume A + t * volume B := mul_add _ _ _
    _ ≤ 24 * d * N + 2 * c * volume (Icc (-R) R) * N := add_le_add hA hB
    _ = (24 * d + 2 * c * volume (Icc (-R) R)) * N := by ring

/-- **The local weak type bound for functions in `L¹(Π)`.** For `R` there is a constant `C_R`,
depending only on `R`, such that `t |{x ∈ [-R, R] : M_1 P[‖g‖ dx](x) > t}| ≤ C_R ∫ |g| dΠ` for
every `g` with `‖g‖ₑ` a.e.-measurable and every `t`. -/
theorem exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le
    (R : ℝ) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : ℝ → F, AEMeasurable (fun s => ‖g s‖ₑ) → ∀ t : ℝ≥0∞,
      t * volume {x ∈ Icc (-R) R | t < nontangentialMaximalFunction 1 1
          (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x} ≤
        C * ∫⁻ s, ‖g s‖ₑ ∂upperHalfPlanePoissonMeasure := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le
      (F := F) R
  refine ⟨C, hC, fun g hg t => (mul_le_mul' le_rfl (measure_mono <|
    ofPred_subset_ofPred.2 fun x hx => ⟨hx.1, hx.2.trans_le
      (nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_lIntegral 1 1 _ x)⟩)).trans
    (hbound g hg t)⟩

end Local

end TauCeti
