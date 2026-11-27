/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CoreChart
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The end annuli and the output circle of the pair of pants as cylinders

The truncation `S_R = TauCeti.ThricePuncturedSphere.truncation R` of the pair of pants
`S = ℂ ∖ {0, 1}` is what remains of `S` after removing the three cylindrical ends beyond the
height `R`. For `0 ≤ a ≤ b`, the part of `S_b` beyond the height `a` on the end `q`, the points
whose signed longitudinal coordinate `±s` on that end lies in `(a, b]`, is an annulus swept out by
the end chart `TauCeti.Floer.endChart q`, which sends `(s, t)` to the end lift at `s + i t`. This
file describes these annuli, and with them the whole truncation `S_R`, through the cylinders of
the end charts.

For a map `u` of the pair of pants into a manifold `M`:

* **The area of an end annulus.** If `u` is `C¹` on `S`, then for every continuous two-form `φ`
  the integral of `φ` over `u` composed with the end chart on `[±a, ±b] × [0, 1]` is `±` the
  integral of `u^* φ` over the annulus between the heights `a` and `b` of the end
  (`TauCeti.Floer.rectangleIntegral_comp_endChart`). The sign is that of the end: the end chart
  preserves orientation, and on the output end `∞` the heights `±s` grow as `s` decreases.
* **The end annuli as cylinders.** The **end annulus chart**
  `TauCeti.Floer.endAnnulusChart q a b` runs through the end chart from the circle at height `a`
  to the circle at height `b`, reparametrized by the smooth transition in its first variable. If
  `u` is `C²` on `S`, then `u` composed with it is a cylinder (`TauCeti.IsLoopCylinder`) from the
  loop of `u` along the circle `±s = a` of the end to its loop along the circle `±s = b`
  (`TauCeti.Floer.isLoopCylinder_comp_endAnnulusChart`), with the area of the end annulus
  (`TauCeti.Floer.rectangleIntegral_comp_endAnnulusChart`). These loops are the loops
  `t ↦ u(φ_q(±R + i t))` whose limits as `R → ∞` are the asymptotic orbits of a Floer pair of
  pants.
* **The truncation as core and annuli.** For `0 ≤ a ≤ b` the truncation `S_b` is the disjoint
  union of `S_a` and of the three annuli between the heights `a` and `b`
  (`TauCeti.Floer.setIntegral_preimage_truncation_eq_add_sum`). With the core chart of
  `TauCeti.Geometry.Symplectic.Floer.PairOfPants.CoreChart`, which describes `S₀`, the integral of
  `u^* φ` over `S_R` is minus the integral over `u` composed with the core chart plus the signed
  integrals over `u` composed with the three end charts on `[0, ±R] × [0, 1]`
  (`TauCeti.Floer.setIntegral_preimage_truncation_eq_neg_rectangleIntegral_add_sum`).

* **The output circle.** The core chart ends at the output circle `‖w‖ = 2`, which it runs around
  at the speed of the angle about `1/2`, while the end chart of the output end runs around the same
  circle, its circle at height `0`, at the speed of the angle about `0`. The **output circle chart**
  `TauCeti.Floer.pairOfPantsOutputCircleChart` joins the two parametrizations on the circle,
  through the smooth lift `TauCeti.Floer.pairOfPantsOutputLift` of the first to the angular
  coordinate of the end. If `u` is `C²` on `S`,
  then `u` composed with it is a cylinder from the output loop of `u` along the core chart to its
  loop along the circle at height `0` of the output end
  (`TauCeti.Floer.isLoopCylinder_comp_pairOfPantsOutputCircleChart`), and this cylinder has no
  area (`TauCeti.Floer.rectangleIntegral_comp_pairOfPantsOutputCircleChart`): it lies in a loop, and
  the pullback of a two-form along a map through a curve vanishes
  (`TauCeti.rectangleIntegral_comp_eq_zero`).

This is the form in which the topological term `∫ u^* ω` of the energy identity of a Floer pair of
pants is carried from the core `S₀` out to the circles at height `R`, where the loops of a Floer
solution converge to its asymptotic orbits: the caps of the input loops are transported along the
input annuli, and the cap of the output loop along the output annulus, by the gluing of cylinders
(`TauCeti.cappedLoopAction_rectangleTrans_sub_cappedLoopAction`).

The area formula is the change of variables formula for the end chart, a holomorphic map whose
Jacobian `|φ_q'|²` is positive (`TauCeti.Floer.det_fderiv_endChart_pos`), together with the
Jacobian rule for the pullback of a two-form (`TauCeti.mpullback_comp_apply_eq_det_smul`). The end
chart stays in `S` a little below the circle at height `0`
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_ne_zero_and_ne_one_of_neg_log_two_lt`),
so the composites with `u` are first replaced by globally `C¹` maps that agree with them on the
closed annuli.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and the energy of its solutions.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  capped orbits and the action of glued caps.
-/

public section

noncomputable section

open Set Real Function MeasureTheory Manifold Filter TauCeti.ThricePuncturedSphere
open scoped Topology

namespace TauCeti.Floer

/-! ### The end charts near the circles at height `0` -/

/-- The end chart of `q` sends the half-plane `2π (±s) > -log 2`, which contains the circle at
height `0` of the end, into `S`. This extends
`TauCeti.Floer.endChart_mem_thricePuncturedSphereReal`, for the part `±s > 0` of the end, a little
beyond that circle. -/
theorem endChart_mem_thricePuncturedSphereReal_of_neg_log_two_lt {q : Puncture}
    {z : ℝ × ℝ} (hz : -Real.log 2 < 2 * π * (q.endSign * z.1)) :
    endChart q z ∈ thricePuncturedSphereReal := by
  rw [mem_thricePuncturedSphereReal_iff, equivRealProdCLM_symm_endChart]
  exact q.cylindricalEndLift_ne_zero_and_ne_one_of_neg_log_two_lt (by simpa using hz)

/-- The circle at height `0` of the output end lies in `S`. -/
private theorem endChart_inf_mk_zero_mem_thricePuncturedSphereReal (τ : ℝ) :
    endChart .inf (0, τ) ∈ thricePuncturedSphereReal :=
  endChart_mem_thricePuncturedSphereReal_of_neg_log_two_lt (by simp [Real.log_pos one_lt_two])

/-- A smooth height that is the identity on `[0, ∞)` and stays above `-1/10`. -/
private def heightClamp (x : ℝ) : ℝ :=
  x * smoothTransition (1 + 10 * x)

private theorem heightClamp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : heightClamp x = x := by
  rw [heightClamp, smoothTransition.one_of_one_le (by linarith), mul_one]

private theorem neg_tenth_le_heightClamp (x : ℝ) : -(1 / 10) ≤ heightClamp x := by
  rcases le_or_gt x (-(1 / 10)) with h | h
  · rw [heightClamp, smoothTransition.zero_of_nonpos (by linarith), mul_zero]
    norm_num
  · have h₀ := smoothTransition.nonneg (1 + 10 * x)
    have h₁ := smoothTransition.le_one (1 + 10 * x)
    rw [heightClamp]
    rcases le_or_gt 0 x with hx | hx
    · nlinarith [mul_nonneg hx h₀]
    · nlinarith [mul_le_mul_of_nonpos_left h₁ hx.le]

private theorem contDiff_heightClamp {n : ℕ∞} : ContDiff ℝ n heightClamp :=
  contDiff_id.mul (smoothTransition.contDiff.comp (contDiff_const.add (contDiff_const.mul
    contDiff_id)))

/-- The end chart of `q` with its signed height clamped by `heightClamp`: it agrees with the end
chart where `±s ≥ 0`, and lies in `S` everywhere. -/
private def endClampChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  endChart q (q.endSign * heightClamp (q.endSign * z.1), z.2)

private theorem endClampChart_of_nonneg {q : Puncture} {z : ℝ × ℝ} (hz : 0 ≤ q.endSign * z.1) :
    endClampChart q z = endChart q z := by
  rw [endClampChart, heightClamp_of_nonneg hz, Puncture.endSign_mul_endSign_mul]

private theorem endClampChart_eventuallyEq {q : Puncture} {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) : endClampChart q =ᶠ[𝓝 z] endChart q := by
  have hc : Continuous fun w : ℝ × ℝ ↦ q.endSign * w.1 := continuous_const.mul continuous_fst
  exact Filter.eventually_of_mem (hc.isOpen_preimage _ isOpen_Ioi |>.mem_nhds hz) fun w hw ↦
    endClampChart_of_nonneg (le_of_lt hw)

private theorem endClampChart_mem_thricePuncturedSphereReal (q : Puncture) (z : ℝ × ℝ) :
    endClampChart q z ∈ thricePuncturedSphereReal := by
  refine endChart_mem_thricePuncturedSphereReal_of_neg_log_two_lt ?_
  rw [Puncture.endSign_mul_endSign_mul]
  have h := neg_tenth_le_heightClamp (q.endSign * z.1)
  have hπ := Real.pi_lt_d2
  have hl := Real.log_two_gt_d9
  nlinarith [Real.pi_pos]

private theorem contDiff_endClampChart (q : Puncture) {n : ℕ∞} :
    ContDiff ℝ n (endClampChart q) :=
  (contDiff_endChart q n).comp
    ((contDiff_const.mul (contDiff_heightClamp.comp (contDiff_const.mul contDiff_fst))).prodMk
      contDiff_snd)

variable {E HM M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contMDiff_comp_endClampChart {n : ℕ∞} {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u thricePuncturedSphereReal) (q : Puncture) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (u ∘ endClampChart q) :=
  hu.comp_contMDiff (contDiff_endClampChart q).contMDiff
    (endClampChart_mem_thricePuncturedSphereReal q)

/-- Between two circles `±s = a` and `±s = b` of nonnegative heights the clamp does nothing, so
the integrals over `u` composed with the clamped end chart and with the end chart agree. -/
private theorem rectangleIntegral_comp_endClampChart {φ : RoughForm I M F 2} {u : ℝ × ℝ → M}
    (q : Puncture) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rectangleIntegral φ (u ∘ endClampChart q) (q.endSign * a, 0) (q.endSign * b, 1) =
      rectangleIntegral φ (u ∘ endChart q) (q.endSign * a, 0) (q.endSign * b, 1) := by
  refine rectangleIntegral_congr fun z hz ↦ ?_
  simp only [Function.comp_apply]
  rw [endClampChart_of_nonneg]
  have h₁ := hz.1
  rcases q.endSign_eq_one_or_eq_neg_one with h | h <;>
    simp only [h, one_mul, neg_one_mul, mem_uIcc] at h₁ ⊢ <;>
    rcases h₁ with h₁ | h₁ <;> linarith [h₁.1, h₁.2]

/-! ### The area of an end annulus -/

/-- On the open part `±s > 0` of an end, the integrand along `u` composed with the clamped end
chart is the Jacobian of the end chart times the area density of `u` at the image point. -/
private theorem mpullback_comp_endClampChart_apply (φ : RoughForm I M F 2) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {q : Puncture} {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) :
    mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ endClampChart q) φ z ![(1, 0), (0, 1)] =
      |(fderiv ℝ (endChart q) z).det| • φ (u (endChart q z))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (endChart q z) (1, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I u (endChart q z) (0, 1)] := by
  have hmem := endChart_mem_thricePuncturedSphereReal hz
  have hud : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q z) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hmem)).mdifferentiableAt
      one_ne_zero
  rw [((endClampChart_eventuallyEq hz).fun_comp u).mpullback_eq φ,
    mpullback_comp_apply_eq_det_smul φ
      ((contDiff_endChart q 1).differentiable one_ne_zero z).hasFDerivAt hud,
    abs_of_pos (det_fderiv_endChart_pos q z)]
  exact congrArg₂ (· • ·) rfl (mpullback_apply_pair u φ _ _ _)

/-- The area of the annulus over a set `P` of heights a.e. equal to `[lo, hi]`, in the
coordinates of the end. -/
private theorem setIntegral_image_endChart_eq_rectangleIntegral [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (q : Puncture)
    {P : Set ℝ} (hP : MeasurableSet P) (hPpos : ∀ s ∈ P, 0 < q.endSign * s) {lo hi : ℝ}
    (hlo : lo ≤ hi) (hPae : P =ᵐ[volume] Icc lo hi) :
    ∫ z in endChart q '' (P ×ˢ Ico 0 1), φ (u z)
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] =
      rectangleIntegral φ (u ∘ endClampChart q) (lo, 0) (hi, 1) := by
  have hs : MeasurableSet (P ×ˢ Ico (0 : ℝ) 1) := hP.prod measurableSet_Ico
  have hinj : InjOn (endChart q) (P ×ˢ Ico (0 : ℝ) 1) :=
    (injOn_endChart_univ_prod_Ico q 0).mono (prod_mono (subset_univ _) (by norm_num))
  rw [integral_image_eq_integral_of_eq_abs_det_smul (f := fun z ↦
      mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ endClampChart q) φ z ![(1, 0), (0, 1)]) hs hinj
      (fun z _ ↦ (contDiff_endChart q 1).differentiable one_ne_zero z)
      (fun z hz ↦ mpullback_comp_endClampChart_apply φ hu (hPpos _ hz.1)),
    ← hφ.setIntegral_eq_rectangleIntegral (contMDiff_comp_endClampChart hu q)
      (Prod.mk_le_mk.2 ⟨hlo, zero_le_one⟩)]
  have hae : (P ×ˢ Ico (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] Icc ((lo, 0) : ℝ × ℝ) (hi, 1) := by
    rw [← Icc_prod_Icc, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq hPae Ico_ae_eq_Icc
  rw [setIntegral_congr_set hae]
  exact setIntegral_congr_fun measurableSet_Icc fun z _ ↦ mpullback_apply_pair _ φ z _ _

/-- **The area of an end annulus.** For a continuous two-form `φ` on a manifold `M`, a map `u` of
the pair of pants `S` into `M` which is `C¹` on `S`, and heights `0 ≤ a ≤ b`, the integral of `φ`
over `u` composed with the end chart of `q` on `[±a, ±b] × [0, 1]` is `±` the integral of `u^* φ`
over the annulus of the points of the truncation `S_b` beyond the height `a` on the end `q`. The
sign `±` is that of the end. -/
theorem rectangleIntegral_comp_endChart [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (q : Puncture) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    rectangleIntegral φ (u ∘ endChart q) (q.endSign * a, 0) (q.endSign * b, 1) =
      q.endSign • ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation b ∩
          {z | a < (positiveEndCoord q z).1},
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  simp_rw [fst_positiveEndCoord]
  rw [preimage_truncation_inter_eq_image_endChart q ha b]
  have hmeas (c : ℝ) : MeasurableSet {s : ℝ | c < q.endSign * s} :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  have hmeas' : MeasurableSet {s : ℝ | q.endSign * s ≤ b} :=
    measurableSet_le (measurable_const.mul measurable_id) measurable_const
  have hP : MeasurableSet {s : ℝ | a < q.endSign * s ∧ q.endSign * s ≤ b} :=
    (hmeas a).inter hmeas'
  have hPpos (s : ℝ) (hs : s ∈ {s : ℝ | a < q.endSign * s ∧ q.endSign * s ≤ b}) :
      0 < q.endSign * s := ha.trans_lt hs.1
  rw [← rectangleIntegral_comp_endClampChart q ha (ha.trans hab)]
  rcases q.endSign_eq_one_or_eq_neg_one with h | h
  · have hPae : {s : ℝ | a < q.endSign * s ∧ q.endSign * s ≤ b} =ᵐ[volume] Icc a b := by
      simp only [h, one_mul]
      exact Ioc_ae_eq_Icc
    rw [setIntegral_image_endChart_eq_rectangleIntegral hφ hu q hP hPpos hab hPae, h, one_mul,
      one_mul, one_smul]
  · have hPae :
        {s : ℝ | a < q.endSign * s ∧ q.endSign * s ≤ b} =ᵐ[volume] Icc (-b) (-a) := by
      have hset : {s : ℝ | a < q.endSign * s ∧ q.endSign * s ≤ b} = Ico (-b) (-a) := by
        ext s
        simp only [h, neg_one_mul, mem_ofPred_eq, mem_Ico]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
      rw [hset]
      exact Ico_ae_eq_Icc
    rw [setIntegral_image_endChart_eq_rectangleIntegral hφ hu q hP hPpos (neg_le_neg hab) hPae, h,
      neg_one_mul, neg_one_mul, rectangleIntegral_symm_fst, neg_one_smul]

/-! ### The end annuli as cylinders -/

/-- The **end annulus chart** of the end `q` between the heights `a` and `b`: the end chart of `q`
at the signed height `±(a + (b - a) β (s))` and the angle `t`, where `β = Real.smoothTransition`
rests at `0` for `s ≤ 0` and at `1` for `s ≥ 1`. It runs from the circle `±s = a` of the end to the
circle `±s = b`, and is `1`-periodic in `t`. -/
def endAnnulusChart (q : Puncture) (a b : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  endChart q (q.endSign * (a + (b - a) * smoothTransition z.1), z.2)

theorem endAnnulusChart_apply (q : Puncture) (a b : ℝ) (z : ℝ × ℝ) :
    endAnnulusChart q a b z =
      endChart q (q.endSign * (a + (b - a) * smoothTransition z.1), z.2) := (rfl)

/-- The end annulus chart starts at the circle `±s = a` of the end. -/
@[simp]
theorem endAnnulusChart_mk_zero (q : Puncture) (a b t : ℝ) :
    endAnnulusChart q a b (0, t) = endChart q (q.endSign * a, t) := by
  simp [endAnnulusChart_apply]

/-- The end annulus chart ends at the circle `±s = b` of the end. -/
@[simp]
theorem endAnnulusChart_mk_one (q : Puncture) (a b t : ℝ) :
    endAnnulusChart q a b (1, t) = endChart q (q.endSign * b, t) := by
  simp [endAnnulusChart_apply]

/-- The end annulus chart is `1`-periodic in its second variable. -/
@[simp]
theorem endAnnulusChart_apply_add_one (q : Puncture) (a b s t : ℝ) :
    endAnnulusChart q a b (s, t + 1) = endAnnulusChart q a b (s, t) := by
  simp only [endAnnulusChart_apply, endChart_add_one]

/-- The end annulus chart is smooth. -/
theorem contDiff_endAnnulusChart (q : Puncture) (a b : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (endAnnulusChart q a b) :=
  (contDiff_endChart q n).comp ((contDiff_const.mul (contDiff_const.add (contDiff_const.mul
    (smoothTransition.contDiff.comp contDiff_fst)))).prodMk contDiff_snd)

/-- The signed height of the end annulus chart lies between `a` and `b`. -/
private theorem endSign_mul_fst_endAnnulusChart_mem (q : Puncture) {a b : ℝ} (s : ℝ) :
    q.endSign * (q.endSign * (a + (b - a) * smoothTransition s)) ∈ uIcc a b := by
  rw [Puncture.endSign_mul_endSign_mul]
  have h₀ := smoothTransition.nonneg s
  have h₁ := smoothTransition.le_one s
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    constructor <;> nlinarith
  · rw [uIcc_of_ge h]
    constructor <;> nlinarith

/-- The end annulus chart is the clamped end chart reparametrized in its first variable. -/
private theorem endAnnulusChart_eq_endClampChart_comp {q : Puncture} {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    endAnnulusChart q a b = endClampChart q ∘
      Prod.map (fun s ↦ q.endSign * (a + (b - a) * smoothTransition s)) id := by
  funext z
  have h := endSign_mul_fst_endAnnulusChart_mem q (a := a) (b := b) z.1
  rw [Function.comp_apply, endClampChart_of_nonneg]
  · rfl
  · exact le_trans (le_min ha hb) h.1

/-- **An end annulus as a cylinder.** For a map `u` of the pair of pants `S` into a manifold `M`
which is `C²` on `S`, and heights `a, b ≥ 0`, the composite of `u` with the end annulus chart of
`q` is a cylinder from the loop of `u` along the circle `±s = a` of the end `q` to its loop along
the circle `±s = b`. -/
theorem isLoopCylinder_comp_endAnnulusChart {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u thricePuncturedSphereReal) (q : Puncture) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsLoopCylinder I (u ∘ endAnnulusChart q a b) (fun t ↦ u (endChart q (q.endSign * a, t)))
      fun t ↦ u (endChart q (q.endSign * b, t)) where
  contMDiff := by
    rw [endAnnulusChart_eq_endClampChart_comp ha hb, ← Function.comp_assoc]
    exact (contMDiff_comp_endClampChart hu q).comp
      ((contDiff_const.mul (contDiff_const.add (contDiff_const.mul
        smoothTransition.contDiff))).prodMap contDiff_id).contMDiff
  apply_add_one z := by
    simp only [Function.comp_apply, endAnnulusChart_apply_add_one]
  apply_zero t := by
    simp only [Function.comp_apply, endAnnulusChart_mk_zero]
  apply_one t := by
    simp only [Function.comp_apply, endAnnulusChart_mk_one]

/-- **The area of an end annulus cylinder.** For a continuous two-form `φ`, a map `u` of the pair
of pants which is `C¹` on `S`, and heights `a, b ≥ 0`, the integral of `φ` over `u` composed with
the end annulus chart of `q` is the integral over `u` composed with the end chart of `q` on
`[±a, ±b] × [0, 1]`; for `a ≤ b` this is `±` the integral of `u^* φ` over the annulus between the
heights `a` and `b` (`TauCeti.Floer.rectangleIntegral_comp_endChart`). -/
theorem rectangleIntegral_comp_endAnnulusChart [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (q : Puncture) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rectangleIntegral φ (u ∘ endAnnulusChart q a b) (0, 0) (1, 1) =
      rectangleIntegral φ (u ∘ endChart q) (q.endSign * a, 0) (q.endSign * b, 1) := by
  rw [endAnnulusChart_eq_endClampChart_comp ha hb, ← Function.comp_assoc,
    rectangleIntegral_comp_prodMap_of_contDiff hφ (contMDiff_comp_endClampChart hu q)
      (contDiff_const.mul (contDiff_const.add (contDiff_const.mul smoothTransition.contDiff)))]
  simp only [smoothTransition.zero, smoothTransition.one, mul_zero, add_zero, mul_one,
    add_sub_cancel]
  exact rectangleIntegral_comp_endClampChart q ha hb

/-! ### The truncation as its core and its end annuli -/

/-- **The truncation as a smaller truncation and annuli.** For heights `0 ≤ a ≤ b`, the truncation
`S_b` of the pair of pants is the disjoint union of `S_a` and of the three annuli of the points of
`S_b` beyond the height `a` on the end `q`, so the integral of every function integrable on `S_b`
splits accordingly. -/
theorem setIntegral_preimage_truncation_eq_add_sum {f : ℝ × ℝ → F} {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hf : IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' truncation b)) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation b, f z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation a, f z) +
        ∑ q : Puncture, ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation b ∩
          {z | a < (positiveEndCoord q z).1}, f z := by
  set Sa := Complex.equivRealProdCLM.symm ⁻¹' truncation a
  set Sb := Complex.equivRealProdCLM.symm ⁻¹' truncation b
  set A : Puncture → Set (ℝ × ℝ) := fun q ↦ Sb ∩ {z | a < (positiveEndCoord q z).1}
  have hA (q : Puncture) : MeasurableSet (A q) :=
    (isCompact_preimage_truncation b).isClosed.measurableSet.inter
      (measurableSet_lt measurable_const (measurable_positiveEndCoord q).fst)
  have hsub : Sa ⊆ Sb := fun z hz ↦ truncation_mono hab hz
  have hunion : Sb = Sa ∪ ⋃ q, A q := by
    refine Subset.antisymm (fun z hz ↦ ?_) (union_subset hsub (iUnion_subset fun q ↦
      inter_subset_left))
    by_cases h : ∀ q : Puncture, (positiveEndCoord q z).1 ≤ a
    · exact .inl (mem_preimage_truncation_iff.2
        ⟨(mem_preimage_truncation_iff.1 hz).1, h⟩)
    · simp only [not_forall, not_le] at h
      obtain ⟨q, hq⟩ := h
      exact .inr (mem_iUnion.2 ⟨q, hz, hq⟩)
  have hdisj : Disjoint Sa (⋃ q, A q) := by
    refine disjoint_iUnion_right.2 fun q ↦ disjoint_left.2 fun z hz hzA ↦ ?_
    exact (not_lt.2 ((mem_preimage_truncation_iff.1 hz).2 q)) hzA.2
  have hpair : Pairwise (Disjoint on A) := by
    intro q r hqr
    refine disjoint_left.2 fun z hzq hzr ↦ ?_
    exact (not_lt.2 (fst_positiveEndCoord_nonpos_of_ne hqr (ha.trans_lt hzq.2))) (ha.trans_lt
      hzr.2)
  have hfA (q : Puncture) : IntegrableOn f (A q) := hf.mono_set inter_subset_left
  conv_lhs => rw [hunion]
  rw [setIntegral_union hdisj (MeasurableSet.iUnion hA) (hf.mono_set hsub)
    (hf.mono_set (iUnion_subset fun q ↦ inter_subset_left)), integral_iUnion_fintype hA hpair hfA]

/-- **The area of a truncation through its core and its end annuli.** For a continuous two-form
`φ` on a manifold `M`, a map `u` of the pair of pants `S` into `M` which is `C¹` on `S`, and
`R ≥ 0`, the integral of `u^* φ` over the truncation `S_R` is minus the integral of `φ` over `u`
composed with the core chart, plus, for each end `q`, `±` the integral of `φ` over `u` composed
with the end chart of `q` on `[0, ±R] × [0, 1]`, with the sign of the end. -/
theorem setIntegral_preimage_truncation_eq_neg_rectangleIntegral_add_sum [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] =
      -rectangleIntegral φ (u ∘ pairOfPantsCoreChart) (0, 0) (1, 1) +
        ∑ q : Puncture,
          q.endSign • rectangleIntegral φ (u ∘ endChart q) (0, 0) (q.endSign * R, 1) := by
  have hint : IntegrableOn (fun z ↦ φ (u z)
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)])
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    ((hφ.continuousOn_apply_mfderiv isOpen_thricePuncturedSphereReal hu (1, 0) (0, 1)).mono
      (preimage_truncation_subset_thricePuncturedSphereReal R)).integrableOn_compact
      (isCompact_preimage_truncation R)
  rw [setIntegral_preimage_truncation_eq_add_sum le_rfl hR hint,
    rectangleIntegral_comp_pairOfPantsCoreChart hφ hu, neg_neg]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun q _ ↦ ?_)
  have h := rectangleIntegral_comp_endChart hφ hu q le_rfl hR
  rw [mul_zero] at h
  rw [h, smul_smul, Puncture.endSign_mul_self, one_smul]

/-! ### The output circle of the core

The core chart runs at `s = 1` around the output circle `‖w‖ = 2` at the speed of the angle about
`1/2` (`TauCeti.Floer.pairOfPantsCoreChart_mk_one`), while the end loop of the output end at
height `0` runs around the same circle at the speed of the angle about `0`. The output circle
chart joins the two parametrizations on the circle, through the smooth lift
`TauCeti.Floer.pairOfPantsOutputLift` of the first to the angular coordinate of the end. -/

/-- The angular coordinate of the output circle chart: the straight path from the lift of the
output loop of the core to the identity, reparametrized by the smooth transition. -/
private def outputCircleAngle (z : ℝ × ℝ) : ℝ :=
  (1 - smoothTransition z.1) * pairOfPantsOutputLift z.2 + smoothTransition z.1 * z.2

private theorem contDiff_outputCircleAngle {n : ℕ∞} : ContDiff ℝ n outputCircleAngle :=
  ((contDiff_const.sub (smoothTransition.contDiff.comp contDiff_fst)).mul
    (contDiff_pairOfPantsOutputLift.comp contDiff_snd)).add
    ((smoothTransition.contDiff.comp contDiff_fst).mul contDiff_snd)

/-- The **output circle chart** of the pair of pants. For each `s` it runs once around the output
circle `‖w‖ = 2` of the pair of pants (`TauCeti.Floer.norm_symm_pairOfPantsOutputCircleChart`), at
the circle of height `0` of the output end. For `s ≤ 0` it runs through the output loop of the core
chart, at the speed of the angle about `1/2`, and for `s ≥ 1` through the end chart of the output
end at height `0`, at the speed of the angle about `0`; in between it interpolates the two
angular parametrizations. -/
def pairOfPantsOutputCircleChart (z : ℝ × ℝ) : ℝ × ℝ :=
  endChart .inf (0, outputCircleAngle z)

/-- The output circle chart starts at the output loop of the core chart. -/
@[simp]
theorem pairOfPantsOutputCircleChart_mk_zero (t : ℝ) :
    pairOfPantsOutputCircleChart (0, t) = pairOfPantsCoreChart (1, t) := by
  rw [pairOfPantsOutputCircleChart, outputCircleAngle]
  simp only [smoothTransition.zero, sub_zero, one_mul, zero_mul, add_zero]
  exact endChart_inf_pairOfPantsOutputLift t

/-- The output circle chart ends at the circle at height `0` of the output end, run through by the
end chart. -/
@[simp]
theorem pairOfPantsOutputCircleChart_mk_one (t : ℝ) :
    pairOfPantsOutputCircleChart (1, t) = endChart .inf (0, t) := by
  rw [pairOfPantsOutputCircleChart, outputCircleAngle]
  simp only [smoothTransition.one, sub_self, zero_mul, one_mul, zero_add]

/-- The output circle chart is `1`-periodic in its second variable. -/
@[simp]
theorem pairOfPantsOutputCircleChart_apply_add_one (s t : ℝ) :
    pairOfPantsOutputCircleChart (s, t + 1) = pairOfPantsOutputCircleChart (s, t) := by
  have h : outputCircleAngle (s, t + 1) = outputCircleAngle (s, t) + 1 := by
    simp only [outputCircleAngle, pairOfPantsOutputLift_add_one]
    ring
  rw [pairOfPantsOutputCircleChart, pairOfPantsOutputCircleChart, h, endChart_add_one]

/-- The output circle chart is smooth. -/
theorem contDiff_pairOfPantsOutputCircleChart {n : ℕ∞} :
    ContDiff ℝ n pairOfPantsOutputCircleChart :=
  (contDiff_endChart _ n).comp (contDiff_const.prodMk contDiff_outputCircleAngle)

/-- The output circle chart takes values in the output circle `‖w‖ = 2`. -/
theorem norm_symm_pairOfPantsOutputCircleChart (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (pairOfPantsOutputCircleChart z)‖ = 2 := by
  rw [pairOfPantsOutputCircleChart, endChart_mk, ContinuousLinearEquiv.symm_apply_apply,
    Puncture.cylindricalEndLift_inf]
  beta_reduce
  rw [norm_mul, Complex.norm_exp]
  simp

private theorem pairOfPantsOutputCircleChart_mem_thricePuncturedSphereReal (z : ℝ × ℝ) :
    pairOfPantsOutputCircleChart z ∈ thricePuncturedSphereReal :=
  endChart_inf_mk_zero_mem_thricePuncturedSphereReal _

/-- **The output circle as a cylinder.** For a map `u` of the pair of pants `S` into a manifold
`M` which is `C²` on `S`, the composite of `u` with the output circle chart is a cylinder from
the loop of `u` along the output circle of the core chart to the loop of `u` along the circle at
height `0` of the output end, run through by its end chart. -/
theorem isLoopCylinder_comp_pairOfPantsOutputCircleChart {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u thricePuncturedSphereReal) :
    IsLoopCylinder I (u ∘ pairOfPantsOutputCircleChart) (fun t ↦ u (pairOfPantsCoreChart (1, t)))
      fun t ↦ u (endChart .inf (0, t)) where
  contMDiff := hu.comp_contMDiff contDiff_pairOfPantsOutputCircleChart.contMDiff
    pairOfPantsOutputCircleChart_mem_thricePuncturedSphereReal
  apply_add_one z := by
    simp only [Function.comp_apply, pairOfPantsOutputCircleChart_apply_add_one]
  apply_zero t := by
    simp only [Function.comp_apply, pairOfPantsOutputCircleChart_mk_zero]
  apply_one t := by
    simp only [Function.comp_apply, pairOfPantsOutputCircleChart_mk_one]

/-- **The output circle cylinder has no area.** For every two-form `φ` and every map `u` of the
pair of pants which is `C¹` on `S`, the integral of `φ` over `u` composed with the output circle
chart vanishes: the cylinder lies in the loop of `u` along the output circle. -/
theorem rectangleIntegral_comp_pairOfPantsOutputCircleChart {φ : RoughForm I M F 2}
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (a b : ℝ × ℝ) :
    rectangleIntegral φ (u ∘ pairOfPantsOutputCircleChart) a b = 0 := by
  have hγ : MDifferentiable 𝓘(ℝ, ℝ) I fun τ : ℝ ↦ u (endChart .inf (0, τ)) := by
    have hc : ContDiff ℝ 1 fun τ : ℝ ↦ endChart .inf (0, τ) :=
      (contDiff_endChart _ 1).comp (contDiff_const.prodMk contDiff_id)
    exact (hu.comp_contMDiff hc.contMDiff
      endChart_inf_mk_zero_mem_thricePuncturedSphereReal).mdifferentiable one_ne_zero
  exact rectangleIntegral_comp_eq_zero φ hγ (contDiff_outputCircleAngle (n := 1).differentiable
    one_ne_zero) a b

end TauCeti.Floer
