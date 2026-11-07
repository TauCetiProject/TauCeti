/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The curvature of perturbation data on the cylindrical ends of the pair of pants

Integrals of Floer data over the thrice-punctured sphere `S = ℂ ∖ {0, 1}` are computed end by
end, in the cylinder coordinates `(s, t)` of each end, through the end charts
`TauCeti.Floer.endChart`. This file reduces curvature bounds for perturbation data supported on
the ends to one-variable integrals along the ends. The target is a manifold `M` with a smooth
two-form `ω`, as in `TauCeti.Geometry.Symplectic.Floer.Manifold`; a symplectic vector space is
the case of the constant form `TauCeti.SymplecticForm.constSmooth`, whose curvature is the
vector-space curvature (`TauCeti.SymplecticForm.hamiltonianCurvature_constSmooth`).

* If a perturbation one-form `K` on `ℂ` is `P(±s) h(t) dt` on an end, so is its pullback along
  the end chart (`TauCeti.Floer.perturbationPullback_endChart_of_eq`), and its curvature there is
  `±P'(±s) h(t)`
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_perturbationPullback_endChart_of_eq`).
* If `K` vanishes wherever the signed longitudinal coordinate of every end is at most `1`, its
  curvature vanishes where all of them are less than `1`
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt`), and its
  integrated curvature along any map is at most the sum of its integrals over the images of the
  end strips (`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_le_sum_endStrip`).
* If the curvature of the pullback of `K` along the end chart is at most `f(s)` on the strip of an
  end, the integrated curvature over the image of the strip is at most `∫ f(s) ds`
  (`TauCeti.SmoothTwoForm.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le_lintegral`).
  In particular, where `K` is `P(±s) h(t) dt` with `|h| ≤ B`, it is at most `B ∫ |P'(±s)| ds`
  (`TauCeti.SmoothTwoForm.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le`).
* An integral over the strip of an end of a function of `s` alone is an integral over the
  half-line `±s > 1/2` (`TauCeti.Floer.setLIntegral_endStrip_fst`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 4, on
  cylindrical end coordinates of punctured Riemann surfaces, and Section 8.1, on the curvature of
  Hamiltonian perturbations.
-/

public noncomputable section

open Set Real Function MeasureTheory
open scoped Topology ENNReal Manifold

namespace TauCeti.Floer

open TauCeti.ThricePuncturedSphere

variable {X : Type*}

/-- An integral over the strip of the end `q` of a function of the longitudinal coordinate alone
is its integral over the half-line `±s > 1/2`, since the angular coordinate ranges over an
interval of length one. -/
theorem setLIntegral_endStrip_fst (q : Puncture) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in endStrip q, f z.1 = ∫⁻ s in {s | 1 / 2 < q.endSign * s}, f s := by
  have hvol : volume (Ico (-1 / 2 : ℝ) (1 / 2)) = 1 := by
    rw [Real.volume_Ico]
    norm_num
  rw [Measure.volume_eq_prod, endStrip_def,
    setLIntegral_prod (fun z : ℝ × ℝ ↦ f z.1) (hf.comp measurable_fst).aemeasurable]
  simp only [setLIntegral_const, hvol, mul_one]

/-- **Data of the form `P(±s) h(t) dt` on an end.** If the datum `K`, pulled back along the end
lift of `q`, is `P(±s) h(t) dt` on the part `±s > 0` of the end, then so is its pullback along the
end chart: it sends a tangent vector `v = (v₁, v₂)` of the cylinder to `v₂ · P(±s) h(t)`. -/
theorem perturbationPullback_endChart_of_eq {K : ℂ → X → ℂ →L[ℝ] ℝ} {q : Puncture} {P : ℝ → ℝ}
    {h : ℝ → X → ℝ}
    (hK : ∀ z : ℂ, 0 < q.endSign * z.re → ∀ x v,
      K (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
        v.im * (P (q.endSign * z.re) * h z.im x))
    {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) (v : ℝ × ℝ) (x : X) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v z x =
      v.2 * (P (q.endSign * z.1) * h z.2 x) := by
  rw [perturbationPullback_endChart_eq_cylindricalEndLift K]
  beta_reduce
  rw [hK _ (by simpa using hz)]
  simp

end TauCeti.Floer

/-! ### The curvature of data supported on the ends -/

namespace TauCeti.SmoothTwoForm

open Floer TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {K : ℂ → M → ℂ →L[ℝ] ℝ}

/-- **The curvature of a datum supported on the ends.** Let `K` be a perturbation one-form on
`ℂ` that vanishes wherever the signed longitudinal coordinate of every end is at most `1`. At a
point of `S` where the signed longitudinal coordinate of every end is less than `1`, `K` vanishes
nearby, and so does its curvature. -/
theorem hamiltonianCurvature_eq_zero_of_forall_endCoord_lt (ω : SmoothTwoForm I M)
    (hK : ∀ w, (∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) → ∀ x, K w x = 0)
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (h : ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1)
    (x : M) :
    ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z x = 0 := by
  have hev : ∀ᶠ z' in 𝓝 z, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z')).re < 1 := by
    refine Filter.eventually_all.2 fun q ↦ ?_
    have hc : ContinuousAt
        (fun z' ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z')).re) z :=
      continuousAt_const.mul
        (((q.contDiffAt_re_endCoord (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)
          (n := 0)).continuousAt).comp
          Complex.equivRealProdCLM.symm.continuous.continuousAt)
    exact hc.eventually (gt_mem_nhds (h q))
  have hK' : ∀ᶠ z' in 𝓝 z, ∀ y, K (Complex.equivRealProdCLM.symm z') y = 0 :=
    hev.mono fun z' hz' ↦ hK _ fun q ↦ (hz' q).le
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
    (hK'.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y])
    (hK'.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y]), hamiltonianCurvature_zero_left]
  simp

/-- **The integrated curvature of a datum supported on the ends.** Let `K` be a perturbation
one-form on `ℂ` that vanishes wherever the signed longitudinal coordinate of every end is at most
`1`. Then for every map `u` into the target, the integral of `|R_K(z, u(z))|` over the plane is at
most the sum over the three ends of its integrals over the images of their strips. -/
theorem lintegral_enorm_hamiltonianCurvature_le_sum_endStrip (ω : SmoothTwoForm I M)
    (hK : ∀ w, (∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) → ∀ x, K w x = 0)
    (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ ≤
      ∑ q : Puncture, ∫⁻ z in endChart q '' endStrip q,
        ‖ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ := by
  set N : Set (ℝ × ℝ) := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1}
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  -- Off the two punctures, the curvature is supported in the images of the strips of the ends.
  have hsupp : support (fun z ↦ ‖ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ) ⊆
        (⋃ q : Puncture, endChart q '' endStrip q) ∪ N := by
    intro z hz
    by_cases h₀ : Complex.equivRealProdCLM.symm z = 0
    · exact Or.inr (Or.inl ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₀)))
    by_cases h₁ : Complex.equivRealProdCLM.symm z = 1
    · exact Or.inr (Or.inr ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₁)))
    by_cases hq : ∃ q : Puncture,
        1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
    · obtain ⟨q, hq⟩ := hq
      exact Or.inl (mem_iUnion.2 ⟨q, mem_image_endChart ⟨h₀, h₁⟩ hq⟩)
    · simp only [not_exists, not_lt] at hq
      refine absurd ?_ hz
      simp [ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt hK ⟨h₀, h₁⟩
        (fun q ↦ (hq q).trans_lt (by norm_num))]
  calc _ = ∫⁻ z in (⋃ q : Puncture, endChart q '' endStrip q) ∪ N, ‖ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ = _ := tsum_fintype _

/-- **The curvature of data of the form `P(±s) h(t) dt` on an end.** If the datum `K`, pulled back
along the end lift of `q`, is `P(±s) h(t) dt` on the part `±s > 0` of the end, then the curvature
of its pullback along the end chart is `±P'(±s) h(t)` there. -/
theorem hamiltonianCurvature_perturbationPullback_endChart_of_eq (ω : SmoothTwoForm I M)
    {q : Puncture} {P : ℝ → ℝ} {h : ℝ → M → ℝ}
    (hK : ∀ z : ℂ, 0 < q.endSign * z.re → ∀ x v,
      K (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
        v.im * (P (q.endSign * z.re) * h z.im x))
    {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) {x : M}
    (hP : DifferentiableAt ℝ P (q.endSign * z.1))
    (hhx : DifferentiableAt ℝ (fun t ↦ h t x) z.2) :
    ω.hamiltonianCurvature
        (perturbationPullback (endChart q) (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (endChart q) (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag) z x =
      q.endSign * deriv P (q.endSign * z.1) * h z.2 x := by
  have hU : {w : ℝ × ℝ | 0 < q.endSign * w.1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_const.mul continuous_fst)).mem_nhds hz
  have hs : perturbationPullback (endChart q) (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal =ᶠ[𝓝 z]
        fun _ _ ↦ 0 := by
    filter_upwards [hU] with w hw
    funext y
    rw [perturbationPullback_endChart_of_eq hK hw, stdComplexLineReal_snd, zero_mul]
  have ht : perturbationPullback (endChart q) (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag =ᶠ[𝓝 z]
        fun w y ↦ P (q.endSign * w.1) * h w.2 y := by
    filter_upwards [hU] with w hw
    funext y
    rw [perturbationPullback_endChart_of_eq hK hw, stdComplexLineImag_snd, one_mul]
  have hβ : HasDerivAt (fun s ↦ P (q.endSign * s))
      (deriv P (q.endSign * z.1) * q.endSign) z.1 :=
    hP.hasDerivAt.comp z.1 ((hasDerivAt_id' z.1).const_mul q.endSign |>.congr_deriv (by ring))
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht,
    ω.hamiltonianCurvature_continuation (β := fun s ↦ P (q.endSign * s)) hβ.differentiableAt hhx,
    hβ.deriv]
  ring

/-- **The integrated curvature over an end strip, from a pointwise bound.** Let `K` be a
perturbation one-form on `ℂ` which is differentiable on `S` separately in the domain point and in
the target point. If the curvature of its pullback along the end chart of `q` is at most `f(s)` at
every point `(s, t)` of the strip of `q`, for a measurable `f`, then for every map `u` into the
target, the integral of `|R_K(z, u(z))|` over the image of the strip of `q` is at most
`∫ f(s) ds`. -/
theorem setLIntegral_image_endChart_enorm_hamiltonianCurvature_le_lintegral
    (ω : SmoothTwoForm I M) {q : Puncture}
    (hKd : ∀ w : ℂ, w ≠ 0 ∧ w ≠ 1 → ∀ x v, DifferentiableAt ℝ (fun w' ↦ K w' x v) w)
    (hKx : ∀ w : ℂ, w ≠ 0 ∧ w ≠ 1 → ∀ x v, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ K w y v) x)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hR : ∀ z ∈ endStrip q, ∀ x, ‖ω.hamiltonianCurvature
      (perturbationPullback (endChart q) (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
      (perturbationPullback (endChart q) (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag) z x‖ₑ ≤
      f z.1)
    (u : ℝ × ℝ → M) :
    ∫⁻ z in endChart q '' endStrip q,
        ‖ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ ≤
      ∫⁻ s, f s := by
  have hS {z : ℝ × ℝ} (hz : z ∈ endStrip q) :=
    mem_thricePuncturedSphereReal_iff.1
      (endChart_mem_thricePuncturedSphereReal (endSign_mul_pos_of_mem_endStrip hz))
  -- The datum is differentiable in the domain point, read in real coordinates, at points of `S`.
  have hdom {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) (x : M) (v : ℂ) :
      DifferentiableAt ℝ (fun z' ↦ K (Complex.equivRealProdCLM.symm z') x v) z :=
    (hKd _ hz x v).comp z Complex.equivRealProdCLM.symm.differentiableAt
  rw [ω.lintegral_enorm_hamiltonianCurvature_image (measurableSet_endStrip q) (injOn_endChart q)
    (fun w _ ↦ (contDiff_endChart q _).contDiffAt) (fun w hw ↦ hdom (hS hw) _ 1)
    (fun w hw ↦ hdom (hS hw) _ _) (fun w hw ↦ hKx _ (hS hw) _ 1) (fun w hw ↦ hKx _ (hS hw) _ _)]
  calc _ ≤ ∫⁻ z in endStrip q, f z.1 :=
        setLIntegral_mono' (measurableSet_endStrip q) fun z hz ↦ hR z hz _
    _ = ∫⁻ s in {s | 1 / 2 < q.endSign * s}, f s := setLIntegral_endStrip_fst q hf
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- **The integrated curvature over an end strip.** Let `K` be a perturbation one-form on `ℂ`
which is differentiable on `S` separately in the domain point and in the target point, and which,
pulled back along the end lift of `q`, is `P(±s) h(t) dt` on the part `±s > 0` of the end, with
`|h| ≤ B`. Then for every map `u` into the target, the integral of `|R_K(z, u(z))|` over the image
of the strip of `q` is at most `B` times the total variation `∫ |P'(±s)| ds` of the profile `P`. -/
theorem setLIntegral_image_endChart_enorm_hamiltonianCurvature_le (ω : SmoothTwoForm I M)
    {q : Puncture} {P : ℝ → ℝ} {h : ℝ → M → ℝ}
    (hKd : ∀ w : ℂ, w ≠ 0 ∧ w ≠ 1 → ∀ x v, DifferentiableAt ℝ (fun w' ↦ K w' x v) w)
    (hKx : ∀ w : ℂ, w ≠ 0 ∧ w ≠ 1 → ∀ x v, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ K w y v) x)
    (hK : ∀ z : ℂ, 0 < q.endSign * z.re → ∀ x v,
      K (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
        v.im * (P (q.endSign * z.re) * h z.im x))
    (hP : Differentiable ℝ P) (hh : ∀ x, Differentiable ℝ fun t ↦ h t x) {B : ℝ}
    (hB : ∀ t x, |h t x| ≤ B) (u : ℝ × ℝ → M) :
    ∫⁻ z in endChart q '' endStrip q,
        ‖ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ ≤
      (∫⁻ s, ‖deriv P (q.endSign * s)‖ₑ) * ENNReal.ofReal B := by
  have hm : Measurable fun s ↦ ‖deriv P (q.endSign * s)‖ₑ * ENNReal.ofReal B :=
    ((measurable_deriv P).comp (measurable_const.mul measurable_id)).enorm.mul_const _
  refine (ω.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le_lintegral hKd hKx hm
    (fun z hz x ↦ ?_) u).trans_eq (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top)
  rw [ω.hamiltonianCurvature_perturbationPullback_endChart_of_eq hK
    (endSign_mul_pos_of_mem_endStrip hz) (hP _) (hh _ _), enorm_mul, enorm_mul,
    Real.enorm_eq_ofReal_abs q.endSign, abs_endSign, ENNReal.ofReal_one, one_mul,
    Real.enorm_eq_ofReal_abs (h _ _)]
  gcongr
  exact hB _ _

end TauCeti.SmoothTwoForm

