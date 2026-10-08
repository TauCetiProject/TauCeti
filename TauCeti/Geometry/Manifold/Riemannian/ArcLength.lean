/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Arc-length reparametrization of regular Riemannian curves

Every regular `C¹` curve on a compact interval admits a unit-speed forward reparametrization,
whether it is `C¹` on an open parameter set containing the interval or only within the interval
itself. The new parameter is the accumulated Riemannian speed

`s(t) = ∫ r in a..t, ‖γ'(r)‖`.

Extending the speed by constants outside `[a, b]` makes `s` a `C¹` increasing bijection of `ℝ`
with positive derivative. Its inverse `ψ` is `C¹`, with derivative the reciprocal speed, and
the chain rule then gives `‖(γ ∘ ψ)'‖ = 1`. Besides unit speed, the theorems record the inverse
identities, endpoint values, monotonicity, and invariance of `Manifold.pathELength`, making the
results usable without unfolding their construction.

## Main results

* `ContMDiffOn.continuousOn_norm_curveVelocityWithin`: the speed of a `C¹` curve is continuous on
  a parameter set with unique derivatives.
* `ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin`: the Riemannian length of a
  `C¹` curve over a compact interval is the integral of its speed.
* `TauCeti.Manifold.exists_unit_speed_reparametrization`: a regular curve, `C¹` on an open set
  containing `[a, b]`, has a `C¹`, unit-speed reparametrization on the interval from zero to its
  length.
* `TauCeti.Manifold.exists_unit_speed_reparametrization_Icc`: the same for a curve which is only
  `C¹` within `[a, b]`, with velocities read within the parameter intervals.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 2.49(a).
* The proof is adapted from `LeeLib/Ch02/ArcLengthReparametrization.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`. This version works at the
  `C¹` regularity of the theorem and uses Mathlib's Riemannian bundle and path-length APIs.
-/

public section

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-! ### Length as the integral of speed -/

/-- The Riemannian speed of a `C¹` curve, read within a parameter set with unique derivatives, is
continuous on that set. -/
theorem _root_.ContMDiffOn.continuousOn_norm_curveVelocityWithin {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (hs : UniqueMDiffOn 𝓘(ℝ, ℝ) s) :
    ContinuousOn (fun t ↦ ‖curveVelocityWithin I γ s t‖) s := by
  have hlift : ContinuousOn
      (fun t ↦ (TotalSpace.mk' E (γ t) (curveVelocityWithin I γ s t) : TangentBundle I M)) s :=
    (ContMDiffOn.continuousOn_curveVelocityLiftWithin hγ hs).congr fun t _ ↦
      (curveVelocityLiftWithin_apply (I := I) γ s t).symm
  exact (TauCeti.continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp_continuousOn hlift

/-- The Riemannian length of a `C¹` curve over a compact interval inside its parameter set is the
integral of its speed. -/
theorem _root_.ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
    {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (hs : UniqueMDiffOn 𝓘(ℝ, ℝ) s)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    Manifold.pathELength I γ a b =
      ENNReal.ofReal (∫ t in a..b, ‖curveVelocityWithin I γ s t‖) := by
  have hcont : ContinuousOn (fun t ↦ ‖curveVelocityWithin I γ s t‖) (Icc a b) :=
    (hγ.continuousOn_norm_curveVelocityWithin hs).mono hsub
  have hint : IntegrableOn (fun t ↦ ‖curveVelocityWithin I γ s t‖) (Ioo a b) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ ↦ norm_nonneg _),
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have hmem : s ∈ 𝓝 t := mem_nhds_iff.2 ⟨Ioo a b, Ioo_subset_Icc_self.trans hsub, isOpen_Ioo, ht⟩
  rw [ofReal_norm, curveVelocityWithin_of_mem_nhds hmem, curveVelocity_apply]
  -- both sides are the Riemannian norm at `γ t`; they differ only in how the fibre is presented
  rfl

/-! ### Inverting accumulated speed -/

/-- Accumulated speed `t ↦ ∫ r in a..t, v r`, for a speed `v` continuous and positive on `[a, b]`,
has an inverse `ψ` on `[0, ∫ r in a..b, v r]` which is the restriction of a strictly increasing
`C¹` function on `ℝ`, maps into `[a, b]`, and has derivative the reciprocal speed. -/
private theorem exists_contDiff_inverse_intervalIntegral {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t) :
    ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ ContDiff ℝ 1 ψ ∧
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, v r) = t) ∧
      ∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, v r),
        ψ s ∈ Icc a b ∧ (∫ r in a..ψ s, v r) = s ∧ HasDerivAt ψ (v (ψ s))⁻¹ s := by
  -- Extend the speed by constants outside `[a, b]`. Its primitive `φ` is then `C¹`, with
  -- derivative bounded below by a positive constant, hence an increasing bijection of `ℝ`.
  let c : ℝ → ℝ := fun t ↦ max a (min b t)
  have hcmem : ∀ t, c t ∈ Icc a b := fun t ↦ ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hcid : ∀ t ∈ Icc a b, c t = t := fun t ht ↦ by simp [c, ht.1, ht.2]
  let w : ℝ → ℝ := fun t ↦ v (c t)
  have hw : Continuous w :=
    hv.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) hcmem
  have hwpos : ∀ t, 0 < w t := fun t ↦ hpos _ (hcmem t)
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hv
  have hm : 0 < v x₀ := hpos x₀ hx₀
  have hwm : ∀ t, v x₀ ≤ w t := fun t ↦ hmin (hcmem t)
  let φ : ℝ → ℝ := fun t ↦ ∫ r in a..t, w r
  have hφ : ∀ t, HasDerivAt φ (w t) t := fun t ↦ (hw.integral_hasStrictDerivAt a t).hasDerivAt
  have hφcont : Continuous φ := continuous_iff_continuousAt.2 fun t ↦ (hφ t).continuousAt
  have hφmono : StrictMono φ := strictMono_of_hasDerivAt_pos hφ hwpos
  have hg : Monotone fun t ↦ φ t - v x₀ * t := by
    have hgd : ∀ t, HasDerivAt (fun t ↦ φ t - v x₀ * t) (w t - v x₀) t := fun t ↦
      (hφ t).sub (by simpa using (hasDerivAt_id t).const_mul (v x₀))
    refine monotone_of_deriv_nonneg (fun t ↦ (hgd t).differentiableAt) fun t ↦ ?_
    rw [(hgd t).deriv]
    exact sub_nonneg.2 (hwm t)
  have htop : Tendsto φ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_left _ (φ 0) (tendsto_id.const_mul_atTop hm))
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h := hg ht
    simp only [mul_zero, sub_zero] at h
    simp only [id]
    linarith
  have hbot : Tendsto φ atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_
      (tendsto_atBot_add_const_left _ (φ 0) (tendsto_id.const_mul_atBot hm))
    filter_upwards [eventually_le_atBot 0] with t ht
    have h := hg ht
    simp only [mul_zero, sub_zero] at h
    simp only [id]
    linarith
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective φ hφmono (hφcont.surjective htop hbot)
  let ψ : ℝ → ℝ := e.symm
  have hψφ : ∀ t, ψ (φ t) = t := e.symm_apply_apply
  have hφψ : ∀ s, φ (ψ s) = s := e.apply_symm_apply
  have hψcont : Continuous ψ := e.symm.continuous
  have hψd : ∀ s, HasDerivAt ψ (w (ψ s))⁻¹ s := fun s ↦
    HasDerivAt.of_local_left_inverse hψcont.continuousAt (hφ (ψ s)) (hwpos _).ne'
      (Eventually.of_forall hφψ)
  have hψC1 : ContDiff ℝ 1 ψ := by
    refine contDiff_one_iff_deriv.2 ⟨fun s ↦ (hψd s).differentiableAt, ?_⟩
    rw [show deriv ψ = fun s ↦ (w (ψ s))⁻¹ from funext fun s ↦ (hψd s).deriv]
    exact (hw.comp hψcont).inv₀ fun s ↦ (hwpos _).ne'
  -- On `[a, b]` the extended primitive is the accumulated speed itself.
  have hφeq : ∀ t ∈ Icc a b, φ t = ∫ r in a..t, v r := fun t ht ↦
    intervalIntegral.integral_congr fun r hr ↦
      congrArg v (hcid r (uIcc_subset_Icc (left_mem_Icc.2 hab) ht hr))
  have hψa : ψ 0 = a := by
    simpa [φ] using hψφ a
  refine ⟨ψ, e.symm.strictMono, hψC1, fun t ht ↦ by rw [← hφeq t ht, hψφ], fun s hs ↦ ?_⟩
  have hψs : ψ s ∈ Icc a b := by
    constructor
    · exact hψa ▸ e.symm.monotone hs.1
    · rw [← hψφ b, hφeq b (right_mem_Icc.2 hab)]
      exact e.symm.monotone hs.2
  refine ⟨hψs, by rw [← hφeq _ hψs, hφψ], ?_⟩
  simpa only [w, hcid _ hψs] using hψd s

/-! ### Unit-speed reparametrization -/

/-- **Arc-length reparametrization of a regular curve.** Let `γ` be `C¹` on an open set `J`
containing `[a, b]`, with nonzero velocity along `[a, b]`. There is an increasing `C¹` function
`ψ` from
`[0, ∫_a^b ‖γ'(t)‖ dt]` to `[a, b]` which inverts accumulated length. The curve `γ ∘ ψ`
has the same endpoints and path length as `γ`, and its velocity has norm one throughout its
parameter interval. The accumulated-speed endpoint is identified with the real value of
`Manifold.pathELength`.

The case `a = b` is included: the new parameter interval is then the singleton `{0}`. For a curve
which is only `C¹` within `[a, b]`, see `exists_unit_speed_reparametrization_Icc`. -/
theorem exists_unit_speed_reparametrization {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ J) (hreg : ∀ t ∈ Icc a b, curveVelocity I γ t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, ‖curveVelocity I γ r‖) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocity I γ r‖),
        (∫ r in a..ψ s, ‖curveVelocity I γ r‖) = s) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocity I γ r‖), ψ s ∈ Icc a b) ∧
      StrictMonoOn ψ (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) ∧
      ContDiffOn ℝ 1 ψ (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ) (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) ∧
      (γ ∘ ψ) 0 = γ a ∧
      (γ ∘ ψ) (∫ r in a..b, ‖curveVelocity I γ r‖) = γ b ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocity I γ r‖),
        ‖curveVelocity I (γ ∘ ψ) s‖ = 1) ∧
      Manifold.pathELength I (γ ∘ ψ) 0 (∫ r in a..b, ‖curveVelocity I γ r‖) =
        Manifold.pathELength I γ a b ∧
      (∫ r in a..b, ‖curveVelocity I γ r‖) = (Manifold.pathELength I γ a b).toReal := by
  -- On an open parameter set the velocity is the velocity within that set.
  have hvJ : ContinuousOn (fun t ↦ ‖curveVelocity I γ t‖) J :=
    (hγ.continuousOn_norm_curveVelocityWithin hJ.uniqueMDiffOn).congr fun t ht ↦ by
      dsimp only
      rw [curveVelocityWithin_of_mem_nhds (hJ.mem_nhds ht)]
  have hv := hvJ.mono hsub
  obtain ⟨ψ, hψmono, hψC1, hleft, hright⟩ :=
    exists_contDiff_inverse_intervalIntegral hab hv fun t ht ↦ norm_pos_iff.2 (hreg t ht)
  set L := ∫ r in a..b, ‖curveVelocity I γ r‖ with hLdef
  have hψa : ψ 0 = a := by simpa using hleft a (left_mem_Icc.2 hab)
  have hψb : ψ L = b := hleft b (right_mem_Icc.2 hab)
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _
  have hlength : Manifold.pathELength I (γ ∘ ψ) 0 L = Manifold.pathELength I γ a b := by
    have h := Manifold.pathELength_comp_of_monotoneOn (I := I) hL (hψmono.monotone.monotoneOn _)
      (hψC1.differentiable one_ne_zero).differentiableOn
      (by rw [hψa, hψb]; exact (hγ.mdifferentiableOn one_ne_zero).mono hsub)
    simpa only [hψa, hψb] using h
  have hlength_toReal : L = (Manifold.pathELength I γ a b).toReal := by
    rw [hLdef, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (hv.integrableOn_compact isCompact_Icc).aestronglyMeasurable,
      Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    congr 1
    refine lintegral_congr fun t ↦ ?_
    rw [curveVelocity_apply, ofReal_norm]
    rfl
  refine ⟨ψ, hleft, fun s hs ↦ (hright s hs).2.1, fun s hs ↦ (hright s hs).1,
    hψmono.strictMonoOn _, hψC1.contDiffOn,
    hγ.comp (contMDiffOn_iff_contDiffOn.2 hψC1.contDiffOn) fun s hs ↦ hsub (hright s hs).1,
    by rw [Function.comp_apply, hψa], by rw [Function.comp_apply, hψb], fun s hs ↦ ?_,
    hlength, hlength_toReal⟩
  obtain ⟨hψs, -, hψd⟩ := hright s hs
  have hpos : 0 < ‖curveVelocity I γ (ψ s)‖ := norm_pos_iff.2 (hreg _ hψs)
  rw [curveVelocity_comp hψd
      ((hγ.contMDiffAt (hJ.mem_nhds (hsub hψs))).mdifferentiableAt one_ne_zero),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  exact inv_mul_cancel₀ hpos.ne'

/-- **Arc-length reparametrization of a regular curve on a closed interval.** Let `γ` be `C¹`
within `[a, b]`, where `a < b`, with nonzero velocity within `[a, b]` at every point of `[a, b]`.
There is an increasing `C¹` function `ψ` from `[0, ∫_a^b ‖γ'(t)‖ dt]` onto `[a, b]` which inverts
accumulated length. The curve `γ ∘ ψ` has the same endpoints and path length as `γ`, and its
velocity within its parameter interval has norm one throughout that interval. The
accumulated-speed endpoint is identified with the real value of `Manifold.pathELength`.

Unlike `exists_unit_speed_reparametrization`, nothing is assumed about `γ` outside `[a, b]`, and
all velocities are read within the parameter interval. The interval is nondegenerate because a
velocity within a singleton carries no information. -/
theorem exists_unit_speed_reparametrization_Icc {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hreg : ∀ t ∈ Icc a b, curveVelocityWithin I γ (Icc a b) t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, ‖curveVelocityWithin I γ (Icc a b) r‖) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖),
        (∫ r in a..ψ s, ‖curveVelocityWithin I γ (Icc a b) r‖) = s) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖),
        ψ s ∈ Icc a b) ∧
      StrictMonoOn ψ (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) ∧
      ContDiffOn ℝ 1 ψ (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ)
        (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) ∧
      (γ ∘ ψ) 0 = γ a ∧
      (γ ∘ ψ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖) = γ b ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖),
        ‖curveVelocityWithin I (γ ∘ ψ)
          (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) s‖ = 1) ∧
      Manifold.pathELength I (γ ∘ ψ) 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖) =
        Manifold.pathELength I γ a b ∧
      (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖) =
        (Manifold.pathELength I γ a b).toReal := by
  have hU : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) :=
    uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc hab)
  obtain ⟨ψ, hψmono, hψC1, hleft, hright⟩ :=
    exists_contDiff_inverse_intervalIntegral hab.le
      (hγ.continuousOn_norm_curveVelocityWithin hU) fun t ht ↦ norm_pos_iff.2 (hreg t ht)
  set L := ∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖ with hLdef
  have hψa : ψ 0 = a := by simpa using hleft a (left_mem_Icc.2 hab.le)
  have hψb : ψ L = b := hleft b (right_mem_Icc.2 hab.le)
  have hL : 0 < L := hψmono.lt_iff_lt.1 (by rw [hψa, hψb]; exact hab)
  have hmaps : MapsTo ψ (Icc 0 L) (Icc a b) := fun s hs ↦ (hright s hs).1
  have hlength : Manifold.pathELength I (γ ∘ ψ) 0 L = Manifold.pathELength I γ a b := by
    have h := Manifold.pathELength_comp_of_monotoneOn (I := I) hL.le (hψmono.monotone.monotoneOn _)
      (hψC1.differentiable one_ne_zero).differentiableOn
      (by rw [hψa, hψb]; exact hγ.mdifferentiableOn one_ne_zero)
    simpa only [hψa, hψb] using h
  have hlength_toReal : L = (Manifold.pathELength I γ a b).toReal := by
    rw [hγ.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hU hab.le subset_rfl,
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab.le fun _ _ ↦ norm_nonneg _)]
  refine ⟨ψ, hleft, fun s hs ↦ (hright s hs).2.1, hmaps, hψmono.strictMonoOn _,
    hψC1.contDiffOn, hγ.comp (contMDiffOn_iff_contDiffOn.2 hψC1.contDiffOn) hmaps,
    by rw [Function.comp_apply, hψa], by rw [Function.comp_apply, hψb], fun s hs ↦ ?_,
    hlength, hlength_toReal⟩
  obtain ⟨hψs, -, hψd⟩ := hright s hs
  have hpos : 0 < ‖curveVelocityWithin I γ (Icc a b) (ψ s)‖ := norm_pos_iff.2 (hreg _ hψs)
  rw [curveVelocityWithin_comp hψd.hasDerivWithinAt hmaps
      (hγ.mdifferentiableOn one_ne_zero _ hψs) (uniqueDiffOn_Icc hL s hs),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  exact inv_mul_cancel₀ hpos.ne'

end TauCeti.Manifold

end
