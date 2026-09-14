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
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Arc-length reparametrization of regular Riemannian curves

Every regular `C¹` curve on an open parameter set admits a unit-speed forward
reparametrization on each compact subinterval. The new parameter is the accumulated Riemannian
speed

`s(t) = ∫ r in a..t, ‖γ'(r)‖`.

Its derivative is the positive continuous speed, so `s` is strictly increasing. The one-variable
inverse function theorem supplies a `C¹` inverse `ψ`; the chain rule then gives
`‖(γ ∘ ψ)'‖ = 1`. Besides unit speed, the theorem records the inverse identities, endpoint
values, monotonicity, and invariance of `Manifold.pathELength`, making the result usable without
unfolding its construction.

## Main result

* `TauCeti.Manifold.exists_unit_speed_reparametrization`: a regular `C¹` curve has a `C¹`,
  unit-speed reparametrization on the interval from zero to its length.

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

/-- **Arc-length reparametrization of a regular curve.** Let `γ` be `C¹` on an open set `J`
containing `[a, b]`, with nonzero velocity along `[a, b]`. There is an increasing `C¹` function
`ψ` from
`[0, ∫_a^b ‖γ'(t)‖ dt]` to `[a, b]` which inverts accumulated length. The curve `γ ∘ ψ`
has the same endpoints and path length as `γ`, and its velocity has norm one throughout its
parameter interval. The accumulated-speed endpoint is identified with the real value of
`Manifold.pathELength`.

The case `a = b` is included: the new parameter interval is then the singleton `{0}`. -/
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
  let v : ℝ → ℝ := fun t ↦ ‖curveVelocity I γ t‖
  have hvelocity : ContinuousOn (curveVelocityLift I γ) J :=
    ContMDiffOn.continuousOn_curveVelocityLift hγ hJ
  have hvelocity' : ContinuousOn
      (fun t ↦ (TotalSpace.mk' E (γ t) (curveVelocity I γ t) : TangentBundle I M)) J := by
    simpa only [← curveVelocityLift_apply] using hvelocity
  have hsq : ContinuousOn
      (fun t ↦ inner ℝ (curveVelocity I γ t) (curveVelocity I γ t)) J := by
    exact hvelocity'.inner_bundle (F := E) hvelocity'
  have hv : ContinuousOn v J := by
    refine (Real.continuous_sqrt.comp_continuousOn hsq).congr fun t _ ↦ ?_
    exact (norm_eq_sqrt_real_inner (curveVelocity I γ t)).symm
  let V : Set ℝ := {t | t ∈ J ∧ 0 < v t}
  have hV_open : IsOpen V := by
    have hV_eq : V = J ∩ v ⁻¹' Ioi 0 := by
      ext t
      simp only [V, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
    rw [hV_eq]
    exact hv.isOpen_inter_preimage hJ isOpen_Ioi
  have haV : a ∈ V := ⟨hsub (left_mem_Icc.mpr hab),
    norm_pos_iff.mpr (hreg a (left_mem_Icc.mpr hab))⟩
  have hbV : b ∈ V := ⟨hsub (right_mem_Icc.mpr hab),
    norm_pos_iff.mpr (hreg b (right_mem_Icc.mpr hab))⟩
  -- Enlarge `[a, b]` slightly inside the regular locus, so the inverse constructed below is
  -- smooth at both endpoints of the new parameter interval as well as in its interior.
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hV_open a haV
  obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hV_open b hbV
  let δ : ℝ := min εa εb / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  let U : Set ℝ := Ioo (a - δ) (b + δ)
  have hU_open : IsOpen U := isOpen_Ioo
  have hU_sub : U ⊆ V := by
    intro t ht
    have hδεa : δ ≤ εa := (half_le_self (lt_min hεa hεb).le).trans (min_le_left εa εb)
    have hδεb : δ ≤ εb := (half_le_self (lt_min hεa hεb).le).trans (min_le_right εa εb)
    rcases lt_or_ge t a with hta | hta
    · apply hballa
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      have ht_lower := ht.1
      constructor <;> linarith
    rcases le_or_gt t b with htb | htb
    · exact ⟨hsub ⟨hta, htb⟩, norm_pos_iff.mpr (hreg t ⟨hta, htb⟩)⟩
    · apply hballb
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      have ht_upper := ht.2
      constructor <;> linarith
  have hIccU : Icc a b ⊆ U := fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have haU : a ∈ U := hIccU (left_mem_Icc.mpr hab)
  have hbU : b ∈ U := hIccU (right_mem_Icc.mpr hab)
  have hU_ord : ∀ s ∈ U, ∀ t ∈ U, Icc s t ⊆ U := by
    intro s hs t ht r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hU_J : U ⊆ J := fun t ht ↦ (hU_sub ht).1
  have hvU : ContinuousOn v U := hv.mono hU_J
  have hInt : ∀ s ∈ U, ∀ t ∈ U, IntervalIntegrable v volume s t := by
    intro s hs t ht
    apply (hvU.mono ?_).intervalIntegrable
    rcases le_total s t with hst | hts
    · rw [uIcc_of_le hst]
      exact hU_ord s hs t ht
    · rw [uIcc_of_ge hts]
      exact hU_ord t ht s hs
  have hlength_toReal :
      (∫ r in a..b, v r) = (Manifold.pathELength I γ a b).toReal := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
        (hInt a haU b hbU)).aestronglyMeasurable]
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    congr 1
    apply lintegral_congr
    intro t
    rw [curveVelocity_apply, ofReal_norm]
    rfl
  -- The accumulated-speed function is `C¹` with positive derivative, hence strictly increasing.
  let φ : ℝ → ℝ := fun t ↦ ∫ r in a..t, v r
  have hφ_deriv : ∀ t ∈ U, HasDerivAt φ (v t) t := by
    intro t ht
    exact intervalIntegral.integral_hasDerivAt_right (hInt a haU t ht)
      (hvU.stronglyMeasurableAtFilter hU_open t ht)
      ((hvU t ht).continuousAt (hU_open.mem_nhds ht))
  have hφ_strict : StrictMonoOn φ U := by
    have hU_convex : Convex ℝ U := convex_Ioo _ _
    apply strictMonoOn_of_deriv_pos hU_convex
    · exact fun t ht ↦ (hφ_deriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [hU_open.interior_eq] at ht
      rw [(hφ_deriv t ht).deriv]
      exact (hU_sub ht).2
  have hφ_contDiff : ContDiffOn ℝ 1 φ U := by
    rw [contDiffOn_one_iff_derivWithin hU_open.uniqueDiffOn]
    refine ⟨fun t ht ↦ (hφ_deriv t ht).differentiableAt.differentiableWithinAt, ?_⟩
    refine hvU.congr fun t ht ↦ ?_
    rw [derivWithin_of_isOpen hU_open ht, (hφ_deriv t ht).deriv]
  have hφ_inj : InjOn φ U := hφ_strict.injOn
  -- Its set-theoretic inverse agrees locally with the inverse supplied by the inverse function
  -- theorem. This gives both an open domain of definition and a `C¹` inverse there.
  let ψ : ℝ → ℝ := Function.invFunOn φ U
  have hleft : ∀ t ∈ U, ψ (φ t) = t := fun t ht ↦ hφ_inj.leftInvOn_invFunOn ht
  let W : Set ℝ := φ '' U
  have hψ_local : ∀ t ∈ U, HasDerivAt ψ (v t)⁻¹ (φ t) ∧ W ∈ 𝓝 (φ t) := by
    intro t ht
    have hv_ne : v t ≠ 0 := (hU_sub ht).2.ne'
    have hφ_strictDeriv : HasStrictDerivAt φ (v t) t := by
      have h := (hφ_contDiff.contDiffAt (hU_open.mem_nhds ht)).hasStrictDerivAt one_ne_zero
      rwa [(hφ_deriv t ht).deriv] at h
    let ζ : ℝ → ℝ := hφ_strictDeriv.localInverse φ _ t hv_ne
    have hζ_deriv : HasDerivAt ζ (v t)⁻¹ (φ t) :=
      (hφ_strictDeriv.to_localInverse hv_ne).hasDerivAt
    have hζ_t : ζ (φ t) = t :=
      (hφ_strictDeriv.eventually_left_inverse hv_ne).self_of_nhds
    have hζ_mem : ∀ᶠ x in 𝓝 (φ t), ζ x ∈ U := by
      apply hζ_deriv.continuousAt.eventually_mem
      simpa only [hζ_t] using hU_open.mem_nhds ht
    have hψζ : ψ =ᶠ[𝓝 (φ t)] ζ := by
      filter_upwards [hφ_strictDeriv.eventually_right_inverse hv_ne, hζ_mem] with x hx hxU
      have hex : ∃ y ∈ U, φ y = x := ⟨ζ x, hxU, hx⟩
      apply hφ_inj (Function.invFunOn_mem hex) hxU
      exact (Function.invFunOn_eq hex).trans hx.symm
    refine ⟨hζ_deriv.congr_of_eventuallyEq hψζ, ?_⟩
    have hmap := hφ_strictDeriv.map_nhds_eq hv_ne
    rw [← hmap]
    exact mem_map.mpr (mem_of_superset (hU_open.mem_nhds ht) (subset_preimage_image φ U))
  have hW_open : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨t, ht, rfl⟩
    exact (hψ_local t ht).2
  have hψ_mem : ∀ s ∈ W, ψ s ∈ U := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hleft t ht]
    exact ht
  have hψ_deriv : ∀ s ∈ W, HasDerivAt ψ (v (ψ s))⁻¹ s := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hleft t ht]
    exact (hψ_local t ht).1
  have hψ_diff : DifferentiableOn ℝ ψ W := fun s hs ↦
    (hψ_deriv s hs).differentiableAt.differentiableWithinAt
  have hψ_contDiff : ContDiffOn ℝ 1 ψ W := by
    rw [contDiffOn_one_iff_derivWithin hW_open.uniqueDiffOn]
    refine ⟨hψ_diff, ?_⟩
    have hcomp : ContinuousOn (fun s ↦ v (ψ s)) W :=
      hvU.comp hψ_diff.continuousOn hψ_mem
    have hinv : ContinuousOn (fun s ↦ (v (ψ s))⁻¹) W :=
      hcomp.inv₀ fun s hs ↦ (hU_sub (hψ_mem s hs)).2.ne'
    refine hinv.congr fun s hs ↦ ?_
    rw [derivWithin_of_isOpen hW_open hs, (hψ_deriv s hs).deriv]
  -- The intermediate value theorem identifies the whole closed parameter interval inside the
  -- open image `W` where the inverse is `C¹`.
  have hφa : φ a = 0 := by simp [φ]
  have hφ_cont : ContinuousOn φ (Icc a b) :=
    (hφ_contDiff.mono hIccU).continuousOn
  have himage : Icc (0 : ℝ) (φ b) ⊆ φ '' Icc a b := by
    have h := intermediate_value_Icc hab hφ_cont
    rwa [hφa] at h
  have hL : 0 ≤ φ b := by
    rw [← hφa]
    exact hφ_strict.monotoneOn haU hbU hab
  have hIccW : Icc (0 : ℝ) (φ b) ⊆ W := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := himage hs
    exact ⟨t, hIccU ht, rfl⟩
  have hright : ∀ s ∈ Icc (0 : ℝ) (φ b), φ (ψ s) = s := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := himage hs
    rw [← hts, hleft t (hIccU ht)]
  have hψ_Icc : ∀ s ∈ Icc (0 : ℝ) (φ b), ψ s ∈ Icc a b := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := himage hs
    rw [← hts, hleft t (hIccU ht)]
    exact ht
  have hψ_strict : StrictMonoOn ψ (Icc (0 : ℝ) (φ b)) := by
    intro s hs t ht hst
    have hsU := hψ_mem s (hIccW hs)
    have htU := hψ_mem t (hIccW ht)
    by_contra hnot
    have hle : ψ t ≤ ψ s := le_of_not_gt hnot
    have := hφ_strict.monotoneOn htU hsU hle
    rw [hright s hs, hright t ht] at this
    exact (not_le_of_gt hst) this
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ) (Icc 0 (φ b)) := by
    apply (hγ.mono hU_J).comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact hψ_contDiff.mono hIccW
    · exact fun s hs ↦ hψ_mem s (hIccW hs)
  have hunit : ∀ s ∈ Icc (0 : ℝ) (φ b), ‖curveVelocity I (γ ∘ ψ) s‖ = 1 := by
    intro s hs
    have hsW := hIccW hs
    have hψsU := hψ_mem s hsW
    have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (ψ s) :=
      (hγ.contMDiffAt (hJ.mem_nhds (hU_J hψsU))).mdifferentiableAt one_ne_zero
    rw [curveVelocity_comp (hψ_deriv s hsW) hγdiff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hU_sub hψsU).2)]
    exact inv_mul_cancel₀ (hU_sub hψsU).2.ne'
  have hlength : Manifold.pathELength I (γ ∘ ψ) 0 (φ b) =
      Manifold.pathELength I γ a b := by
    have hψ_zero : ψ 0 = a := by
      rw [← hφa, hleft a haU]
    have hψ_end : ψ (φ b) = b := hleft b hbU
    have hγdiff : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Icc (ψ 0) (ψ (φ b))) := by
      rw [hψ_zero, hψ_end]
      exact hγ.mdifferentiableOn one_ne_zero |>.mono hsub
    have h := Manifold.pathELength_comp_of_monotoneOn (I := I) hL hψ_strict.monotoneOn
      (hψ_contDiff.differentiableOn one_ne_zero |>.mono hIccW)
      hγdiff
    simpa only [hψ_zero, hψ_end] using h
  -- Rewrite the local names `v` and `φ` back to the intrinsic formula in the public statement.
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [φ, v] using hleft t (hIccU ht)
  · simpa only [φ, v] using hright
  · simpa only [φ, v] using hψ_Icc
  · simpa only [φ, v] using hψ_strict
  · exact hψ_contDiff.mono hIccW
  · simpa only [φ, v] using hη
  · rw [← hφa, Function.comp_apply, hleft a haU]
  · simpa only [φ, v, Function.comp_apply] using congrArg γ (hleft b hbU)
  · simpa only [φ, v] using hunit
  · simpa only [φ, v] using hlength
  · simpa only [v] using hlength_toReal

end TauCeti.Manifold

end
