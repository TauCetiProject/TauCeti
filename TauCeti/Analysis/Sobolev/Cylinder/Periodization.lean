/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.MeasureTheory.Function.MemLpLoc
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.Cylinder.Morrey
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Integral.Bochner.PeriodicStrip

/-!
# Periodization on the cylinder and weak annihilators on the plane

Sections over the cylinder `ℝ × S¹` are maps `ℝ × ℝ → V` of period one in `t`, and their `L²`
theory lives on the strip `ℝ × [0, 1]` (`TauCeti.StripSobolev.stripMeasure`). Local elliptic
regularity, on the other hand, is stated on open subsets of the plane, for locally `Lᵖ` functions
annihilating an operator on compactly supported test maps. This file passes between the two.

* **Periodization.** For a compactly supported map `ξ`, the sum `∑ₙ ξ (s, t + n)` over `n ∈ ℤ`
  is locally finite (`TauCeti.exists_finset_eventually_eq_zero_add_intCast`) and `C^k` when `ξ`
  is (`TauCeti.contDiff_tsum_add_intCast`). It is a test section of the cylinder when `ξ` is `C²`
  (`TauCeti.CylinderSobolev.tsum_add_intCast_mem_testSection`); its jet is the sum of the
  translates of the jet of `ξ` (`TauCeti.CylinderSobolev.jet_tsum_add_intCast`).
* **Periodic extension.** An `Lᵖ` function on the strip agrees there with a strongly measurable
  function of period one in `t`
  (`TauCeti.CylinderSobolev.exists_stronglyMeasurable_periodic_ae_eq`), and such a function is
  locally `Lᵖ` on the plane (`TauCeti.CylinderSobolev.memLpLoc_univ_of_periodic`), since a unit
  ball of the plane sees at most two periods.
* **Weak annihilators.** Let `M` be a continuous coefficient field of period one in `t`,
  essentially bounded on the strip, so that `x ↦ M x` is a bounded operator
  `TauCeti.jetOperator stripMeasure M` on `L²` jets. If `η ∈ L²(ℝ × [0, 1], W)` is orthogonal to
  `M x` for every `x ∈ W^{1,2}(ℝ × S¹, V)`, then the periodic extension `g` of `η` satisfies
  `∫ ⟪g z, M z (jet ξ z)⟫ = 0` over the whole plane for every compactly supported `C²` map `ξ`
  (`TauCeti.CylinderSobolev.integral_inner_jet_eq_zero_of_forall_inner_jetOperator_eq_zero`).
  The integral unfolds onto the strip, where it becomes the pairing of `η` with `M` applied to the
  jet of the periodization of `ξ` (`TauCeti.integral_eq_setIntegral_tsum_add_zsmul`).

For the linearized Floer operator along a Floer cylinder this says that a cokernel element of the
Sobolev realization is a weak cokernel element on the plane, the form taken by elliptic regularity
and unique continuation.
-/

public section

open MeasureTheory Set Filter Topology

namespace TauCeti.CylinderSobolev
open StripSobolev (jet jet_apply stripMeasure stripMeasure_eq_restrict_univ_prod_Ico jetLp
  jetLp_mem_jetClosure coeFn_jetLp integrable_inner_apply_jet)
open scoped ENNReal NNReal InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]

section Periodization

variable {ξ : ℝ × ℝ → V}

/-- **The periodization in `t` of a compactly supported `C²` map is a test section of the
cylinder**: it has period one in `t` and vanishes for `|s|` large. -/
theorem tsum_add_intCast_mem_testSection (hξ : ContDiff ℝ 2 ξ) (hc : HasCompactSupport ξ) :
    (fun z : ℝ × ℝ ↦ ∑' n : ℤ, ξ (z.1, z.2 + n)) ∈ testSection V := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image continuous_fst).isBounded.subset_closedBall 0
  refine mem_testSection_iff.2 ⟨contDiff_tsum_add_intCast hξ hc, fun s t ↦ ?_, R + 1,
    fun s t hs ↦ ?_⟩
  · exact periodic_tsum_add_intCast ξ s t
  · -- Every translate vanishes off the projection of the support of `ξ` to the `s`-axis.
    refine (tsum_congr fun n : ℤ ↦ image_eq_zero_of_notMem_tsupport fun h ↦ ?_).trans tsum_zero
    have hsR := hR ⟨_, h, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hsR
    linarith

/-- The derivative of the translate `w ↦ ξ (w.1, w.2 + n)` at `z` is that of `ξ` at
`(z.1, z.2 + n)`. -/
private lemma fderiv_comp_add_intCast (n : ℤ) (z : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ ↦ ξ (w.1, w.2 + n)) z = fderiv ℝ ξ (z.1, z.2 + n) := by
  have htr : (fun w : ℝ × ℝ ↦ ξ (w.1, w.2 + n)) = fun w ↦ ξ (w + ((0 : ℝ), (n : ℝ))) := by
    funext ⟨a, b⟩
    simp
  rw [htr, fderiv_comp_add_right]
  congr 1
  ext <;> simp

/-- A translate that vanishes near `z` has vanishing jet at `z`. -/
private lemma jet_add_intCast_eq_zero {S : Finset ℤ} {z : ℝ × ℝ}
    (hS : ∀ᶠ w in 𝓝 z, ∀ n ∉ S, ξ (w.1, w.2 + n) = 0) {n : ℤ} (hn : n ∉ S) :
    jet ξ (z.1, z.2 + n) = 0 := by
  have h0 : (fun w : ℝ × ℝ ↦ ξ (w.1, w.2 + n)) =ᶠ[𝓝 z] fun _ ↦ 0 := hS.mono fun w hw ↦ hw n hn
  have h1 : ξ (z.1, z.2 + n) = 0 := h0.eq_of_nhds
  have h2 : fderiv ℝ ξ (z.1, z.2 + n) = 0 := by
    rw [← fderiv_comp_add_intCast, h0.fderiv_eq]
    simp
  simp [jet_apply, h1, h2]

/-- **The jet of the periodization is the sum of the translates of the jet.** For a compactly
supported `C¹` map `ξ`, the jet of `z ↦ ∑ₙ ξ (z.1, z.2 + n)` at `z` is `∑ₙ jet ξ (z.1, z.2 + n)`. -/
theorem jet_tsum_add_intCast (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℝ × ℝ) :
    jet (fun w : ℝ × ℝ ↦ ∑' n : ℤ, ξ (w.1, w.2 + n)) z = ∑' n : ℤ, jet ξ (z.1, z.2 + n) := by
  obtain ⟨S, hS⟩ := exists_finset_eventually_eq_zero_add_intCast hc z
  have hd (n : ℤ) : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ ξ (w.1, w.2 + n)) z :=
    (hξ.differentiable one_ne_zero).differentiableAt.comp z
      (differentiableAt_fst.prodMk (differentiableAt_snd.add_const _))
  -- Near `z` the periodization is the finite sum over `S`.
  have hev : (fun w : ℝ × ℝ ↦ ∑' n : ℤ, ξ (w.1, w.2 + n)) =ᶠ[𝓝 z]
      fun w ↦ ∑ n ∈ S, ξ (w.1, w.2 + n) := hS.mono fun w hw ↦ tsum_eq_sum hw
  rw [tsum_eq_sum fun n hn ↦ jet_add_intCast_eq_zero hS hn, jet_apply, hev.eq_of_nhds,
    hev.fderiv_eq, fderiv_fun_sum fun n _ ↦ hd n]
  simp only [sum_apply, fderiv_comp_add_intCast, jet_apply, Prod.ext_iff,
    Prod.fst_sum, Prod.snd_sum, and_self]

end Periodization

section PeriodicExtension

/-- **Periodic extension of an `Lᵖ` function on the strip.** Every `f ∈ Lᵖ(ℝ × [0, 1], W)` agrees
almost everywhere on the strip with a strongly measurable function of period one in `t`. -/
theorem exists_stronglyMeasurable_periodic_ae_eq {p : ℝ≥0∞} (f : Lp W p stripMeasure) :
    ∃ g : ℝ × ℝ → W, StronglyMeasurable g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
      g =ᵐ[stripMeasure] f := by
  set hf := Lp.aestronglyMeasurable f
  refine ⟨fun z ↦ hf.mk f (z.1, Int.fract z.2), hf.stronglyMeasurable_mk.comp_measurable
    (measurable_fst.prodMk (measurable_fract.comp measurable_snd)), fun s t ↦ by simp, ?_⟩
  have hmem : ∀ᵐ z ∂stripMeasure, z ∈ (univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 := by
    rw [stripMeasure_eq_restrict_univ_prod_Ico]
    exact ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)
  filter_upwards [hmem, hf.ae_eq_mk] with z hz hfz
  rw [hfz, Int.fract_eq_self.2 hz.2]

/-- **Periodic functions are locally `Lᵖ` on the plane.** A strongly measurable function of
period one in `t` which is `Lᵖ` on the strip, `1 ≤ p < ∞`, is locally `Lᵖ` on `ℝ × ℝ`. -/
theorem memLpLoc_univ_of_periodic {f : ℝ × ℝ → W} (hf : StronglyMeasurable f)
    (hper : ∀ s t, f (s, t + 1) = f (s, t)) {p : ℝ≥0} (hp : 1 ≤ p)
    (h : MemLp f p stripMeasure) : MemLpLoc p univ f := by
  refine memLpLoc_iff.2 fun K _ hK ↦ ?_
  -- Cover `K` by finitely many unit balls, on each of which `f` sees at most two periods.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K ↦ Metric.ball (z : ℝ × ℝ) 1)
    (fun _ ↦ Metric.isOpen_ball) fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, Metric.mem_ball_self one_pos⟩
  refine MemLp.restrict_of_subset_iUnion (t := fun i : (t : Set K) ↦ Metric.ball (i : ℝ × ℝ) 1)
    (fun z hz ↦ ?_) fun i ↦ (eLpNorm_restrict_ball_le_two_mul_of_periodic hf hper hp _).trans_lt
      (ENNReal.mul_lt_top (by simp) h.eLpNorm_lt_top)
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (ht hz)
  exact mem_iUnion.2 ⟨⟨i, hi⟩, hzi⟩

end PeriodicExtension

section Annihilator

variable [InnerProductSpace ℝ W]

/-- **`L²` annihilators of a periodic first-order operator are weak annihilators on the plane.**
Let `M` be a continuous coefficient field of period one in `t`, essentially bounded on the strip,
and let `η ∈ L²(ℝ × [0, 1], W)` be orthogonal to `M x` for every `x` in the Sobolev space
`W^{1,2}(ℝ × S¹, V)`. If `g` is a strongly measurable function of period one in `t` agreeing with
`η` on the strip, then `∫ ⟪g z, M z (jet ξ z)⟫ = 0` over the whole plane for every compactly
supported `C²` map `ξ`. -/
theorem integral_inner_jet_eq_zero_of_forall_inner_jetOperator_eq_zero
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) (hMc : Continuous M)
    (hMper : ∀ s t, M (s, t + 1) = M (s, t)) {η : Lp W 2 stripMeasure}
    (hη : ∀ x ∈ H1 V, ⟪η, jetOperator stripMeasure M x⟫_ℝ = 0) {g : ℝ × ℝ → W}
    (hg : StronglyMeasurable g) (hgper : ∀ s t, g (s, t + 1) = g (s, t))
    (hgη : g =ᵐ[stripMeasure] η) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hξc : HasCompactSupport ξ) :
    ∫ z, ⟪g z, M z (jet ξ z)⟫_ℝ = 0 := by
  set F : ℝ × ℝ → ℝ := fun z ↦ ⟪g z, M z (jet ξ z)⟫_ℝ
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le one_le_two
  -- `g` and `M` have every integer period.
  have hgZ (n : ℤ) (s t : ℝ) : g (s, t + n) = g (s, t) := by
    simpa using (Function.Periodic.int_mul (f := fun t ↦ g (s, t)) (hgper s) n) t
  have hMZ (n : ℤ) (s t : ℝ) : M (s, t + n) = M (s, t) := by
    simpa using (Function.Periodic.int_mul (f := fun t ↦ M (s, t)) (hMper s) n) t
  have hgloc := memLpLoc_univ_of_periodic hg hgper one_le_two ((Lp.memLp η).ae_eq hgη.symm)
  have hFint : Integrable F := integrable_inner_apply_jet hMc (locallyIntegrableOn_univ.1
    (hgloc.locallyIntegrableOn one_le_two isOpen_univ.isLocallyClosed)) hξ1 hξc
  -- The periodization of `ξ` is a test section, so `η` annihilates `M` applied to its jet.
  set P : ℝ × ℝ → V := fun z ↦ ∑' n : ℤ, ξ (z.1, z.2 + n)
  have hP : P ∈ testSection V := tsum_add_intCast_mem_testSection hξ hξc
  have h0 := hη _ (jetLp_mem_jetClosure ⟨P, hP⟩)
  rw [MeasureTheory.L2.inner_def] at h0
  -- Pointwise on the plane, `⟪g, M (jet P)⟫` is the sum of the translates of `F`.
  have hsum (z : ℝ × ℝ) : ⟪g z, M z (jet P z)⟫_ℝ = ∑' n : ℤ, F (z.1, z.2 + n • (1 : ℝ)) := by
    obtain ⟨S, hS⟩ := exists_finset_eventually_eq_zero_add_intCast hξc z
    have hsumm : Summable fun n : ℤ ↦ jet ξ (z.1, z.2 + n) :=
      summable_of_ne_finset_zero fun n hn ↦ jet_add_intCast_eq_zero hS hn
    rw [jet_tsum_add_intCast hξ1 hξc z, ← innerSL_apply_apply (𝕜 := ℝ),
      ← ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_tsum _ hsumm]
    refine tsum_congr fun n ↦ ?_
    simp only [F, zsmul_one, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hgZ, hMZ]
  -- Unfold the integral over the plane onto the band `ℝ × [0, 1)`.
  have hunf := integral_eq_setIntegral_tsum_add_zsmul (μ := (volume : Measure ℝ)) one_pos
    (by rwa [← Measure.volume_eq_prod]) 0
  rw [← Measure.volume_eq_prod, zero_add] at hunf
  simp only [hunf, ← hsum]
  rw [← stripMeasure_eq_restrict_univ_prod_Ico, ← h0]
  refine integral_congr_ae ?_
  filter_upwards [hgη, coeFn_jetOperator hM (jetLp 2 (testSection V) ⟨P, hP⟩),
    coeFn_jetLp 2 (S := testSection V) ⟨P, hP⟩] with z hgz hMz hjz
  rw [hgz, hMz, hjz]

end Annihilator

end TauCeti.CylinderSobolev
