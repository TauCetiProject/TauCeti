/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.LevelSet

import Mathlib.MeasureTheory.Function.UnifTight

/-!
# Continuity of positive truncation

For `1 ≤ p < ∞` and `0 ≤ k`, the truncation `u ↦ (u - k)⁺` is continuous in
`W^{1,p}(Ω)` and preserves `W^{1,p}_0(Ω)`. Neither assertion requires boundedness or
boundary regularity of `Ω`.

Positive parts of functions with zero boundary values are therefore admissible Sobolev test
functions. In particular, this applies to the difference of two functions with the same
Dirichlet boundary data, as needed in weak comparison arguments.

* `TauCeti.W1p.continuous_posPartAbove`: continuity in the full Sobolev norm.
* `TauCeti.W1p.posPartAbove_mem_w1p0Submodule`: preservation of the homogeneous Dirichlet
  condition.

The corresponding positive-part results are the special case `k = 0`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E]

private def posPartJet (z : Sobolev1Jet E) : Sobolev1Jet E :=
  if 0 < z.fst then z else 0

private theorem norm_posPartJet_le (z : Sobolev1Jet E) :
    ‖posPartJet z‖ ≤ ‖z‖ := by
  by_cases hz : 0 < z.fst <;> simp [posPartJet, hz]

private theorem continuousAt_posPartJet {z : Sobolev1Jet E}
    (hzero : z.fst = 0 → z = 0) : ContinuousAt posPartJet z := by
  rcases lt_trichotomy 0 z.fst with hpos | heq | hneg
  · have he : ∀ᶠ w in 𝓝 z, 0 < w.fst :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_gt_nhds hpos)
    rw [ContinuousAt, posPartJet, ite_eq_left hpos]
    exact tendsto_id.congr' (he.mono fun w hw ↦ by simp [posPartJet, hw])
  · have hz := hzero heq.symm
    subst z
    simpa only [ContinuousAt, posPartJet, WithLp.zero_fst, lt_self_iff_false,
      ite_false] using squeeze_zero_norm norm_posPartJet_le tendsto_norm_zero
  · have he : ∀ᶠ w in 𝓝 z, w.fst < 0 :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_lt_nhds hneg)
    rw [ContinuousAt, posPartJet, ite_eq_right (not_lt_of_gt hneg)]
    exact tendsto_const_nhds.congr' (he.mono fun w hw ↦ by
      simp [posPartJet, not_lt_of_gt hw])

private def posPartAboveJet (k : ℝ) (z : Sobolev1Jet E) : Sobolev1Jet E :=
  posPartJet (z - WithLp.toLp 2 (k, 0))

private theorem norm_posPartAboveJet_le {k : ℝ} (hk : 0 ≤ k) (z : Sobolev1Jet E) :
    ‖posPartAboveJet k z‖ ≤ ‖z‖ := by
  by_cases hz : k < z.fst
  · simp only [posPartAboveJet, posPartJet, WithLp.sub_fst, WithLp.toLp_fst,
      sub_pos.mpr hz, ite_true]
    rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      sub_zero, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz.le),
      abs_of_nonneg (hk.trans hz.le)]
    gcongr
    exact sub_le_self _ hk
  · simp [posPartAboveJet, posPartJet, sub_pos, hz]

private theorem continuousAt_posPartAboveJet (k : ℝ) {z : Sobolev1Jet E}
    (hzero : z.fst = k → z.snd = 0) : ContinuousAt (posPartAboveJet k) z := by
  have hz : (z - WithLp.toLp 2 (k, 0)).fst = 0 → z - WithLp.toLp 2 (k, 0) = 0 := by
    intro hx
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simpa only [WithLp.ofLp_fst, WithLp.zero_fst] using hx
    · simp only [WithLp.ofLp_snd, WithLp.sub_snd, WithLp.toLp_snd, sub_zero,
        WithLp.zero_snd]
      exact hzero (sub_eq_zero.mp (by simpa only [WithLp.sub_fst, WithLp.toLp_fst] using hx))
  have hshift : ContinuousAt (fun w : Sobolev1Jet E ↦ w - WithLp.toLp 2 (k, 0)) z :=
    continuousAt_id.sub continuousAt_const
  exact (continuousAt_posPartJet hz).comp
    (f := fun w : Sobolev1Jet E ↦ w - WithLp.toLp 2 (k, 0)) hshift

variable [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem posPartAbove_coe_ae (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    (u : W1p mu Omega p) :
    ⇑(W1p.posPartAbove hp hk u : Sobolev1JetLp mu Omega p) =ᵐ[mu.restrict Omega]
      fun x ↦ posPartAboveJet k ((u : Sobolev1JetLp mu Omega p) x) := by
  filter_upwards [W1p.value_apply_ae (W1p.posPartAbove hp hk u),
    W1p.gradient_apply_ae (W1p.posPartAbove hp hk u), W1p.value_apply_ae u,
    W1p.gradient_apply_ae u, W1p.value_posPartAbove_ae hp hk u,
    W1p.gradient_posPartAbove_ae hp hk u] with x hv hg huv hug hvp hgp
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [WithLp.ofLp_fst]
    rw [← hv, hvp]
    by_cases hx : k < W1p.value u x
    · simp [posPartAboveJet, posPartJet, ← huv, sub_pos, hx,
        max_eq_left (sub_nonneg.mpr hx.le)]
    · simp [posPartAboveJet, posPartJet, ← huv, sub_pos, hx,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))]
  · simp only [WithLp.ofLp_snd]
    rw [← hg, hgp]
    by_cases hx : k < W1p.value u x <;>
      simp [posPartAboveJet, posPartJet, ← huv, ← hug, sub_pos, hx]

/-- Truncation above a nonnegative level is continuous in the Sobolev norm for finite
exponents. -/
theorem W1p.continuous_posPartAbove (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k) :
    Continuous (W1p.posPartAbove (mu := mu) (Omega := Omega) hp hk) := by
  rw [continuous_iff_seqContinuous]
  intro a u ha
  apply tendsto_subtype_rng.mpr
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hsrc : Tendsto (fun n ↦ (a (ns n) : Sobolev1JetLp mu Omega p)) atTop
      (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    (tendsto_subtype_rng.mp ha).comp hns
  -- An almost-everywhere convergent subsequence identifies the truncated limit.
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsrc).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  let f : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ a (ns (ms n))
  let g : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ W1p.posPartAbove hp hk (a (ns (ms n)))
  have hf : Tendsto f atTop (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    hsrc.comp hms.tendsto_atTop
  have hvitali := (tendstoInMeasure_iff_tendsto_Lp (Fact.out : 1 ≤ p) hp
    (fun n ↦ Lp.memLp (f n)) (Lp.memLp (u : Sobolev1JetLp mu Omega p))).mpr
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hf)
  have hnorm (n : ℕ) : ∀ᵐ x ∂mu.restrict Omega, ‖g n x‖ ≤ ‖f n x‖ := by
    filter_upwards [posPartAbove_coe_ae hp hk (a (ns (ms n)))] with x hx
    dsimp only [g, f]
    rw [hx]
    exact norm_posPartAboveJet_le hk _
  have hui : UnifIntegrable (fun n x ↦ g n x) p (mu.restrict Omega) :=
    hvitali.2.1.ae_mono (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable) fun n ↦
      (hnorm n).mono fun x hx ↦ by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  have hut : UnifTight (fun n x ↦ g n x) p (mu.restrict Omega) := by
    intro ε hε
    obtain ⟨s, hs, hfinite, hbound⟩ := hvitali.2.2.exists_measurableSet_indicator hε.ne'
    refine ⟨s, hfinite.ne, fun n ↦ (eLpNorm_mono_ae
      ((Lp.memLp (g n)).aestronglyMeasurable.indicator hs.compl) ?_).trans (hbound n)⟩
    filter_upwards [hnorm n] with x hx
    by_cases hxs : x ∈ sᶜ
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simp only [Set.indicator_of_notMem hxs, norm_zero, le_refl]
  -- The only discontinuity of the jet truncation disappears on Sobolev level sets.
  have hzero : ∀ᵐ x ∂mu.restrict Omega,
      ((u : Sobolev1JetLp mu Omega p) x).fst = k →
        ((u : Sobolev1JetLp mu Omega p) x).snd = 0 := by
    filter_upwards [W1p.value_apply_ae u, W1p.gradient_apply_ae u,
      W1p.gradient_ae_eq_zero_on_level_set hp u k] with x hv hg hz
    intro hx
    rw [← hg]
    exact hz (hv.trans hx)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ p) hp
    (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable)
    (Lp.memLp (W1p.posPartAbove hp hk u : Sobolev1JetLp mu Omega p)) hui hut
  filter_upwards [hae, hzero,
    ae_all_iff.mpr (fun n ↦ posPartAbove_coe_ae hp hk (a (ns (ms n)))),
    posPartAbove_coe_ae hp hk u] with x hx hz hg hu
  rw [hu]
  exact ((continuousAt_posPartAboveJet k hz).tendsto.comp hx).congr'
    (Eventually.of_forall fun n ↦ (hg n).symm)

/-- Taking the positive part is continuous in the Sobolev norm for finite exponents. -/
theorem W1p.continuous_posPart (hp : p ≠ ∞) :
    Continuous (W1p.posPart (mu := mu) (Omega := Omega) hp) := by
  exact (W1p.continuous_posPartAbove (mu := mu) (Omega := Omega) hp (le_refl 0)).congr
    (W1p.posPartAbove_zero hp)

/-- Truncation above a nonnegative level preserves the homogeneous Dirichlet boundary
condition. -/
theorem W1p.posPartAbove_mem_w1p0Submodule (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.posPartAbove hp hk u ∈ w1p0Submodule mu Omega p := by
  refine w1p0Submodule_subset_of_isClosed
    ((w1p0Submodule mu Omega p).isClosed.preimage (W1p.continuous_posPartAbove hp hk)) ?_ hu
  intro phi
  apply W1p.mem_w1p0Submodule_of_isCompact hp phi.hasCompactSupport phi.tsupport_subset
  filter_upwards [W1p.value_posPartAbove_ae hp hk (W1p.ofTestFunctionₗ mu Omega p phi),
    testFunctionLp_apply_ae (mu := mu) p phi] with x hx hphi
  intro hxK
  rw [hx, W1p.value_ofTestFunctionₗ, hphi, image_eq_zero_of_notMem_tsupport hxK,
    max_eq_right (sub_nonpos.mpr hk)]

/-- Positive truncation preserves the homogeneous Dirichlet boundary condition. -/
theorem W1p.posPart_mem_w1p0Submodule (hp : p ≠ ∞) {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.posPart hp u ∈ w1p0Submodule mu Omega p := by
  simpa only [W1p.posPartAbove_zero] using
    W1p.posPartAbove_mem_w1p0Submodule hp (le_refl 0) hu

end TauCeti
