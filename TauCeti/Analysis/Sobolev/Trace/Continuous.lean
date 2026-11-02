/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Multiplication
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic
import TauCeti.Analysis.Sobolev.W1p.Mollification
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Traces of continuous Sobolev functions

For `1 ≤ p < ∞`, the flat, half-space and graph traces of `W^{1,p}` functions are defined
abstractly, as continuous extensions of restriction from test functions. This file proves that
they are the classical boundary values whenever the function is continuous up to the boundary.

* `TauCeti.W1p.hyperplaneTrace_apply_ae_of_continuous`: if `u ∈ W^{1,p}(ℝ × E)` has a continuous
  representative `f`, its trace on `{a} × E` is `y ↦ f (a, y)` almost everywhere.
* `TauCeti.W1p.halfSpaceTrace_apply_ae_of_continuousOn`: if `u ∈ W^{1,p}` of the half-space
  `{a < t}` agrees almost everywhere with a function continuous on the closed half-space
  `{a ≤ t}`, its trace is the restriction of that function to `{a} × E`.
* `TauCeti.W1p.normalEpigraphTrace_apply_ae_of_continuousOn`: if `u ∈ W^{1,p}` of the region above
  the graph of a Lipschitz function `φ` agrees almost everywhere with a function `f` continuous
  on the closed region `{φ y ≤ t}`, its graph trace is `y ↦ f (φ y, y)`.

For a compactly supported continuous representative, mollification produces test functions
converging to `u` in `W^{1,p}` and to `f` pointwise; their traces are their restrictions and
converge in `Lᵖ`, so a subsequence converges almost everywhere and the two limits agree. The
general whole-space case follows by multiplying with cutoffs, using that the trace commutes
with smooth multipliers. On the half-space, the even reflection extension of a function
continuous up to the boundary is continuous; on a graph domain, flattening is a homeomorphism
of the closed regions.

Together with density of functions smooth up to the boundary, this identification is what
makes traces taken in overlapping boundary charts agree.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1 (the trace of a
  function continuous up to the boundary is its restriction).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped Convolution Distributions ENNReal Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The flat trace -/

/-- The whole-space restriction of volume is an additive Haar measure. -/
local instance :
    ((volume : Measure (WithLp 2 (ℝ × E))).restrict
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-- The flat trace of a whole-space `W^{1,p}` function with a continuous compactly supported
representative is its restriction. Mollifications are test functions whose traces are their
restrictions; they converge to `u` in `W^{1,p}` and to `f` pointwise. -/
private theorem hyperplaneTrace_apply_ae_of_hasCompactSupport (hp : p ≠ ∞) (a : ℝ)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p} {f : WithLp 2 (ℝ × E) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hu : W1p.value u =ᵐ[volume] f) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.hyperplaneTrace hp a u y = f (WithLp.toLp 2 (a, y)) := by
  let phi : ℕ → ContDiffBump (0 : WithLp 2 (ℝ × E)) := fun k =>
    ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun k => (phi k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let conv : ℕ → WithLp 2 (ℝ × E) → ℝ := fun k =>
    (phi k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  -- The jet of `u` vanishes off the support of `f`.
  have hjet : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))),
      x ∉ tsupport f → (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) x = 0 := by
    let V : Opens (WithLp 2 (ℝ × E)) := ⟨(tsupport f)ᶜ, (isClosed_tsupport f).isOpen_compl⟩
    have hV : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (V : Set _),
        W1p.value u x = 0 := by
      filter_upwards [ae_restrict_of_ae hu, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport hxV
    exact ae_restrict_of_ae <| (ae_restrict_iff' V.isOpen.measurableSet).1
      (W1p.coe_ae_eq_zero_of_value_ae_eq_zero (le_top : V ≤ ⊤) hV)
  choose Φ hΦ using fun k => W1p.normedBumpL_mem_range_of_ae_eq_zero hp (phi k)
    hfc hjet
  -- Each mollification is the test function `Φ k`, which is the pointwise convolution.
  have hΦconv (k : ℕ) : (Φ k : WithLp 2 (ℝ × E) → ℝ) = conv k := by
    have hmem : MemLp f p ((volume : Measure (WithLp 2 (ℝ × E))).restrict
        ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))) := by
      rw [Opens.coe_top, Measure.restrict_univ]
      exact hf.memLp_of_hasCompactSupport hfc
    have hval : W1p.value u = hmem.toLp f := by
      apply Lp.ext
      filter_upwards [hmem.coeFn_toLp, ae_restrict_of_ae (s := univ) hu] with x h1 h2
      rw [h1, h2]
    have h1 := normedBumpLp_ae_eq_convolution hp (phi k) hmem
    have h2 := W1p.value_ofTestFunctionₗ (mu := volume) (Omega := ⊤) (p := p) (Φ k)
    have h3 := testFunctionLp_apply_ae (mu := (volume : Measure (WithLp 2 (ℝ × E)))) p (Φ k)
    rw [hΦ k, W1p.value_normedBumpL, hval] at h2
    rw [← h2] at h3
    simp only [Opens.coe_top, Measure.restrict_univ] at h1 h3
    refine (Continuous.ae_eq_iff_eq volume (Φ k).continuous ?_).1 ?_
    · exact (phi k).hasCompactSupport_normed.continuous_convolution_left _
        (phi k).continuous_normed hf.locallyIntegrable
    · filter_upwards [h1, h3] with x h1 h3
      rw [← h3, h1]
  have htend : Tendsto
      (fun k => W1p.hyperplaneTrace hp a
        (W1p.normedBumpL hp (phi k) u))
      atTop (𝓝 (W1p.hyperplaneTrace hp a u)) :=
    ((W1p.hyperplaneTrace hp a).continuous.tendsto u).comp
      (W1p.tendsto_normedBumpL _ hphi u)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp htend).exists_seq_tendsto_ae
  have htest : ∀ᵐ y ∂(volume : Measure E), ∀ k,
      W1p.hyperplaneTrace hp a (W1p.normedBumpL hp (phi k) u) y =
        conv k (WithLp.toLp 2 (a, y)) := by
    rw [ae_all_iff]
    intro k
    rw [← hΦ k, ← hΦconv k]
    exact W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a (Φ k)
  filter_upwards [hae, htest] with y hy hk
  refine tendsto_nhds_unique hy ?_
  simp only [hk]
  exact (ContDiffBump.convolution_tendsto_right_of_continuous hphi hf _).comp
    hns.tendsto_atTop

/-- **The flat trace of a continuous Sobolev function is its restriction.** If a whole-space
`W^{1,p}` function `u` is represented almost everywhere by a continuous function `f`, then its trace
on the hyperplane `{a} × E` is `y ↦ f (a, y)` almost everywhere. -/
theorem W1p.hyperplaneTrace_apply_ae_of_continuous (hp : p ≠ ∞) (a : ℝ)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p} {f : WithLp 2 (ℝ × E) → ℝ}
    (hf : Continuous f) (hu : W1p.value u =ᵐ[volume] f) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.hyperplaneTrace hp a u y = f (WithLp.toLp 2 (a, y)) := by
  have key (n : ℕ) : ∀ᵐ y ∂(volume : Measure E), ‖WithLp.toLp 2 (a, y)‖ < n →
      W1p.hyperplaneTrace hp a u y = f (WithLp.toLp 2 (a, y)) := by
    obtain ⟨ψ, M, hψ, -, hone, hψc, -, hM, hψM, hgM⟩ :=
      (isCompact_closedBall (0 : WithLp 2 (ℝ × E)) n).exists_contDiff_cutoff_with_bounds
        isOpen_univ (subset_univ _)
    have hv := W1p.value_contDiffSMul_ae hψ hM (fun x _ => hψM x) (fun x _ => hgM x) u
    simp only [Opens.coe_top, Measure.restrict_univ] at hv
    have hcut := hyperplaneTrace_apply_ae_of_hasCompactSupport hp a (hψ.continuous.mul hf)
      hψc.mul_right
      (by filter_upwards [hv, hu] with x h1 h2; rw [h1, h2, smul_eq_mul, Pi.mul_apply])
    filter_upwards [hcut, W1p.hyperplaneTrace_contDiffSMul_ae hp a hψ hψM hgM u] with y h1 h2 hy
    have hψ1 : ψ (WithLp.toLp 2 (a, y)) = 1 :=
      interior_subset (hone (mem_closedBall_zero_iff.2 hy.le))
    rw [h2, hψ1, one_mul] at h1
    rw [h1, Pi.mul_apply, hψ1, one_mul]
  filter_upwards [ae_all_iff.2 key] with y hy
  obtain ⟨n, hn⟩ := exists_nat_gt ‖WithLp.toLp 2 (a, y)‖
  exact hy n hn

/-! ### The half-space trace -/

/-- **The half-space trace of a function continuous up to the boundary is its restriction.** If
`u ∈ W^{1,p}` of the half-space `{a < t}` agrees almost everywhere with a function `f` continuous on
the closed half-space `{a ≤ t}`, then the trace of `u` on `{a} × E` is `y ↦ f (a, y)` almost
everywhere. -/
theorem W1p.halfSpaceTrace_apply_ae_of_continuousOn (hp : p ≠ ∞) (a : ℝ)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f {x | a ≤ x.fst})
    (hu : W1p.value u =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] f) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.halfSpaceTrace hp a u y = f (WithLp.toLp 2 (a, y)) := by
  -- The reflection extension is represented by `f` composed with the fold onto `{a ≤ t}`.
  let fold : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) := fun x =>
    WithLp.toLp 2 (a + |x.fst - a|, x.snd)
  have hfold : Continuous fold := by fun_prop
  have hg : Continuous (f ∘ fold) :=
    hf.comp_continuous hfold fun x => by simp [fold]
  have hu' := (ae_restrict_iff' (normalHalfSpace (E := E) a).isOpen.measurableSet).1 hu
  have hext : W1p.value (W1p.extendByReflectionL a u) =ᵐ[volume] f ∘ fold := by
    filter_upwards [W1p.value_extendByReflectionL_ae a u, hu',
      (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving.ae hu',
      measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_setOf_fst_eq (E := E) volume a)] with
      x hx h1 h2 h3
    rw [hx]
    rcases lt_trichotomy a x.fst with hlt | heq | hgt
    · have hxH : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
        (mem_normalHalfSpace a x).2 hlt
      have hρ : normalReflection E a x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
        fun h => (lt_asymm hlt) ((normalReflection_mem_normalHalfSpace_iff a x).1 h)
      rw [indicator_of_mem hxH, indicator_of_notMem hρ, add_zero, h1 hxH, Function.comp_apply]
      simp only [fold, abs_of_pos (sub_pos.2 hlt), add_sub_cancel]
      rfl
    · exact absurd heq.symm h3
    · have hxH : x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
        fun h => lt_asymm hgt ((mem_normalHalfSpace a x).1 h)
      have hρ : normalReflection E a x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
        (normalReflection_mem_normalHalfSpace_iff a x).2 hgt
      rw [indicator_of_notMem hxH, indicator_of_mem hρ, zero_add, h2 hρ, Function.comp_apply]
      congr 1
      simp only [normalReflection_apply, fold, abs_of_neg (sub_neg.2 hgt)]
      congr 2
      ring
  filter_upwards [W1p.hyperplaneTrace_apply_ae_of_continuous hp a hg hext] with y hy
  rw [W1p.halfSpaceTrace_apply, hy]
  simp [fold]

/-! ### The trace on a Lipschitz graph -/

/-- **The graph trace of a function continuous up to the graph is its restriction.** Let `φ` be
Lipschitz and `1 ≤ p < ∞`. If `u ∈ W^{1,p}` of the region `{φ y < t}` above the graph agrees
almost everywhere with a function `f` continuous on the closed region `{φ y ≤ t}`, then the trace
of `u` is `y ↦ f (φ y, y)` almost everywhere. -/
theorem W1p.normalEpigraphTrace_apply_ae_of_continuousOn {φ : C(E, ℝ)} {K : NNReal}
    (hp : p ≠ ∞) (hφ : LipschitzWith K φ)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalEpigraph φ) p}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f {x | φ x.snd ≤ x.fst})
    (hu : W1p.value u =ᵐ[volume.restrict (normalEpigraph φ)] f) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.normalEpigraphTrace hp hφ u y = f (normalGraphEmbedding φ y) := by
  set Φ := graphFlattening φ φ.continuous
  have hg : ContinuousOn (f ∘ Φ.symm) {x | (0 : ℝ) ≤ x.fst} :=
    hf.comp Φ.symm.continuous.continuousOn fun x hx => by
      simpa [Φ] using hx
  have hu' := (measurePreserving_graphFlattening_symm φ φ.continuous).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (normalEpigraph φ).isOpen.measurableSet).1 hu)
  have hv : W1p.value (W1p.normalEpigraphEquivL hφ u) =ᵐ[volume.restrict
      (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E)))] f ∘ Φ.symm := by
    filter_upwards [W1p.value_normalEpigraphEquivL_ae hφ u, ae_restrict_of_ae hu',
      ae_restrict_mem (normalHalfSpace (E := E) 0).isOpen.measurableSet] with x h1 h2 hx
    rw [h1, Function.comp_apply]
    refine h2 ?_
    simpa [Φ] using hx
  filter_upwards [W1p.halfSpaceTrace_apply_ae_of_continuousOn hp 0 hg hv] with y hy
  have hγ : normalGraphEmbedding φ y = WithLp.toLp 2 (φ y, y) :=
    (WithLp.ext_iff 2).2 (Prod.ext (normalGraphEmbedding_fst φ y) (normalGraphEmbedding_snd φ y))
  rw [W1p.normalEpigraphTrace_apply, hy, hγ]
  simp [Φ]

end TauCeti
