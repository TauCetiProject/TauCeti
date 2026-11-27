/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Inner
public import TauCeti.Analysis.Sobolev.Local.Reflection.Odd
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.MemLpLoc.Inner

/-!
# Integration by parts up to the real axis against compactly supported weights

For an open `Ω ⊆ ℂ`, let `g'` be a weak derivative of `g` in the direction `v` on the open upper
part `Ω ∩ {0 < im}`, with `g` and `g'` locally `L¹` up to the axis. This file proves two forms of
integration by parts on the upper half-plane in which the test function is not required to vanish
on the real axis.

* `TauCeti.HasWeakLineDerivOn.setIntegral_im_pos_eq_zero`: if `g` and `g'` vanish off a compact
  set whose part in `{0 ≤ im}` lies in `Ω`, then `∫_{0 < im} g' = 0`, provided `v` is tangent to
  the axis, or `g` is continuous up to the axis and zero on it.
* `TestFunction.setIntegral_im_pos_inner_fderiv_eq_neg`: for `g = w` with values in a
  finite-dimensional inner product space and a vector-valued test function `φ ∈ 𝓓(Ω, V)`,
  `∫_{0 < im} ⟪∂_v φ, w⟫ = -∫_{0 < im} ⟪φ, w'⟫`, under the same alternative for `⟪φ, w⟫`.

Both test the scalar identities `TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg` and
`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_of_continuousOn` against a cutoff
equal to `1` near the support. Local integrability up to the axis gives integrability against
test functions on the upper half-plane through
`TauCeti.MemLpLoc.locallyIntegrableOn_restrict_setOf_im_nonneg`; the resulting statements are
`TestFunction.integrableOn_im_pos_inner_of_memLpLoc` and its derivative form.
-/

public section

open MeasureTheory TopologicalSpace Complex Set Filter
open scoped InnerProductSpace ContDiff Distributions Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens ℂ}

omit [NormedSpace ℝ F] in
/-- A function locally `L¹` up to the axis on `Ω ∩ {0 ≤ im}` is locally integrable on `Ω` for
Lebesgue measure restricted to the closed upper half-plane, so its pairings with test functions on
`Ω` are integrable on `{0 ≤ im}`. -/
theorem MemLpLoc.locallyIntegrableOn_restrict_setOf_im_nonneg {w : ℂ → F}
    (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) :
    LocallyIntegrableOn w Ω (volume.restrict {z : ℂ | 0 ≤ z.im}) :=
  (hw.locallyIntegrableOn le_rfl (Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0))
    |>.restrict_of_inter Ω.isOpen (isClosed_le continuous_const continuous_im)

/-- **The integral of a compactly supported weak derivative up to the axis vanishes.** Let `g'` be
a weak derivative of `g` in the direction `v` on the upper part of `Ω`, with `g`, `g'` locally
`L¹` up to the axis and vanishing off a compact set `K` whose part in the closed upper half-plane
lies in `Ω`. If `v` is tangent to the axis, or `g` is continuous up to the axis and zero on
`ℝ ∩ Ω`, then `∫_{0 < im} g' = 0`. -/
theorem HasWeakLineDerivOn.setIntegral_im_pos_eq_zero {g g' : ℂ → F} {v : ℂ}
    (hg : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' v)
    (hg1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg'1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ∩ {z | 0 ≤ z.im} ⊆ Ω) (hgK : ∀ z ∉ K, g z = 0) (hg'K : ∀ z ∉ K, g' z = 0)
    (hv : v.im = 0 ∨ ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      ∀ s : ℝ, (s : ℂ) ∈ Ω → g s = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, g' z = 0 := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψΩ⟩ := (hK.inter_right (isClosed_le continuous_const
    continuous_im)).exists_contDiff_cutoff_eventuallyEq_one Ω.isOpen hKΩ
  have key : ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ ψ z v • g z =
      -∫ z in {z : ℂ | 0 < z.im}, ψ z • g' z := by
    rcases hv with hv | ⟨hgc, hg0⟩
    · exact hg.setIntegral_fderiv_smul_eq_neg hg1 hg'1 hψ hψc (fun z hz => hψΩ hz.1) (Or.inl hv)
    · exact hg.setIntegral_fderiv_smul_eq_neg_of_continuousOn hgc hg0 hg'1 hψ hψc
        fun z hz => hψΩ hz.1
  -- On the upper half-plane `ψ = 1` near `K`, so `∂_v ψ • g = 0` and `ψ • g' = g'`.
  have hl (z : ℂ) (hz : 0 < z.im) : fderiv ℝ ψ z v • g z = 0 := by
    by_cases hzK : z ∈ K
    · have h1 : ψ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := hψ1 z ⟨hzK, hz.le⟩
      simp [h1.fderiv_eq]
    · simp [hgK z hzK]
  have hr (z : ℂ) (hz : 0 < z.im) : ψ z • g' z = g' z := by
    by_cases hzK : z ∈ K
    · simp [(hψ1 z ⟨hzK, hz.le⟩).self_of_nhds]
    · simp [hg'K z hzK]
  rwa [setIntegral_congr_fun hH hl, setIntegral_congr_fun hH hr, integral_zero, eq_comm,
    neg_eq_zero] at key

end TauCeti

namespace TestFunction

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Ω : Opens ℂ}

/-- The pairing of a test function with a field locally `L¹` up to the axis is integrable on the
upper half-plane. -/
theorem integrableOn_im_pos_inner_of_memLpLoc (φ : 𝓓(Ω, V)) {w : ℂ → V}
    (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) :
    IntegrableOn (fun z => ⟪(φ : ℂ → V) z, w z⟫_ℝ) {z : ℂ | 0 < z.im} :=
  IntegrableOn.mono_set (φ.integrable_inner hw.locallyIntegrableOn_restrict_setOf_im_nonneg)
    (ofPred_subset_ofPred.2 fun _ h => h.le)

/-- The pairing of a directional derivative of a test function with a field locally `L¹` up to
the axis is integrable on the upper half-plane. -/
theorem integrableOn_im_pos_inner_fderiv_of_memLpLoc (φ : 𝓓(Ω, V)) {w : ℂ → V}
    (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) (v : ℂ) :
    IntegrableOn (fun z => ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ) {z : ℂ | 0 < z.im} :=
  IntegrableOn.mono_set
    (φ.integrable_inner_fderiv hw.locallyIntegrableOn_restrict_setOf_im_nonneg v)
    (ofPred_subset_ofPred.2 fun _ h => h.le)

variable [FiniteDimensional ℝ V]

/-- **Integration by parts on the upper half-plane against a vector-valued test function.** Let
`w'` be a weak derivative of `w` in the direction `v` on the upper part of `Ω`, with `w` and `w'`
locally `L¹` up to the axis, and let `φ ∈ 𝓓(Ω, V)`. If `v` is tangent to the axis, or if `w` is
continuous up to the axis with `⟪φ(s), w(s)⟫ = 0` on `ℝ ∩ Ω`, then
`∫_{0 < im} ⟪∂_v φ, w⟫ = -∫_{0 < im} ⟪φ, w'⟫`: the boundary term `∫_ℝ ⟪φ, w⟫ v.im` vanishes. -/
theorem setIntegral_im_pos_inner_fderiv_eq_neg (φ : 𝓓(Ω, V)) {w w' : ℂ → V} {v : ℂ}
    (hw : HasWeakLineDerivOn volume Ω.upperHalf w w' v)
    (hw1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w)
    (hw'1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w')
    (hv : v.im = 0 ∨ ContinuousOn w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      ∀ s : ℝ, (s : ℂ) ∈ Ω → ⟪(φ : ℂ → V) s, w s⟫_ℝ = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ =
      -∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, w' z⟫_ℝ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → V) := φ.contDiff.of_le (by simp)
  have hdφ (z : ℂ) : fderiv ℝ (fun z => innerSL ℝ ((φ : ℂ → V) z)) z v =
      innerSL ℝ (fderiv ℝ (φ : ℂ → V) z v) := by
    rw [fderiv_fun_comp z (innerSL ℝ).differentiableAt (hφ1.differentiable one_ne_zero z),
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  -- The pairing `⟪φ, w⟫` is weakly differentiable on the upper part, by the Leibniz rule.
  have hg : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
      (fun z => ⟪(φ : ℂ → V) z, w z⟫_ℝ)
      (fun z => ⟪(φ : ℂ → V) z, w' z⟫_ℝ + ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ) v := by
    rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf]
    simpa [hdφ] using hw.contDiffOn_clm_apply_of_ne_zero
      (Φ := fun z => innerSL ℝ ((φ : ℂ → V) z)) ((innerSL ℝ).contDiff.comp hφ1).contDiffOn
      one_ne_zero
  have hc := φ.continuous.continuousOn (s := (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
  have hdc : ContinuousOn (fun z => fderiv ℝ (φ : ℂ → V) z v) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    ((φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have key := hg.setIntegral_im_pos_eq_zero (hw1.inner_continuousOn hc)
    ((hw'1.inner_continuousOn hc).add (hw1.inner_continuousOn hdc))
    φ.hasCompactSupport.isCompact (fun z hz => φ.tsupport_subset hz.1)
    (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
    (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz])
    (hv.imp_right fun ⟨hwc, hw0⟩ => ⟨hc.inner hwc, hw0⟩)
  rw [integral_add (φ.integrableOn_im_pos_inner_of_memLpLoc hw'1)
    (φ.integrableOn_im_pos_inner_fderiv_of_memLpLoc hw1 v)] at key
  linarith

end TestFunction
