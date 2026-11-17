/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
import Mathlib.Topology.Algebra.Group.Order
import TauCeti.Analysis.Calculus.Deriv.TraceNearTangent
import TauCeti.Order.Interval.Set.Injective

/-!
# The side of a Jordan curve entered by a transverse curve

Near a point where a curve `γ` has nonzero derivative `v`, and which `γ` visits only once on a
compact parameter set, the trace of `γ` lies in arbitrarily thin double cones
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line
(`IsCompact.exists_pos_forall_abs_im_conj_mul_sub_le`).

For a simple closed absolutely continuous curve, this upgrades the normal identification of the
orientation sign `jordanSign γ a b` (normal rays at a regular point enter the inside or the
outside) to arbitrary curves `p` leaving `γ t₀` transversally at a parameter `s₀`: a short segment
joins `p s` to the normal ray without meeting the trace. A curve leaving strictly to the left of
the tangent, that is with `0 < Im (conj v * w)` for its right derivative `w`, enters the bounded
inside of a positively oriented curve and the unbounded outside of a negatively oriented one.

## Main results

* `AbsolutelyContinuousOnInterval.eventually_mem_filledHull_sdiff_of_hasDerivAt`: a curve leaving
  a regular point on the side selected by `jordanSign γ a b` enters the bounded inside.
* `AbsolutelyContinuousOnInterval.eventually_notMem_filledHull_of_hasDerivAt`: a curve leaving a
  regular point on the other side enters the unbounded outside.

`AbsolutelyContinuousOnInterval.jordanSign_mul_im_conj_mul_pos_iff_eventually_mem_filledHull_sdiff`
states that a transverse curve enters the inside exactly when its direction agrees with the
orientation.

`AbsolutelyContinuousOnInterval.jordanSign_mul_im_conj_mul_neg_iff_eventually_notMem_filledHull`
states that a transverse curve enters the outside exactly when its direction opposes the
orientation.
-/

public section

open Complex ComplexConjugate Filter Metric Set
open scoped Topology

open TauCeti TauCeti.Contour

namespace AbsolutelyContinuousOnInterval

variable {γ : ℝ → ℂ} {a b t₀ s₀ : ℝ} {v w : ℂ} {p : ℝ → ℂ}

/-- A transverse curve on the side selected by `σ = ±1` avoids the trace on a segment to
that side's normal ray. The transverse inequality also guarantees that the tangent is nonzero. -/
private theorem eventually_segment_subset_compl_of_hasDerivAt {σ : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hσ : σ = 1 ∨ σ = -1) (hp0 : p s₀ = γ t₀)
    (hp : HasDerivWithinAt p w (Ici s₀) s₀) (hw : 0 < σ * (conj v * w).im) :
    v ≠ 0 ∧ ∀ᶠ s in 𝓝[>] s₀,
      segment ℝ (p s) (γ t₀ + (s - s₀) • (σ • (I * v))) ⊆ (γ '' uIcc a b)ᶜ := by
  have hab : a < b := ht₀.1.trans ht₀.2
  have hv : v ≠ 0 := by
    rintro rfl
    simp at hw
  have hu : σ • v = v ∨ σ • v = -v := by
    rcases hσ with rfl | rfl <;> simp
  have hw' : 0 < (conj (σ • v) * w).im := by
    simpa [Complex.real_smul, mul_assoc] using hw
  have huniq : ∀ t ∈ uIcc a b, γ t = γ t₀ → t = t₀ := fun t ht ↦
    hinj.eq_of_mem_Ioo_of_mem_Icc hclosed ht₀ (uIcc_of_le hab.le ▸ ht)
  refine ⟨hv, ?_⟩
  simp only [← mul_smul_comm σ I v]
  refine hp.eventually_segment_subset_compl_of_abs_im_conj_mul_sub_le (fun η hη ↦ ?_) hp0 hw'
  obtain ⟨ρ, hρ, h⟩ := isCompact_uIcc.exists_pos_forall_abs_im_conj_mul_sub_le hγ.continuousOn
    huniq hd.hasDerivWithinAt hη
  refine ⟨ρ, hρ, forall_mem_image.2 (fun s hs hsρ ↦ ?_)⟩
  rcases hu with hu | hu <;> simpa only [hu, map_neg, neg_mul, neg_im, abs_neg] using h s hs hsρ

/-- **A transverse curve enters the inside on the side selected by the orientation.** Let `γ` be
a simple closed absolutely continuous curve on `[a, b]`, with derivative `v` at an interior
parameter `t₀`. A curve `p` with `p s₀ = γ t₀` and right derivative `w` at `s₀` satisfying
`0 < jordanSign γ a b * Im (conj v * w)` lies in the bounded inside
`filledHull (γ '' uIcc a b) \ γ '' uIcc a b` for parameters sufficiently close to `s₀` from above.
For a positively oriented curve, this is the case of a curve leaving `γ t₀` strictly to the left
of the tangent. -/
theorem eventually_mem_filledHull_sdiff_of_hasDerivAt
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p s₀ = γ t₀)
    (hp : HasDerivWithinAt p w (Ici s₀) s₀)
    (hw : 0 < (jordanSign γ a b : ℝ) * (conj v * w).im) :
    ∀ᶠ s in 𝓝[>] s₀, p s ∈ filledHull (γ '' uIcc a b) \ γ '' uIcc a b := by
  have hab : a < b := ht₀.1.trans ht₀.2
  obtain ⟨hv, hseg⟩ := eventually_segment_subset_compl_of_hasDerivAt hγ hclosed hinj ht₀ hd
    (by exact_mod_cast hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj) hp0 hp hw
  have hsub : Tendsto (fun s : ℝ ↦ s - s₀) (𝓝[>] s₀) (𝓝[>] 0) :=
    le_of_eq (by rw [Filter.map_subRight_nhdsGT, sub_self])
  filter_upwards [hsub.eventually
    (hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt hclosed hinj ht₀ hd hv),
    hseg] with s hn hseg
  have hmem := (convex_segment _ _).isPreconnected.subset_connectedComponentIn
    (right_mem_segment _ _ _) hseg (left_mem_segment _ _ _)
  exact ⟨(mem_filledHull_iff_of_mem_connectedComponentIn hmem).mpr hn.1.1,
    hseg (left_mem_segment _ _ _)⟩

/-- **A transverse curve enters the outside on the side opposite to the orientation.** Let `γ` be
a simple closed absolutely continuous curve on `[a, b]`, with derivative `v` at an interior
parameter `t₀`. A curve `p` with `p s₀ = γ t₀` and right derivative `w` at `s₀` satisfying
`jordanSign γ a b * Im (conj v * w) < 0` lies outside `filledHull (γ '' uIcc a b)` for parameters
sufficiently close to `s₀` from above. For a negatively oriented curve, this is the case of a curve
leaving `γ t₀` strictly to the left of the tangent. -/
theorem eventually_notMem_filledHull_of_hasDerivAt
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p s₀ = γ t₀)
    (hp : HasDerivWithinAt p w (Ici s₀) s₀)
    (hw : (jordanSign γ a b : ℝ) * (conj v * w).im < 0) :
    ∀ᶠ s in 𝓝[>] s₀, p s ∉ filledHull (γ '' uIcc a b) := by
  have hab : a < b := ht₀.1.trans ht₀.2
  have hσ : -((jordanSign γ a b : ℤ) : ℝ) = 1 ∨ -((jordanSign γ a b : ℤ) : ℝ) = -1 := by
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> simp [h]
  obtain ⟨hv, hseg⟩ := eventually_segment_subset_compl_of_hasDerivAt hγ hclosed hinj ht₀ hd
    hσ hp0 hp (by simpa using hw)
  have hsub : Tendsto (fun s : ℝ ↦ s - s₀) (𝓝[>] s₀) (𝓝[>] 0) :=
    le_of_eq (by rw [Filter.map_subRight_nhdsGT, sub_self])
  filter_upwards [hsub.eventually
    (hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt hclosed hinj ht₀ hd hv),
    hseg] with s hn hseg
  simp only [neg_smul, smul_neg, ← sub_eq_add_neg] at hseg
  have hmem := (convex_segment _ _).isPreconnected.subset_connectedComponentIn
    (right_mem_segment _ _ _) hseg (left_mem_segment _ _ _)
  exact mt (mem_filledHull_iff_of_mem_connectedComponentIn hmem).mp hn.2

/-- A transverse curve enters the bounded inside for all parameters sufficiently close to `s₀`
from above if and only if its right derivative lies on the side selected by the orientation sign. -/
theorem jordanSign_mul_im_conj_mul_pos_iff_eventually_mem_filledHull_sdiff
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p s₀ = γ t₀)
    (hp : HasDerivWithinAt p w (Ici s₀) s₀) (hw : (conj v * w).im ≠ 0) :
    0 < (jordanSign γ a b : ℝ) * (conj v * w).im ↔
      ∀ᶠ s in 𝓝[>] s₀, p s ∈ filledHull (γ '' uIcc a b) \ γ '' uIcc a b := by
  have hab : a < b := ht₀.1.trans ht₀.2
  refine ⟨hγ.eventually_mem_filledHull_sdiff_of_hasDerivAt hclosed hinj ht₀ hd hp0 hp, ?_⟩
  intro hmem
  have hne := mul_ne_zero (Int.cast_ne_zero.mpr (hγ.jordanSign_ne_zero hab hclosed hinj)) hw
  by_contra h
  have hout := hγ.eventually_notMem_filledHull_of_hasDerivAt hclosed hinj ht₀ hd hp0 hp
    (lt_of_le_of_ne (le_of_not_gt h) hne)
  obtain ⟨ε, hin, hout⟩ := (hmem.and hout).exists
  exact hout hin.1

/-- A transverse curve enters the unbounded outside for all parameters sufficiently close to `s₀`
from above if and only if its right derivative lies on the side opposite to the orientation sign. -/
theorem jordanSign_mul_im_conj_mul_neg_iff_eventually_notMem_filledHull
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hp0 : p s₀ = γ t₀)
    (hp : HasDerivWithinAt p w (Ici s₀) s₀) (hw : (conj v * w).im ≠ 0) :
    (jordanSign γ a b : ℝ) * (conj v * w).im < 0 ↔
      ∀ᶠ s in 𝓝[>] s₀, p s ∉ filledHull (γ '' uIcc a b) := by
  have hab : a < b := ht₀.1.trans ht₀.2
  refine ⟨hγ.eventually_notMem_filledHull_of_hasDerivAt hclosed hinj ht₀ hd hp0 hp, ?_⟩
  intro hout
  have hne := mul_ne_zero (Int.cast_ne_zero.mpr (hγ.jordanSign_ne_zero hab hclosed hinj)) hw
  by_contra h
  have hmem := hγ.eventually_mem_filledHull_sdiff_of_hasDerivAt hclosed hinj ht₀ hd hp0 hp
    (lt_of_le_of_ne (le_of_not_gt h) hne.symm)
  obtain ⟨ε, hin, hout⟩ := (hmem.and hout).exists
  exact hout hin.1

end AbsolutelyContinuousOnInterval
