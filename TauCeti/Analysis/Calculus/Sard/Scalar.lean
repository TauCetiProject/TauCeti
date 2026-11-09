/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.MorseVanishing.Basic
public import TauCeti.Analysis.Calculus.Sard.Oscillation
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.MeasureTheory.Measure.LocallyNull
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The scalar Morse--Sard theorem at the sharp finite regularity

The critical values of a real-valued C^n function on an n-dimensional real normed space
have measure zero. The Morse vanishing decomposition preserves the order during dimension
reduction. No measurability assumption is placed on the critical set.

Adapted from [KLS](https://github.com/human-ai-mathematics/kls-lean) at commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Sharp.lean`.
The decomposition follows A. Norton, *A critical set with nonnull image has large Hausdorff
dimension*, Trans. Amer. Math. Soc. 296 (1986), Section 4, in its integer-regularity case.
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter Topology Function Module
open scoped ContDiff

namespace TauCeti

variable {n k : ℕ}

/-- **Sard's theorem for `C^n` real-valued functions on `Fin n → ℝ`.**  The critical set is not
assumed measurable.  This is the sharp finite regularity: `C^n`, not `C^∞`. -/
private theorem scalar_sard_pi : ∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ n u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  rintro (_ | m) u hu
  · refine Set.Subsingleton.measure_zero ?_ _
    exact Set.Subsingleton.image (fun a _ b _ => Subsingleton.elim a b) u
  · obtain ⟨A₀, P, hA₀, hP, hcov, hmod⟩ :=
      exists_cover_of_critical (k := m) {x : Fin (m + 1) → ℝ | fderiv ℝ u x = 0} hu
        (fun x hx => hx)
    refine measure_mono_null (Set.image_mono hcov) ?_
    rw [Set.image_union]
    refine measure_union_null ((hA₀.image u).measure_zero _) ?_
    rw [Set.sUnion_eq_biUnion, Set.image_iUnion₂]
    refine (measure_biUnion_null_iff hP).mpr fun S hS => ?_
    exact volume_image_eq_zero_of_oscillation_pow (hmod S hS).1 (hmod S hS).2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {s : Set E}

private theorem scalar_sard (hf : ContDiff ℝ (finrank ℝ E) f) :
    volume (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  let e : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp)
  rw [e.image_vanishingFDeriv_comp f]
  exact scalar_sard_pi _ _ (hf.comp e.contDiff)

/-- **Scalar Morse--Sard at the sharp finite regularity, on an arbitrary set.**
If a real-valued function is `C^(finrank ℝ E)` at each point of a set where its derivative
vanishes, its image has additive Haar measure zero. The set need not be open or measurable,
and dimension zero is included. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero_of_real (ν : Measure ℝ) [ν.IsAddHaarMeasure]
    {r : ℕ∞ω} (hf : ∀ x ∈ s, ContDiffAt ℝ r f x)
    (hk : (finrank ℝ E : ℕ∞ω) ≤ r) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : ν (f '' s) = 0 := by
  apply Measure.absolutelyContinuous_isAddHaarMeasure ν volume
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun x hx ↦ ?_
  obtain ⟨g, hg, -, hgf⟩ :=
    ((hf x hx).of_le hk).exists_contDiff_eventuallyEq_of_finiteDimensional _
  obtain ⟨U, hU, hUopen, hxU⟩ := _root_.mem_nhds_iff.1 (hgf.and (hgf.fderiv (𝕜 := ℝ)))
  refine ⟨s ∩ U, inter_mem_nhdsWithin s (hUopen.mem_nhds hxU), ?_⟩
  refine measure_mono_null ?_ (scalar_sard hg)
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, (hU hy.2).2.trans (hs y hy.1), (hU hy.2).1⟩

/-- **Scalar Morse--Sard at the sharp finite regularity.** The values taken at nonsurjective
derivative points of a real-valued map are null, provided the map is `C^(finrank ℝ E)` at each
point of `s`. No measurability or openness hypothesis on `s` is required. -/
theorem addHaar_image_criticalPoints_eq_zero_of_real (ν : Measure ℝ) [ν.IsAddHaarMeasure]
    {r : ℕ∞ω} (hf : ∀ x ∈ s, ContDiffAt ℝ r f x)
    (hk : (finrank ℝ E : ℕ∞ω) ≤ r) :
    ν (f '' (s ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 := by
  refine addHaar_image_eq_zero_of_fderiv_eq_zero_of_real ν (fun x hx ↦ hf x hx.1) hk ?_
  intro x hx
  by_contra hne
  exact hx.2 (LinearMap.surjective_iff_ne_zero.2 fun h ↦ hne (by
    ext v
    exact LinearMap.congr_fun h v))

/-- The critical values of a globally `C^(finrank ℝ E)` real-valued map have additive Haar
measure zero. -/
theorem _root_.ContDiff.addHaar_image_criticalPoints_eq_zero_of_real
    {r : ℕ∞ω} (hf : ContDiff ℝ r f) (ν : Measure ℝ) [ν.IsAddHaarMeasure]
    (hk : (finrank ℝ E : ℕ∞ω) ≤ r) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  simpa using TauCeti.addHaar_image_criticalPoints_eq_zero_of_real (s := univ) ν
    (fun x _ ↦ hf.contDiffAt) hk

/-- Almost every level of a `C^(finrank ℝ E)` real-valued map is regular at every point of
that level, including for a zero-dimensional source. -/
theorem _root_.ContDiff.ae_forall_surjective_fderiv_of_real
    {r : ℕ∞ω} (hf : ContDiff ℝ r f) (ν : Measure ℝ) [ν.IsAddHaarMeasure]
    (hk : (finrank ℝ E : ℕ∞ω) ≤ r) :
    ∀ᵐ t ∂ν, ∀ x, f x = t → Surjective (fderiv ℝ f x) := by
  have hnull := hf.addHaar_image_criticalPoints_eq_zero_of_real ν hk
  rw [ae_iff]
  apply measure_mono_null _ hnull
  intro t ht
  push Not at ht
  obtain ⟨x, hxt, hx⟩ := ht
  exact ⟨x, hx, hxt⟩

/-- The regular values of a `C^(finrank ℝ E)` real-valued map are dense. -/
theorem _root_.ContDiff.dense_compl_image_criticalPoints_of_real
    {r : ℕ∞ω} (hf : ContDiff ℝ r f) (hk : (finrank ℝ E : ℕ∞ω) ≤ r) :
    Dense (f '' {x | ¬ Surjective (fderiv ℝ f x)})ᶜ :=
  interior_eq_empty_iff_dense_compl.1 <| Measure.interior_eq_empty_of_null <|
    hf.addHaar_image_criticalPoints_eq_zero_of_real volume hk

end TauCeti
