/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.Oscillation
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Analysis.Calculus.Sard.MorseVanishing.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# Sard's theorem on the locus where the derivative vanishes

Let `f : E → F` be a map between finite-dimensional real normed spaces of dimensions `m` and
`d ≥ 1`, and let `s` be a set of points at which the Fréchet derivative of `f` vanishes. If `f`
is `C^k` at the points of `s` and `m ≤ k * d`, then `f '' s` has additive Haar measure zero. The
set `s` need not be measurable.

This is the estimate that the Morse--Sard theorem needs on the innermost part of the critical
set. At Sard's regularity `k = max 1 (m - d + 1)` the inequality `m ≤ k * d` always holds, since
`(m - d + 1) * d - m = (m - d) * (d - 1)`; so the vanishing-derivative locus causes no loss of
regularity in any codimension. The remaining critical points, at which the derivative is nonzero
but not surjective, are handled by a Fubini argument in
`TauCeti.Analysis.Calculus.Sard.OutermostStratum`, where the theorem itself is assembled.

The proof is Morse's. By the Morse criticality lemma `TauCeti.exists_cover_of_critical`, the
locus is covered by a countable set and countably many bounded pieces on each of which
`‖f y - f x‖ = o(‖y - x‖ ^ k)` uniformly. Such a piece has an image of `d`-dimensional Hausdorff
measure at most a multiple of `ε ^ d` times its `k * d`-dimensional Hausdorff measure, for every
`ε > 0`, and `k * d ≥ m` makes the latter finite
(`TauCeti.addHaar_image_eq_zero_of_oscillation_pow`). Since the order of the modulus is not
lowered by passing to lower-dimensional pieces, no derivatives are lost along the way.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`: the image of a set of points at which the
  derivative vanishes is null, for a map that is `C^k` at those points with `m ≤ k * d`.
* `ContDiff.addHaar_image_vanishingFDeriv_eq_zero` and
  `ContDiff.dense_compl_image_vanishingFDeriv`: the global forms.
* `TauCeti.setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero_of_finrank_eq_one`: for a
  one-dimensional target, the critical locus is exactly the vanishing-derivative locus.

## References

* A. P. Morse, *The behavior of a function on its critical set*, Ann. of Math. 40 (1939),
  62–70.
* A. Norton, *A critical set with nonnull image has large Hausdorff dimension*, Trans. Amer. Math.
  Soc. 296 (1986), Sections 4 and 5, in their integer-regularity case.
* The coordinate reduction follows [KLS](https://github.com/human-ai-mathematics/kls-lean) at
  commit `65810c73f9dd7945fc646ab484cb19d673f5291d`,
  `formalization/FunctionalInequalities/Analysis/Sard/Sharp.lean`.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

section Sard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F] (ν : Measure F) [IsAddHaarMeasure ν]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → F} {s : Set E} {k : ℕ}

/-- The vanishing-derivative locus of a globally `C^(k+1)` map out of a coordinate space has null
image when `m ≤ (k + 1) * d`. -/
private theorem addHaar_image_vanishingFDeriv_eq_zero_pi {m : ℕ} {u : (Fin m → ℝ) → F}
    (hu : ContDiff ℝ (k + 1) u) (hdim : m ≤ (k + 1) * finrank ℝ F) :
    ν (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  obtain ⟨A₀, P, hA₀, hP, hcov, hmod⟩ :=
    exists_cover_of_critical {x : Fin m → ℝ | fderiv ℝ u x = 0} hu fun x hx ↦ hx
  refine measure_mono_null (image_mono hcov) ?_
  rw [image_union]
  refine measure_union_null ((hA₀.image u).measure_zero _) ?_
  rw [sUnion_eq_biUnion, image_iUnion₂]
  refine (measure_biUnion_null_iff hP).mpr fun S hS ↦ ?_
  exact addHaar_image_eq_zero_of_oscillation_pow ν (hmod S hS).1 (by simpa using hdim)
    (hmod S hS).2

/-- **Sard's theorem on the locus where the derivative vanishes.** Let `f` be a map between
finite-dimensional real normed spaces with nontrivial target, and let `s` be a set at each point
of which `f` is `C^k` and its Fréchet derivative vanishes. If
`finrank ℝ E ≤ k * finrank ℝ F`, then `f '' s` has additive Haar measure zero. The set `s` need
not be open or measurable. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero (hf : ∀ x ∈ s, ContDiffAt ℝ k f x)
    (hdim : finrank ℝ E ≤ k * finrank ℝ F) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) :
    ν (f '' s) = 0 := by
  rcases k with _ | k
  · have : Subsingleton E := Module.finrank_zero_iff.mp (by simpa using hdim)
    exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun x hx ↦ ?_
  -- Near `x`, replace `f` by a globally `C^(k+1)` map with the same values and derivatives.
  obtain ⟨g, hg, -, hgf⟩ := (hf x hx).exists_contDiff_eventuallyEq_of_finiteDimensional _
  obtain ⟨U, hU, hUopen, hxU⟩ := _root_.mem_nhds_iff.1 (hgf.and (hgf.fderiv (𝕜 := ℝ)))
  refine ⟨s ∩ U, inter_mem_nhdsWithin s (hUopen.mem_nhds hxU), ?_⟩
  let e : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hnull : ν (g '' {y | fderiv ℝ g y = 0}) = 0 := by
    rw [e.image_vanishingFDeriv_comp g]
    exact addHaar_image_vanishingFDeriv_eq_zero_pi ν (hg.comp e.contDiff) hdim
  refine measure_mono_null ?_ hnull
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, (hU hy.2).2.trans (hs y hy.1), (hU hy.2).1⟩

/-- The image under a `C^k` map with nontrivial target of the whole locus where its Fréchet
derivative vanishes has additive Haar measure zero, provided `finrank ℝ E ≤ k * finrank ℝ F`. -/
theorem _root_.ContDiff.addHaar_image_vanishingFDeriv_eq_zero (hf : ContDiff ℝ k f)
    (hdim : finrank ℝ E ≤ k * finrank ℝ F) :
    ν (f '' {x | fderiv ℝ f x = 0}) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero ν (fun _ _ ↦ hf.contDiffAt) hdim fun _ hx ↦ hx

/-- The complement of the image of the locus where the derivative of a `C^k` map with nontrivial
target vanishes is dense, provided `finrank ℝ E ≤ k * finrank ℝ F`. -/
theorem _root_.ContDiff.dense_compl_image_vanishingFDeriv (hf : ContDiff ℝ k f)
    (hdim : finrank ℝ E ≤ k * finrank ℝ F) :
    Dense (f '' {x | fderiv ℝ f x = 0})ᶜ :=
  interior_eq_empty_iff_dense_compl.1 <| Measure.interior_eq_empty_of_null <|
    hf.addHaar_image_vanishingFDeriv_eq_zero (ν := addHaar) hdim

section OneDimensional

variable (hF : finrank ℝ F = 1)

include hF

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
  [FiniteDimensional ℝ E] in
/-- A linear map into a one-dimensional space is surjective exactly when it is nonzero, so the
critical points of a map into such a space are the points where its derivative vanishes. -/
@[simp] theorem setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero_of_finrank_eq_one :
    {x | ¬ Surjective (fderiv ℝ f x)} = {x | fderiv ℝ f x = 0} := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  ext x
  simp only [mem_ofPred_eq, not_iff_comm]
  constructor
  · intro hx
    exact _root_.surjective_of_ne_zero_of_finrank_eq_one (f := (fderiv ℝ f x : E →ₗ[ℝ] F)) hF
      fun hzero ↦ hx (ContinuousLinearMap.coe_injective hzero)
  · rintro hsurj h
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    obtain ⟨v, hv⟩ := hsurj y
    exact hy (by simpa [h] using hv.symm)

end OneDimensional

end Sard

end TauCeti

end
