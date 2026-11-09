/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.FlatStratum
public import TauCeti.Analysis.Calculus.Sard.MorseVanishing.Basic
public import TauCeti.Analysis.Calculus.Sard.Oscillation
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# Sard's theorem on the locus where the derivative vanishes

Let `f` be a map between finite-dimensional real normed spaces `E` and `F`, with `F` nontrivial,
which is `C^k` at every point of a set `s` where its Fréchet derivative vanishes. If
`finrank ℝ E ≤ k * finrank ℝ F`, then `f '' s` has additive Haar measure zero
(`TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`). Neither `s` nor its image needs to be
measurable or open.

This is the vanishing-derivative input of the Morse--Sard theorem at the sharp regularity. For
`k ≥ max 1 (finrank ℝ E - finrank ℝ F + 1)` and a nontrivial target the dimension condition holds,
since `(m - p + 1) * p - m = (m - p) * (p - 1) ≥ 0` when `m ≥ p ≥ 1`; the remaining stratum, where
the derivative is nonzero but not surjective, is treated in
`TauCeti.Analysis.Calculus.Sard.OutermostStratum`, where the theorem is assembled. Since a linear
map onto a one-dimensional space is surjective exactly when it is nonzero, the result here is
already the Morse--Sard theorem for real-valued maps, at regularity `C^(finrank ℝ E)`.

The proof follows A. P. Morse and A. Norton. Reading `E` in coordinates, the Morse criticality
lemma `TauCeti.exists_cover_of_critical` covers the vanishing-derivative locus of a `C^k` map by a
countable set and countably many bounded pieces on each of which `‖f y - f x‖ = o(‖y - x‖ ^ k)`
uniformly. A countable set has null image, and on each piece the map is Hölder of exponent `k` with
arbitrarily small constant at small scales, so the image of the piece has `finrank ℝ F`-dimensional
Hausdorff measure zero as soon as `finrank ℝ E ≤ k * finrank ℝ F`
(`TauCeti.addHaar_image_eq_zero_of_oscillation_pow`). Unlike Milnor's stratification by the order
of vanishing of the higher derivatives, this loses no derivatives to implicit-function charts, which
is what makes the sharp regularity reachable in every codimension.

The coordinate argument extends to maps into any finite-dimensional space the scalar sharp
theorem adapted from [KLS](https://github.com/human-ai-mathematics/kls-lean) at commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Sharp.lean`.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`: the image of a set of points at which the
  derivative vanishes is null, for a map that is `C^k` at those points with
  `finrank ℝ E ≤ k * finrank ℝ F`.
* `TauCeti.ContDiff.addHaar_image_vanishingFDeriv_eq_zero`: its global form.
* `TauCeti.setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero_of_finrank_eq_one`: for a
  one-dimensional target, the critical locus is exactly the vanishing-derivative locus.

## References

* A. P. Morse, *The behavior of a function on its critical set*, Ann. of Math. 40 (1939), 62–70.
* A. Norton, *A critical set with nonnull image has large Hausdorff dimension*, Trans. Amer. Math.
  Soc. 296 (1986), 367–376, Sections 4 and 5.
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

/-- The global form of `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero` on a coordinate space,
from the Morse criticality lemma and the oscillation estimate. -/
private theorem addHaar_image_vanishingFDeriv_eq_zero_pi {m : ℕ} {g : (Fin m → ℝ) → F}
    (hg : ContDiff ℝ k g) (hdim : m ≤ k * finrank ℝ F) :
    ν (g '' {x | fderiv ℝ g x = 0}) = 0 := by
  rcases k with _ | k
  · -- With `k = 0` the source is a point.
    obtain rfl : m = 0 := by simpa using hdim
    exact (Set.Subsingleton.image (fun a _ b _ ↦ Subsingleton.elim a b) g).measure_zero ν
  obtain ⟨A₀, P, hA₀, hP, hcov, hmod⟩ :=
    exists_cover_of_critical {x : Fin m → ℝ | fderiv ℝ g x = 0} (by exact_mod_cast hg)
      fun x hx ↦ hx
  refine measure_mono_null (image_mono hcov) ?_
  rw [image_union, sUnion_eq_biUnion, image_iUnion₂]
  refine measure_union_null ((hA₀.image g).measure_zero ν)
    ((measure_biUnion_null_iff hP).2 fun S hS ↦ ?_)
  exact addHaar_image_eq_zero_of_oscillation_pow ν (hmod S hS).1 hdim (hmod S hS).2

/-- **Sard's theorem on the locus where the derivative vanishes.** Let `f` be a map between
finite-dimensional real normed spaces with nontrivial target, and let `s` be a set at each point
of which `f` is `C^k` and the Fréchet derivative of `f` vanishes. If
`finrank ℝ E ≤ k * finrank ℝ F`, then `f '' s` has additive Haar measure zero. The set need not be
open or measurable.

The dimension condition holds at the sharp regularity `k ≥ max 1 (finrank ℝ E - finrank ℝ F + 1)`
of the Morse--Sard theorem; for a real-valued map it reads `finrank ℝ E ≤ k`. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero (hdim : finrank ℝ E ≤ k * finrank ℝ F)
    (hf : ∀ x ∈ s, ContDiffAt ℝ k f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : ν (f '' s) = 0 := by
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun x hx ↦ ?_
  -- Near `x`, replace `f` by a globally `C^k` map, then read the source in coordinates.
  obtain ⟨g, hg, -, hgf⟩ := (hf x hx).exists_contDiff_eventuallyEq_of_finiteDimensional _
  obtain ⟨U, hU, hUopen, hxU⟩ := _root_.mem_nhds_iff.1 (hgf.and (hgf.fderiv (𝕜 := ℝ)))
  refine ⟨s ∩ U, inter_mem_nhdsWithin s (hUopen.mem_nhds hxU), ?_⟩
  let e : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine measure_mono_null ?_ (addHaar_image_vanishingFDeriv_eq_zero_pi ν (g := g ∘ e)
    (hg.comp e.contDiff) (by simpa using hdim))
  rw [← e.image_vanishingFDeriv_comp g]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, (hU hy.2).2.trans (hs y hy.1), (hU hy.2).1⟩

/-- The image under a `C^k` map with nontrivial target of the whole locus where its Fréchet
derivative vanishes has additive Haar measure zero, when `finrank ℝ E ≤ k * finrank ℝ F`. -/
theorem ContDiff.addHaar_image_vanishingFDeriv_eq_zero (hf : ContDiff ℝ k f)
    (hdim : finrank ℝ E ≤ k * finrank ℝ F) :
    ν (f '' {x | fderiv ℝ f x = 0}) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero ν hdim (fun _ _ ↦ hf.contDiffAt) fun _ hx ↦ hx

/-- The complement of the image of the locus where the derivative of a `C^k` map with nontrivial
target vanishes is dense, when `finrank ℝ E ≤ k * finrank ℝ F`. -/
theorem ContDiff.dense_compl_image_vanishingFDeriv (hf : ContDiff ℝ k f)
    (hdim : finrank ℝ E ≤ k * finrank ℝ F) :
    Dense (f '' {x | fderiv ℝ f x = 0})ᶜ :=
  interior_eq_empty_iff_dense_compl.1 <| Measure.interior_eq_empty_of_null <|
    ContDiff.addHaar_image_vanishingFDeriv_eq_zero (ν := addHaar) hf hdim

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
    have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_one, h, norm_zero]
    exact not_surjective_fderiv_of_iteratedFDeriv_one_eq_zero h1 hsurj

end OneDimensional

end Sard

end TauCeti

end
