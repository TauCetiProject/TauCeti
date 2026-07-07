/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Lipschitz images of low-dimensional sets have dense complement

A Lipschitz map does not raise Hausdorff dimension, so if a set `s` has Hausdorff dimension strictly
below the (finite) dimension of the target space, the complement of its image is dense — a Lipschitz
strengthening of Mathlib's `C¹` Sard result `ContDiffOn.dense_compl_image_of_dimH_lt_finrank`.
Specialized to a curve `f : ℝ → ℂ` (source dimension `1 < 2`), every nonempty open subset of `ℂ`
therefore contains a point off the image.

The `ℝ → ℂ` corollary is the prerequisite that supplies the interior evaluation point off a curve in
the Cauchy integral formula: a piecewise-`C¹` curve is Lipschitz on its compact parameter interval,
so its image cannot cover a nonempty open set.

## Main results

* `TauCeti.dense_compl_image_of_lipschitzOnWith` — the complement of a Lipschitz image is dense when
  the source has Hausdorff dimension below the target's finite dimension.
* `TauCeti.exists_mem_notMem_image_of_isOpen_of_lipschitzOnWith` — a curve `f : ℝ → ℂ` Lipschitz on
  `s ⊆ ℝ` leaves a point of every nonempty open `U ⊆ ℂ` off its image.

## Provenance

Replaces the measure-theoretic `CurveMeasureZero.lean` argument from the AINTLIB `LeanModularForms`
development with Mathlib's Hausdorff-dimension machinery, giving a stronger (dense-complement)
conclusion with no measure theory. Prerequisite for the homology Cauchy theorem and the generalized
residue theorem on the roadmap.
-/

public section

noncomputable section

namespace TauCeti

open Set Module

/-- **A Lipschitz case of Sard's theorem.** A map `f` Lipschitz on `s` does not raise Hausdorff
dimension, so if `dimH s` lies below the dimension of the finite-dimensional real target `F`, the
complement of the image `f '' s` is dense. This strengthens Mathlib's `C¹`
`ContDiffOn.dense_compl_image_of_dimH_lt_finrank` to maps that are merely Lipschitz. -/
theorem dense_compl_image_of_lipschitzOnWith {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : NNReal} {f : E → F} {s : Set E} (hf : LipschitzOnWith K f s)
    (hs : dimH s < finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank (hf.dimH_image_le.trans_lt hs)

/-- A curve `f : ℝ → ℂ` Lipschitz on `s ⊆ ℝ` cannot cover a nonempty open set: its image has dense
complement (source dimension `1 < 2 = finrank ℝ ℂ`), so every nonempty open `U ⊆ ℂ` contains a point
off `f '' s`. -/
theorem exists_mem_notMem_image_of_isOpen_of_lipschitzOnWith {U : Set ℂ} (hU : IsOpen U)
    (hU_ne : U.Nonempty) {K : NNReal} {f : ℝ → ℂ} {s : Set ℝ} (hf : LipschitzOnWith K f s) :
    ∃ w ∈ U, w ∉ f '' s := by
  have hs : dimH s < finrank ℝ ℂ := by
    have h1 : dimH s ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ s)
    rw [Real.dimH_univ_eq_finrank] at h1
    rw [Complex.finrank_real_complex]
    refine h1.trans_lt ?_
    rw [finrank_self]
    norm_num
  obtain ⟨w, hw_notMem, hw_mem⟩ :=
    (dense_compl_image_of_lipschitzOnWith hf hs).exists_mem_open hU hU_ne
  exact ⟨w, hw_mem, hw_notMem⟩

end TauCeti

end
