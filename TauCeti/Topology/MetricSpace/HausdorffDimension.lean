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

## Main results

* `TauCeti.dense_compl_image_of_lipschitzOnWith` — the complement of a Lipschitz image is dense when
  the source has Hausdorff dimension below the target's finite dimension.

## Provenance

Replaces the measure-theoretic `CurveMeasureZero.lean` argument from the AINTLIB `LeanModularForms`
development with Mathlib's Hausdorff-dimension machinery, giving a stronger (dense-complement)
conclusion with no measure theory. (The off-curve base point of the homology Cauchy theorem is
supplied by the weaker-hypothesis `TauCeti.Contour.exists_mem_off_curve`, which needs only
continuity; this density theorem remains as the quantitatively stronger Lipschitz statement.)
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


end TauCeti

end
