/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smooth maps between finite products of manifolds

On finite products `∀ i, M i` of charted spaces, modelled on `ModelWithCorners.pi I`, this file
records two smoothness results:

* a finite product of `C^n` maps is `C^n` (`ContMDiff.piMap`), the finite-product analogue of
  Mathlib's `ContMDiff.prodMap`;
* the coordinate insertion `Function.update x i : M i → ∀ j, M j`, the inclusion of the
  coordinate fiber through `x`, is `C^n` (`TauCeti.contMDiff_update`).

## Main results

* `ContMDiff.piMap`: a finite product of `C^n` maps is `C^n`.
* `TauCeti.contMDiff_update`: a coordinate insertion is `C^n`.
-/

public section

open Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  {n : WithTop ℕ∞}

/-- A finite product of `C^n` maps between manifolds is `C^n`. -/
theorem ContMDiff.piMap {E' : ι → Type*}
    [∀ i, NormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)] {H' : ι → Type*}
    [∀ i, TopologicalSpace (H' i)] {I' : ∀ i, ModelWithCorners 𝕜 (E' i) (H' i)} {M' : ι → Type*}
    [∀ i, TopologicalSpace (M' i)] [∀ i, ChartedSpace (H' i) (M' i)] {f : ∀ i, M i → M' i}
    (hf : ∀ i, ContMDiff (I i) (I' i) n (f i)) :
    ContMDiff (ModelWithCorners.pi I) (ModelWithCorners.pi I') n (Pi.map f) :=
  contMDiff_pi_iff.2 fun i ↦ (hf i).comp contMDiff_apply

namespace TauCeti

variable [DecidableEq ι]

/-- The coordinate insertion `Function.update x i : M i → ∀ j, M j`, the inclusion of the `i`-th
coordinate fiber through `x`, is `C^n`. -/
theorem contMDiff_update (x : ∀ i, M i) (i : ι) :
    ContMDiff (I i) (ModelWithCorners.pi I) n (update x i) := by
  refine contMDiff_pi_iff.2 fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp only [update_self]
    exact contMDiff_id
  · simpa [hj] using contMDiff_const

end TauCeti
