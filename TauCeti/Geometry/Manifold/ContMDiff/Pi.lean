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

It also records that a family of maps which is a `C^n` map at one index and zero at the others is
`C^n` at every index (`ContMDiff.piSingle_apply`), as are the uncurried members of such a family of
two-variable maps (`ContMDiff.uncurry_piSingle_apply`).

## Main results

* `ContMDiff.piMap`: a finite product of `C^n` maps is `C^n`.
* `TauCeti.contMDiff_update`: a coordinate insertion is `C^n`.
* `ContMDiff.piSingle_apply`: the members of `Pi.single i f` are `C^n` when `f` is.
* `ContMDiff.uncurry_piSingle_apply`: the uncurried members of `Pi.single i f` are `C^n` when
  `uncurry f` is.
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

/-- The family which is a `C^n` map `f` at the index `i` and zero at the other indices is `C^n` at
every index. -/
theorem ContMDiff.piSingle_apply {κ : Type*} [DecidableEq κ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [Zero M'] {f : M → M'}
    (hf : ContMDiff I I' n f) (i j : κ) : ContMDiff I I' n ((Pi.single i f : κ → M → M') j) := by
  rcases eq_or_ne j i with rfl | h
  · simpa using hf
  · rw [Pi.single_eq_of_ne h]
    exact contMDiff_const

/-- If the uncurried map `uncurry f` is `C^n`, then so is the uncurried map at every index of the
family which is `f` at the index `i` and zero at the other indices. -/
theorem ContMDiff.uncurry_piSingle_apply {κ : Type*} [DecidableEq κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {X Y : Type*}
    [TopologicalSpace (X × Y)] [ChartedSpace H (X × Y)] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [Zero M'] {f : X → Y → M'}
    (hf : ContMDiff I I' n (uncurry f)) (i j : κ) :
    ContMDiff I I' n (uncurry ((Pi.single i f : κ → X → Y → M') j)) := by
  rw [Pi.apply_single (fun _ ↦ uncurry) (fun _ ↦ rfl) i f j]
  exact hf.piSingle_apply i j

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
