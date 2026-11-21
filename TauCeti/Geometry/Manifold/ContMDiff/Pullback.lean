/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Smoothness of maps for pulled-back charted-space structures

Given a charted space `M` modelled on `H` and a homeomorphism `e : M' ≃ₜ M`, the pulled-back
charted-space structure `e.pullbackChartedSpace` makes `e` a `C^n` diffeomorphism
(`Homeomorph.pullbackDiffeomorph`). Consequently, smoothness (within a set at a point, at a point,
on a set, or globally) of maps out of or into `M'` is equivalent to smoothness of the corresponding
maps conjugated by `e`.

No `IsManifold` or boundarylessness hypothesis is needed: the coordinate changes with the
pulled-back charts cancel `e` directly.

## Main results

* `Homeomorph.contMDiff_pullbackChartedSpace`,
  `Homeomorph.contMDiff_symm_pullbackChartedSpace`: `e` and `e.symm` are `C^n` for
  `e.pullbackChartedSpace`.
* `Homeomorph.contMDiffWithinAt_pullbackChartedSpace_left_iff`,
  `Homeomorph.contMDiffAt_pullbackChartedSpace_left_iff`,
  `Homeomorph.contMDiffOn_pullbackChartedSpace_left_iff`,
  `Homeomorph.contMDiff_pullbackChartedSpace_left_iff`: smoothness of maps out of a pulled-back
  charted space.
* `Homeomorph.contMDiffWithinAt_pullbackChartedSpace_right_iff`,
  `Homeomorph.contMDiffAt_pullbackChartedSpace_right_iff`,
  `Homeomorph.contMDiffOn_pullbackChartedSpace_right_iff`,
  `Homeomorph.contMDiff_pullbackChartedSpace_right_iff`: smoothness of maps into a pulled-back
  charted space.
* `Homeomorph.contMDiffWithinAt_pullbackChartedSpace_iff`,
  `Homeomorph.contMDiffAt_pullbackChartedSpace_iff`,
  `Homeomorph.contMDiffOn_pullbackChartedSpace_iff`,
  `Homeomorph.contMDiff_pullbackChartedSpace_iff`: smoothness when both source and target carry
  pulled-back charted-space structures.

## References

* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume I,
  Chapter I, Section 1.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Homeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {N' : Type*} [TopologicalSpace N']
  {n : ℕ∞ω}

/-- A homeomorphism onto a charted space is `C^n` for the pulled-back charted-space structure. -/
theorem contMDiff_pullbackChartedSpace (e : M' ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiff I I n e := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph] using (e.pullbackDiffeomorph I n).contMDiff

/-- The inverse of a homeomorphism onto a charted space is `C^n` for the pulled-back charted-space
structure. -/
theorem contMDiff_symm_pullbackChartedSpace (e : M' ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiff I I n e.symm := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph_symm] using (e.pullbackDiffeomorph I n).symm.contMDiff

/-! ### Pulling back the source atlas -/

/-- Precomposing a map with `e : M' ≃ₜ M` is `C^n` within `s` at `x` for `e.pullbackChartedSpace`
if and only if the map is `C^n` within `e.symm ⁻¹' s` at `e x`. -/
@[simp]
theorem contMDiffWithinAt_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N}
    {s : Set M'} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiffWithinAt I I' n (f ∘ e) s x ↔ ContMDiffWithinAt I I' n f (e.symm ⁻¹' s) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph, coe_pullbackDiffeomorph_symm] using
    (e.pullbackDiffeomorph I n).contMDiffWithinAt_comp_diffeomorph_iff
      (I' := I') (f := f) (s := s) (x := x) le_rfl

/-- A map out of `M'` is `C^n` within `s` at `x` for `e.pullbackChartedSpace` if and only if
`g ∘ e.symm` is `C^n` within `e.symm ⁻¹' s` at `e x`. -/
theorem contMDiffWithinAt_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N}
    {s : Set M'} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiffWithinAt I I' n g s x ↔
      ContMDiffWithinAt I I' n (g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.contMDiffWithinAt_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-- Precomposing a map with `e : M' ≃ₜ M` is `C^n` at `x` for `e.pullbackChartedSpace` if and only
if the map is `C^n` at `e x`. -/
@[simp]
theorem contMDiffAt_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiffAt I I' n (f ∘ e) x ↔ ContMDiffAt I I' n f (e x) := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph] using
    (e.pullbackDiffeomorph I n).contMDiffAt_comp_diffeomorph_iff
      (I' := I') (f := f) (x := x) le_rfl

/-- A map out of `M'` is `C^n` at `x` for `e.pullbackChartedSpace` if and only if `g ∘ e.symm` is
`C^n` at `e x`. -/
theorem contMDiffAt_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiffAt I I' n g x ↔ ContMDiffAt I I' n (g ∘ e.symm) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.contMDiffAt_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-- Precomposing a map with `e : M' ≃ₜ M` is `C^n` on `s` for `e.pullbackChartedSpace` if and only
if the map is `C^n` on `e.symm ⁻¹' s`. -/
@[simp]
theorem contMDiffOn_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N} {s : Set M'} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiffOn I I' n (f ∘ e) s ↔ ContMDiffOn I I' n f (e.symm ⁻¹' s) := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph, coe_pullbackDiffeomorph_symm] using
    (e.pullbackDiffeomorph I n).contMDiffOn_comp_diffeomorph_iff
      (I' := I') (f := f) (s := s) le_rfl

/-- A map out of `M'` is `C^n` on `s` for `e.pullbackChartedSpace` if and only if `g ∘ e.symm` is
`C^n` on `e.symm ⁻¹' s`. -/
theorem contMDiffOn_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N} {s : Set M'} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiffOn I I' n g s ↔ ContMDiffOn I I' n (g ∘ e.symm) (e.symm ⁻¹' s) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.contMDiffOn_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-- Precomposing a map with `e : M' ≃ₜ M` is `C^n` for `e.pullbackChartedSpace` if and only if the
map is `C^n`. -/
@[simp]
theorem contMDiff_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiff I I' n (f ∘ e) ↔ ContMDiff I I' n f := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph] using
    (e.pullbackDiffeomorph I n).contMDiff_comp_diffeomorph_iff (I' := I') (f := f) le_rfl

/-- A map out of `M'` is `C^n` for `e.pullbackChartedSpace` if and only if `g ∘ e.symm` is `C^n`. -/
theorem contMDiff_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N} :
    letI := e.pullbackChartedSpace (H := H)
    ContMDiff I I' n g ↔ ContMDiff I I' n (g ∘ e.symm) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.contMDiff_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-! ### Pulling back the target atlas -/

/-- A map into `N'` is `C^n` within `s` at `x` for `e'.pullbackChartedSpace` if and only if
`e' ∘ g` is `C^n` within `s` at `x`. -/
theorem contMDiffWithinAt_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'}
    {s : Set M} {x : M} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffWithinAt I I' n g s x ↔ ContMDiffWithinAt I I' n (e' ∘ g) s x := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).contMDiffWithinAt_diffeomorph_comp_iff
      (I' := I) (f := g) (s := s) (x := x) le_rfl).symm

/-- Postcomposing a map into `N` with `e'.symm` is `C^n` within `s` at `x` for
`e'.pullbackChartedSpace` if and only if the map is `C^n` within `s` at `x`. -/
@[simp]
theorem contMDiffWithinAt_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N}
    {s : Set M} {x : M} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffWithinAt I I' n (e'.symm ∘ f) s x ↔ ContMDiffWithinAt I I' n f s x := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.contMDiffWithinAt_diffeomorph_comp_iff
      (I' := I) (f := f) (s := s) (x := x) le_rfl

/-- A map into `N'` is `C^n` at `x` for `e'.pullbackChartedSpace` if and only if `e' ∘ g` is `C^n`
at `x`. -/
theorem contMDiffAt_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'} {x : M} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffAt I I' n g x ↔ ContMDiffAt I I' n (e' ∘ g) x := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).contMDiffAt_diffeomorph_comp_iff
      (I' := I) (f := g) (x := x) le_rfl).symm

/-- Postcomposing a map into `N` with `e'.symm` is `C^n` at `x` for `e'.pullbackChartedSpace` if
and only if the map is `C^n` at `x`. -/
@[simp]
theorem contMDiffAt_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N} {x : M} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffAt I I' n (e'.symm ∘ f) x ↔ ContMDiffAt I I' n f x := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.contMDiffAt_diffeomorph_comp_iff
      (I' := I) (f := f) (x := x) le_rfl

/-- A map into `N'` is `C^n` on `s` for `e'.pullbackChartedSpace` if and only if `e' ∘ g` is `C^n`
on `s`. -/
theorem contMDiffOn_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'} {s : Set M} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffOn I I' n g s ↔ ContMDiffOn I I' n (e' ∘ g) s := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).contMDiffOn_diffeomorph_comp_iff
      (I' := I) (f := g) (s := s) le_rfl).symm

/-- Postcomposing a map into `N` with `e'.symm` is `C^n` on `s` for `e'.pullbackChartedSpace` if
and only if the map is `C^n` on `s`. -/
@[simp]
theorem contMDiffOn_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N} {s : Set M} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffOn I I' n (e'.symm ∘ f) s ↔ ContMDiffOn I I' n f s := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.contMDiffOn_diffeomorph_comp_iff
      (I' := I) (f := f) (s := s) le_rfl

/-- A map into `N'` is `C^n` for `e'.pullbackChartedSpace` if and only if `e' ∘ g` is `C^n`. -/
theorem contMDiff_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiff I I' n g ↔ ContMDiff I I' n (e' ∘ g) := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).contMDiff_diffeomorph_comp_iff
      (I' := I) (f := g) le_rfl).symm

/-- Postcomposing a map into `N` with `e'.symm` is `C^n` for `e'.pullbackChartedSpace` if and only
if the map is `C^n`. -/
@[simp]
theorem contMDiff_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N} :
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiff I I' n (e'.symm ∘ f) ↔ ContMDiff I I' n f := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.contMDiff_diffeomorph_comp_iff
      (I' := I) (f := f) le_rfl

/-! ### Pulling back both source and target atlases -/

/-- A map between spaces carrying pulled-back charted-space structures is `C^n` within `s` at `x`
if and only if its conjugate `e' ∘ g ∘ e.symm` is `C^n` within `e.symm ⁻¹' s` at `e x`. -/
theorem contMDiffWithinAt_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'}
    {s : Set M'} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffWithinAt I I' n g s x ↔
      ContMDiffWithinAt I I' n (e' ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.contMDiffWithinAt_pullbackChartedSpace_right_iff (I := I)).trans
    (e.contMDiffWithinAt_pullbackChartedSpace_left_iff (I' := I'))

/-- A map between spaces carrying pulled-back charted-space structures is `C^n` at `x` if and only
if its conjugate `e' ∘ g ∘ e.symm` is `C^n` at `e x`. -/
theorem contMDiffAt_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'}
    {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffAt I I' n g x ↔ ContMDiffAt I I' n (e' ∘ g ∘ e.symm) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.contMDiffAt_pullbackChartedSpace_right_iff (I := I)).trans
    (e.contMDiffAt_pullbackChartedSpace_left_iff (I' := I'))

/-- A map between spaces carrying pulled-back charted-space structures is `C^n` on `s` if and only
if its conjugate `e' ∘ g ∘ e.symm` is `C^n` on `e.symm ⁻¹' s`. -/
theorem contMDiffOn_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'}
    {s : Set M'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiffOn I I' n g s ↔ ContMDiffOn I I' n (e' ∘ g ∘ e.symm) (e.symm ⁻¹' s) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.contMDiffOn_pullbackChartedSpace_right_iff (I := I)).trans
    (e.contMDiffOn_pullbackChartedSpace_left_iff (I' := I'))

/-- A map between spaces carrying pulled-back charted-space structures is `C^n` if and only if its
conjugate `e' ∘ g ∘ e.symm` is `C^n`. -/
theorem contMDiff_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    ContMDiff I I' n g ↔ ContMDiff I I' n (e' ∘ g ∘ e.symm) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.contMDiff_pullbackChartedSpace_right_iff (I := I)).trans
    (e.contMDiff_pullbackChartedSpace_left_iff (I' := I'))

end Homeomorph
