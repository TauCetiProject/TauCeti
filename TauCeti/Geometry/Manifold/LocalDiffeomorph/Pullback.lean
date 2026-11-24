/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph

/-!
# Local diffeomorphisms for pulled-back charted-space structures

Given a charted space `M` modelled on `H` and a homeomorphism `e : M' ≃ₜ M`, the pulled-back
charted-space structure `e.pullbackChartedSpace` makes `e` and `e.symm` `C^n` diffeomorphisms
(`Homeomorph.pullbackDiffeomorph`). Consequently, being a `C^n` local diffeomorphism (at a point,
on a set, or globally) out of or into `M'` is equivalent to being a `C^n` local diffeomorphism
after conjugation by `e`.

These criteria allow constructions specified by local diffeomorphisms, such as compatible open
gluing, to transport atlases along arbitrary homeomorphisms without `IsManifold` or
boundarylessness assumptions.

## Main results

* `Homeomorph.isLocalDiffeomorph_pullbackChartedSpace`,
  `Homeomorph.isLocalDiffeomorph_symm_pullbackChartedSpace`: `e` and `e.symm` are `C^n` local
  diffeomorphisms for `e.pullbackChartedSpace`.
* `Homeomorph.isLocalDiffeomorphAt_pullbackChartedSpace_left_iff`,
  `Homeomorph.isLocalDiffeomorphOn_pullbackChartedSpace_left_iff`,
  `Homeomorph.isLocalDiffeomorph_pullbackChartedSpace_left_iff`: local diffeomorphisms out of a
  pulled-back charted space.
* `Homeomorph.isLocalDiffeomorphAt_pullbackChartedSpace_right_iff`,
  `Homeomorph.isLocalDiffeomorphOn_pullbackChartedSpace_right_iff`,
  `Homeomorph.isLocalDiffeomorph_pullbackChartedSpace_right_iff`: local diffeomorphisms into a
  pulled-back charted space.
* `Homeomorph.isLocalDiffeomorphAt_pullbackChartedSpace_iff`,
  `Homeomorph.isLocalDiffeomorphOn_pullbackChartedSpace_iff`,
  `Homeomorph.isLocalDiffeomorph_pullbackChartedSpace_iff`: local diffeomorphisms when both source
  and target carry pulled-back charted-space structures.

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

/-- A homeomorphism onto a charted space is a `C^n` local diffeomorphism for the pulled-back
charted-space structure. -/
theorem isLocalDiffeomorph_pullbackChartedSpace (e : M' ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I n e := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph] using (e.pullbackDiffeomorph I n).isLocalDiffeomorph

/-- The inverse of a homeomorphism onto a charted space is a `C^n` local diffeomorphism for the
pulled-back charted-space structure. -/
theorem isLocalDiffeomorph_symm_pullbackChartedSpace (e : M' ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I n e.symm := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e.pullbackDiffeomorph I n).symm.isLocalDiffeomorph

/-! ### Pulling back the source atlas -/

/-- Precomposing a map with `e : M' ≃ₜ M` is a `C^n` local diffeomorphism at `x` for
`e.pullbackChartedSpace` if and only if the map is one at `e x`. -/
@[simp]
theorem isLocalDiffeomorphAt_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorphAt I I' n (f ∘ e) x ↔ IsLocalDiffeomorphAt I I' n f (e x) := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph] using
    (e.pullbackDiffeomorph I n).isLocalDiffeomorphAt_comp_diffeomorph_iff
      (K := I') (f := f) (x := x) le_rfl

/-- A map out of `M'` is a `C^n` local diffeomorphism at `x` for `e.pullbackChartedSpace` if and
only if `g ∘ e.symm` is one at `e x`. -/
theorem isLocalDiffeomorphAt_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N} {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorphAt I I' n g x ↔ IsLocalDiffeomorphAt I I' n (g ∘ e.symm) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.isLocalDiffeomorphAt_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-- Precomposing a map with `e : M' ≃ₜ M` is a `C^n` local diffeomorphism on `s` for
`e.pullbackChartedSpace` if and only if the map is one on `e.symm ⁻¹' s`. -/
@[simp]
theorem isLocalDiffeomorphOn_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N} {s : Set M'} :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorphOn I I' n (f ∘ e) s ↔ IsLocalDiffeomorphOn I I' n f (e.symm ⁻¹' s) := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph, coe_pullbackDiffeomorph_symm] using
    (e.pullbackDiffeomorph I n).isLocalDiffeomorphOn_comp_diffeomorph_iff
      (K := I') (f := f) (s := s) le_rfl

/-- A map out of `M'` is a `C^n` local diffeomorphism on `s` for `e.pullbackChartedSpace` if and
only if `g ∘ e.symm` is one on `e.symm ⁻¹' s`. -/
theorem isLocalDiffeomorphOn_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N} {s : Set M'} :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorphOn I I' n g s ↔
      IsLocalDiffeomorphOn I I' n (g ∘ e.symm) (e.symm ⁻¹' s) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.isLocalDiffeomorphOn_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-- Precomposing a map with `e : M' ≃ₜ M` is a `C^n` local diffeomorphism for
`e.pullbackChartedSpace` if and only if the map is one. -/
@[simp]
theorem isLocalDiffeomorph_comp_pullbackChartedSpace_iff (e : M' ≃ₜ M) {f : M → N} :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I' n (f ∘ e) ↔ IsLocalDiffeomorph I I' n f := by
  let := e.pullbackChartedSpace (H := H)
  simpa only [coe_pullbackDiffeomorph] using
    (e.pullbackDiffeomorph I n).isLocalDiffeomorph_comp_diffeomorph_iff
      (K := I') (f := f) le_rfl

/-- A map out of `M'` is a `C^n` local diffeomorphism for `e.pullbackChartedSpace` if and only if
`g ∘ e.symm` is one. -/
theorem isLocalDiffeomorph_pullbackChartedSpace_left_iff (e : M' ≃ₜ M) {g : M' → N} :
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I' n g ↔ IsLocalDiffeomorph I I' n (g ∘ e.symm) := by
  let := e.pullbackChartedSpace (H := H)
  have heq : (g ∘ e.symm) ∘ e = g := funext fun y ↦ congrArg g (e.symm_apply_apply y)
  rw [← e.isLocalDiffeomorph_comp_pullbackChartedSpace_iff (f := g ∘ e.symm), heq]

/-! ### Pulling back the target atlas -/

/-- A map into `N'` is a `C^n` local diffeomorphism at `x` for `e'.pullbackChartedSpace` if and
only if `e' ∘ g` is one at `x`. -/
theorem isLocalDiffeomorphAt_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'} {x : M} :
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorphAt I I' n g x ↔ IsLocalDiffeomorphAt I I' n (e' ∘ g) x := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).isLocalDiffeomorphAt_diffeomorph_comp_iff
      (K := I) (f := g) le_rfl (x := x)).symm

/-- Postcomposing a map into `N` with `e'.symm` is a `C^n` local diffeomorphism at `x` for
`e'.pullbackChartedSpace` if and only if the map is one at `x`. -/
@[simp]
theorem isLocalDiffeomorphAt_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N}
    {x : M} :
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorphAt I I' n (e'.symm ∘ f) x ↔ IsLocalDiffeomorphAt I I' n f x := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.isLocalDiffeomorphAt_diffeomorph_comp_iff
      (K := I) (f := f) le_rfl (x := x)

/-- A map into `N'` is a `C^n` local diffeomorphism on `s` for `e'.pullbackChartedSpace` if and
only if `e' ∘ g` is one on `s`. -/
theorem isLocalDiffeomorphOn_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'}
    {s : Set M} :
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorphOn I I' n g s ↔ IsLocalDiffeomorphOn I I' n (e' ∘ g) s := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).isLocalDiffeomorphOn_diffeomorph_comp_iff
      (K := I) (f := g) le_rfl (s := s)).symm

/-- Postcomposing a map into `N` with `e'.symm` is a `C^n` local diffeomorphism on `s` for
`e'.pullbackChartedSpace` if and only if the map is one on `s`. -/
@[simp]
theorem isLocalDiffeomorphOn_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N}
    {s : Set M} :
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorphOn I I' n (e'.symm ∘ f) s ↔ IsLocalDiffeomorphOn I I' n f s := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.isLocalDiffeomorphOn_diffeomorph_comp_iff
      (K := I) (f := f) le_rfl (s := s)

/-- A map into `N'` is a `C^n` local diffeomorphism for `e'.pullbackChartedSpace` if and only if
`e' ∘ g` is one. -/
theorem isLocalDiffeomorph_pullbackChartedSpace_right_iff (e' : N' ≃ₜ N) {g : M → N'} :
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorph I I' n g ↔ IsLocalDiffeomorph I I' n (e' ∘ g) := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph] using
    ((e'.pullbackDiffeomorph I' n).isLocalDiffeomorph_diffeomorph_comp_iff
      (K := I) (f := g) le_rfl).symm

/-- Postcomposing a map into `N` with `e'.symm` is a `C^n` local diffeomorphism for
`e'.pullbackChartedSpace` if and only if the map is one. -/
@[simp]
theorem isLocalDiffeomorph_symm_comp_pullbackChartedSpace_iff (e' : N' ≃ₜ N) {f : M → N} :
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorph I I' n (e'.symm ∘ f) ↔ IsLocalDiffeomorph I I' n f := by
  let := e'.pullbackChartedSpace (H := H')
  simpa only [coe_pullbackDiffeomorph_symm] using
    (e'.pullbackDiffeomorph I' n).symm.isLocalDiffeomorph_diffeomorph_comp_iff
      (K := I) (f := f) le_rfl

/-! ### Pulling back both source and target atlases -/

/-- A map between spaces carrying pulled-back charted-space structures is a `C^n` local
diffeomorphism at `x` if and only if its conjugate `e' ∘ g ∘ e.symm` is one at `e x`. -/
theorem isLocalDiffeomorphAt_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'}
    {x : M'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorphAt I I' n g x ↔
      IsLocalDiffeomorphAt I I' n (e' ∘ g ∘ e.symm) (e x) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.isLocalDiffeomorphAt_pullbackChartedSpace_right_iff (I := I)).trans
    (e.isLocalDiffeomorphAt_pullbackChartedSpace_left_iff (I' := I'))

/-- A map between spaces carrying pulled-back charted-space structures is a `C^n` local
diffeomorphism on `s` if and only if its conjugate `e' ∘ g ∘ e.symm` is one on `e.symm ⁻¹' s`. -/
theorem isLocalDiffeomorphOn_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'}
    {s : Set M'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorphOn I I' n g s ↔
      IsLocalDiffeomorphOn I I' n (e' ∘ g ∘ e.symm) (e.symm ⁻¹' s) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.isLocalDiffeomorphOn_pullbackChartedSpace_right_iff (I := I)).trans
    (e.isLocalDiffeomorphOn_pullbackChartedSpace_left_iff (I' := I'))

/-- A map between spaces carrying pulled-back charted-space structures is a `C^n` local
diffeomorphism if and only if its conjugate `e' ∘ g ∘ e.symm` is one. -/
theorem isLocalDiffeomorph_pullbackChartedSpace_iff (e : M' ≃ₜ M) (e' : N' ≃ₜ N) {g : M' → N'} :
    letI := e.pullbackChartedSpace (H := H)
    letI := e'.pullbackChartedSpace (H := H')
    IsLocalDiffeomorph I I' n g ↔ IsLocalDiffeomorph I I' n (e' ∘ g ∘ e.symm) := by
  let := e.pullbackChartedSpace (H := H)
  let := e'.pullbackChartedSpace (H := H')
  exact (e'.isLocalDiffeomorph_pullbackChartedSpace_right_iff (I := I)).trans
    (e.isLocalDiffeomorph_pullbackChartedSpace_left_iff (I' := I'))

end Homeomorph
