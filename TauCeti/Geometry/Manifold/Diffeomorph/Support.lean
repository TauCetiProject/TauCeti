/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Supports of functions transported by diffeomorphisms

Transporting a function `F : M → α` along a diffeomorphism `ψ : M → N` gives `F ∘ ψ⁻¹`, whose
topological support is the image `ψ(tsupport F)`. Consequently `F ∘ ψ⁻¹` is supported in the
interior of `ψ(s)` when `F` is supported in the interior of `s`, and away from the boundary of
`N` when `F` is supported away from the boundary of `M`. These are the support conditions that
transport of compactly supported Hamiltonians along symplectomorphisms needs.

## Main results

* `Diffeomorph.tsupport_comp_symm`: `tsupport (F ∘ ψ⁻¹) = ψ(tsupport F)`.
* `Diffeomorph.tsupport_comp_symm_subset_interior_image`: support in the interior of a set is
  transported to support in the interior of its image.
* `Diffeomorph.tsupport_comp_symm_subset_interior_manifold`: support away from the boundary of the
  manifold is transported to support away from the boundary.
-/

public section

open Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {α : Type*} [Zero α]

namespace Diffeomorph

/-- The topological support of a function transported along a diffeomorphism `ψ` is the image
under `ψ` of its topological support. -/
theorem tsupport_comp_symm (ψ : M ≃ₘ^n⟮I, J⟯ N) (F : M → α) :
    tsupport (F ∘ ψ.symm) = ψ '' tsupport F := by
  rw [ψ.image_eq_preimage_symm, ← ψ.symm.coe_toHomeomorph,
    ← tsupport_comp_eq_preimage F ψ.symm.toHomeomorph]

/-- A function supported in the interior of `s`, transported along a diffeomorphism `ψ`, is
supported in the interior of `ψ(s)`. -/
theorem tsupport_comp_symm_subset_interior_image (ψ : M ≃ₘ^n⟮I, J⟯ N) {F : M → α} {s : Set M}
    (h : tsupport F ⊆ interior s) : tsupport (F ∘ ψ.symm) ⊆ interior (ψ '' s) := by
  rw [ψ.tsupport_comp_symm, ← ψ.coe_toHomeomorph, ← ψ.toHomeomorph.image_interior]
  exact image_mono h

/-- A function supported away from the boundary of `M`, transported along a diffeomorphism `ψ`,
is supported away from the boundary of `N`. -/
theorem tsupport_comp_symm_subset_interior_manifold (hn : n ≠ 0) (ψ : M ≃ₘ^n⟮I, J⟯ N) {F : M → α}
    (h : tsupport F ⊆ I.interior M) : tsupport (F ∘ ψ.symm) ⊆ J.interior N := by
  rw [ψ.tsupport_comp_symm, ← ψ.image_interior hn]
  exact image_mono h

end Diffeomorph
