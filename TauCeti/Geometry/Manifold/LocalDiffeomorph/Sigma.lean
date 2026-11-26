/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ContMDiff.Sigma

/-!
# The inclusions of an indexed disjoint union are local diffeomorphisms

For a family of manifolds `M i` modelled on the same space, the disjoint union `Σ i, M i` is
charted by the charts of its components (`ChartedSpace.sigma`). Each inclusion
`Sigma.mk i : M i → Σ i, M i` is then a `C^n` diffeomorphism onto its open range: an inverse is
the map sending the copy of `M i` identically to `M i` and every other component to a fixed point
of `M i`, and it is `C^n` because its restriction to every component is
(`TauCeti.contMDiff_sigma_iff`). In particular the inclusions are `C^n` local diffeomorphisms,
so structures read through derivatives, such as orientations, transfer between the disjoint union
and its components. This is the indexed form of `TauCeti.isLocalDiffeomorph_sumInl`.

## Main results

* `TauCeti.isLocalDiffeomorph_sigmaMk`: the inclusion of a component of a disjoint union is a
  `C^n` local diffeomorphism.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

/-- The inclusion of a component of a disjoint union of manifolds is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_sigmaMk (i : ι) :
    IsLocalDiffeomorph I I n (Sigma.mk i : M i → Σ i, M i) := fun x ↦ by
  classical
  -- A global inverse on the range: the identity on the copy of `M i`, constant elsewhere.
  let g : (Σ j, M j) → M i := fun p ↦ if h : p.1 = i then h ▸ p.2 else x
  have hg (j : ι) : ContMDiff I I n (g ∘ Sigma.mk j) := by
    by_cases hj : j = i
    · subst hj
      exact contMDiff_id.congr fun y ↦ by simp [g]
    · exact (contMDiff_const (c := x)).congr fun y ↦ by simp [g, hj]
  let Φ : PartialDiffeomorph I I (M i) (Σ j, M j) n :=
    { toFun := Sigma.mk i
      invFun := g
      source := univ
      target := range (Sigma.mk i)
      map_source' := fun y _ ↦ mem_range_self y
      map_target' := fun _ _ ↦ mem_univ _
      left_inv' := fun y _ ↦ by simp [g]
      right_inv' := by rintro _ ⟨y, rfl⟩; simp [g]
      open_source := isOpen_univ
      open_target := isOpen_range_sigmaMk
      contMDiffOn_toFun := (contMDiff_sigmaMk i).contMDiffOn
      contMDiffOn_invFun := (contMDiff_sigma_iff.mpr hg).contMDiffOn }
  exact Φ.isLocalDiffeomorphAt I I n (mem_univ x)

end TauCeti
