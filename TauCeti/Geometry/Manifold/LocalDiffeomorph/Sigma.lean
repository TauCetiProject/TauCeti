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

The disjoint union `Σ i, M i` of manifolds on a common model is charted by the charts of its
components. Each inclusion `Sigma.mk i : M i → Σ i, M i` is then a `C^n` diffeomorphism onto its
open range, whose inverse is the second projection. In particular it is a `C^n` local
diffeomorphism. This is the indexed form of `TauCeti.isLocalDiffeomorph_sumInl`.

## Main results

* `TauCeti.isLocalDiffeomorph_sigmaMk`: the inclusion of a component into a disjoint union is a
  `C^n` local diffeomorphism.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {n : ℕ∞ω}

/-- The inclusion of a component into a disjoint union is a `C^n` local diffeomorphism: it is a
diffeomorphism onto the open copy of the component, with inverse the second projection. -/
theorem isLocalDiffeomorph_sigmaMk (i : ι) :
    IsLocalDiffeomorph I I n (Sigma.mk i : M i → Σ i, M i) := by
  intro x
  have : Nonempty (M i) := ⟨x⟩
  have hσ : Topology.IsOpenEmbedding (Sigma.mk i : M i → Σ i, M i) := .sigmaMk
  let Φ : PartialDiffeomorph I I (M i) (Σ i, M i) n :=
    { toPartialEquiv := (hσ.toOpenPartialHomeomorph _).toPartialEquiv
      open_source := (hσ.toOpenPartialHomeomorph _).open_source
      open_target := (hσ.toOpenPartialHomeomorph _).open_target
      contMDiffOn_toFun := by
        simpa using (contMDiff_sigmaMk (I := I) (n := n) i).contMDiffOn
      contMDiffOn_invFun := by
        rintro _ ⟨y, -, rfl⟩
        refine (contMDiffAt_sigma_iff.2
          (contMDiffAt_id.congr_of_eventuallyEq ?_)).contMDiffWithinAt
        exact Filter.Eventually.of_forall fun z ↦ hσ.toOpenPartialHomeomorph_left_inv }
  exact Φ.isLocalDiffeomorphAt I I n (Set.mem_univ x)

end TauCeti
