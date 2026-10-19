/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Joint regularity of derivatives in vector-space families

For a jointly `C^m` family of maps from a normed space to another normed space, the derivative
in the vector-space variable is jointly `C^n` when `n + 1 ≤ m`. The parameter may range over
a manifold. This supplies derivative regularity for parameter-dependent coordinate formulas,
including the Christoffel symbols of a metric family.

## Formal sources

* Mathlib's `ContMDiffAt.mfderiv`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners 𝕜 G H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : P → E → F} {m n : ℕ∞ω} {z : P × E}

/-- The derivative in the vector-space variable of a jointly `C^m` family is jointly `C^n`
at a point when `n + 1 ≤ m`. No finite-dimensionality or completeness is required. -/
theorem contMDiffAt_fderiv_family
    (hg : ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) :
    ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, E →L[𝕜] F) n
      (fun q : P × E ↦ fderiv 𝕜 (g q.1) q.2) z := by
  have hfamily : ContMDiffAt ((J.prod 𝓘(𝕜, E)).prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m
      (fun q : (P × E) × E ↦ g q.1.1 q.2) (z, z.2) :=
    hg.comp (z, z.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hfamily.mfderiv (fun q : P × E ↦ g q.1) Prod.snd contMDiffAt_snd hnm
  convert h using 1
  ext q : 1
  -- `mfderiv` uses the normed-space instances on tangent fibres, whereas the model-space
  -- lemma uses those on E and F. `erw` unfolds these fibre instances; `rw` cannot match them.
  erw [inTangentCoordinates_model_space (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, F))]
  exact (mfderiv_eq_fderiv (𝕜 := 𝕜) (f := g q.1) (x := q.2)).symm

end TauCeti
