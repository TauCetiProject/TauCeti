/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Tangent cones under differentiable embeddings

A parametrization with a differentiable left inverse transports tangent cones exactly by its
differential. Unlike a change of coordinates by a local diffeomorphism, the parametrization
may take values in a higher-dimensional space. This applies in particular to graph embeddings,
whose left inverse is coordinate projection.

Only derivatives within the parameter set and its image are needed. Neither openness,
finite dimension, nor completeness is required.
-/

public section

open Set

namespace HasFDerivWithinAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {g : F → E} {f' : E →L[𝕜] F} {g' : F →L[𝕜] E} {s : Set E} {x : E}

/-- A parametrization with a differentiable left inverse carries the tangent cone of its
parameter set onto the tangent cone of its image. The inverse need only be differentiable
within that image. -/
theorem image_tangentConeAt_of_leftInverse (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' (f '' s) (f x)) (hgf : Function.LeftInverse g f) :
    f' '' tangentConeAt 𝕜 s x = tangentConeAt 𝕜 (f '' s) (f x) := by
  have hmaps : MapsTo g (f '' s) s := by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [hgf y] using hy
  have hcomp : HasFDerivWithinAt (fun y => f (g y)) (f'.comp g') (f '' s) (f x) := by
    have hf' : HasFDerivWithinAt f f' s (g (f x)) := by rwa [hgf x]
    exact hf'.comp (f x) hg hmaps
  have hid : HasFDerivWithinAt (fun y => f (g y)) (ContinuousLinearMap.id 𝕜 F)
      (f '' s) (f x) := by
    apply (hasFDerivWithinAt_id (f x) (f '' s)).congr
    · rintro _ ⟨y, hy, rfl⟩
      simp only [id_eq, hgf y]
    · simp only [id_eq, hgf x]
  refine Subset.antisymm hf.mapsTo_tangent_cone.image_subset ?_
  intro v hv
  refine ⟨g' v, ?_, hcomp.unique_on hid hv⟩
  have hcone := hg.mapsTo_tangent_cone hv
  rwa [hgf.image_image, hgf x] at hcone

end HasFDerivWithinAt
