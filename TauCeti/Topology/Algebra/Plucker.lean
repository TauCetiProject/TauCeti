/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker

/-!
# Continuity of Plücker coordinates

The maximal minors of a finite family of coordinate vectors vary continuously with
that family. This allows Plücker coordinates to define continuous projective maps
from spaces of frames and their Grassmannian quotients.
-/

public section

namespace TauCeti

variable {R ι : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LinearOrder ι] {p : ℕ}

/-- Plücker coordinates are continuous functions of the vectors, with the product
topologies on both coordinate spaces. -/
@[fun_prop]
theorem continuous_plucker : Continuous (plucker (R := R) (ι := ι) (p := p)) := by
  classical
  refine continuous_pi fun s ↦ ?_
  simp only [plucker_apply]
  exact (continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply (Set.powersetCard.ofFinEmbEquiv.symm s j)).comp
      (continuous_apply i)).matrix_det

end TauCeti
