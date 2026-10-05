/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Graphs are locally flat

A graph of a continuous map is locally flat.  The proof shears the standard coordinate slice by
the map, and so uses only continuity and the additive topological-group structure of the model.
The affine case is exposed in the `ContinuousAffineMap` namespace for consumers building PL
embeddings.

This is the graph building block for the locally flat embedding side of geometric topology.
-/

public section

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The graph of a continuous map is locally flat, with complementary model `F`. -/
theorem isLocallyFlat_graph (f : E → F) (hf : Continuous f) :
    IsLocallyFlat E F (fun x : E => (x, f x)) := by
  let shear : E × F ≃ₜ E × F :=
    { toFun := fun p => (p.1, p.2 + f p.1)
      invFun := fun p => (p.1, p.2 - f p.1)
      left_inv := by
        intro p
        simp
      right_inv := by
        intro p
        simp
      continuous_toFun := continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst))
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst)) }
  have h := (isLocallyFlat_prodMkLeft (N := E) (F := E) (F' := F)).homeomorph_comp shear
  convert h using 1
  ext x
  · rfl
  · dsimp [Function.comp_apply, shear]
    simp only [zero_add]

/-- The graph of a continuous affine map is locally flat, with complementary model `F`. -/
theorem _root_.ContinuousAffineMap.isLocallyFlat_affineGraph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →ᴬ[ℝ] F) :
    IsLocallyFlat E F (fun x : E => (x, A x)) :=
  TauCeti.isLocallyFlat_graph A A.continuous

end TauCeti
