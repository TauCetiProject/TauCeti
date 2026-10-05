/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Topology.PL.Map

/-!
# Affine PL embeddings are locally flat

A graph of a continuous affine map is the basic affine piece in a piecewise-linear
embedding.  This file records two facts used when passing from affine charts to
locally flat embeddings: the graph map is PL, and its image is locally flat.
The latter is obtained by shearing the standard coordinate slice; the shear is a
homeomorphism, so no differentiable structure is involved.

This is the affine building block for the PL embedding side of geometric topology.
-/

public section

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The graph of a continuous affine map is piecewise affine on every subset of its domain. -/
theorem isPLOn_affineGraph (A : E →ᴬ[ℝ] F) (s : Set E) :
    IsPLOn (fun x : E => (x, A x)) s := by
  convert isPLOn_continuousAffineMap ((ContinuousAffineMap.id ℝ E).prod A) s using 1
  funext x
  rfl

/-- The graph of a continuous affine map is locally flat, with complementary model `F`. -/
theorem isLocallyFlat_affineGraph (A : E →ᴬ[ℝ] F) :
    IsLocallyFlat E F (fun x : E => (x, A x)) := by
  let shear : E × F ≃ₜ E × F :=
    { toFun := fun p => (p.1, p.2 + A p.1)
      invFun := fun p => (p.1, p.2 - A p.1)
      left_inv := by
        intro p
        simp
      right_inv := by
        intro p
        simp
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  have h := (isLocallyFlat_prodMkLeft (N := E) (F := E) (F' := F)).homeomorph_comp shear
  convert h using 1
  ext x
  · rfl
  · change A x = 0 + A x
    simp

end TauCeti
