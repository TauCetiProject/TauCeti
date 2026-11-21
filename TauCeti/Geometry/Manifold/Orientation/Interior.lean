/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Interior
public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Transporting smooth orientations to the interior vector-space atlas

Let `(M, I)` be a boundaryless `C¹` manifold (`[BoundarylessManifold I M]`) modelled on a
finite-dimensional real normed space `E`. Pulling an orientation `o` of `M` back along the inverse
of `TauCeti.BoundarylessModel.interiorDiffeomorph I 1` equips the vector-space copy
`TauCeti.BoundarylessModel I M` (with the interior chart structure
`TauCeti.BoundarylessModel.interiorChartedSpace`) with an orientation `o.interiorOrientation`
under which both directions of `TauCeti.BoundarylessModel.interiorDiffeomorph` preserve orientation
at every point.

## Main definitions

* `TauCeti.Manifold.Orientation.interiorOrientation`: transport a manifold orientation of a
  boundaryless `C¹` manifold `(M, I)` to the interior vector-space atlas.

## Main results

* `TauCeti.Manifold.Orientation.interiorOrientation_neg`: reversing `o` negates
  `o.interiorOrientation`.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_interiorDiffeomorph_symm`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_interiorDiffeomorph`: both directions of
  `TauCeti.BoundarylessModel.interiorDiffeomorph` preserve orientation between `o` and
  `o.interiorOrientation`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Manifold.Orientation

attribute [local instance] BoundarylessModel.interiorChartedSpace

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {ι : Type*} [Fintype ι]

/-- The orientation on the interior vector-space copy `BoundarylessModel I M` pulled back from
`o : Manifold.Orientation I M ι` along `(BoundarylessModel.interiorDiffeomorph I 1).symm`. -/
def interiorOrientation (o : Manifold.Orientation I M ι) :
    Manifold.Orientation 𝓘(ℝ, E) (BoundarylessModel I M) ι :=
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) 1
  o.pullback Φ.symm.contMDiff (fun _ ↦ Φ.symm.isInvertible_mfderiv one_ne_zero) o.card_eq

/-- Reversing `o` negates `o.interiorOrientation`. -/
@[simp]
theorem interiorOrientation_neg (o : Manifold.Orientation I M ι) :
    (-o).interiorOrientation = -o.interiorOrientation :=
  pullback_neg o _ _ _

/-- The inverse interior-model diffeomorphism `(BoundarylessModel.interiorDiffeomorph I k).symm`
preserves orientations from `o.interiorOrientation` to `o`. -/
theorem isOrientationPreservingAt_interiorDiffeomorph_symm
    (o : Manifold.Orientation I M ι) (k : ℕ∞ω) (z : BoundarylessModel I M) :
    IsOrientationPreservingAt o.interiorOrientation o
      (BoundarylessModel.interiorDiffeomorph I (M := M) k).symm z := by
  have hcoe : ⇑(BoundarylessModel.interiorDiffeomorph I (M := M) k).symm =
      ⇑(BoundarylessModel.interiorDiffeomorph I (M := M) 1).symm := by
    rw [BoundarylessModel.coe_interiorDiffeomorph_symm,
      BoundarylessModel.coe_interiorDiffeomorph_symm]
  rw [hcoe]
  exact isOrientationPreservingAt_pullback _ _ _ _ z

/-- The interior-model diffeomorphism `BoundarylessModel.interiorDiffeomorph I k` preserves
orientations from `o` to `o.interiorOrientation`. -/
theorem isOrientationPreservingAt_interiorDiffeomorph
    (o : Manifold.Orientation I M ι) (k : ℕ∞ω) (x : M) :
    IsOrientationPreservingAt o o.interiorOrientation
      (BoundarylessModel.interiorDiffeomorph I (M := M) k) x := by
  have hcoe : ⇑(BoundarylessModel.interiorDiffeomorph I (M := M) k) =
      ⇑(BoundarylessModel.interiorDiffeomorph I (M := M) 1) := by
    rw [BoundarylessModel.coe_interiorDiffeomorph, BoundarylessModel.coe_interiorDiffeomorph]
  rw [hcoe]
  exact (o.isOrientationPreservingAt_interiorDiffeomorph_symm 1
    (BoundarylessModel.interiorDiffeomorph I (M := M) 1 x)).diffeomorph_symm
    (e := (BoundarylessModel.interiorDiffeomorph I (M := M) 1).symm) one_ne_zero

end TauCeti.Manifold.Orientation
