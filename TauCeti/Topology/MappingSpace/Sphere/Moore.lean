/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Sphere.Group
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Maps from the two-sphere into a group, with Moore loops

For a topological group `G`, the space `Map(S², G)` is homeomorphic to `G × Ω²G`, with `Ω²G` the
fixed-interval double loop space (`TauCeti.sphere2GroupHomeomorphIteratedLoopSpace`). Replacing
the outer loop space of `Ω²G = Ω(ΩG)` by the space of Moore loops in the fixed-interval loop space
`ΩG`, which is homotopy equivalent to it (`TauCeti.MooreLoopSpace.homotopyEquivPath`), gives a
homotopy equivalence of `Map(S², G)` with `G × Ω^M(ΩG)`, in which the group coordinate is the
value at the north pole.

## Main declarations

* `TauCeti.sphere2GroupHomotopyEquivMoore`: `G × Ω^M(ΩG) ≃ₕ Map(S², G)`.
* `TauCeti.sphere2GroupHomotopyEquivMoore_apply_north`: the value at the north pole of the image
  of `(g, γ)` is `g`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

namespace TauCeti

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **`Map(S², G)` is homotopy equivalent to `G × Ω^M(ΩG)`**, with `Ω^M(ΩG)` the Moore loops in
the fixed-interval loop space of `G`, based at the constant loop. -/
-- `Ω² G = (iteratedLoopSpace ⟨G, 1⟩ 2).carrier` is `Path (refl 1) (refl 1)` by the definition of
-- the iterated loop space, so the Moore comparison for the loops at `refl 1` in `ΩG` lands in it.
def sphere2GroupHomotopyEquivMoore :
    ContinuousMap.HomotopyEquiv (G × MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) C(Sphere2, G) :=
  (ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl G)
    (MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)))).trans
      (sphere2GroupHomeomorphIteratedLoopSpace G).toHomotopyEquiv

variable {G}

/-- The forward map of `sphere2GroupHomotopyEquivMoore` reparametrizes the Moore loop to the unit
interval and applies the decomposition `G × Ω²G ≃ₜ Map(S², G)`. -/
theorem sphere2GroupHomotopyEquivMoore_apply (g : G)
    (γ : MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) :
    sphere2GroupHomotopyEquivMoore G (g, γ) =
      sphere2GroupHomeomorphIteratedLoopSpace G
        (g, MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)) γ) := by
  rw [sphere2GroupHomotopyEquivMoore]
  rfl

/-- The value at the north pole of the image of `(g, γ)` is `g`. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_apply_north (g : G)
    (γ : MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) :
    sphere2GroupHomotopyEquivMoore G (g, γ) Sphere2.north = g := by
  have h := sphere2GroupHomeomorphIteratedLoopSpace_symm_fst
    (sphere2GroupHomeomorphIteratedLoopSpace G
      (g, MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)) γ))
  rw [Homeomorph.symm_apply_apply] at h
  exact h.symm

end TauCeti
