/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Sphere.Group
public import TauCeti.Topology.Sphere.Suspension
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Maps from the two-sphere into a group, with Moore loops

For a topological group `G`, the space `Map(S², G)` is homeomorphic to `G × Ω²G`, with `Ω²G` the
fixed-interval double loop space (`TauCeti.sphereGroupHomeomorphIteratedLoopSpace`). Replacing
the outer loop space of `Ω²G = Ω(ΩG)` by the space of Moore loops in the fixed-interval loop space
`ΩG`, which is homotopy equivalent to it (`TauCeti.MooreLoopSpace.homotopyEquivPath`), gives a
homotopy equivalence of `Map(S², G)` with `G × Ω^M(ΩG)`, in which the group coordinate is the
value at the north pole.

## Main declarations

* `TauCeti.sphere2GroupHomotopyEquivMoore`: `G × Ω^M(ΩG) ≃ₕ Map(S², G)`.
* `TauCeti.sphere2GroupHomotopyEquivMoore_apply_north` and
  `TauCeti.sphere2GroupHomotopyEquivMoore_symm_apply_fst`: the value at the north pole of the image
  of `(g, γ)` is `g`, and the group coordinate of the image under the homotopy inverse is the value
  at the north pole.
* `TauCeti.sphere2GroupHomotopyEquivMoore_symm_apply_snd`: the Moore-loop coordinate of the image
  under the homotopy inverse is the fixed-interval double loop, as a length-one Moore loop.

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
      (sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north).toHomotopyEquiv

variable {G}

/-- The forward map of `sphere2GroupHomotopyEquivMoore` reparametrizes the Moore loop to the unit
interval and applies the decomposition `G × Ω²G ≃ₜ Map(S², G)`. -/
theorem sphere2GroupHomotopyEquivMoore_apply (g : G)
    (γ : MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) :
    sphere2GroupHomotopyEquivMoore G (g, γ) =
      sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north
        (g, MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)) γ) := by
  rw [sphere2GroupHomotopyEquivMoore]
  rfl

/-- The value at the north pole of the image of `(g, γ)` is `g`. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_apply_north (g : G)
    (γ : MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) :
    sphere2GroupHomotopyEquivMoore G (g, γ) Sphere2.north = g := by
  have h := sphereGroupHomeomorphIteratedLoopSpace_symm_fst (s₀ := Sphere2.north)
    (sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north
      (g, MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)) γ))
  rw [Homeomorph.symm_apply_apply] at h
  exact h.symm

/-- The group coordinate of the image under the homotopy inverse of `sphere2GroupHomotopyEquivMoore`
is the value at the north pole. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_symm_apply_fst (f : C(Sphere2, G)) :
    ((sphere2GroupHomotopyEquivMoore G).symm f).1 = f Sphere2.north := by
  rw [sphere2GroupHomotopyEquivMoore]
  exact sphereGroupHomeomorphIteratedLoopSpace_symm_fst (s₀ := Sphere2.north) f

/-- The Moore-loop coordinate of the image under the homotopy inverse of
`sphere2GroupHomotopyEquivMoore` is the corresponding fixed-interval double loop, reparametrized to
a Moore loop of length one: the homotopy inverse of `MooreLoopSpace.homotopyEquivPath` is
`Path.toMooreLoop`. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_symm_apply_snd (f : C(Sphere2, G)) :
    ((sphere2GroupHomotopyEquivMoore G).symm f).2 =
      Path.toMooreLoop ((sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north).symm f).2 := by
  rw [sphere2GroupHomotopyEquivMoore]
  exact MooreLoopSpace.homotopyEquivPath_symm_apply (X := Path (1 : G) 1) (x := Path.refl 1)
    ((sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north).symm f).2

end TauCeti
