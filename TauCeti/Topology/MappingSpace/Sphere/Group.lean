/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Group
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.Sphere.Suspension

/-!
# Maps from the two-sphere into a topological group

Evaluation at the north pole `Map(S², Q) → Q` has the constant spheres `ContinuousMap.const` as a
section, and its fibre over the basepoint is the based mapping space `Map_*(S², Q)`. For a
topological group `G` the fibration is trivial, `G × Map_*(S², G) ≃ₜ Map(S², G)`
(`TauCeti.mappingSpaceGroupHomeomorph`), and by the identification of based maps out of the sphere
with double loops, `G × Ω²G ≃ₜ Map(S², G)`.

## Main declarations

* `TauCeti.sphere2GroupHomeomorphIteratedLoopSpace`: `G × Ω²G ≃ₜ Map(S², G)`, sending `(g, γ)`
  to the product of the constant sphere `g` and the based sphere map of `γ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

namespace TauCeti

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **`Map(S², G) ≃ₜ G × Ω²G` for a topological group `G`**, through the identification of
based maps out of `S²` with the double loop space. -/
def sphere2GroupHomeomorphIteratedLoopSpace :
    G × (BasedTopologicalSpace.iteratedLoopSpace ⟨G, 1⟩ 2).carrier ≃ₜ C(Sphere2, G) :=
  (Homeomorph.prodCongr (Homeomorph.refl G)
    (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨G, 1⟩
      Sphere2.north).symm).trans (mappingSpaceGroupHomeomorph Sphere2.north)

variable {G}

theorem sphere2GroupHomeomorphIteratedLoopSpace_apply (g : G)
    (γ : (BasedTopologicalSpace.iteratedLoopSpace ⟨G, 1⟩ 2).carrier) :
    sphere2GroupHomeomorphIteratedLoopSpace G (g, γ) =
      ContinuousMap.const Sphere2 g *
        ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨G, 1⟩
          Sphere2.north).symm γ).1 := by
  rw [sphere2GroupHomeomorphIteratedLoopSpace, Homeomorph.trans_apply,
    mappingSpaceGroupHomeomorph_apply]
  rfl

/-- The group coordinate of the decomposition of a sphere map is its value at the north pole. -/
theorem sphere2GroupHomeomorphIteratedLoopSpace_symm_fst (f : C(Sphere2, G)) :
    ((sphere2GroupHomeomorphIteratedLoopSpace G).symm f).1 = f Sphere2.north := by
  rw [sphere2GroupHomeomorphIteratedLoopSpace, Homeomorph.symm_trans_apply]
  exact mappingSpaceGroupHomeomorph_symm_fst Sphere2.north f

end TauCeti
