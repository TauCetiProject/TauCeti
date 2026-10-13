/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Group
public import TauCeti.Topology.MappingSpace.Sphere
public import TauCeti.Topology.MappingSpace.SphereSuspension

/-!
# Maps from the two-sphere into a topological group

Evaluation at the north pole `Map(S², Q) → Q` has the constant spheres `Q → Map(S², Q)` as a
section, and its fibre over the basepoint is the based mapping space `Map_*(S², Q)`. For a
topological group `G` the fibration is trivial: `G × Map_*(S², G) ≃ₜ Map(S², G)`, and by the
identification of based maps out of the sphere with double loops,
`G × Ω²G ≃ₜ Map(S², G)`.

## Main declarations

* `TauCeti.constSphere2`: the section `Q → Map(S², Q)` of constant spheres, with
  `TauCeti.eval_north_constSphere2`.
* `TauCeti.sphere2GroupHomeomorph`: `G × Map_*(S², G) ≃ₜ Map(S², G)`.
* `TauCeti.sphere2GroupHomeomorphIteratedLoopSpace`: `G × Ω²G ≃ₜ Map(S², G)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

namespace TauCeti

section Const

variable {Q : Type*} [TopologicalSpace Q]

/-- The section of the evaluation at the north pole by constant spheres. -/
def constSphere2 : C(Q, C(Sphere2, Q)) :=
  ⟨ContinuousMap.const Sphere2, ContinuousMap.continuous_const'⟩

theorem constSphere2_apply (q : Q) (x : Sphere2) : constSphere2 q x = q := by
  rw [constSphere2]
  rfl

/-- Constant spheres are a section of evaluation at the north pole. -/
theorem eval_north_constSphere2 (q : Q) : constSphere2 q Sphere2.north = q :=
  constSphere2_apply q _

end Const

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **`Map(S², G)` for a topological group `G` is `G × Map_*(S², G)`.** -/
def sphere2GroupHomeomorph : G × BasedMap Sphere2 G Sphere2.north 1 ≃ₜ C(Sphere2, G) :=
  mappingSpaceGroupHomeomorph Sphere2.north

/-- **`Map(S², G) ≃ₜ G × Ω²G` for a topological group `G`**, through the identification of
based maps out of `S²` with the double loop space. -/
def sphere2GroupHomeomorphIteratedLoopSpace :
    G × (BasedTopologicalSpace.iteratedLoopSpace ⟨G, 1⟩ 2).carrier ≃ₜ C(Sphere2, G) :=
  (Homeomorph.prodCongr (Homeomorph.refl G)
    (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨G, 1⟩
      Sphere2.north).symm).trans (sphere2GroupHomeomorph G)

end TauCeti
