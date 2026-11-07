/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import TauCeti.AlgebraicTopology.SimplicialObject.TopCat
public import TauCeti.Topology.CategoryTheory.Etale
public import TauCeti.Topology.CategoryTheory.Nerve
public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# Clopen latching loci of étale nerves

An `n + 1`-simplex of the nerve of a category, a string `x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ₊₁` of composable
arrows, lies in the image of the `i`-th degeneracy exactly when its `i`-th arrow `xᵢ ⟶ xᵢ₊₁` is
an identity arrow (`CategoryTheory.nerve.mem_range_σ_iff`, in `Set.range` form
`CategoryTheory.nerve.range_σ_eq_preimage`, both in
`TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic`).
The degenerate simplices, the union of these images, form the latching object of the nerve in
each degree.

Now let the total arrows of the category carry a topology and give the strings of composable
arrows the topology of `TauCeti.topologicalNerve`. Each image of a degeneracy is then the
preimage of the set of identity arrows along a continuous map, so it is open or closed when the
identity arrows are, and each degeneracy is an embedding, as in any simplicial space
(`CategoryTheory.SimplicialObject.isEmbedding_σ`, in
`TauCeti.AlgebraicTopology.SimplicialObject.TopCat`). The degenerate locus is a finite union of
such images, so it is open or closed too (`TauCeti.isOpen_nerve_degenerate`,
`TauCeti.isClosed_nerve_degenerate`).

For a topological category whose source is a local homeomorphism (an étale category, such as
a proper étale groupoid presenting an orbifold), with continuous units and Hausdorff arrow
space, the identity arrows form a clopen set: they are the image of a continuous section of the
source, hence open (`TauCeti.isOpen_range_unit`), and the fixed points of the continuous map
`a ↦ 𝟙 a.left`, hence closed (`TauCeti.isClosed_range_unit`); these facts about the arrow space
are in `TauCeti.Topology.CategoryTheory.Etale`.
So each degeneracy is an open and closed embedding
(`TauCeti.isClosedEmbedding_topologicalNerve_σ`, `TauCeti.isOpenEmbedding_topologicalNerve_σ`),
the degenerate locus in each degree is clopen
(`TauCeti.isClopen_nerve_degenerate`), and its inclusion has the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_nerve_degenerate`). Its complement, the nondegenerate
locus, is clopen too (`TauCeti.isClopen_nerve_nonDegenerate`). These facts about the latching
inclusions are the input for treating the topological nerve of an étale groupoid as a proper
simplicial space, whose thin realization is built from its skeleta by closed attachments.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public section

open CategoryTheory Topology

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C]

variable [TopologicalSpace (Quiver.Total C)]

/-- If the identity arrows form a closed set, each degeneracy of the topological nerve is a
closed embedding. -/
theorem isClosedEmbedding_topologicalNerve_σ
    (h : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) {n : ℕ}
    (i : Fin (n + 1)) :
    IsClosedEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  ⟨SimplicialObject.isEmbedding_σ (topologicalNerve C) i, nerve.range_σ_eq_preimage (C := C) i ▸
    h.preimage (ComposableArrows.continuous_totalArrow _ _ _)⟩

/-- If the identity arrows form an open set, each degeneracy of the topological nerve is an open
embedding. -/
theorem isOpenEmbedding_topologicalNerve_σ
    (h : IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) {n : ℕ}
    (i : Fin (n + 1)) :
    IsOpenEmbedding (SimplicialObject.σ (topologicalNerve C) i) :=
  ⟨SimplicialObject.isEmbedding_σ (topologicalNerve C) i, nerve.range_σ_eq_preimage (C := C) i ▸
    h.preimage (ComposableArrows.continuous_totalArrow _ _ _)⟩

/-- If the identity arrows form a closed set, the degenerate simplices of the topological nerve
form a closed set in each degree. -/
theorem isClosed_nerve_degenerate
    (h : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) (n : ℕ) :
    IsClosed (X := ComposableArrows C n) ((nerve C).degenerate n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (nerve C) ▸ isClosed_empty
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ]
    exact isClosed_iUnion_of_finite fun i ↦
      (isClosedEmbedding_topologicalNerve_σ h i).isClosed_range

/-- If the identity arrows form an open set, the degenerate simplices of the topological nerve
form an open set in each degree. -/
theorem isOpen_nerve_degenerate
    (h : IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) (n : ℕ) :
    IsOpen (X := ComposableArrows C n) ((nerve C).degenerate n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (nerve C) ▸ isOpen_empty
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ]
    exact isOpen_iUnion fun i ↦ (isOpenEmbedding_topologicalNerve_σ h i).isOpen_range

variable [TopologicalSpace C] (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
include hu

variable [T2Space (Quiver.Total C)]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
include hs

/-- **The latching loci of an étale nerve are clopen.** In a topological category with
continuous units, locally homeomorphic source and Hausdorff arrow space, the degenerate
simplices of the topological nerve form a clopen set in each degree. -/
theorem isClopen_nerve_degenerate (n : ℕ) :
    IsClopen (X := ComposableArrows C n) ((nerve C).degenerate n) :=
  ⟨isClosed_nerve_degenerate (isClopen_range_unit hu hs).isClosed n,
    isOpen_nerve_degenerate (isClopen_range_unit hu hs).isOpen n⟩

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the nondegenerate simplices of the topological nerve form a clopen set in each
degree. -/
theorem isClopen_nerve_nonDegenerate (n : ℕ) :
    IsClopen (X := ComposableArrows C n) ((nerve C).nonDegenerate n) :=
  (isClopen_nerve_degenerate hu hs n).compl

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the inclusion of the degenerate simplices of the topological nerve has the homotopy
extension property in each degree. -/
theorem hasHomotopyExtensionProperty_nerve_degenerate (n : ℕ) :
    HasHomotopyExtensionProperty (X := ComposableArrows C n) ((nerve C).degenerate n) :=
  (isClopen_nerve_degenerate hu hs n).hasHomotopyExtensionProperty

end TauCeti
