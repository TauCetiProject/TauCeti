/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Morrey
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Sobolev sections with boundary values in a subbundle

Let `M` be a `C¹` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a compact surface with boundary, let `V → M` be a real vector bundle with
finite-dimensional model fibre `F`, let `A` be a finite bundle atlas and let `2 < p ≤ ∞`. By
Morrey's embedding every element `w` of the Sobolev space `W^{1,p}(V)` of
`TauCeti.BorderedSobolevSection A p 1` has a continuous representative
`TauCeti.BorderedSobolevSection.toSection`, defined at every point of `M`, boundary points
included, and its value at a point `x` is a continuous linear function of `w`
(`TauCeti.BorderedSobolevSection.evalL`). This file uses this to define the space `W^{1,p}_F(V)`
of elements whose boundary values lie in a given family `F` of subspaces of the fibres of `V` over
the boundary.

The boundary of `M` is the complement of its manifold interior `TauCeti.borderedInterior M`. For a
family `L x` of real subspaces of the fibres, `TauCeti.BorderedSobolevSection.withBoundaryIn hp L`
consists of the elements whose continuous representative takes the value at every boundary point
`x` in `L x`. It is a closed subspace: the intersection of the preimages of the finite-dimensional,
hence closed (`VectorBundle.isClosed_submodule`), subspaces `L x` under the continuous evaluation
maps. Neither a totally real
condition nor smoothness of `L` is needed for this; the Sobolev spaces `W^{1,p}_F(Σ, E)` of
pseudoholomorphic curve theory take for `L` a smooth totally real subbundle `F ⊆ E|∂Σ`.

## Main definitions

* `TauCeti.BorderedSobolevSection.withBoundaryIn`: the subspace `W^{1,p}_F(V)` of elements with
  boundary values in a family of subspaces.

## Main results

* `TauCeti.BorderedSobolevSection.isClosed_withBoundaryIn`: `W^{1,p}_F(V)` is closed, so it is a
  Banach space (`TauCeti.BorderedSobolevSection.instCompleteSpaceWithBoundaryIn`).
* `TauCeti.BorderedSobolevSection.exists_mem_withBoundaryIn_toSection_eq_iff`: a `C¹` section lies
  in `W^{1,p}_F(V)` exactly when its boundary values lie in `F`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1 (the spaces `W^{k,p}_F(Σ, E)`).
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal Topology

namespace TauCeti

section BoundaryCondition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BorderedSobolevSection

variable (A) in
/-- **Sobolev sections with boundary values in a family of subspaces.** For `2 < p ≤ ∞` and a family
`L x` of real subspaces of the fibres of `V`, the subspace `W^{1,p}_L(V)` of `W^{1,p}(V)` of the
elements whose continuous representative takes its value at every boundary point `x` of `M`, a
point outside the manifold interior `TauCeti.borderedInterior M`, in `L x`. Only the subspaces at
boundary points matter. In pseudoholomorphic curve theory `L` is a smooth totally real subbundle
`F ⊆ E|∂Σ`, and this is the space `W^{1,p}_F(Σ, E)`. -/
def withBoundaryIn (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x)) :
    Submodule ℝ (BorderedSobolevSection A p 1) :=
  ⨅ x ∈ (borderedInterior M : Set M)ᶜ, (L x).comap (evalL (A := A) hp x).toLinearMap

@[simp]
theorem mem_withBoundaryIn_iff {hp : 2 < p} {L : ∀ x, Submodule ℝ (V x)}
    {w : BorderedSobolevSection A p 1} :
    w ∈ withBoundaryIn A hp L ↔ ∀ x ∉ borderedInterior M, toSection hp w x ∈ L x := by
  simp [withBoundaryIn, Submodule.mem_iInf]

/-- **`W^{1,p}_L(V)` is closed** in `W^{1,p}(V)`, for every family `L` of real subspaces of the
fibres. -/
theorem isClosed_withBoundaryIn (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x)) :
    IsClosed (withBoundaryIn A hp L : Set (BorderedSobolevSection A p 1)) := by
  have h : (withBoundaryIn A hp L : Set (BorderedSobolevSection A p 1)) =
      ⋂ x ∈ (borderedInterior M : Set M)ᶜ, evalL hp x ⁻¹' (L x : Set (V x)) := by
    ext w
    simp [mem_withBoundaryIn_iff]
  rw [h]
  exact isClosed_biInter fun x _ ↦
    (VectorBundle.isClosed_submodule ℝ F V x (L x)).preimage (evalL hp x).cont

/-- **Completeness.** `W^{1,p}_L(V)` is a Banach space. -/
instance instCompleteSpaceWithBoundaryIn (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x)) :
    CompleteSpace (withBoundaryIn A hp L) :=
  (isClosed_withBoundaryIn hp L).completeSpace_coe

/-- A `C¹` section lies in `W^{1,p}_L(V)` exactly when its values at the boundary points lie in
`L`. The smoothness instances are stated at `(1 : ℕ)`, as in
`TauCeti.BorderedSobolevSection.ofContMDiffSection`. -/
theorem ofContMDiffSection_mem_withBoundaryIn_iff [IsManifold closedUpperHalfPlaneModel (1 : ℕ) M]
    [ContMDiffVectorBundle (1 : ℕ) F V closedUpperHalfPlaneModel] {hp : 2 < p}
    {L : ∀ x, Submodule ℝ (V x)} {s : Cₛ^(1 : ℕ)⟮closedUpperHalfPlaneModel; F, V⟯} :
    ofContMDiffSection A p 1 s ∈ withBoundaryIn A hp L ↔ ∀ x ∉ borderedInterior M, s x ∈ L x := by
  rw [mem_withBoundaryIn_iff, toSection_ofContMDiffSection]

/-- A `C¹` section is the continuous representative of an element of `W^{1,p}_L(V)` exactly when its
values at the boundary points lie in `L`. -/
theorem exists_mem_withBoundaryIn_toSection_eq_iff
    [IsManifold closedUpperHalfPlaneModel (1 : ℕ) M]
    [ContMDiffVectorBundle (1 : ℕ) F V closedUpperHalfPlaneModel] {hp : 2 < p}
    {L : ∀ x, Submodule ℝ (V x)} {s : Cₛ^(1 : ℕ)⟮closedUpperHalfPlaneModel; F, V⟯} :
    (∃ w ∈ withBoundaryIn A hp L, toSection hp w = s) ↔ ∀ x ∉ borderedInterior M, s x ∈ L x := by
  refine ⟨fun ⟨w, hw, hws⟩ ↦ ?_, fun h ↦ ⟨_, ofContMDiffSection_mem_withBoundaryIn_iff.2 h,
    toSection_ofContMDiffSection hp s⟩⟩
  rw [← hws]
  exact mem_withBoundaryIn_iff.1 hw

end BorderedSobolevSection

end BoundaryCondition

end TauCeti
