/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition

/-!
# Sobolev sections of higher order with boundary values in a subbundle

Let `M` be a `C¹` manifold modelled on the closed upper half-plane, for instance a compact surface
with boundary, let `V → M` be a real vector bundle with finite-dimensional model fibre `F`, let `A`
be a finite bundle atlas and let `2 < p ≤ ∞`. For a family `L x` of real subspaces of the fibres,
`TauCeti.BorderedSobolevSection.withBoundaryIn A hp L` is the closed subspace `W^{1,p}_L(V)` of the
elements of `W^{1,p}(V)` whose continuous representative takes its boundary values in `L`. This file
defines its counterpart `W^{1+k,p}_L(V)` at every order `1 + k ≥ 1`
(`TauCeti.BorderedSobolevSection.higherWithBoundaryIn`): the elements of `W^{1+k,p}(V)` whose image
in `W^{1,p}(V)`, forgetting `k` derivatives, lies in `W^{1,p}_L(V)`. Since every element of
`W^{1+k,p}(V)` lies in `W^{1,p}(V)`, it has a continuous representative, and the condition is again
that its values at the boundary points lie in `L`.

So `W^{1+k,p}_L(V)` is closed, hence a Banach space; it is `W^{1,p}_L(V)` at `k = 0`; forgetting a
derivative maps `W^{1+(k+1),p}_L(V)` into `W^{1+k,p}_L(V)`; and a `C^{1+k}` section lies in it
exactly when its boundary values lie in `L`.

The order is written `1 + k`, the order of the source of
`TauCeti.SectionChartData.lowerOrdersL volume p 1 k`, as in the other statements about lowering the
order of Sobolev sections.

## Main definitions

* `TauCeti.BorderedSobolevSection.higherWithBoundaryIn`: the subspace `W^{1+k,p}_L(V)` of elements
  of `W^{1+k,p}(V)` with boundary values in a family of subspaces.

## Main results

* `TauCeti.BorderedSobolevSection.mem_higherWithBoundaryIn_iff`: the boundary values of the
  continuous representative lie in `L`.
* `TauCeti.BorderedSobolevSection.higherWithBoundaryIn_zero`: at order one this is
  `TauCeti.BorderedSobolevSection.withBoundaryIn`.
* `TauCeti.BorderedSobolevSection.mem_higherWithBoundaryIn_succ_iff`: forgetting one derivative.
* `TauCeti.BorderedSobolevSection.isClosed_higherWithBoundaryIn`: `W^{1+k,p}_L(V)` is closed, so it
  is a Banach space (`TauCeti.BorderedSobolevSection.instCompleteSpaceHigherWithBoundaryIn`).
* `TauCeti.BorderedSobolevSection.ofContMDiffSection_mem_higherWithBoundaryIn_iff`,
  `TauCeti.BorderedSobolevSection.exists_mem_higherWithBoundaryIn_toSection_eq_iff`: a `C^{1+k}`
  section lies in `W^{1+k,p}_L(V)` exactly when its boundary values lie in `L`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1 (the spaces `W^{k,p}_F(Σ, E)`).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ENNReal

namespace TauCeti

namespace BorderedSobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (A) in
/-- **Sobolev sections of higher order with boundary values in a family of subspaces.** For
`2 < p ≤ ∞`, a family `L x` of real subspaces of the fibres of `V` and every `k`, the subspace
`W^{1+k,p}_L(V)` of `W^{1+k,p}(V)` of the elements whose image in `W^{1,p}(V)` lies in
`TauCeti.BorderedSobolevSection.withBoundaryIn A hp L`: their continuous representative takes its
value at every boundary point `x` of `M` in `L x`. In pseudoholomorphic curve theory `L` is a smooth
totally real subbundle `F ⊆ E|∂Σ`, and this is the space `W^{1+k,p}_F(Σ, E)`. -/
def higherWithBoundaryIn (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x)) (k : ℕ) :
    Submodule ℝ (BorderedSobolevSection A p (1 + k)) :=
  (withBoundaryIn A hp L).comap (A.halfSectionChartData.lowerOrdersL volume p 1 k).toLinearMap

theorem mem_higherWithBoundaryIn_iff_lowerOrdersL {hp : 2 < p} {L : ∀ x, Submodule ℝ (V x)}
    {k : ℕ} {w : BorderedSobolevSection A p (1 + k)} :
    w ∈ higherWithBoundaryIn A hp L k ↔
      A.halfSectionChartData.lowerOrdersL volume p 1 k w ∈ withBoundaryIn A hp L :=
  Iff.rfl

/-- An element of `W^{1+k,p}(V)` lies in `W^{1+k,p}_L(V)` exactly when the continuous
representative of its image in `W^{1,p}(V)` takes its boundary values in `L`. -/
@[simp]
theorem mem_higherWithBoundaryIn_iff {hp : 2 < p} {L : ∀ x, Submodule ℝ (V x)} {k : ℕ}
    {w : BorderedSobolevSection A p (1 + k)} :
    w ∈ higherWithBoundaryIn A hp L k ↔ ∀ x ∉ borderedInterior M,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) x ∈ L x := by
  rw [mem_higherWithBoundaryIn_iff_lowerOrdersL, mem_withBoundaryIn_iff]

/-- At order one, `W^{1+0,p}_L(V)` is `W^{1,p}_L(V)`; the order `1 + 0` is `1` by definition, so
both are subspaces of `W^{1,p}(V)`. -/
@[simp]
theorem higherWithBoundaryIn_zero (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x)) :
    higherWithBoundaryIn A hp L 0 = withBoundaryIn A hp L := by
  ext w
  rw [mem_higherWithBoundaryIn_iff_lowerOrdersL,
    SectionChartData.lowerOrdersL_zero]

/-- **Forgetting a derivative.** An element of `W^{1+(k+1),p}(V)` lies in `W^{1+(k+1),p}_L(V)`
exactly when its image in `W^{1+k,p}(V)` lies in `W^{1+k,p}_L(V)`. -/
theorem mem_higherWithBoundaryIn_succ_iff {hp : 2 < p} {L : ∀ x, Submodule ℝ (V x)} {k : ℕ}
    {w : BorderedSobolevSection A p (1 + (k + 1))} :
    w ∈ higherWithBoundaryIn A hp L (k + 1) ↔
      A.halfSectionChartData.lowerOrderL volume p (1 + k) w ∈ higherWithBoundaryIn A hp L k := by
  rw [mem_higherWithBoundaryIn_iff_lowerOrdersL, mem_higherWithBoundaryIn_iff_lowerOrdersL,
    SectionChartData.lowerOrdersL_succ, ContinuousLinearMap.comp_apply]

/-- **`W^{1+k,p}_L(V)` is closed** in `W^{1+k,p}(V)`, for every family `L` of real subspaces of the
fibres. -/
theorem isClosed_higherWithBoundaryIn (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x)) (k : ℕ) :
    IsClosed (higherWithBoundaryIn A hp L k : Set (BorderedSobolevSection A p (1 + k))) :=
  (isClosed_withBoundaryIn hp L).preimage
    (A.halfSectionChartData.lowerOrdersL volume p 1 k).continuous

/-- **Completeness.** `W^{1+k,p}_L(V)` is a Banach space. -/
instance instCompleteSpaceHigherWithBoundaryIn (hp : 2 < p) (L : ∀ x, Submodule ℝ (V x))
    (k : ℕ) : CompleteSpace (higherWithBoundaryIn A hp L k) :=
  (isClosed_higherWithBoundaryIn hp L k).completeSpace_coe

/-- The continuous representative of the image in `W^{1,p}(V)` of the element of `W^{1+k,p}(V)`
given by a `C^{1+k}` section is the section itself. -/
@[simp]
theorem toSection_lowerOrdersL_ofContMDiffSection {k : ℕ}
    [IsManifold closedUpperHalfPlaneModel (1 + k : ℕ) M]
    [ContMDiffVectorBundle (1 + k : ℕ) F V closedUpperHalfPlaneModel] (hp : 2 < p)
    (s : Cₛ^(1 + k : ℕ)⟮closedUpperHalfPlaneModel; F, V⟯) :
    toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k
      (ofContMDiffSection A p (1 + k) s)) = s :=
  (eq_toSection hp s.contMDiff.continuous fun i ↦ by
    rw [SectionChartData.chartValueL_lowerOrdersL]
    exact chartValueL_ofContMDiffSection_ae A p (1 + k) s i).symm

/-- A `C^{1+k}` section lies in `W^{1+k,p}_L(V)` exactly when its values at the boundary points lie
in `L`. -/
theorem ofContMDiffSection_mem_higherWithBoundaryIn_iff {k : ℕ}
    [IsManifold closedUpperHalfPlaneModel (1 + k : ℕ) M]
    [ContMDiffVectorBundle (1 + k : ℕ) F V closedUpperHalfPlaneModel] {hp : 2 < p}
    {L : ∀ x, Submodule ℝ (V x)} {s : Cₛ^(1 + k : ℕ)⟮closedUpperHalfPlaneModel; F, V⟯} :
    ofContMDiffSection A p (1 + k) s ∈ higherWithBoundaryIn A hp L k ↔
      ∀ x ∉ borderedInterior M, s x ∈ L x := by
  rw [mem_higherWithBoundaryIn_iff, toSection_lowerOrdersL_ofContMDiffSection]

/-- A `C^{1+k}` section is the continuous representative of the image in `W^{1,p}(V)` of an
element of `W^{1+k,p}_L(V)` exactly when its values at the boundary points lie in `L`. -/
theorem exists_mem_higherWithBoundaryIn_toSection_eq_iff {k : ℕ}
    [IsManifold closedUpperHalfPlaneModel (1 + k : ℕ) M]
    [ContMDiffVectorBundle (1 + k : ℕ) F V closedUpperHalfPlaneModel] {hp : 2 < p}
    {L : ∀ x, Submodule ℝ (V x)} {s : Cₛ^(1 + k : ℕ)⟮closedUpperHalfPlaneModel; F, V⟯} :
    (∃ w ∈ higherWithBoundaryIn A hp L k,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) = s) ↔
      ∀ x ∉ borderedInterior M, s x ∈ L x := by
  refine ⟨fun ⟨w, hw, hws⟩ ↦ ?_, fun h ↦ ⟨_, ofContMDiffSection_mem_higherWithBoundaryIn_iff.2 h,
    toSection_lowerOrdersL_ofContMDiffSection hp s⟩⟩
  rw [← hws]
  exact mem_higherWithBoundaryIn_iff.1 hw

end BorderedSobolevSection

end TauCeti
