/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Morrey
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Sobolev sections with boundary values in a subbundle

Let `M` be a `C¹` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a compact surface with boundary, let `V → M` be a real vector bundle with
finite-dimensional model fibre `F`, let `A` be a finite bundle atlas and let `2 < p ≤ ∞`. By
Morrey's embedding every element `w` of the Sobolev space `W^{1,p}(V)` of
`TauCeti.BorderedSobolevSection A p 1` has a continuous representative
`TauCeti.BorderedSobolevSection.toSection`, defined at every point of `M`, boundary points
included. This file proves that its values depend continuously on `w`, and uses this to define the
space `W^{1,p}_F(V)` of elements whose boundary values lie in a given family `F` of subspaces of
the fibres of `V` over the boundary.

Continuity is proved chart by chart with the closed graph theorem. The chart expression of the
continuous representative extends continuously to the closure of the interior `A.halfImage i` of
the chart image, a compact set, and restricting to it gives a linear map from `W^{1,p}(V)` to the
Banach space of continuous functions on that compact set. If `wₙ → w` and the restrictions converge
uniformly to `g`, then the chart data converge in `Lᵖ`, so a subsequence converges almost
everywhere, and `g` agrees with the chart expression of the representative of `w` almost
everywhere on `A.halfImage i`. Both are continuous, so they agree on its closure, which contains
the points of the chart image on the real axis.

The boundary of `M` is the complement of its manifold interior `TauCeti.borderedInterior M`. For a
family `L x` of real subspaces of the fibres, `TauCeti.BorderedSobolevSection.withBoundaryIn hp L`
consists of the elements whose continuous representative takes the value at every boundary point
`x` in `L x`. It is a closed subspace: the intersection of the preimages of the finite-dimensional,
hence closed, subspaces `L x` under the continuous evaluation maps. Neither a totally real
condition nor smoothness of `L` is needed for this; the Sobolev spaces `W^{1,p}_F(Σ, E)` of
pseudoholomorphic curve theory take for `L` a smooth totally real subbundle `F ⊆ E|∂Σ`.

## Main definitions

* `TauCeti.BorderedSobolevSection.halfCoordL`: the chart expression of the continuous
  representative in chart `i`, as a continuous linear map to continuous functions on the closure
  of the chart image.
* `TauCeti.BorderedSobolevSection.evalL`: evaluation of the continuous representative at a point,
  as a continuous linear map.
* `TauCeti.BorderedSobolevSection.withBoundaryIn`: the subspace `W^{1,p}_F(V)` of elements with
  boundary values in a family of subspaces.

## Main results

* `TauCeti.BorderedSobolevSection.exists_norm_halfCoord_toSection_le`: the chart expressions of
  the continuous representative are bounded by a constant times the Sobolev norm, up to the real
  axis.
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

section Atlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- A point of the closure of the interior of the image of chart `i` in `ℂ` comes from a point of
the closure of the chart domain. -/
private theorem exists_mem_closure_dom_of_mem_closure_halfImage {i : Fin A.n} {z : ℂ}
    (hz : z ∈ closure (A.halfImage i : Set ℂ)) :
    ∃ x ∈ closure (A.dom i), closedUpperHalfPlaneModel.symm z = A.chart i x := by
  obtain ⟨x, hx, rfl⟩ := closure_minimal (A.halfImage_subset_extChartAt_image_closure_dom i)
    (A.isCompact_extChartAt_image_closure_dom i).isClosed hz
  exact ⟨x, hx, by rw [extChartAt_coe, Function.comp_apply, ModelWithCorners.left_inv]⟩

/-- On the closure of the interior of the image of chart `i` in `ℂ`, the chart expression of a
section is the image of its value under the trivialization of chart `i`, a linear map. -/
private theorem halfCoord_eq_continuousLinearMapAt [NormedSpace ℝ F] [∀ x, AddCommMonoid (V x)]
    [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] {i : Fin A.n} {z : ℂ}
    (hz : z ∈ closure (A.halfImage i : Set ℂ)) (s : ∀ x, V x) :
    A.halfCoord i s z = (A.triv i).continuousLinearMapAt ℝ
      ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))
        (s ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) := by
  obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
  have hb : (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ (A.triv i).baseSet := by
    rw [hxz, (A.chart i).left_inv (A.closure_dom_subset_source i hx)]
    exact A.closure_dom_subset_baseSet i hx
  rw [halfCoord_def, coord_def, Trivialization.continuousLinearMapAt_apply_of_mem ℝ (A.triv i) hb]

/-- The chart expression in chart `i` of a continuous section is continuous on the closure of the
interior of the image of the chart in `ℂ`, which contains the points of the image on the real
axis and lies in the image of the closure of the chart domain. -/
theorem continuousOn_halfCoord_closure_halfImage {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) (i : Fin A.n) :
    ContinuousOn (A.halfCoord i s) (closure (A.halfImage i : Set ℂ)) := by
  have hmaps : MapsTo closedUpperHalfPlaneModel.symm (closure (A.halfImage i : Set ℂ))
      (A.chart i).target := fun z hz ↦ by
    obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
    rw [hxz]
    exact (A.chart i).map_source (A.closure_dom_subset_source i hx)
  have hpt : ContinuousOn (fun z ↦ (A.chart i).symm (closedUpperHalfPlaneModel.symm z))
      (closure (A.halfImage i : Set ℂ)) :=
    (A.chart i).continuousOn_symm.comp closedUpperHalfPlaneModel.continuous_symm.continuousOn
      hmaps
  refine (continuous_snd.comp_continuousOn ((A.triv i).continuousOn.comp
    (hs.comp_continuousOn hpt) fun z hz ↦ ?_)).congr fun z _ ↦ by
      rw [A.halfCoord_def i s z, coord_def]; rfl
  obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
  refine (A.triv i).mem_source.2 ?_
  change (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ (A.triv i).baseSet
  rw [hxz, (A.chart i).left_inv (A.closure_dom_subset_source i hx)]
  exact A.closure_dom_subset_baseSet i hx

end FiniteBundleAtlas

end Atlas

section Evaluation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BorderedSobolevSection

open FiniteBundleAtlas

/-- The chart expression in chart `i` of the continuous representative, restricted to the closure
of the interior of the chart image, as a linear map to continuous functions. -/
private def halfCoordₗ (hp : 2 < p) (i : Fin A.n) :
    BorderedSobolevSection A p 1 →ₗ[ℝ] C(closure (A.halfImage i : Set ℂ), F) where
  toFun w := ⟨fun z ↦ A.halfCoord i (toSection hp w) z,
    continuousOn_iff_continuous_domRestrict.1
      (A.continuousOn_halfCoord_closure_halfImage (continuous_toSection hp w) i)⟩
  map_add' w v := by
    ext z
    change A.halfCoord i (toSection hp (w + v)) z =
      A.halfCoord i (toSection hp w) z + A.halfCoord i (toSection hp v) z
    simp only [A.halfCoord_eq_continuousLinearMapAt z.2, toSection_add, Pi.add_apply, map_add]
  map_smul' c w := by
    ext z
    change A.halfCoord i (toSection hp (c • w)) z = c • A.halfCoord i (toSection hp w) z
    simp only [A.halfCoord_eq_continuousLinearMapAt z.2, toSection_smul, Pi.smul_apply, map_smul]

private theorem halfCoordₗ_apply (hp : 2 < p) (i : Fin A.n) (w : BorderedSobolevSection A p 1)
    (z : closure (A.halfImage i : Set ℂ)) :
    halfCoordₗ hp i w z = A.halfCoord i (toSection hp w) z :=
  (rfl)

/-- If `wₙ → w` in `W^{1,p}(V)` and the chart expressions in chart `i` of the continuous
representatives of `wₙ` converge to `y` at almost every point of the interior of the chart image,
then `y` is the chart expression of the continuous representative of `w` there. -/
private theorem ae_eq_halfCoord_toSection_of_tendsto (hp : 2 < p) (i : Fin A.n)
    {u : ℕ → BorderedSobolevSection A p 1} {w : BorderedSobolevSection A p 1} {y : ℂ → F}
    (hu : Tendsto u atTop (𝓝 w))
    (hy : ∀ z ∈ A.halfImage i,
      Tendsto (fun n ↦ A.halfCoord i (toSection hp (u n)) z) atTop (𝓝 (y z))) :
    y =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i (toSection hp w) := by
  have hL := (((A.halfSectionChartData.chartValueL volume p 1 i).continuous.comp
    continuous_subtype_val).tendsto w).comp hu
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.2 fun n ↦ chartValueL_ae_eq_halfCoord_toSection hp (u n) i,
    chartValueL_ae_eq_halfCoord_toSection hp w i,
    ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hn hw hzU
  simp only [Function.comp_apply, hn, hw] at hz
  exact tendsto_nhds_unique ((hy z hzU).comp hns.tendsto_atTop) hz

/-- The restriction of the chart expression of the continuous representative is continuous, by
the closed graph theorem. -/
private theorem continuous_halfCoordₗ (hp : 2 < p) (i : Fin A.n) :
    Continuous (halfCoordₗ (A := A) hp i) := by
  classical
  have := isCompact_iff_compactSpace.1 (A.isCompact_closure_halfImage i)
  refine (halfCoordₗ hp i).continuous_of_seq_closed_graph fun u w g hu hg ↦ ?_
  let G : ℂ → F := fun z ↦ if h : z ∈ closure (A.halfImage i : Set ℂ) then g ⟨z, h⟩ else 0
  have hGK : (closure (A.halfImage i : Set ℂ)).domRestrict G = g := by
    ext z
    simp only [domRestrict_apply, G, dite_eq_left z.2]
  have hG : ContinuousOn G (closure (A.halfImage i : Set ℂ)) :=
    continuousOn_iff_continuous_domRestrict.2 (hGK ▸ g.continuous)
  have hcont := A.continuousOn_halfCoord_closure_halfImage (continuous_toSection hp w) i
  have hae : G =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i (toSection hp w) := by
    refine ae_eq_halfCoord_toSection_of_tendsto hp i hu fun z hz ↦ ?_
    have hzK : z ∈ closure (A.halfImage i : Set ℂ) := subset_closure hz
    have h := ((continuous_eval_const (⟨z, hzK⟩ : closure (A.halfImage i : Set ℂ))).tendsto
      g).comp hg
    simp only [G, dite_eq_left hzK]
    exact h
  have heq := (Measure.eqOn_open_of_ae_eq hae (A.halfImage i).isOpen (hG.mono subset_closure)
    (hcont.mono subset_closure)).of_subset_closure hG hcont subset_closure subset_rfl
  ext z
  rw [halfCoordₗ_apply, ← heq z.2, ← hGK, domRestrict_apply]

/-- The chart expression in chart `i` of the continuous representative of an element of
`W^{1,p}(V)`, for `2 < p ≤ ∞`, on the closure of the interior of the chart image, as a continuous
linear map to the continuous functions on this compact set. The closure contains the points of the
chart image on the real axis. -/
def halfCoordL (hp : 2 < p) (i : Fin A.n) :
    BorderedSobolevSection A p 1 →L[ℝ] C(closure (A.halfImage i : Set ℂ), F) where
  toLinearMap := halfCoordₗ hp i
  cont := continuous_halfCoordₗ hp i

@[simp]
theorem halfCoordL_apply (hp : 2 < p) (i : Fin A.n) (w : BorderedSobolevSection A p 1)
    (z : closure (A.halfImage i : Set ℂ)) :
    halfCoordL hp i w z = A.halfCoord i (toSection hp w) z :=
  (rfl)

/-- **Morrey's inequality for Sobolev sections over surfaces with boundary.** For `2 < p ≤ ∞`, the
chart expression in chart `i` of the continuous representative of an element `w` of `W^{1,p}(V)`
is bounded by a constant times the norm of `w`, on the closure of the interior of the chart image,
which contains the points of the chart image on the real axis. -/
theorem exists_norm_halfCoord_toSection_le (hp : 2 < p) (i : Fin A.n) :
    ∃ C : ℝ≥0, ∀ (w : BorderedSobolevSection A p 1), ∀ z ∈ closure (A.halfImage i : Set ℂ),
      ‖A.halfCoord i (toSection hp w) z‖ ≤ C * ‖w‖ := by
  have := isCompact_iff_compactSpace.1 (A.isCompact_closure_halfImage i)
  refine ⟨‖halfCoordL (A := A) hp i‖₊, fun w z hz ↦ ?_⟩
  have h := ((halfCoordL hp i w).norm_coe_le_norm ⟨z, hz⟩).trans ((halfCoordL hp i).le_opNorm w)
  rwa [halfCoordL_apply] at h

/-- The value of the continuous representative at a point depends continuously on the element of
`W^{1,p}(V)`. -/
theorem continuous_toSection_apply (hp : 2 < p) (x : M) :
    Continuous fun w : BorderedSobolevSection A p 1 ↦ toSection hp w x := by
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hb := A.dom_subset_baseSet i hx
  have hz : (A.chart i x : ℂ) ∈ closure (A.halfImage i : Set ℂ) :=
    A.halfClosedImage_subset_closure_halfImage i
      (A.coe_mem_halfClosedImage.2 (A.mem_image.2 ⟨x, hx, rfl⟩))
  set e := (A.triv i).continuousLinearEquivAt ℝ x hb
  have h (w : BorderedSobolevSection A p 1) :
      toSection hp w x = e.symm (halfCoordL hp i w ⟨_, hz⟩) := by
    rw [halfCoordL_apply, A.halfCoord_coe_chart _ hx]
    exact (e.symm_apply_apply _).symm
  simp only [h]
  exact e.symm.continuous.comp ((continuous_eval_const _).comp
    (halfCoordL hp i).continuous)

/-- Evaluation of the continuous representative at a point `x` of `M`, boundary points included,
as a continuous linear map from `W^{1,p}(V)`, for `2 < p ≤ ∞`, to the fibre of `V` at `x`. -/
def evalL (hp : 2 < p) (x : M) : BorderedSobolevSection A p 1 →L[ℝ] V x where
  toFun w := toSection hp w x
  map_add' w v := by rw [toSection_add, Pi.add_apply]
  map_smul' c w := by rw [toSection_smul, Pi.smul_apply, RingHom.id_apply]
  cont := continuous_toSection_apply hp x

@[simp]
theorem evalL_apply (hp : 2 < p) (x : M) (w : BorderedSobolevSection A p 1) :
    evalL hp x w = toSection hp w x :=
  (rfl)

end BorderedSobolevSection

end Evaluation

section BoundaryCondition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real subspace of a fibre of a vector bundle with finite-dimensional model fibre is closed. -/
private theorem isClosed_submodule_fiber {M : Type*} [TopologicalSpace M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*}
    [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V] (x : M)
    (L : Submodule ℝ (V x)) :
    IsClosed (L : Set (V x)) := by
  let e := (trivializationAt F V x).continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt F V x)
  rw [← e.toHomeomorph.isClosed_image]
  exact (L.map (e : V x →ₗ[ℝ] F)).isClosed_of_finiteDimensional

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
    (isClosed_submodule_fiber (F := F) x (L x)).preimage (evalL hp x).cont

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
