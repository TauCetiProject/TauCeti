/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.ModelTransport.Interior
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# The interior of a manifold with corners as a manifold without boundary

Let `M` be a `C¹` manifold modelled on a model with corners `I : H → E`, possibly with boundary
and corners. Its interior `I.interior M` is open (`ModelWithCorners.isOpen_interior`), and
`TauCeti.ManifoldInterior I M` is a copy of this open subset whose charts take values in the
model vector space `E` itself: a chart `c` of `M` is replaced by `I ∘ c`, restricted to the
interior. With these charts the interior is a manifold without boundary modelled on `E`, as
smooth as `M`. The original charted-space structure of `M` is not changed.

The inclusion `TauCeti.ManifoldInterior.val` of the interior into `M` is an open embedding with
image `I.interior M`. It is `C^n` and a `C^n` local diffeomorphism at every regularity, and in
the extended charts it is the identity: the extended chart of the interior at `x` is the
extended chart of `M` at `x`, restricted to the interior. So its manifold derivative is the
identity of `E` (`TauCeti.ManifoldInterior.mfderiv_val`). A map into the interior is `C^n`
exactly when its composite with the inclusion is
(`TauCeti.ManifoldInterior.contMDiff_iff_contMDiff_val_comp`). When `M` has no boundary, the
inclusion is a diffeomorphism onto `M` (`TauCeti.ManifoldInterior.diffeomorph`).

Constructions stated for boundaryless manifolds charted by a vector space, such as the local
homology system, homological orientations and fundamental classes along compact sets, thereby
apply to the interior of a manifold with boundary or corners, and through the open embedding
`TauCeti.ManifoldInterior.val` to `M` at its interior points.

## Main definitions

* `ModelWithCorners.interiorOpens`: the interior of a `C¹` manifold with corners, as an open
  subset.
* `TauCeti.ManifoldInterior I M`: the interior, charted by the model vector space `E`.
* `TauCeti.ManifoldInterior.val`: its inclusion into `M`.
* `TauCeti.ManifoldInterior.mk`: the point of the interior carrier at an interior point of `M`.
* `TauCeti.ManifoldInterior.diffeomorph`: for `M` without boundary, the inclusion as a
  diffeomorphism.

## Main results

* `TauCeti.ManifoldInterior.isOpenEmbedding_val`, `TauCeti.ManifoldInterior.range_val`: the
  inclusion is an open embedding onto `I.interior M`.
* `TauCeti.ManifoldInterior.extChartAt_apply`, `TauCeti.ManifoldInterior.extChartAt_source`,
  `TauCeti.ManifoldInterior.extChartAt_target`, `TauCeti.ManifoldInterior.val_extChartAt_symm`:
  the extended charts of the interior are those of `M`, restricted to the interior.
* `TauCeti.ManifoldInterior.isLocalDiffeomorph_val`: the inclusion is a `C^n` local
  diffeomorphism.
* `TauCeti.ManifoldInterior.mfderiv_val`: its manifold derivative is the identity of `E`.
* `TauCeti.ManifoldInterior.contMDiff_iff_contMDiff_val_comp`: maps into the interior are `C^n`
  exactly when they are as maps into `M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, section Smooth Manifolds with Boundary (invariance of the boundary, and the interior
  as an open manifold without boundary).
-/

public noncomputable section

open Function Set TopologicalSpace
open Topology
open scoped Manifold ContDiff

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

namespace ModelWithCorners

/-- The interior `I.interior M` of a `C¹` manifold with corners, as an open subset. -/
def interiorOpens : Opens M :=
  ⟨I.interior M, I.isOpen_interior one_ne_zero⟩

/-- The underlying set of `I.interiorOpens M` is the interior `I.interior M`. -/
@[simp]
theorem coe_interiorOpens : (I.interiorOpens M : Set M) = I.interior M :=
  (rfl)

variable {I M} in
/-- A point lies in `I.interiorOpens M` exactly when it is an interior point. -/
@[simp]
theorem mem_interiorOpens {x : M} : x ∈ I.interiorOpens M ↔ I.IsInteriorPoint x :=
  Iff.rfl

/-- The interior of a manifold with corners has no boundary. -/
instance : BoundarylessManifold I (I.interiorOpens M) :=
  ⟨fun x ↦ I.isInteriorPoint_iff_isInteriorPoint_val.2 x.2⟩

end ModelWithCorners

namespace TauCeti

/-- The **interior of a `C¹` manifold with corners** `M`, charted by the model vector space `E`:
a copy of the open subset `I.interior M` on which each chart `c` of `M` is replaced by `I ∘ c`.
It is a manifold without boundary modelled on `E`, as smooth as `M`. -/
-- The instances below are transported along this body under Lean's module system.
@[expose] def ManifoldInterior : Type _ :=
  BoundarylessModel I (I.interiorOpens M)

namespace ManifoldInterior

/-- The interior carrier has the subspace topology of `I.interior M`. -/
instance : TopologicalSpace (ManifoldInterior I M) :=
  inferInstanceAs (TopologicalSpace (BoundarylessModel I (I.interiorOpens M)))

/-- The interior of a Hausdorff manifold is Hausdorff. -/
instance [T2Space M] : T2Space (ManifoldInterior I M) :=
  inferInstanceAs (T2Space (I.interiorOpens M))

/-- The charts of the interior: the charts of `M`, followed by the model map `I` and restricted
to the interior. -/
instance : ChartedSpace E (ManifoldInterior I M) :=
  BoundarylessModel.interiorChartedSpace I (M := I.interiorOpens M)

/-- The interior is a manifold modelled on `E`, as smooth as `M`. -/
instance {n : ℕ∞ω} [IsManifold I n M] : IsManifold 𝓘(𝕜, E) n (ManifoldInterior I M) :=
  BoundarylessModel.instIsManifoldInteriorChartedSpace I (M := I.interiorOpens M)

variable {I M}

/-- The homeomorphism from the interior carrier to the open subset `I.interior M` of `M`. -/
def homeomorph : ManifoldInterior I M ≃ₜ I.interiorOpens M :=
  (BoundarylessModel.homeomorph I (I.interiorOpens M)).symm

/-- The **inclusion of the interior** into `M`. -/
def val (x : ManifoldInterior I M) : M :=
  (homeomorph x : M)

/-- The point of the interior carrier at an interior point of `M`. -/
def mk (x : M) (hx : I.IsInteriorPoint x) : ManifoldInterior I M :=
  homeomorph.symm ⟨x, hx⟩

/-- The homeomorphism to `I.interior M` is the inclusion of the interior. -/
@[simp]
theorem coe_homeomorph (x : ManifoldInterior I M) : (homeomorph x : M) = x.val :=
  (rfl)

/-- The point of the interior carrier at an interior point `x` of `M` lies over `x`. -/
@[simp]
theorem val_mk (x : M) (hx : I.IsInteriorPoint x) : (mk x hx : ManifoldInterior I M).val = x := by
  simp only [mk, val, Homeomorph.apply_symm_apply]

/-- The points of the interior carrier lie over interior points of `M`. -/
theorem isInteriorPoint_val (x : ManifoldInterior I M) : I.IsInteriorPoint x.val :=
  ModelWithCorners.mem_interiorOpens.1 (homeomorph x).2

/-- Every point of the interior carrier is the point over its image in `M`. -/
@[simp]
theorem mk_val (x : ManifoldInterior I M) : mk x.val (isInteriorPoint_val x) = x := by
  simp only [mk, val, Subtype.coe_eta, Homeomorph.symm_apply_apply]

/-- The inclusion of the interior is injective. -/
theorem val_injective : Injective (val : ManifoldInterior I M → M) :=
  Subtype.val_injective.comp homeomorph.injective

/-- Two points of the interior carrier are equal exactly when their images in `M` are. -/
@[simp]
theorem val_inj {x y : ManifoldInterior I M} : x.val = y.val ↔ x = y :=
  val_injective.eq_iff

/-- Points of the interior carrier are determined by their images in `M`. -/
@[ext]
theorem ext {x y : ManifoldInterior I M} (h : x.val = y.val) : x = y :=
  val_injective h

/-- The inclusion of the interior has image `I.interior M`. -/
@[simp]
theorem range_val : range (val : ManifoldInterior I M → M) = I.interior M := by
  refine Subset.antisymm (range_subset_iff.2 isInteriorPoint_val) fun x hx ↦ ?_
  exact ⟨mk x hx, val_mk x hx⟩

/-- The inclusion of the interior is an open embedding. -/
theorem isOpenEmbedding_val : IsOpenEmbedding (val : ManifoldInterior I M → M) :=
  (I.interiorOpens M).isOpenEmbedding'.comp homeomorph.isOpenEmbedding

/-- The inclusion of the interior is continuous. -/
@[continuity, fun_prop]
theorem continuous_val : Continuous (val : ManifoldInterior I M → M) :=
  isOpenEmbedding_val.continuous

/-! ### The extended charts of the interior -/

attribute [local instance] BoundarylessModel.interiorChartedSpace

/-- The chart of the interior at `x` is the vector-space chart of the open subset `I.interior M`
built from the chart of `M` at `x`. -/
private theorem chartAt_eq (x : ManifoldInterior I M) :
    chartAt E x = BoundarylessModel.interiorChart I (chartAt H (homeomorph x))
      (chart_mem_atlas H _) :=
  BoundarylessModel.interiorChartAt_eq I x

/-- The chart of the interior at `x` is the extended chart of `M` at `x`. -/
@[simp]
theorem chartAt_apply (x y : ManifoldInterior I M) :
    chartAt E x y = extChartAt I x.val y.val :=
  BoundarylessModel.interiorChartAt_apply I (M := I.interiorOpens M) x y

/-- The extended chart of the interior at `x` is the extended chart of `M` at `x`. -/
theorem extChartAt_apply (x y : ManifoldInterior I M) :
    extChartAt 𝓘(𝕜, E) x y = extChartAt I x.val y.val := by
  rw [extChartAt_coe, comp_apply, modelWithCornersSelf_coe, id, chartAt_apply]

/-- The source of the extended chart of the interior at `x` consists of the interior points in the
source of the extended chart of `M` at `x`. -/
theorem extChartAt_source (x : ManifoldInterior I M) :
    (extChartAt 𝓘(𝕜, E) x).source = val ⁻¹' (extChartAt I x.val).source := by
  rw [_root_.extChartAt_source, _root_.extChartAt_source, chartAt_eq,
    BoundarylessModel.interiorChart_source, Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source]
  -- Both sides are the preimage under the definition of `val`, composed through `homeomorph`.
  rfl

/-- A point lies in the target of the extended chart of the interior at `x` exactly when it lies in
the range of `I`, its preimage under `I` lies in the target of the chart of `M` at `x`, and the
corresponding point of `M` is an interior point. -/
private theorem mem_extChartAt_target_iff (x : ManifoldInterior I M) {v : E} :
    v ∈ (extChartAt 𝓘(𝕜, E) x).target ↔ v ∈ range I ∧ I.symm v ∈ (chartAt H x.val).target ∧
      I.IsInteriorPoint ((chartAt H x.val).symm (I.symm v)) := by
  rw [_root_.extChartAt_target, chartAt_eq, BoundarylessModel.interiorChart_target]
  simp only [modelWithCornersSelf_coe_symm, preimage_id, modelWithCornersSelf_coe, range_id,
    inter_univ, mem_inter_iff, mem_preimage, Opens.mem_chartAt_target_iff,
    ModelWithCorners.mem_interiorOpens]
  tauto

/-- The target of the extended chart of the interior at `x` consists of the points of the target
of the extended chart of `M` at `x` lying in the interior of the range of `I`. -/
theorem extChartAt_target (x : ManifoldInterior I M) :
    (extChartAt 𝓘(𝕜, E) x).target = (extChartAt I x.val).target ∩ interior (range I) := by
  ext v
  rw [mem_extChartAt_target_iff, _root_.extChartAt_target]
  simp only [mem_inter_iff, mem_preimage]
  -- At a point of the chart target, interiority is read off from the model coordinates.
  have key (hv : v ∈ range I) (hc : I.symm v ∈ (chartAt H x.val).target) :
      I.IsInteriorPoint ((chartAt H x.val).symm (I.symm v)) ↔ v ∈ interior (range I) := by
    rw [TauCeti.ModelWithCorners.isInteriorPoint_iff_mem_interior_range one_ne_zero
        (IsManifold.chart_mem_maximalAtlas x.val) ((chartAt H x.val).map_target hc),
      (chartAt H x.val).right_inv hc, I.right_inv hv]
  exact ⟨fun ⟨hv, hc, hi⟩ ↦ ⟨⟨hc, hv⟩, (key hv hc).1 hi⟩,
    fun ⟨⟨hc, hv⟩, hi⟩ ↦ ⟨hv, hc, (key hv hc).2 hi⟩⟩

/-- The inverse of the extended chart of the interior at `x` is the inverse of the extended chart
of `M` at `x`, on the target of the former. -/
theorem val_extChartAt_symm (x : ManifoldInterior I M) {v : E}
    (hv : v ∈ (extChartAt 𝓘(𝕜, E) x).target) :
    ((extChartAt 𝓘(𝕜, E) x).symm v).val = (extChartAt I x.val).symm v := by
  have h := congrArg Subtype.val
    (BoundarylessModel.interiorChartAt_symm_apply I (M := I.interiorOpens M) x v)
  have hc := ((mem_extChartAt_target_iff x).1 hv).2.1
  rw [extChartAt_coe_symm, extChartAt_coe_symm, comp_apply, modelWithCornersSelf_coe_symm, id,
    comp_apply]
  refine h.trans ?_
  rw [extChartAt_coe_symm, comp_apply]
  exact (chartAt H x.val).subtypeRestr_symm_apply _
    (((I.interiorOpens M).mem_chartAt_target_iff (homeomorph x)).2
      ⟨hc, ((mem_extChartAt_target_iff x).1 hv).2.2⟩)

/-! ### Smoothness of the inclusion -/

variable (I M) in
/-- The identity diffeomorphism from the interior carrier, charted by `E`, to the open subset
`I.interior M` of `M` with the charts of `M` restricted to it. -/
def opensDiffeomorph (n : ℕ∞ω) : ManifoldInterior I M ≃ₘ^n⟮𝓘(𝕜, E), I⟯ I.interiorOpens M :=
  (BoundarylessModel.interiorDiffeomorph I (M := I.interiorOpens M) n).symm

/-- The diffeomorphism to `I.interior M` is the homeomorphism `homeomorph`. -/
@[simp]
theorem coe_opensDiffeomorph (n : ℕ∞ω) : ⇑(opensDiffeomorph I M n) = homeomorph :=
  BoundarylessModel.coe_interiorDiffeomorph_symm I n

/-- The inverse diffeomorphism from `I.interior M` is the inverse of `homeomorph`. -/
@[simp]
theorem coe_opensDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(opensDiffeomorph I M n).symm = homeomorph.symm :=
  BoundarylessModel.coe_interiorDiffeomorph I n

/-- The inclusion of the interior is the identity diffeomorphism to the open subset
`I.interior M`, followed by the inclusion of that open subset. -/
theorem val_eq_comp (n : ℕ∞ω) :
    (val : ManifoldInterior I M → M) = Subtype.val ∘ opensDiffeomorph I M n := by
  rw [coe_opensDiffeomorph]
  -- This is the definition of `val`.
  rfl

/-- The inclusion of the interior is a `C^n` local diffeomorphism, for every model with corners
and every regularity. -/
theorem isLocalDiffeomorph_val (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(𝕜, E) I n (val : ManifoldInterior I M → M) := fun x ↦ by
  rw [val_eq_comp n]
  exact IsLocalDiffeomorphAt.comp (hf := (opensDiffeomorph I M n).isLocalDiffeomorph x)
    (hg := isLocalDiffeomorph_subtype_val _)

/-- The inclusion of the interior is `C^n` at every regularity. -/
theorem contMDiff_val (n : ℕ∞ω) : ContMDiff 𝓘(𝕜, E) I n (val : ManifoldInterior I M → M) :=
  (isLocalDiffeomorph_val n).contMDiff

/-- The inclusion of the interior reads as the identity in extended charts, near the image of the
base point. -/
theorem writtenInExtChartAt_val_eventuallyEq (x : ManifoldInterior I M) :
    writtenInExtChartAt 𝓘(𝕜, E) I x val =ᶠ[𝓝 (extChartAt 𝓘(𝕜, E) x x)] id := by
  filter_upwards [extChartAt_target_mem_nhds x] with v hv
  rw [writtenInExtChartAt, comp_apply, comp_apply, val_extChartAt_symm x hv, id]
  exact (extChartAt I x.val).right_inv ((extChartAt_target x ▸ hv).1)

/-- The inclusion of the interior has the identity of `E` as its manifold derivative. -/
theorem hasMFDerivAt_val (x : ManifoldInterior I M) :
    HasMFDerivAt 𝓘(𝕜, E) I val x (ContinuousLinearMap.id 𝕜 E) := by
  refine ⟨continuous_val.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id]
  exact (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
    (nhdsWithin_le_nhds (writtenInExtChartAt_val_eventuallyEq x))
    (writtenInExtChartAt_val_eventuallyEq x).eq_of_nhds

/-- The inclusion of the interior has the identity of `E` as its manifold derivative. -/
theorem mfderiv_val (x : ManifoldInterior I M) :
    mfderiv 𝓘(𝕜, E) I val x = ContinuousLinearMap.id 𝕜 E :=
  (hasMFDerivAt_val x).mfderiv

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

/-- A map into the interior is `C^n` exactly when it is `C^n` as a map into `M`. -/
theorem contMDiff_iff_contMDiff_val_comp {f : N → ManifoldInterior I M} :
    ContMDiff J 𝓘(𝕜, E) n f ↔ ContMDiff J I n (val ∘ f) := by
  rw [val_eq_comp n, comp_assoc, TauCeti.ContMDiff.subtypeVal_comp_iff]
  exact ((opensDiffeomorph I M n).contMDiff_diffeomorph_comp_iff le_rfl).symm

/-- A map into `M` with values in the interior is `C^n` as a map into the interior exactly when
it is `C^n` as a map into `M`. -/
theorem contMDiff_mk_iff {f : N → M} (hf : ∀ y, I.IsInteriorPoint (f y)) :
    ContMDiff J 𝓘(𝕜, E) n (fun y ↦ mk (f y) (hf y)) ↔ ContMDiff J I n f := by
  rw [contMDiff_iff_contMDiff_val_comp]
  exact Iff.of_eq (congrArg _ (funext fun y ↦ val_mk (f y) (hf y)))

/-! ### Manifolds without boundary -/

variable (I M) in
/-- For a manifold `M` without boundary, the inclusion of the interior is a `C^n` diffeomorphism
onto `M`. -/
def diffeomorph [BoundarylessManifold I M] (n : ℕ∞ω) :
    ManifoldInterior I M ≃ₘ^n⟮𝓘(𝕜, E), I⟯ M :=
  (opensDiffeomorph I M n).trans (Diffeomorph.ofTop _ (SetLike.coe_injective I.interior_eq_univ))

/-- The diffeomorphism onto a manifold without boundary is the inclusion of the interior. -/
@[simp]
theorem coe_diffeomorph [BoundarylessManifold I M] (n : ℕ∞ω) :
    ⇑(diffeomorph I M n) = val := by
  rw [diffeomorph, Diffeomorph.coe_trans, Diffeomorph.coe_ofTop, val_eq_comp n]

/-- The inverse of the diffeomorphism onto a manifold without boundary sends a point to the point
of the interior carrier over it. -/
@[simp]
theorem val_diffeomorph_symm [BoundarylessManifold I M] (n : ℕ∞ω) (x : M) :
    ((diffeomorph I M n).symm x).val = x :=
  (congrFun (coe_diffeomorph (I := I) (M := M) n) _).symm.trans
    ((diffeomorph I M n).apply_symm_apply x)

end ManifoldInterior

end TauCeti
