/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
public import TauCeti.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Algebra.LieGroup

/-!
# Vector-space charts for a manifold with no boundary

A boundaryless C¹ manifold admits a copy with the same carrier and topology and charts in the
model vector space. Its original model with corners may have boundary. The identity maps in
both directions are smooth at every regularity. The smooth identity homomorphisms let Lie-group
constructions over a vector-space model be transported back to their original models, and
supply the native Lie-algebra comparison.

The construction uses `TauCeti.BoundarylessModel`, preserving its carrier and topology.
`TauCeti.BoundarylessModel.interiorChartedSpace` explicitly selects the extended atlas on this
copy; the original manifold retains its atlas.

## Main results

* `TauCeti.BoundarylessModel.interiorChart`, `interiorChart_toPartialEquiv`, and
  `interiorChart_source`, `interiorChart_apply`, `interiorChart_symm_apply`, and
  `interiorChart_target`: the transported chart and its coordinates, source and target.
* `TauCeti.BoundarylessModel.interiorChartedSpace`: the vector-space atlas constructor.
* `TauCeti.BoundarylessModel.interior_atlas_eq`, `interiorChartAt_eq`,
  `interiorChartAt_apply`, and `interiorChartAt_symm_apply`: its chosen-chart equations.
* `TauCeti.BoundarylessModel.interiorChart_eq_chart` and `interiorChartedSpace_eq`:
  comparison with the chosen atlas for globally boundaryless models.
* `TauCeti.BoundarylessModel.instIsManifoldInteriorChartedSpace`: preservation of regularity.
* `TauCeti.BoundarylessModel.interiorExtChartAt_eq`: the preferred extended-chart comparison.
* `TauCeti.BoundarylessModel.interiorDiffeomorph`, `coe_interiorDiffeomorph`, and
  `coe_interiorDiffeomorph_symm`: the identity diffeomorphism and its coercion laws.
* `TauCeti.BoundarylessModel.interiorLieGroup` and `interiorLieAddGroup`: transport of
  smooth group operations at every regularity.
* `TauCeti.BoundarylessModel.toInteriorModelHom`, `fromInteriorModelHom`,
  `toInteriorModelAddHom`, and `fromInteriorModelAddHom`: the smooth identity morphisms.
* `TauCeti.BoundarylessModel.coe_toInteriorModelHom`, `coe_fromInteriorModelHom`,
  `coe_toInteriorModelAddHom`, and `coe_fromInteriorModelAddHom`: their coercion laws.
* `TauCeti.BoundarylessModel.fromInteriorModelHom_comp_toInteriorModelHom`,
  `toInteriorModelHom_comp_fromInteriorModelHom`,
  `fromInteriorModelAddHom_comp_toInteriorModelAddHom`, and
  `toInteriorModelAddHom_comp_fromInteriorModelAddHom`: the inverse composition identities.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1 (Smooth Manifolds), section Smooth Structures, Proposition 1.17, pp.13–14.
-/

public noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

namespace TauCeti.BoundarylessModel

variable (I) [IsManifold I 1 M] [BoundarylessManifold I M]

/-- An atlas chart of a boundaryless C¹ manifold, with values in its model vector space. -/
def interiorChart (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    OpenPartialHomeomorph (BoundarylessModel I M) E where
  toPartialEquiv := c.extend I
  open_source := c.isOpen_extend_source (I := I)
  open_target := c.isOpen_extend_target_of_mem_atlas (I := I) hc
  continuousOn_toFun := c.continuousOn_extend (I := I)
  continuousOn_invFun := c.continuousOn_extend_symm (I := I)

/-- The transported chart has the original extended partial equivalence. -/
theorem interiorChart_toPartialEquiv (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    (interiorChart I c hc).toPartialEquiv = c.extend I := by rfl

/-- The transported chart has the original chart source on the copied carrier. -/
@[simp]
theorem interiorChart_source (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    (interiorChart I c hc).source = (homeomorph I M).symm ⁻¹' c.source := by
  -- The source is a projection of toPartialEquiv, which is not exposed in this goal.
  -- There is no source rewrite for interiorChart yet; change exposes the defining projection.
  change (c.extend I).source = _
  rw [OpenPartialHomeomorph.extend_source, coe_homeomorph_symm]
  rfl

/-- The transported chart is the original chart followed by the model map. -/
@[simp]
theorem interiorChart_apply (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
    (x : BoundarylessModel I M) :
    interiorChart I c hc x = I (c ((homeomorph I M).symm x)) := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv, interiorChart_toPartialEquiv,
    OpenPartialHomeomorph.extend_coe, coe_homeomorph_symm]
  exact Function.comp_apply

/-- The inverse transported chart has the original extended inverse coordinates. -/
@[simp]
theorem interiorChart_symm_apply (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
    (v : E) :
    (interiorChart I c hc).symm v = homeomorph I M (c.symm (I.symm v)) := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv_symm, interiorChart_toPartialEquiv,
    coe_homeomorph]
  exact congrFun (c.extend_coe_symm (I := I)) v

/-- The transported chart target is the model extension of the original target. -/
@[simp]
theorem interiorChart_target (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    (interiorChart I c hc).target = I.symm ⁻¹' c.target ∩ range I := by
  -- The target is likewise a projection of toPartialEquiv, not exposed for rewriting here.
  -- There is no target rewrite for interiorChart yet; change exposes the defining projection.
  change (c.extend I).target = _
  exact c.extend_target

/-- The atlas of extended charts on the copy of a boundaryless C¹ manifold. -/
@[instance_reducible]
def interiorChartedSpace : ChartedSpace E (BoundarylessModel I M) where
  atlas := {e | ∃ (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M), e = interiorChart I c hc}
  chartAt x := interiorChart I (chartAt H ((homeomorph I M).symm x)) (chart_mem_atlas H _)
  mem_chart_source x := by
    rw [interiorChart_source]
    exact mem_chart_source H ((homeomorph I M).symm x)
  chart_mem_atlas x := ⟨_, chart_mem_atlas H _, rfl⟩

attribute [local instance] interiorChartedSpace

/-- The interior atlas consists exactly of the extended original atlas charts. -/
theorem interior_atlas_eq : atlas E (BoundarylessModel I M) =
    {e | ∃ (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M), e = interiorChart I c hc} := by
  rfl

/-- The preferred interior chart extends the original preferred chart. -/
theorem interiorChartAt_eq (x : BoundarylessModel I M) :
    chartAt E x =
      interiorChart I (chartAt H ((homeomorph I M).symm x)) (chart_mem_atlas H _) := by rfl

/-- The preferred interior chart has the original extended coordinates. -/
theorem interiorChartAt_apply (z y : BoundarylessModel I M) :
    chartAt E z y = extChartAt I ((homeomorph I M).symm z) ((homeomorph I M).symm y) := by
  rw [interiorChartAt_eq, interiorChart_apply, extChartAt_coe, comp_apply]

/-- The inverse preferred interior chart has the original extended inverse coordinates. -/
theorem interiorChartAt_symm_apply (z : BoundarylessModel I M) (v : E) :
    (homeomorph I M).symm ((chartAt E z).symm v) =
      (extChartAt I ((homeomorph I M).symm z)).symm v := by
  rw [interiorChartAt_eq, interiorChart_symm_apply, Homeomorph.symm_apply_apply,
    extChartAt_coe_symm, comp_apply]

/-- For a globally boundaryless model, the atlas chart is the existing transported chart. -/
theorem interiorChart_eq_chart [I.Boundaryless]
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    interiorChart I c hc = chart I c :=
  OpenPartialHomeomorph.toPartialEquiv_injective
    ((interiorChart_toPartialEquiv I c hc).trans (chart_toPartialEquiv I c).symm)

/-- For a globally boundaryless model, both constructors give the same chosen atlas. -/
theorem interiorChartedSpace_eq [I.Boundaryless] :
    interiorChartedSpace I (M := M) = instChartedSpace (I := I) (M := M) := by
  have ha : (interiorChartedSpace I (M := M)).atlas =
      (instChartedSpace (I := I) (M := M)).atlas := by
    ext e
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (interiorChart_eq_chart I c hc).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (interiorChart_eq_chart I c hc).symm⟩
  have hp : (interiorChartedSpace I (M := M)).chartAt =
      (instChartedSpace (I := I) (M := M)).chartAt := by
    funext x
    exact interiorChart_eq_chart I _ (chart_mem_atlas H _)
  exact ChartedSpace.ext ha hp

/-- Preferred extended charts are unchanged on the copied carrier. -/
theorem interiorExtChartAt_eq (x : BoundarylessModel I M) :
    extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x) :=
  extChartAt_eq_of_chartAt_toPartialEquiv I
    (fun _ ↦ interiorChart_toPartialEquiv I _ _) x

/-- The interior atlas preserves every manifold regularity of the original atlas. -/
instance instIsManifoldInteriorChartedSpace {n : ℕ∞ω} [IsManifold I n M] :
    IsManifold 𝓘(𝕜, E) n (BoundarylessModel I M) := by
  apply isManifold_of_atlas_extend I (M := M)
  intro C hC
  rw [interior_atlas_eq] at hC
  obtain ⟨c, hc, hC⟩ := hC
  rw [hC]
  exact ⟨c, hc, interiorChart_toPartialEquiv I c hc⟩

/-- The identity diffeomorphism to the vector-space atlas, at any regularity. -/
def interiorDiffeomorph (n : ℕ∞ω) : Diffeomorph I 𝓘(𝕜, E) M (BoundarylessModel I M) n :=
  diffeomorphOfExtChartAtEq I (interiorExtChartAt_eq I) n

/-- The diffeomorphism has the identity homeomorphism as its underlying map. -/
@[simp]
theorem coe_interiorDiffeomorph (n : ℕ∞ω) :
    ⇑(interiorDiffeomorph I (M := M) n) = homeomorph I M :=
  coe_diffeomorphOfExtChartAtEq I _ n

/-- The inverse diffeomorphism has the inverse identity homeomorphism as its map. -/
@[simp]
theorem coe_interiorDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(interiorDiffeomorph I (M := M) n).symm = (homeomorph I M).symm :=
  coe_diffeomorphOfExtChartAtEq_symm I _ n

section Monoids

variable [Monoid M] {n : ℕ∞ω}

/-- The identity smooth monoid morphism to the vector-space model copy. -/
@[to_additive toInteriorModelAddHom
  /-- The identity smooth additive monoid morphism to the vector-space model copy. -/]
def toInteriorModelHom : ContMDiffMonoidMorphism I 𝓘(𝕜, E) n M (BoundarylessModel I M) where
  toFun := homeomorph I M
  map_one' := homeomorph_one I M
  map_mul' := homeomorph_mul I M
  contMDiff_toFun := by
    have h := (interiorDiffeomorph I (M := M) n).contMDiff
    rw [coe_interiorDiffeomorph] at h
    exact h

/-- The inverse identity smooth monoid morphism from the vector-space model copy. -/
@[to_additive fromInteriorModelAddHom
  /-- The inverse identity smooth additive monoid morphism from the vector-space model copy. -/]
def fromInteriorModelHom : ContMDiffMonoidMorphism 𝓘(𝕜, E) I n (BoundarylessModel I M) M where
  toFun := (homeomorph I M).symm
  map_one' := homeomorph_symm_one I M
  map_mul' := homeomorph_symm_mul I M
  contMDiff_toFun := by
    have h := (interiorDiffeomorph I (M := M) n).symm.contMDiff
    rw [coe_interiorDiffeomorph_symm] at h
    exact h

/-- The forward smooth morphism has the identity homeomorphism as its function. -/
@[to_additive (attr := simp) coe_toInteriorModelAddHom
  /-- The forward smooth additive morphism has the identity homeomorphism as its function. -/]
theorem coe_toInteriorModelHom : ⇑(toInteriorModelHom I (M := M) (n := n)) = homeomorph I M := by
  rfl

/-- The reverse smooth morphism has the inverse identity homeomorphism as its function. -/
@[to_additive (attr := simp) coe_fromInteriorModelAddHom
  /-- The reverse smooth additive morphism has the inverse identity homeomorphism
  as its function. -/]
theorem coe_fromInteriorModelHom :
    ⇑(fromInteriorModelHom I (M := M) (n := n)) = (homeomorph I M).symm := by
  rfl

/-- The two identity morphisms compose to the original identity. -/
@[to_additive (attr := simp) fromInteriorModelAddHom_comp_toInteriorModelAddHom
  /-- The two additive identity morphisms compose to the original identity. -/]
theorem fromInteriorModelHom_comp_toInteriorModelHom :
    (fromInteriorModelHom I (n := n)).comp (toInteriorModelHom I (M := M)) =
      ContMDiffMonoidMorphism.id := by
  apply DFunLike.coe_injective
  rw [ContMDiffMonoidMorphism.coe_comp, coe_fromInteriorModelHom, coe_toInteriorModelHom,
    ContMDiffMonoidMorphism.coe_id]
  funext x
  simp only [comp_apply, Homeomorph.symm_apply_apply, id_eq]

/-- The identity morphisms in reverse order compose to the identity of the model copy. -/
@[to_additive (attr := simp) toInteriorModelAddHom_comp_fromInteriorModelAddHom
  /-- The reverse-order additive identity morphisms compose to the copied identity. -/]
theorem toInteriorModelHom_comp_fromInteriorModelHom :
    (toInteriorModelHom I (n := n)).comp (fromInteriorModelHom I (M := M)) =
      ContMDiffMonoidMorphism.id := by
  apply DFunLike.coe_injective
  rw [ContMDiffMonoidMorphism.coe_comp, coe_toInteriorModelHom, coe_fromInteriorModelHom,
    ContMDiffMonoidMorphism.coe_id]
  funext x
  simp only [comp_apply, Homeomorph.apply_symm_apply, id_eq]

end Monoids

section Groups

variable [Group M]

/-- The transported vector-space atlas preserves the regularity of Lie-group operations. -/
@[to_additive
  /-- The vector-space atlas preserves the regularity of additive Lie-group operations. -/]
instance interiorLieGroup {n : ℕ∞ω} [LieGroup I n M] :
    LieGroup 𝓘(𝕜, E) n (BoundarylessModel I M) := by
  have hlocal : IsLocalDiffeomorph I 𝓘(𝕜, E) n
      (toInteriorModelHom I (M := M) (n := n)) := by
    rw [coe_toInteriorModelHom, ← coe_interiorDiffeomorph I n]
    exact (interiorDiffeomorph I n).isLocalDiffeomorph
  apply hlocal.lieGroup (toInteriorModelHom I (M := M) (n := n)).toMonoidHom
  -- The monoid-hom projection and smooth morphism have the same underlying function.
  change Function.Surjective (toInteriorModelHom I (M := M) (n := n))
  rw [coe_toInteriorModelHom]
  exact (homeomorph I M).surjective

end Groups

end TauCeti.BoundarylessModel
