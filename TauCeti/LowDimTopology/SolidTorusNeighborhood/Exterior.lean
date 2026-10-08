/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import TauCeti.Geometry.Manifold.Boundary.BicollarSide
public import TauCeti.Geometry.Manifold.Instances.Torus
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic

/-!
# Knot exteriors from solid-torus neighbourhoods

The exterior of a framed knot is the complement of the open solid torus in a solid-torus
neighbourhood. This file gives that complement a named carrier and records the compactness and
boundary facts needed by Dehn filling.

It also makes the exterior a topological manifold with boundary when the ambient space is a
Hausdorff topological `3`-manifold. A solid torus neighbourhood `Φ` alone does not suffice for
this, since nothing controls the ambient space just outside the image of `Φ`. Shrinking the solid
torus to half its radius, `Φ ∘ SolidTorus.halve`, leaves room on both sides of the new boundary
torus: the annuli `{w | 0 < ‖w‖ < 1}` of `Φ` give it a bicollar
(`TauCeti.IsSolidTorusNeighborhood.isBicollared_comp_halve_comp_boundaryInclusion`), with the
radius `‖w‖ = σ(t)` read through the logistic sigmoid `σ`. The exterior of the shrunken
neighbourhood is the outer side of this bicollar, so `TauCeti.IsBicollar.sideChartedSpace` charts
it on the half-space `EuclideanHalfSpace 3`, with manifold boundary the torus
(`TauCeti.IsSolidTorusNeighborhood.boundary_exteriorChartedSpace`). This file constructs the
topological charted-space structure.

## Main definitions

* `TauCeti.knotExterior`: the exterior of a solid torus neighbourhood.
* `TauCeti.SolidTorus.halve`: the solid torus of half the radius inside the solid torus.
* `TauCeti.IsSolidTorusNeighborhood.exteriorChartedSpace`: the exterior of the half-radius
  neighbourhood, charted on the Euclidean half-space.

## Main results

* `TauCeti.IsSolidTorusNeighborhood.comp_halve`: the half-radius solid torus is again a solid
  torus neighbourhood of the knot.
* `TauCeti.IsSolidTorusNeighborhood.isBicollared_comp_halve_comp_boundaryInclusion`: its boundary
  torus is bicollared.
* `TauCeti.IsSolidTorusNeighborhood.boundary_exteriorChartedSpace`: the manifold boundary of the
  exterior is the boundary torus.

The definition and its elementary topological properties follow Rolfsen, *Knots and Links*,
Sections 2E and 9F.
-/

public section

open Set Topology Metric
open scoped Manifold

namespace TauCeti

variable {X : Type*}

/-- The closed exterior of a solid-torus neighbourhood: the complement of its open solid-torus
image. -/
def knotExterior {Φ : SolidTorus → X} : Set X :=
  (Φ '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1})ᶜ

/-- Membership in the exterior means that a point is outside the open solid-torus image. -/
@[simp]
theorem mem_knotExterior {Φ : SolidTorus → X} {x : X} :
    x ∈ knotExterior (Φ := Φ) ↔ x ∉ Φ '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} :=
  Iff.rfl

/-- The exterior of a solid torus neighbourhood, with its boundary torus removed, is the
complement of the closed solid torus. -/
theorem knotExterior_sdiff_range (Φ : SolidTorus → X) :
    knotExterior (Φ := Φ) \ range (Φ ∘ SolidTorus.boundaryInclusion) = (range Φ)ᶜ := by
  have hunion : {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} ∪ range SolidTorus.boundaryInclusion = univ := by
    rw [SolidTorus.range_boundaryInclusion, eq_univ_iff_forall]
    intro p
    exact (mem_closedBall_zero_iff.mp p.1.2).lt_or_eq
  rw [knotExterior, range_comp, sdiff_eq, ← compl_union, ← image_union, hunion, image_univ]

section Topology

variable [TopologicalSpace X]

/-- The exterior is closed in any ambient topological space. -/
theorem IsSolidTorusNeighborhood.isClosed_exterior
    {f : Circle → X} {Φ : SolidTorus → X} (h : IsSolidTorusNeighborhood f Φ) :
    IsClosed (knotExterior (Φ := Φ)) := by
  exact h.isOpen_image.isClosed_compl

/-- In a compact ambient space, the knot exterior is compact. -/
theorem IsSolidTorusNeighborhood.isCompact_exterior [CompactSpace X]
    {f : Circle → X} {Φ : SolidTorus → X} (h : IsSolidTorusNeighborhood f Φ) :
    IsCompact (knotExterior (Φ := Φ)) := by
  exact h.isClosed_exterior.isCompact

/-- The framed boundary torus is the frontier of the knot exterior. -/
theorem IsSolidTorusNeighborhood.exterior_frontier
    [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
    (h : IsSolidTorusNeighborhood f Φ) :
    frontier (knotExterior (Φ := Φ)) = range (Φ ∘ SolidTorus.boundaryInclusion) := by
  rw [knotExterior, frontier_compl]
  exact h.frontier_image


end Topology

/-! ### The half-radius solid torus -/

namespace SolidTorus

/-- The solid torus of half the radius inside the solid torus: `(w, z) ↦ (w / 2, z)`. -/
noncomputable def halve (p : SolidTorus) : SolidTorus :=
  (⟨(2⁻¹ : ℝ) • (p.1 : ℂ), by
    have hp := mem_closedBall_zero_iff.mp p.1.2
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith⟩, p.2)

@[simp]
theorem coe_halve_fst (p : SolidTorus) : ((halve p).1 : ℂ) = (2⁻¹ : ℝ) • (p.1 : ℂ) :=
  (rfl)

@[simp]
theorem halve_snd (p : SolidTorus) : (halve p).2 = p.2 :=
  (rfl)

/-- Halving the radius is an embedding of the solid torus into itself. -/
theorem isEmbedding_halve : IsEmbedding halve := by
  have h : IsEmbedding fun w : closedBall (0 : ℂ) 1 => (halve (w, 1)).1 := by
    refine IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
    exact (Homeomorph.smulOfNeZero (2⁻¹ : ℝ) (by norm_num)).isEmbedding.comp
      IsEmbedding.subtypeVal
  exact h.prodMap IsEmbedding.id

/-- Halving the radius maps the open solid torus onto the open solid torus of radius `1 / 2`. -/
theorem image_halve_setOf_norm_lt_one :
    halve '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} = {p | ‖(p.1 : ℂ)‖ < 2⁻¹} := by
  ext p
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨q, hq, rfl⟩
    rw [mem_ofPred_eq, coe_halve_fst, norm_smul, Real.norm_of_nonneg (by norm_num)]
    rw [mem_ofPred_eq] at hq
    linarith
  · have hp' : ‖(2 : ℝ) • (p.1 : ℂ)‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      rw [mem_ofPred_eq] at hp
      linarith
    refine ⟨(⟨(2 : ℝ) • (p.1 : ℂ), mem_closedBall_zero_iff.mpr hp'.le⟩, p.2), hp', ?_⟩
    refine Prod.ext (Subtype.ext ?_) rfl
    rw [coe_halve_fst, smul_smul]
    norm_num

end SolidTorus

section Bicollar

variable [TopologicalSpace X] {f : Circle → X} {Φ : SolidTorus → X}

namespace IsSolidTorusNeighborhood

/-- A solid torus neighbourhood restricts to an open embedding on every open subset of the open
solid torus. -/
theorem isOpenEmbedding_comp {Y : Type*} [TopologicalSpace Y] (h : IsSolidTorusNeighborhood f Φ)
    {g : Y → SolidTorus} (hg : IsOpenEmbedding g)
    (hgO : range g ⊆ {p | ‖(p.1 : ℂ)‖ < 1}) : IsOpenEmbedding (Φ ∘ g) := by
  refine ⟨h.isEmbedding.comp hg.isEmbedding, ?_⟩
  obtain ⟨W, hW, hWg⟩ := h.isEmbedding.isInducing.isOpen_iff.mp hg.isOpen_range
  rw [range_comp, ← inter_eq_right.mpr hgO, ← hWg, image_inter_preimage]
  exact h.isOpen_image.inter hW

/-- The solid torus of half the radius is again a solid torus neighbourhood of the knot. -/
theorem comp_halve (h : IsSolidTorusNeighborhood f Φ) :
    IsSolidTorusNeighborhood f (Φ ∘ SolidTorus.halve) where
  isEmbedding := h.isEmbedding.comp SolidTorus.isEmbedding_halve
  apply_zero z := by
    rw [Function.comp_apply, ← h.apply_zero z]
    congr 1
    exact Prod.ext (Subtype.ext (by simp)) rfl
  isOpen_image := by
    rw [image_comp, SolidTorus.image_halve_setOf_norm_lt_one]
    have hO : IsOpen {p : SolidTorus | ‖(p.1 : ℂ)‖ < 2⁻¹} :=
      isOpen_lt (by fun_prop) continuous_const
    have := h.isOpenEmbedding_comp hO.isOpenEmbedding_subtypeVal (by
      rintro _ ⟨p, rfl⟩
      exact (mem_ofPred_eq.mp p.2).trans (by norm_num))
    have hopen := this.isOpen_range
    rwa [range_comp, Subtype.range_coe] at hopen

end IsSolidTorusNeighborhood

/-- Polar coordinates on the punctured open unit disc, with the radius read through the logistic
sigmoid: `(u, t) ↦ σ(t) u`. -/
private noncomputable def sigmoidPolar (q : Circle × ℝ) : ℂ := Real.sigmoid q.2 • (q.1 : ℂ)

private theorem norm_sigmoidPolar (q : Circle × ℝ) : ‖sigmoidPolar q‖ = Real.sigmoid q.2 := by
  rw [sigmoidPolar, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (Real.sigmoid_pos _).le]

private theorem isOpenEmbedding_sigmoidPolar : IsOpenEmbedding sigmoidPolar := by
  let σ : ℝ → Ioi (0 : ℝ) := codRestrict Real.sigmoid (Ioi 0) fun t => Real.sigmoid_pos t
  have hσ : IsOpenEmbedding σ := by
    refine ⟨(IsEmbedding.subtypeVal.comp Topology.isEmbedding_sigmoid).codRestrict _ _, ?_⟩
    have hσr : range σ = Subtype.val ⁻¹' range Real.sigmoid := range_codRestrict _
    rw [hσr]
    refine IsOpen.preimage continuous_subtype_val ?_
    have : range Real.sigmoid = Ioo 0 1 := Real.range_sigmoid
    exact this ▸ isOpen_Ioo
  have hpolar : sigmoidPolar = Subtype.val ∘ (homeomorphUnitSphereProd ℂ).symm ∘
      Prod.map (Homeomorph.refl Circle) σ := by
    funext q
    -- `Circle` is the unit sphere of `ℂ` by definition, so the two sides agree on the nose once
    -- the polar inverse is unfolded.
    simp only [sigmoidPolar, Function.comp_apply, homeomorphUnitSphereProd_symm_apply_coe]
    rfl
  rw [hpolar]
  exact isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp
    ((homeomorphUnitSphereProd ℂ).symm.isOpenEmbedding.comp
      ((Homeomorph.refl Circle).isOpenEmbedding.prodMap hσ))

/-- The bicollar of the boundary torus of the half-radius solid torus inside a solid torus
neighbourhood `Φ`: `((u, z), t) ↦ Φ (σ(t) u, z)`. -/
private noncomputable def halveBicollar (Φ : SolidTorus → X) (q : (Circle × Circle) × ℝ) : X :=
  Φ (⟨sigmoidPolar (q.1.1, q.2), mem_closedBall_zero_iff.mpr
    ((norm_sigmoidPolar _).trans_le (Real.sigmoid_le_one _))⟩, q.1.2)

namespace IsSolidTorusNeighborhood

private theorem isBicollar_halveBicollar (h : IsSolidTorusNeighborhood f Φ) :
    IsBicollar (Φ ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) (halveBicollar Φ) := by
  -- The bicollar is `Φ` after an open embedding into the open solid torus.
  let e : (Circle × Circle) × ℝ ≃ₜ (Circle × ℝ) × Circle :=
    { toFun q := ((q.1.1, q.2), q.1.2)
      invFun p := ((p.1.1, p.2), p.1.2)
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hι : IsOpenEmbedding (codRestrict sigmoidPolar (closedBall (0 : ℂ) 1) fun q =>
      mem_closedBall_zero_iff.mpr ((norm_sigmoidPolar q).trans_le (Real.sigmoid_le_one _))) := by
    refine ⟨isOpenEmbedding_sigmoidPolar.isEmbedding.codRestrict _ _, ?_⟩
    rw [range_codRestrict]
    exact isOpenEmbedding_sigmoidPolar.isOpen_range.preimage continuous_subtype_val
  have hb := h.isOpenEmbedding_comp ((hι.prodMap IsOpenEmbedding.id).comp e.isOpenEmbedding) (by
    rintro _ ⟨q, rfl⟩
    exact (norm_sigmoidPolar _).trans_lt (Real.sigmoid_lt_one _))
  refine ⟨hb, fun q => ?_⟩
  simp only [halveBicollar, Function.comp_apply]
  congr 1
  refine Prod.ext (Subtype.ext ?_) (by simp)
  simp [sigmoidPolar, Real.sigmoid_zero]

/-- The boundary torus of the half-radius solid torus inside a solid torus neighbourhood is
bicollared. -/
theorem isBicollared_comp_halve_comp_boundaryInclusion (h : IsSolidTorusNeighborhood f Φ) :
    IsBicollared (Φ ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) :=
  h.isBicollar_halveBicollar.isBicollared

private theorem preimage_halveBicollar_knotExterior (h : IsSolidTorusNeighborhood f Φ) :
    halveBicollar Φ ⁻¹' knotExterior (Φ := Φ ∘ SolidTorus.halve) = univ ×ˢ Ici 0 := by
  ext q
  simp only [mem_preimage, mem_knotExterior, image_comp, SolidTorus.image_halve_setOf_norm_lt_one,
    halveBicollar, h.isEmbedding.injective.mem_set_image, mem_ofPred_eq, norm_sigmoidPolar,
    mem_prod, mem_univ, mem_Ici, true_and, not_lt]
  rw [← Real.sigmoid_zero, Real.sigmoid_le_iff]

private theorem isOpen_knotExterior_halve_sdiff_range [T2Space X]
    (h : IsSolidTorusNeighborhood f Φ) :
    IsOpen (knotExterior (Φ := Φ ∘ SolidTorus.halve) \
      range (Φ ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion)) := by
  rw [← Function.comp_assoc, knotExterior_sdiff_range]
  exact (isCompact_range (h.comp_halve.isEmbedding.continuous)).isClosed.isOpen_compl

variable [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]

/-- The exterior of the half-radius solid torus inside a solid torus neighbourhood, in a Hausdorff
topological `3`-manifold, as a topological manifold with boundary: it is the outer side of the
bicollar of its boundary torus, charted by `TauCeti.IsBicollar.sideChartedSpace`. Its manifold
boundary is the boundary torus (`TauCeti.IsSolidTorusNeighborhood.boundary_exteriorChartedSpace`).
-/
@[instance_reducible]
noncomputable def exteriorChartedSpace (h : IsSolidTorusNeighborhood f Φ) :
    ChartedSpace (EuclideanHalfSpace 3) (knotExterior (Φ := Φ ∘ SolidTorus.halve)) :=
  letI := torusChartedSpace
  h.isBicollar_halveBicollar.sideChartedSpace (n := 2) h.preimage_halveBicollar_knotExterior
    h.isOpen_knotExterior_halve_sdiff_range

/-- The manifold boundary of the exterior of the half-radius solid torus is its boundary torus. -/
theorem boundary_exteriorChartedSpace (h : IsSolidTorusNeighborhood f Φ) :
    letI := h.exteriorChartedSpace
    (𝓡∂ 3).boundary (knotExterior (Φ := Φ ∘ SolidTorus.halve)) =
      Subtype.val ⁻¹' range (Φ ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) := by
  let := torusChartedSpace
  exact h.isBicollar_halveBicollar.boundary_sideChartedSpace (n := 2)
    h.preimage_halveBicollar_knotExterior h.isOpen_knotExterior_halve_sdiff_range

/-- The manifold interior of the exterior of the half-radius solid torus is the complement of
the closed solid torus. -/
theorem interior_exteriorChartedSpace (h : IsSolidTorusNeighborhood f Φ) :
    letI := h.exteriorChartedSpace
    (𝓡∂ 3).interior (knotExterior (Φ := Φ ∘ SolidTorus.halve)) =
      Subtype.val ⁻¹' (range (Φ ∘ SolidTorus.halve))ᶜ := by
  let := h.exteriorChartedSpace
  rw [← ModelWithCorners.compl_boundary, h.boundary_exteriorChartedSpace, ← preimage_compl,
    ← knotExterior_sdiff_range, Function.comp_assoc, sdiff_eq, preimage_inter,
    Subtype.coe_preimage_self, univ_inter]

end IsSolidTorusNeighborhood

end Bicollar

end TauCeti
