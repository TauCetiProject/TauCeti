/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.LinearAlgebra.Submodule.Relation.FiberProduct

/-!
# Associativity of embedded fibre products

For maps `f : X → B`, `g : Y → B`, `h : Y → C` and `k : Z → C`, the two iterated fibre
products `(X ×_B Y) ×_C Z` and `X ×_B (Y ×_C Z)` parametrize the same matching triples.
This file constructs their canonical diffeomorphism, sending `((x, y), z)` to `(x, (y, z))`.

The four fibre products carry their subspace topologies and any charted structures for which
inclusion into the corresponding product is a smooth embedding. In particular these hypotheses
are supplied by `TauCeti.isSmoothEmbedding_coe_transverseFiberProduct` for transverse fibre
products. They also allow clean embedded fibre products. Smoothness of the associator follows
from the smooth universal property of each embedded fibre product; it requires no new choice
of charts and no dimension arithmetic. The maps into `B` and `C` need no additional regularity
once these embedded structures have been supplied.

The component formulas show that the endpoint map of a composite of three correspondences is
unchanged by regrouping. This is the geometric associator before any excess quotient; it makes
no assertion that an arbitrary relational composite is embedded or that a clean quotient exists.

For transverse fibre products the two groupings need different transversality hypotheses at
their second step. When `f, g` and `h, k` are transverse, the second step of one grouping is
transverse exactly when that of the other is
(`TauCeti.transverse_comp_snd_transverseFiberProduct_iff`), so the four transverse atlases needed
by the associator exist together. At a matching triple both conditions say that the tangent
spaces of `B` and `C` are spanned by the images of `df`, of `(dg, dh)` and of `dk`.

## Main results

* `TauCeti.fiberProductAssocDiffeomorph`: the associator of iterated embedded fibre products.
* `TauCeti.transverse_comp_snd_transverseFiberProduct_iff`: the second steps of the two groupings
  of transverse fibre products are transverse together.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278
  (admissible composition of canonical relations).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.30
  (embedded transverse fibre products).
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

section Embedded

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EX HX X EY HY Y EZ HZ Z B C : Type*}
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] [TopologicalSpace HZ]
  {IX : ModelWithCorners 𝕜 EX HX} {IY : ModelWithCorners 𝕜 EY HY}
  {IZ : ModelWithCorners 𝕜 EZ HZ}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace Z] [ChartedSpace HZ Z]
  {f : X → B} {g : Y → B} {h : Y → C} {k : Z → C}
  {EXY HXY EYZ HYZ EL HL ER HR : Type*}
  [NormedAddCommGroup EXY] [NormedSpace 𝕜 EXY] [TopologicalSpace HXY]
  [NormedAddCommGroup EYZ] [NormedSpace 𝕜 EYZ] [TopologicalSpace HYZ]
  [NormedAddCommGroup EL] [NormedSpace 𝕜 EL] [TopologicalSpace HL]
  [NormedAddCommGroup ER] [NormedSpace 𝕜 ER] [TopologicalSpace HR]
  {IXY : ModelWithCorners 𝕜 EXY HXY} {IYZ : ModelWithCorners 𝕜 EYZ HYZ}
  {IL : ModelWithCorners 𝕜 EL HL} {IR : ModelWithCorners 𝕜 ER HR}
  [ChartedSpace HXY {p : X × Y // f p.1 = g p.2}]
  [ChartedSpace HYZ {p : Y × Z // h p.1 = k p.2}]
  [ChartedSpace HL {p : {q : X × Y // f q.1 = g q.2} × Z // h p.1.1.2 = k p.2}]
  [ChartedSpace HR {p : X × {q : Y × Z // h q.1 = k q.2} // f p.1 = g p.2.1.1}]
  {n : ℕ∞ω}
  (hXY : Manifold.IsSmoothEmbedding IXY (IX.prod IY) n
    (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y))
  (hYZ : Manifold.IsSmoothEmbedding IYZ (IY.prod IZ) n
    (Subtype.val : {p : Y × Z // h p.1 = k p.2} → Y × Z))
  (hL : Manifold.IsSmoothEmbedding IL (IXY.prod IZ) n
    (Subtype.val : {p : {q : X × Y // f q.1 = g q.2} × Z // h p.1.1.2 = k p.2} →
      {p : X × Y // f p.1 = g p.2} × Z))
  (hR : Manifold.IsSmoothEmbedding IR (IX.prod IYZ) n
    (Subtype.val : {p : X × {q : Y × Z // h q.1 = k q.2} // f p.1 = g p.2.1.1} →
      X × {p : Y × Z // h p.1 = k p.2}))

/-- The canonical associator of iterated embedded fibre products. It preserves all three
components and both matching equations. The four inclusion hypotheses hold, in particular,
for the atlases of transverse fibre products when both iterated constructions are transverse. -/
def fiberProductAssocDiffeomorph :
    {p : {q : X × Y // f q.1 = g q.2} × Z // h p.1.1.2 = k p.2} ≃ₘ^n⟮IL, IR⟯
      {p : X × {q : Y × Z // h q.1 = k q.2} // f p.1 = g p.2.1.1} where
  toFun p := ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩
  invFun p := ⟨(⟨(p.1.1, p.1.2.1.1), p.2⟩, p.1.2.1.2), p.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply hR.contMDiff_iff_comp.mpr
    exact (hXY.contMDiff.comp hL.contMDiff.fst).fst.prodMk
      (hYZ.contMDiff_iff_comp.mpr
        ((hXY.contMDiff.comp hL.contMDiff.fst).snd.prodMk hL.contMDiff.snd))
  contMDiff_invFun := by
    apply hL.contMDiff_iff_comp.mpr
    exact (hXY.contMDiff_iff_comp.mpr
      (hR.contMDiff.fst.prodMk (hYZ.contMDiff.comp hR.contMDiff.snd).fst)).prodMk
        (hYZ.contMDiff.comp hR.contMDiff.snd).snd

/-- The associator regroups a matching triple without changing its entries. -/
@[simp]
theorem fiberProductAssocDiffeomorph_apply
    (p : {p : {q : X × Y // f q.1 = g q.2} × Z // h p.1.1.2 = k p.2}) :
    fiberProductAssocDiffeomorph hXY hYZ hL hR p =
      ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩ :=
  (rfl)

/-- The inverse associator regroups a matching triple in the other direction. -/
@[simp]
theorem fiberProductAssocDiffeomorph_symm_apply
    (p : {p : X × {q : Y × Z // h q.1 = k q.2} // f p.1 = g p.2.1.1}) :
    (fiberProductAssocDiffeomorph hXY hYZ hL hR).symm p =
      ⟨(⟨(p.1.1, p.1.2.1.1), p.2⟩, p.1.2.1.2), p.1.2.2⟩ :=
  (rfl)

end Embedded

section Transverse

/-! ### Transversality of iterated fibre products

For transverse fibre products, the second step of either grouping needs its own transversality
hypothesis. At a matching triple `(x, y, z)`, the tangent vectors of `Y` matching a tangent vector
of `X` in `B` are `dg⁻¹(range df)`, so the second step of `(X ×_B Y) ×_C Z` asks that
`dh (dg⁻¹(range df))` and `range dk` span `T C`. Symmetrically, the second step of
`X ×_B (Y ×_C Z)` asks that `range df` and `dg (dh⁻¹(range dk))` span `T B`. When the first steps
`f, g` and `h, k` are transverse, these two conditions agree
(`Submodule.map_comap_sup_eq_top_iff_sup_map_comap_eq_top`). -/

variable {EX HX X EY HY Y EZ HZ Z EB HB B EC HC C : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  {IY : ModelWithCorners ℝ EY HY} [TopologicalSpace Y] [ChartedSpace HY Y]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {IC : ModelWithCorners ℝ EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  {n : ℕ∞ω} [IsManifold IX n X] [IsManifold IY n Y] [IsManifold IZ n Z]
  [IsManifold IB n B] [IsManifold IC n C]
  [IX.Boundaryless] [IY.Boundaryless] [IZ.Boundaryless] [IB.Boundaryless] [IC.Boundaryless]
  [FiniteDimensional ℝ EX] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EZ]
  [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EC]
  {f : X → B} {g : Y → B} {h : Y → C} {k : Z → C}

/-- **Transversality of iterated fibre products is associative.** Let `f : X → B` and
`g : Y → B` be transverse, and let `h : Y → C` and `k : Z → C` be transverse. Then
`(x, y) ↦ h y` on the transverse fibre product `X ×_B Y` is transverse to `k` exactly when `f`
is transverse to `(y, z) ↦ g y` on the transverse fibre product `Y ×_C Z`. So either both
iterated fibre products `(X ×_B Y) ×_C Z` and `X ×_B (Y ×_C Z)` are transverse fibre products,
or neither is. -/
theorem transverse_comp_snd_transverseFiberProduct_iff (hn : 1 ≤ n) (hf : ContMDiff IX IB n f)
    (hg : ContMDiff IY IB n g)
    (hfg : ∀ p : X × Y, f p.1 = g p.2 →
      (mfderiv IX IB f p.1).range ⊔
        (((tangentSpaceCast IB (g p.2) (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IB g p.2)).range = ⊤)
    (hh : ContMDiff IY IC n h) (hk : ContMDiff IZ IC n k)
    (hhk : ∀ p : Y × Z, h p.1 = k p.2 →
      (mfderiv IY IC h p.1).range ⊔
        (((tangentSpaceCast IC (k p.2) (h p.1)).toContinuousLinearMap).comp
          (mfderiv IZ IC k p.2)).range = ⊤) :
    (letI := transverseFiberProductChartedSpace hn hf hg hfg
      ∀ p : {q : X × Y // f q.1 = g q.2} × Z, h p.1.1.2 = k p.2 →
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EB) → ℝ) IC
            (fun q : {q : X × Y // f q.1 = g q.2} ↦ h q.1.2) p.1).range ⊔
          (((tangentSpaceCast IC (k p.2) (h p.1.1.2)).toContinuousLinearMap).comp
            (mfderiv IZ IC k p.2)).range = ⊤) ↔
    (letI := transverseFiberProductChartedSpace hn hh hk hhk
      ∀ p : X × {q : Y × Z // h q.1 = k q.2}, f p.1 = g p.2.1.1 →
        (mfderiv IX IB f p.1).range ⊔
          (((tangentSpaceCast IB (g p.2.1.1) (f p.1)).toContinuousLinearMap).comp
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EZ - finrank ℝ EC) → ℝ) IB
              (fun q : {q : Y × Z // h q.1 = k q.2} ↦ g q.1.1) p.2)).range = ⊤) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let := transverseFiberProductChartedSpace hn hf hg hfg
  let := transverseFiberProductChartedSpace hn hh hk hhk
  have hYZ := (isSmoothEmbedding_coe_transverseFiberProduct hn hh hk hhk).contMDiff
  have hXY := (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg hfg).contMDiff
  -- At a matching triple `(x, y, z)`, the two conditions are the two sides of
  -- `Submodule.map_comap_sup_eq_top_iff_sup_map_comap_eq_top`, once the differentials of
  -- `(x, y) ↦ h y` and `(y, z) ↦ g y` are written through those of the projections.
  have key (x : X) (y : Y) (z : Z) (e₁ : f x = g y) (e₂ : h y = k z) :
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EB) → ℝ) IC
            (fun q : {q : X × Y // f q.1 = g q.2} ↦ h q.1.2) ⟨(x, y), e₁⟩).range ⊔
          (((tangentSpaceCast IC (k z) (h y)).toContinuousLinearMap).comp
            (mfderiv IZ IC k z)).range = ⊤ ↔
        (mfderiv IX IB f x).range ⊔
          (((tangentSpaceCast IB (g y) (f x)).toContinuousLinearMap).comp
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EZ - finrank ℝ EC) → ℝ) IB
              (fun q : {q : Y × Z // h q.1 = k q.2} ↦ g q.1.1) ⟨(y, z), e₂⟩)).range = ⊤ := by
    have hL := mfderiv_comp (g := h) (f := fun q : {q : X × Y // f q.1 = g q.2} ↦ q.1.2)
      ⟨(x, y), e₁⟩ (hh.mdifferentiableAt hn0) (hXY.snd.mdifferentiableAt hn0)
    have hR := mfderiv_comp (g := g) (f := fun q : {q : Y × Z // h q.1 = k q.2} ↦ q.1.1)
      ⟨(y, z), e₂⟩ (hg.mdifferentiableAt hn0) (hYZ.fst.mdifferentiableAt hn0)
    simp only [Function.comp_def] at hL hR
    rw [hL, hR, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      range_mfderiv_snd_transverseFiberProduct hn hf hg hfg,
      ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.toLinearMap_comp
        ((tangentSpaceCast IB (g y) (f x)).toContinuousLinearMap.comp (mfderiv IY IB g y)),
      LinearMap.range_comp, range_mfderiv_fst_transverseFiberProduct hn hh hk hhk]
    exact Submodule.map_comap_sup_eq_top_iff_sup_map_comap_eq_top (hfg (x, y) e₁)
      (hhk (y, z) e₂)
  constructor
  · rintro H ⟨x, ⟨⟨y, z⟩, e₂⟩⟩ e₁
    exact (key x y z e₁ e₂).1 (H (⟨(x, y), e₁⟩, z) e₂)
  · rintro H ⟨⟨⟨x, y⟩, e₁⟩, z⟩ e₂
    exact (key x y z e₁ e₂).2 (H (x, ⟨(y, z), e₂⟩) e₁)

end Transverse

end TauCeti
