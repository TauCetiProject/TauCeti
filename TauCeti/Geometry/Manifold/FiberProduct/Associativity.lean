/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

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

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278
  (admissible composition of canonical relations).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.30
  (embedded transverse fibre products).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

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

end TauCeti
