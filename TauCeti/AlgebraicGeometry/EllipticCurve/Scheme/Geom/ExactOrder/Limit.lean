/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Limit
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Locus
public import TauCeti.AlgebraicGeometry.Limits.GrpObj

/-!
# Spreading out points of exact order `N`

Let `S = lim Dⱼ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps, and let `E` be an elliptic curve over a member `Dᵢ`. This file spreads out
points of `E` and Drinfeld's points of exact order `N`, the `[Γ₁(N)]`-structures of Katz and Mazur,
from `S` to some member `Dⱼ`.

* Every `S`-point of the base change `E_S` is the base change of a `Dⱼ`-point of the base change
  `E_{Dⱼ}`, for some `j ⟶ i` (`EllipticCurveGeom.exists_pointsPullback_baseChangeMap_eq`, in
  `TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Limit`).
* If the base change of a `Dᵢ`-point `P` to `S` has exact order `N`, then so does its base change
  to some `Dⱼ` (`EllipticCurveGeom.exists_isOfExactOrder_pointsPullback_baseChange`). Having exact
  order `N` says that the divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup scheme, a scheme-theoretic
  condition rather than a condition on points, and the divisor is finite locally free, so this is
  the spreading out of subgroup structures on finitely presented schemes
  (`CategoryTheory.Limits.IsLimit.exists_grpObj_isMonHom_overPullback`), through the
  characterisation `EllipticCurveGeom.isOfExactOrder_pointsPullback_baseChange_iff` of exact order
  after base change.
* Combining the two, every `S`-point of exact order `N` of `E_S` is the base change of a `Dⱼ`-point
  of exact order `N` of `E_{Dⱼ}`, for some `j ⟶ i`
  (`EllipticCurveGeom.exists_isOfExactOrder_pointsPullback_baseChangeMap_eq`).

The base change of `E` along `j ⟶ i` is related to its base change to `S` by the canonical map
`E.baseChangeMap`, which forms a pullback square with the structure morphisms
(`EllipticCurveGeom.isPullback_baseChangeMap`); base change of points is taken along this square.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_isOfExactOrder_pointsPullback_baseChange`:
  having exact order `N` spreads out along cofiltered limits.
* `EllipticCurveGeom.exists_isOfExactOrder_pointsPullback_baseChangeMap_eq`: points of exact
  order `N` spread out along cofiltered limits.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Troisième partie, §8.
* The Stacks Project, [Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC).
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 (points of exact
  order `N`) and §3.2 (`[Γ₁(N)]`-structures).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I}
  (E : EllipticCurveGeom (D.obj i))

include hc in
/-- **Spreading out exact order.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps, let `E` be an elliptic curve over a member
`Dᵢ`, and let `P` be a `Dᵢ`-point of `E`. If the base change of `P` to `S` has exact order `N`, then
so does its base change to `Dⱼ`, for some `j ⟶ i`. -/
theorem exists_isOfExactOrder_pointsPullback_baseChange
    (P : 𝟙_ (Over (D.obj i)) ⟶ Over.mk E.structureMap) {N : ℕ}
    (h : (E.baseChange (c.π.app i)).IsOfExactOrder
      (pointsPullback (E.isPullback_baseChange _) (by simp) P) N) :
    ∃ (j : I) (g : j ⟶ i), (E.baseChange (D.map g)).IsOfExactOrder
      (pointsPullback (E.isPullback_baseChange _) (by simp) P) N := by
  obtain ⟨_, _⟩ := (E.isOfExactOrder_pointsPullback_baseChange_iff _ P N).mp h
  -- The divisor `[P] + ⋯ + [NP]` is finite locally free over `Dᵢ`, so of finite presentation.
  have : LocallyOfFinitePresentation
      (Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation ((E.multiplesDivisor P N).subschemeι ≫ _))
  have : QuasiCompact (Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)).hom :=
    inferInstanceAs (QuasiCompact ((E.multiplesDivisor P N).subschemeι ≫ _))
  have : QuasiSeparated (Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)).hom :=
    inferInstanceAs (QuasiSeparated ((E.multiplesDivisor P N).subschemeι ≫ _))
  have : Smooth (Over.mk E.structureMap).hom := SmoothOfRelativeDimension.smooth 1 E.structureMap
  obtain ⟨j, g, _, hg, -⟩ := hc.exists_grpObj_isMonHom_overPullback
    (Over.homMk (E.multiplesDivisor P N).subschemeι rfl :
      Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap)
  exact ⟨j, g, (E.isOfExactOrder_pointsPullback_baseChange_iff _ P N).mpr ⟨_, hg⟩⟩

include hc in
/-- **Spreading out points of exact order `N`**, that is, `[Γ₁(N)]`-structures. Let `S = lim Dⱼ` be
a cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps, and let `E`
be an elliptic curve over a member `Dᵢ`. Every `S`-point of exact order `N` of the base change
`E_S` of `E` is, for some `j ⟶ i`, the base change of a `Dⱼ`-point of exact order `N` of the base
change `E_{Dⱼ}`. -/
theorem exists_isOfExactOrder_pointsPullback_baseChangeMap_eq
    {P : 𝟙_ (Over c.pt) ⟶ Over.mk (E.baseChange (c.π.app i)).structureMap} {N : ℕ}
    (h : (E.baseChange (c.π.app i)).IsOfExactOrder P N) :
    ∃ (j : I) (g : j ⟶ i) (Q : 𝟙_ (Over (D.obj j)) ⟶ Over.mk (E.baseChange (D.map g)).structureMap),
      (E.baseChange (D.map g)).IsOfExactOrder Q N ∧
        pointsPullback (E.isPullback_baseChangeMap (c.π.app j) (c.w g))
          (E.zero_baseChangeMap _ _) Q = P := by
  obtain ⟨j, g, Q, rfl⟩ := E.exists_pointsPullback_baseChangeMap_eq hc P
  -- Whether a base change of `Q` has exact order `N` depends only on the morphism of bases.
  rw [isOfExactOrder_pointsPullback_iff, ← isOfExactOrder_pointsPullback_iff
    ((E.baseChange (D.map g)).isPullback_baseChange _) (by simp)] at h
  obtain ⟨k, l, hl⟩ := (E.baseChange (D.map g)).exists_isOfExactOrder_pointsPullback_baseChange
    hc Q h
  have hlg : D.map l ≫ D.map g = D.map (l ≫ g) := (D.map_comp l g).symm
  refine ⟨k, l ≫ g, pointsPullback (E.isPullback_baseChangeMap _ hlg) (E.zero_baseChangeMap _ _) Q,
    ?_, ?_⟩
  · rwa [isOfExactOrder_pointsPullback_iff, ← isOfExactOrder_pointsPullback_iff
      ((E.baseChange (D.map g)).isPullback_baseChange _) (by simp)]
  · have hcomp : E.baseChangeMap (c.π.app k) (c.w (l ≫ g)) ≫ E.baseChangeMap (D.map l) hlg =
        E.baseChangeMap (c.π.app j) (c.w g) := by
      rw [baseChangeMap_comp]
      congr 1
      exact c.w l
    rw [eq_pointsPullback_iff, ← hcomp, pointsPullback_left_comp_assoc, pointsPullback_left_comp,
      c.w_assoc]

end Limit

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
