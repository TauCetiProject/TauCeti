/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.CommGrp
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Locus
public import TauCeti.AlgebraicGeometry.Limits.GrpObj
public import TauCeti.CategoryTheory.Monoidal.Grp.Subobject
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Spreading out points of exact order `N`

Let `S = lim Dⱼ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps, and let `E` be an elliptic curve over a member `Dᵢ`. This file spreads out
points of `E` and Drinfeld's points of exact order `N`, the `[Γ₁(N)]`-structures of Katz and Mazur,
from `S` to some member `Dⱼ`.

* Every `S`-point of the base change `E_S` is the base change of a `Dⱼ`-point of the base change
  `E_{Dⱼ}`, for some `j ⟶ i` (`EllipticCurveGeom.exists_pointsPullback_baseChangeMap_eq`). This is
  the descent of morphisms to a scheme locally of finite presentation (Stacks 01ZC), applied to
  the composite `S ⟶ E_S ⟶ E`.
* If the base change of a `Dᵢ`-point `P` to `S` has exact order `N`, then so does its base change
  to some `Dⱼ` (`EllipticCurveGeom.exists_isOfExactOrder_pointsPullback_baseChange`). Having exact
  order `N` says that the divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup scheme, a scheme-theoretic
  condition rather than a condition on points, and the divisor is finite locally free, so this is
  the spreading out of subgroup structures on finitely presented schemes
  (`CategoryTheory.Limits.IsLimit.exists_grpObj_isMonHom_overPullback`).
* Combining the two, every `S`-point of exact order `N` of `E_S` is the base change of a `Dⱼ`-point
  of exact order `N` of `E_{Dⱼ}`, for some `j ⟶ i`
  (`EllipticCurveGeom.exists_isOfExactOrder_pointsPullback_baseChangeMap_eq`).

The base change of `E` along `j ⟶ i` is related to its base change to `S` by the canonical map
`E.baseChangeMap`, which forms a pullback square with the structure morphisms
(`EllipticCurveGeom.isPullback_baseChangeMap`); base change of points is taken along this square.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfExactOrder_pointsPullback_baseChange_iff`: the
  base change of `P` along `f` has exact order `N` exactly when the base change along `f` of the
  divisor `[P] + ⋯ + [NP]` is a subgroup scheme of the base change of `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_pointsPullback_baseChangeMap_eq`: points
  spread out along cofiltered limits.
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

section ExactOrder

variable {S T : Scheme.{u}} (E : EllipticCurveGeom S)

open scoped Obj in
/-- **Exact order after base change.** The base change along `f : T ⟶ S` of an `S`-point `P` of
`E` has exact order `N` exactly when the base change along `f` of the divisor
`[P] + [2P] + ⋯ + [NP]` carries a group law for which the base change of its inclusion into `E` is
a homomorphism, that is, when it is a subgroup scheme of the base change of `E`. -/
theorem isOfExactOrder_pointsPullback_baseChange_iff (f : T ⟶ S)
    (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    (E.baseChange f).IsOfExactOrder (pointsPullback (E.isPullback_baseChange f) (by simp) P) N ↔
      ∃ _ : GrpObj ((Over.pullback f).obj
          (Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap))),
        IsMonHom ((Over.pullback f).map (Over.homMk (E.multiplesDivisor P N).subschemeι :
          Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
            Over.mk E.structureMap)) := by
  set D := E.multiplesDivisor P N
  set g := (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f
  have hg : IsPullback g (E.baseChange f).structureMap E.structureMap f :=
    E.isPullback_baseChange f
  have h0 : (E.baseChange f).zero ≫ g = f ≫ E.zero := by simp [g]
  -- The closed subscheme `V(D.comap g)` of the base change is the base change of `V(D)`.
  have hD := D.isPullback_subschemeMap_comap E.structureMap hg
  let ε : Over.mk ((D.comap g).subschemeι ≫ (E.baseChange f).structureMap) ≅
      (Over.pullback f).obj (Over.mk (D.subschemeι ≫ E.structureMap)) :=
    Over.isoMk hD.isoPullback (by simp)
  let e := E.baseChangeOverIso f
  let i : Over.mk ((D.comap g).subschemeι ≫ (E.baseChange f).structureMap) ⟶
      Over.mk (E.baseChange f).structureMap := Over.homMk (D.comap g).subschemeι
  have hε : ε.hom ≫ (Over.pullback f).map
      (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ E.structureMap) ⟶
        Over.mk E.structureMap) = i ≫ e.hom := by
    ext1
    apply pullback.hom_ext <;> simp [ε, e, i, g]
  rw [← Iso.exists_grpObj_isMonHom_iff ε hε]
  -- The divisor cannot be rewritten in place, since the types in `IsOfExactOrder` depend on it.
  have key (D' : (E.baseChange f).carrier.IdealSheafData)
      (hD' : D' = (E.baseChange f).multiplesDivisor (pointsPullback hg h0 P) N) :
      (E.baseChange f).IsOfExactOrder (pointsPullback hg h0 P) N ↔
        ∃ _ : GrpObj (Over.mk (D'.subschemeι ≫ (E.baseChange f).structureMap)),
          IsMonHom (Over.homMk D'.subschemeι :
            Over.mk (D'.subschemeι ≫ (E.baseChange f).structureMap) ⟶
              Over.mk (E.baseChange f).structureMap) := by
    subst hD'
    exact isOfExactOrder_def
  rw [key _ (multiplesDivisor_pointsPullback hg h0 P N).symm]
  -- Composition with the isomorphism of group schemes `e` does not change the homomorphisms.
  refine ⟨fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, ?_⟩⟩
  -- The goal displays the `let`-bound inclusion `i` unfolded; restate it through `i` to rewrite.
  change IsMonHom i
  rw [show i = (i ≫ e.hom) ≫ e.inv by simp]
  infer_instance

end ExactOrder

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I}
  (E : EllipticCurveGeom (D.obj i))

include hc in
/-- **Spreading out points.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps, and let `E` be an elliptic curve over a member
`Dᵢ`. Every `S`-point of the base change `E_S` of `E` is, for some `j ⟶ i`, the base change of a
`Dⱼ`-point of the base change `E_{Dⱼ}`. -/
theorem exists_pointsPullback_baseChangeMap_eq
    (P : 𝟙_ (Over c.pt) ⟶ Over.mk (E.baseChange (c.π.app i)).structureMap) :
    ∃ (j : I) (g : j ⟶ i) (Q : 𝟙_ (Over (D.obj j)) ⟶ Over.mk (E.baseChange (D.map g)).structureMap),
      pointsPullback (E.isPullback_baseChangeMap (c.π.app j) (c.w g))
        (E.zero_baseChangeMap _ _) Q = P := by
  have hg := E.isPullback_baseChange (c.π.app i)
  -- The `S`-point of `E_S` is a morphism `a : S ⟶ E` over `Dᵢ`, which descends to some `Dⱼ`.
  set a := P.left ≫ (E.baseChangeIso (c.π.app i)).hom ≫ pullback.fst _ _
  have ha : a ≫ E.structureMap = c.π.app i := by
    simp [a, hg.w]
  have {j k : Over i} (f : j ⟶ k) : IsAffineHom ((Over.forget i ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  have (j : Over i) : CompactSpace ((Over.forget i ⋙ D).obj j) :=
    inferInstanceAs (CompactSpace (D.obj j.left))
  have (j : Over i) : QuasiSeparatedSpace ((Over.forget i ⋙ D).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  let q : Over.forget i ⋙ D ⟶ (Functor.const _).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality j k f := by simp [← D.map_comp] }
  obtain ⟨j, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over.forget i ⋙ D) q E.structureMap _
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc) a
    (by ext j; exact (c.w j.hom).trans ha.symm)
  have hj := E.isPullback_baseChange (D.map j.hom)
  refine ⟨j.left, j.hom, (pointsBaseChangeEquiv hj (by simp)).symm (Over.homMk b hb'), ?_⟩
  refine ((eq_pointsPullback_iff _ _).mpr ?_).symm
  apply hj.hom_ext
  · simpa [a] using hb.symm
  · simp

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
