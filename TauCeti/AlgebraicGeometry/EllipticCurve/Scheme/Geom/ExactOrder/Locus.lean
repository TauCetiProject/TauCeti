/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Subgroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.WeilRestriction
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# The exact-order locus

Let `E` be an elliptic curve over a scheme `S` and `D ⊆ E` a closed subscheme which is finite
locally free over `S`. Whether the base change of `D` to a scheme `S'` over `S` is a subgroup
scheme of the base change of `E` is a closed condition on `S'`: there is an ideal sheaf
`E.subgroupLocus D` on `S` such that `D_{S'}` is a subgroup scheme of `E_{S'}` exactly when
`S' ⟶ S` factors through its closed subscheme (`EllipticCurveGeom.subgroupLocus_le_ker_iff`).

By the closed-subgroup criterion, `D_{S'}` is a subgroup scheme exactly when the zero section,
the sum of two points of `D_{S'}` and the negative of a point of `D_{S'}` all lie in `D_{S'}`.
The first is the condition that `S' ⟶ S` factors through the inverse image of `D` under the zero
section. The other two say that a family parametrised by the finite locally free scheme
`D ×_S D`, respectively `D`, lies in `D`; such a condition is cut out by a Weil restriction of a
closed subscheme
(`AlgebraicGeometry.Scheme.IdealSheafData.weilRestriction_comap_le_ker_iff`).

Applied to the divisor `[P] + [2P] + ⋯ + [NP]` of an `S`-point `P`, this shows that having exact
order `N` in the sense of Drinfeld is a closed condition on the base: the base change of `P` along
`S' ⟶ S` has exact order `N` exactly when `S' ⟶ S` factors through a closed subscheme of `S`
(`EllipticCurveGeom.isOfExactOrder_pointsPullback_iff`). Applied to the universal point, the
diagonal section of `E ×_S E` over `E`, it gives the **exact-order locus** `E.exactOrderLocus N`, a
closed subscheme of `E`: for every base change `E'` of `E`, an `S'`-point `P'` of `E'` has exact
order `N` exactly when the corresponding morphism `S' ⟶ E` factors through the exact-order locus
(`EllipticCurveGeom.isOfExactOrder_iff_exactOrderLocus_le_ker_comp`). No hypothesis is placed on
`S`, which may be nonreduced, and `N` need not be invertible on it.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.subgroupLocus E D`: the ideal sheaf on `S` of the
  locus over which the finite locally free closed subscheme `V(D)` of `E` is a subgroup scheme.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderLocus E N`: the ideal sheaf on `E` of the
  exact-order locus, the closed subscheme of `E` representing points of exact order `N`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.subgroupLocus_le_ker_iff`: the universal property
  of the subgroup locus.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfExactOrder_pointsPullback_iff`: having exact
  order `N` is a closed condition on the base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfExactOrder_iff_exactOrderLocus_le_ker_comp`:
  the universal property of the exact-order locus; `isOfExactOrder_iff_exactOrderLocus_le_ker` is
  its special case for `S`-points of `E`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, 1.3.7 (the subgroup condition on a finite locally free closed subscheme is closed), §1.4
  (points of exact order `N`), 1.6.2 (the closed locus cut out by the subgroup condition) and §3.2
  (`[Γ₁(N)]`-structures).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### The subgroup locus of a finite locally free closed subscheme -/

section SubgroupLocus

variable (D : E.carrier.IdealSheafData) [IsFinite (D.subschemeι ≫ E.structureMap)]
  [Flat (D.subschemeι ≫ E.structureMap)]
  [LocallyOfFinitePresentation (D.subschemeι ≫ E.structureMap)]

/-- The ideal sheaf on `S` of the **subgroup locus** of a closed subscheme `V(D)` of `E` which is
finite locally free over `S` (Katz–Mazur, 1.3.7): a morphism `S' ⟶ S` factors through its closed
subscheme exactly when the base change of `V(D)` to `S'` is a subgroup scheme of the base change of
`E` (`EllipticCurveGeom.subgroupLocus_le_ker_iff`). It is the supremum of the ideal sheaves of three
loci: where the zero section lies in `V(D)`, where the sum of two points of `V(D)` lies in `V(D)`,
and where the negative of a point of `V(D)` lies in `V(D)`. -/
noncomputable def subgroupLocus : S.IdealSheafData :=
  D.comap E.zero ⊔
    (D.comap (pullback.map (D.subschemeι ≫ E.structureMap) (D.subschemeι ≫ E.structureMap)
      E.structureMap E.structureMap D.subschemeι D.subschemeι (𝟙 S) (by simp) (by simp) ≫
        E.addition)).weilRestriction
      (pullback.fst (D.subschemeι ≫ E.structureMap) (D.subschemeι ≫ E.structureMap) ≫
        D.subschemeι ≫ E.structureMap) ⊔
    (D.comap (D.subschemeι ≫ E.neg)).weilRestriction (D.subschemeι ≫ E.structureMap)

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S}

/-- **The universal property of the subgroup locus** (Katz–Mazur, 1.3.7). Let `g : E' ⟶ E` be a
morphism of elliptic curves lying over `f : S' ⟶ S`, forming a pullback square with the structure
morphisms and carrying the zero section of `E'` to that of `E`, and let `V(D) ⊆ E` be finite
locally free over `S`. Then the inverse image of `V(D)` in `E'` is a subgroup scheme of `E'`
exactly when `f` factors through the closed subscheme of `E.subgroupLocus D`. -/
theorem subgroupLocus_le_ker_iff (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) :
    E.subgroupLocus D ≤ f.ker ↔
      ∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
        IsMonHom (Over.homMk (D.comap g).subschemeι :
          Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap) := by
  let i' : Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap :=
    Over.homMk (D.comap g).subschemeι
  have : IsClosedImmersion i'.left := inferInstanceAs (IsClosedImmersion (D.comap g).subschemeι)
  -- `ρ : V(D.comap g) ⟶ V(D)` is the base change of `V(D)` along `f`
  let ρ := subschemeMap (D.comap g) D g (D.le_map_comap g)
  have hρ : ρ ≫ D.subschemeι = (D.comap g).subschemeι ≫ g := subschemeMap_subschemeι _ _ _ _
  have hD := D.isPullback_subschemeMap_comap E.structureMap hg
  have hi' : i'.left.ker = D.comap g := ker_subschemeι _
  rw [GroupScheme.exists_grpObj_isMonHom_iff_ker_le i', hi']
  simp only [subgroupLocus, sup_le_iff, and_assoc, i', Over.comp_left, one_left, mul_left,
    inv_left, Over.homMk_left, Over.tensorHom_left, Over.tensorObj_left,
    Over.mk_hom]
  refine and_congr ?_ (and_congr ?_ ?_)
  · -- the zero section lies in `V(D)`
    rw [← le_map_iff_comap_le, ← le_map_iff_comap_le, map_ker, map_ker, h0]
  · -- sums of two points of `V(D)` lie in `V(D)`
    refine weilRestriction_comap_le_ker_iff D _ (hD.flip.pullback_map hD.flip) ?_
    rw [Category.assoc, addition_comp_of_isPullback hg h0, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  · -- negatives of points of `V(D)` lie in `V(D)`
    refine weilRestriction_comap_le_ker_iff D _ hD.flip ?_
    rw [Category.assoc, neg_comp_of_isPullback hg h0, reassoc_of% hρ]

end SubgroupLocus

/-! ### Exact order is a closed condition -/

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S}

/-- **Having exact order `N` is a closed condition on the base** (Katz–Mazur, 1.6.2). For a pullback
square of elliptic curves over `f : S' ⟶ S` and an `S`-point `P` of `E`, the base change of `P`
has exact order `N` exactly when `f` factors through the closed subscheme of the subgroup locus of
the divisor `[P] + ⋯ + [NP]`. -/
theorem isOfExactOrder_pointsPullback_iff (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    E'.IsOfExactOrder (pointsPullback hg h0 P) N ↔
      E.subgroupLocus (E.multiplesDivisor P N) ≤ f.ker := by
  rw [subgroupLocus_le_ker_iff _ hg h0]
  -- The divisor cannot be rewritten in place, since the types in `IsOfExactOrder` depend on it.
  have key (D' : E'.carrier.IdealSheafData) (hD' : D' = E'.multiplesDivisor
      (pointsPullback hg h0 P) N) : E'.IsOfExactOrder (pointsPullback hg h0 P) N ↔
      ∃ _ : GrpObj (Over.mk (D'.subschemeι ≫ E'.structureMap)),
        IsMonHom (Over.homMk D'.subschemeι :
          Over.mk (D'.subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap) := by
    -- `IsOfExactOrder` is not exposed outside its module, so it is unfolded through its
    -- characterisation `isOfExactOrder_iff`, rather than by `Iff.rfl`.
    let i' : Over.mk (D'.subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap :=
      Over.homMk D'.subschemeι
    have : IsClosedImmersion i'.left := inferInstanceAs (IsClosedImmersion D'.subschemeι)
    have hi' : i'.left.ker = D' := ker_subschemeι _
    rw [isOfExactOrder_iff, GroupScheme.exists_grpObj_isMonHom_iff_ker_le i', hi', one_left]
    subst hD'
    rfl
  exact key _ (multiplesDivisor_pointsPullback hg h0 P N).symm

/-- A point has exact order `N` exactly when the subgroup locus of the divisor `[P] + ⋯ + [NP]` is
all of `S`. -/
theorem isOfExactOrder_iff_subgroupLocus_eq_bot (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)
    (N : ℕ) : E.IsOfExactOrder P N ↔ E.subgroupLocus (E.multiplesDivisor P N) = ⊥ := by
  rw [← le_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 S),
    ← isOfExactOrder_pointsPullback_iff (.id_horiz E.structureMap) (by simp), pointsPullback_id]

/-! ### The exact-order locus in `E` -/

variable (E) in
/-- The ideal sheaf of the **exact-order locus** in `E`: the closed subscheme of `E` over which the
universal point has exact order `N`. A point of a base change of `E` has exact order `N` exactly
when the corresponding morphism to `E` factors through it
(`EllipticCurveGeom.isOfExactOrder_iff_exactOrderLocus_le_ker_comp`). -/
noncomputable def exactOrderLocus (N : ℕ) : E.carrier.IdealSheafData :=
  (E.baseChange E.structureMap).subgroupLocus
    ((E.baseChange E.structureMap).multiplesDivisor E.universalPoint N)

/-- **The universal property of the exact-order locus** (Katz–Mazur, 1.6.2). For a pullback square
of elliptic curves `g : E' ⟶ E` over `f : S' ⟶ S`, an `S'`-point `P'` of `E'` has exact order `N`
exactly when the morphism `S' ⟶ E` given by `P'` factors through the exact-order locus. -/
theorem isOfExactOrder_iff_exactOrderLocus_le_ker_comp
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) (N : ℕ) :
    E'.IsOfExactOrder P' N ↔ E.exactOrderLocus N ≤ (P'.left ≫ g).ker := by
  conv_lhs => rw [← pointsPullback_universalPoint hg h0 P']
  exact isOfExactOrder_pointsPullback_iff _ _ _ N

/-- An `S`-point of `E` has exact order `N` exactly when it factors through the exact-order
locus. -/
theorem isOfExactOrder_iff_exactOrderLocus_le_ker (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)
    (N : ℕ) : E.IsOfExactOrder P N ↔ E.exactOrderLocus N ≤ P.left.ker := by
  simpa using
    isOfExactOrder_iff_exactOrderLocus_le_ker_comp (.id_horiz E.structureMap) (by simp) P N

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
