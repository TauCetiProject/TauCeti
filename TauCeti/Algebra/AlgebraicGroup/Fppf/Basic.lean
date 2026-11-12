/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.Category.CommAlgCat.Fppf
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Affine-group points on the affine fppf site

For a commutative ring `R`, the category `(CommAlgCat R)ᵒᵖ` is the category of affine schemes
over `Spec R`. The imported generic affine-site module equips it with the fppf topology induced by
Mathlib's fppf topology on schemes over `Spec R`. Thus a presheaf on this site has the expected
variance

```text
CommAlgCat R ⥤ Type.
```

For a commutative Hopf algebra `H`, the imported Yoneda module registers the underlying type-valued
presheaf of convolution points `A ↦ WithConv (H →ₐ[R] A)` as representable. Its representability
and subcanonicity imply that affine-group points form an fppf sheaf.

The points of a closed subgroup, cut out by a Hopf ideal, form an fppf sheaf as well. Hence
membership of a point in a closed subgroup is fppf local: a point lies in the subgroup as soon as
its restrictions along some fppf covering do.

This is the affine-site foundation for fppf sheafification of pointwise quotients. It does not
assert that such a quotient sheaf is representable; representability requires separate hypotheses.

## Main declarations

* `TauCeti.HopfAlgebra.pointsPresheaf_isSheaf`: affine-group points satisfy fppf descent.
* `TauCeti.HopfAlgebra.pointsFppfSheaf`: affine-group points bundled as an fppf sheaf.
* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_of_mem_fppfTopology`: membership in a closed
  subgroup is fppf local.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 2 and 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 1 and 14.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- **Affine-group points form an fppf sheaf.** The type-valued convolution-points presheaf is
representable on the opposite site because the original covariant points functor is
corepresentable. -/
theorem pointsPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsPresheaf H) := by
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr <|
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (pointsPresheaf H)

/-- **The group-valued convolution-points presheaf is an fppf sheaf.** This is the group-valued
form of `pointsPresheaf_isSheaf`; the forgetful functor from groups preserves limits and reflects
isomorphisms. -/
theorem pointsGroupPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsGroupPresheaf H) := by
  exact Presheaf.isSheaf_of_isSheaf_comp
    (CommAlgCat.fppfTopology R) (pointsGroupPresheaf H) (forget GrpCat.{u})
    (pointsPresheaf_isSheaf H)

/-- The convolution-points functor, bundled as a group-valued sheaf on the affine fppf site. -/
noncomputable def pointsFppfSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Sheaf (CommAlgCat.fppfTopology R) GrpCat.{u} :=
  ⟨pointsGroupPresheaf H, pointsGroupPresheaf_isSheaf H⟩

/-- The presheaf underlying `pointsFppfSheaf` is the convolution-points presheaf. -/
@[simp]
theorem pointsFppfSheaf_obj (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsFppfSheaf H).obj = pointsGroupPresheaf H :=
  by rw [pointsFppfSheaf]

/-- The points presheaf restricts a point along a morphism of affine schemes by post-composing
it with the corresponding morphism of value algebras. -/
theorem pointsPresheaf_map_op_apply (H : _root_.CommHopfAlgCat.{u} R)
    {X Y : (CommAlgCat.{u} R)ᵒᵖ} (f : Y ⟶ X) (g : points (R := R) (H := H) X.unop) :
    (pointsPresheaf H).map f.op g = mapPoints (H := H) f.unop g :=
  (rfl)

end HopfAlgebra

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- **Membership in a closed subgroup is fppf local.** If the restrictions of a point `g` of `G`
along every arrow of an fppf covering sieve lie in the closed subgroup cut out by `I`, then `g`
itself lies in it. Both `G` and the closed subgroup have fppf sheaves of points: the restrictions
glue to a point of the subgroup, which agrees with `g` because `G` is separated. -/
theorem mem_quotientPointsSubgroup_of_mem_fppfTopology (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) {X : (CommAlgCat.{u} R)ᵒᵖ} (S : Sieve X)
    (hS : S ∈ CommAlgCat.fppfTopology R X) (g : HopfAlgebra.points (R := R) (H := H) X.unop)
    (hg : ∀ ⦃Y : (CommAlgCat.{u} R)ᵒᵖ⦄ ⦃f : Y ⟶ X⦄, S f →
      HopfAlgebra.mapPoints (H := H) f.unop g ∈ quotientPointsSubgroup H I Y.unop) :
    g ∈ quotientPointsSubgroup H I X.unop := by
  let J := CommAlgCat.fppfTopology R
  have hG := ((isSheaf_iff_isSheaf_of_type J _).mp (HopfAlgebra.pointsPresheaf_isSheaf H)) S hS
  have hN := ((isSheaf_iff_isSheaf_of_type J _).mp
    (HopfAlgebra.pointsPresheaf_isSheaf (_root_.CommHopfAlgCat.quotient H I))) S hS
  -- The restrictions of `g` lie in the subgroup, so they lift to points of the quotient.
  let x : Presieve.FamilyOfElements
      (HopfAlgebra.pointsPresheaf (_root_.CommHopfAlgCat.quotient H I)) S :=
    fun Y (f : Y ⟶ X) (hf : S f) ↦ (liftQuotientPoint H I Y.unop _
      ((mem_quotientPointsSubgroup_iff H I _ _).mp (hg hf)) :
        WithConv (_root_.CommHopfAlgCat.quotient H I →ₐ[R] Y.unop))
  have hx (Y : (CommAlgCat.{u} R)ᵒᵖ) (f : Y ⟶ X) (hf : S f) :
      quotientPointsHom H I Y.unop (x f hf) = HopfAlgebra.mapPoints (H := H) f.unop g :=
    quotientPointsHom_liftQuotientPoint H I _ _ _
  have hcompat : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f k hf
    apply quotientPointsHom_injective H I Z.unop
    rw [HopfAlgebra.pointsPresheaf_map_op_apply, ← mapPoints_quotientPointsHom, hx _ _ hf,
      hx _ _ (S.downward_closed hf k), unop_comp, HopfAlgebra.mapPoints_comp,
      ConcreteCategory.comp_apply]
  -- Glue the lifts to a quotient point; it includes as `g`, having the same restrictions.
  obtain ⟨n, hn⟩ : ∃ n : HopfAlgebra.points (R := R)
      (H := _root_.CommHopfAlgCat.quotient H I) X.unop,
      ∀ ⦃Y : (CommAlgCat.{u} R)ᵒᵖ⦄ (f : Y ⟶ X) (hf : S f),
        HopfAlgebra.mapPoints (H := _root_.CommHopfAlgCat.quotient H I) f.unop n = x f hf :=
    ⟨hN.amalgamate x hcompat, fun _ f hf ↦ hN.valid_glue hcompat f hf⟩
  have hglue : quotientPointsHom H I X.unop n = g := by
    refine hG.isSeparatedFor.ext fun Y f hf ↦ ?_
    rw [HopfAlgebra.pointsPresheaf_map_op_apply, HopfAlgebra.pointsPresheaf_map_op_apply,
      mapPoints_quotientPointsHom, hn f hf, hx _ _ hf]
  exact hglue ▸ quotientPointsHom_mem_quotientPointsSubgroup H I X.unop n

end CommHopfAlgCat

end TauCeti
