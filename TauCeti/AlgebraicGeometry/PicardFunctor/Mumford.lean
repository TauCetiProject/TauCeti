/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Mumford.Basic
public import TauCeti.AlgebraicGeometry.PicardFunctor.Relative

/-!
# The Mumford correspondence on Picard functors

For a line bundle `L` on a monoid scheme `G` over `S`, the normalized Mumford bundle on
`G ×_S G` is a family of line bundles on `G` parametrized by the first factor. It is
rigidified along the unit of the second factor. The family defines a natural transformation
from the functor of points of `G` to its rigidified Picard functor. At a point `a : T ⟶ G`,
its underlying line-bundle class is the translate of `L_T` by `a` divided by `L_T`.
The base factors are the pullbacks of the inverse of `a^*L` and of `e^*L`.

For an abelian variety this is the family underlying the map to the dual abelian variety.

## References

* B. Conrad, *Polarizations*, Example 2.2.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.GroupScheme

noncomputable section

variable {S : Scheme.{u}} {G : Over S} [MonObj G]

private lemma baseChangeSection_unit_self :
    baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) G =
      (lift (𝟙 G) (toUnit G ≫ η[G])).left := by
  apply pullback.hom_ext <;> simp [Over.lift_left, Over.toUnit_left]

private def mumfordRigidifiedLineBundle (L : InvertibleSheaf G.left) :
    RigidifiedLineBundle
      (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) G) where
  lineBundle := mumfordLineBundle G L
  rigidification := by
    rw [baseChangeSection_unit_self]
    exact mumfordLineBundleFstRigidification G L

/-- The family of translated line bundles associated to `L`, rigidified along the unit.
The value on the identity morphism of `G` is the normalized Mumford bundle on `G ×_S G`. -/
def mumfordPicardMap (L : InvertibleSheaf G.left) :
    uliftYoneda.{u + 1}.obj G ⟶ rigidifiedPicardFunctor G.hom η[G].left
      (η[G].w.trans Over.tensorUnit_hom) ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (RigidifiedLineBundleClass.mk (mumfordRigidifiedLineBundle L))

/-- The underlying line-bundle class of the Mumford family at a point `a : T ⟶ G` is the
pullback of the normalized Mumford class along `a × id`. -/
theorem toLineBundleClass_mumfordPicardMap_app_eq_pullback (L : InvertibleSheaf G.left) {T : Over S}
    (a : T ⟶ G) :
    RigidifiedLineBundleClass.toLineBundleClass ((mumfordPicardMap L).app (op T) ⟨a⟩) =
      LineBundleClass.pullback (a ▷ G).left (mumfordClass G (LineBundleClass.mk L)) := by
  have hmap : ((Over.pullback G.hom).map a.op.unop).left = (a ▷ G).left := by
    apply pullback.hom_ext <;> simp
  -- The lifted Yoneda map evaluates by restricting the universal rigidified class along `a`.
  have happ : (mumfordPicardMap L).app (op T) ⟨a⟩ =
      (rigidifiedPicardFunctor G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom)).map a.op
        (RigidifiedLineBundleClass.mk (mumfordRigidifiedLineBundle L)) := rfl
  rw [happ, rigidifiedPicardFunctor_map_apply, RigidifiedLineBundleClass.toLineBundleClass_pullback,
    RigidifiedLineBundleClass.toLineBundleClass_mk, hmap]
  exact congrArg (LineBundleClass.pullback (a ▷ G).left) (mk_mumfordLineBundle G L)

/-- On `T`-points the normalized class is `tₐ^*L_T ⊗ L_T⁻¹` with the inverse of the
pullback of `a^*L` and the pullback of `e^*L` from the base. The product
`(fst T G ≫ a) * snd T G` sends `(t, x)` to `a(t)x`. -/
theorem toLineBundleClass_mumfordPicardMap_app (L : InvertibleSheaf G.left) {T : Over S}
    (a : T ⟶ G) :
    RigidifiedLineBundleClass.toLineBundleClass ((mumfordPicardMap L).app (op T) ⟨a⟩) =
      LineBundleClass.pullback ((fst T G ≫ a) * snd T G).left (LineBundleClass.mk L) /
        (LineBundleClass.pullback (fst T G ≫ a).left (LineBundleClass.mk L) *
         LineBundleClass.pullback (snd T G).left (LineBundleClass.mk L)) *
      LineBundleClass.pullback (toUnit (T ⊗ G) ≫ η[G]).left (LineBundleClass.mk L) := by
  have hmul : (a ▷ G) ≫ μ[G] = (fst T G ≫ a) * snd T G := by
    rw [Hom.mul_def, ← lift_whiskerRight, lift_fst_snd, Category.id_comp]
  rw [toLineBundleClass_mumfordPicardMap_app_eq_pullback, mumfordClass_apply]
  simp only [div_eq_mul_inv, LineBundleClass.pullback_mul, LineBundleClass.pullback_inv,
    LineBundleClass.pullback_comp, ← Over.comp_left, hmul, whiskerRight_fst, whiskerRight_snd,
    comp_toUnit_assoc]

/-- The Mumford family takes the unit point to the trivial rigidified line-bundle class. -/
@[simp]
theorem mumfordPicardMap_app_one (L : InvertibleSheaf G.left) (T : Over S) :
    ConcreteCategory.hom (C := Type (u + 1)) (X := ULift.{u + 1} (T ⟶ G))
      (Y := ToType ((rigidifiedPicardFunctor G.hom η[G].left
        (η[G].w.trans Over.tensorUnit_hom)).obj (op T)))
      ((mumfordPicardMap L).app (op T)) ⟨(1 : T ⟶ G)⟩ =
      (1 : RigidifiedLineBundleClass
        (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)) := by
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)
  rw [toLineBundleClass_mumfordPicardMap_app, RigidifiedLineBundleClass.toLineBundleClass_one,
    MonObj.comp_one, _root_.one_mul, Hom.one_def, div_mul_eq_mul_div, mul_comm, div_self']

/-- Tensor product of line bundles gives pointwise tensor product of their Mumford families. -/
theorem mumfordPicardMap_app_tensorProduct (L M : InvertibleSheaf G.left) {T : Over S}
    (a : T ⟶ G) :
    (mumfordPicardMap (InvertibleSheaf.tensorProduct L M)).app (op T) ⟨a⟩ =
      ((mumfordPicardMap L).app (op T) ⟨a⟩ : RigidifiedLineBundleClass
        (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)) *
        (mumfordPicardMap M).app (op T) ⟨a⟩ := by
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)
  refine Eq.trans ?_ (RigidifiedLineBundleClass.toLineBundleClass_mul
    (s := baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)
    ((mumfordPicardMap L).app (op T) ⟨a⟩) ((mumfordPicardMap M).app (op T) ⟨a⟩)).symm
  simp only [toLineBundleClass_mumfordPicardMap_app_eq_pullback,
    LineBundleClass.mk_tensorProduct, map_mul, LineBundleClass.pullback_mul]

end

end TauCeti.GroupScheme
