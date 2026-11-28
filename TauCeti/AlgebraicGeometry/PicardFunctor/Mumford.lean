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

/-- The normalized Mumford bundle on `G ×_S G`, rigidified along the unit of the second factor
for the projection onto the first factor. -/
def mumfordRigidifiedLineBundle (L : InvertibleSheaf G.left) :
    RigidifiedLineBundle
      (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) G) where
  lineBundle := mumfordLineBundle G L
  rigidification :=
    (Scheme.Modules.pullbackCongr (baseChangeSection_eq_lift_left η[G] G)).app _ ≪≫
      mumfordLineBundleFstRigidification G L

/-- The rigidified Mumford bundle uses the first-axis trivialization, transported along the
identification of the base-changed unit section with `x ↦ (x, 1)`. -/
theorem mumfordRigidifiedLineBundle_eq (L : InvertibleSheaf G.left) :
    mumfordRigidifiedLineBundle L =
      { lineBundle := mumfordLineBundle G L
        rigidification :=
          (Scheme.Modules.pullbackCongr (baseChangeSection_eq_lift_left η[G] G)).app _ ≪≫
            mumfordLineBundleFstRigidification G L } :=
  (rfl)

/-- The family of translated line bundles associated to `L`, rigidified along the unit.
The value on the identity morphism of `G` is the normalized Mumford bundle on `G ×_S G`. -/
def mumfordPicardMap (L : InvertibleSheaf G.left) :
    uliftYoneda.{u + 1}.obj G ⟶ rigidifiedPicardFunctor G.hom η[G].left
      (η[G].w.trans Over.tensorUnit_hom) ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (RigidifiedLineBundleClass.mk (mumfordRigidifiedLineBundle L))

/-- Under the lifted Yoneda equivalence, the Mumford family corresponds to the class of the
normalized Mumford bundle with its rigidification. -/
-- Rewrite before simplifying the object type of the composed functor.
@[simp↓]
theorem uliftYonedaEquiv_mumfordPicardMap (L : InvertibleSheaf G.left) :
    uliftYonedaEquiv (mumfordPicardMap L) =
      RigidifiedLineBundleClass.mk (mumfordRigidifiedLineBundle L) :=
  uliftYonedaEquiv.apply_symm_apply _

/-- At a point `a : T ⟶ G`, the Mumford family pulls back the normalized rigidified
bundle along the base change induced by `a`. -/
theorem mumfordPicardMap_app (L : InvertibleSheaf G.left) {T : Over S} (a : T ⟶ G) :
    (mumfordPicardMap L).app (op T) ⟨a⟩ = RigidifiedLineBundleClass.pullback
      (baseChangeSection_comp_pullback_map G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) a)
      (RigidifiedLineBundleClass.mk (mumfordRigidifiedLineBundle L)) := by
  rw [← rigidifiedPicardFunctor_map_apply]
  have h := uliftYonedaEquiv_symm_apply_app.{u + 1}
    (F := rigidifiedPicardFunctor G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) ⋙
      forget CommGrpCat) (RigidifiedLineBundleClass.mk (mumfordRigidifiedLineBundle L)) (op T)
  exact congrArg (fun f ↦ f ⟨a⟩) h

/-- The underlying line-bundle class of the Mumford family at a point `a : T ⟶ G` is the
pullback of the normalized Mumford class along `a × id`. -/
theorem toLineBundleClass_mumfordPicardMap_app_eq_pullback (L : InvertibleSheaf G.left) {T : Over S}
    (a : T ⟶ G) :
    RigidifiedLineBundleClass.toLineBundleClass ((mumfordPicardMap L).app (op T) ⟨a⟩) =
      LineBundleClass.pullback (a ▷ G).left (mumfordClass G (LineBundleClass.mk L)) := by
  have hmap : ((Over.pullback G.hom).map a).left = (a ▷ G).left := by
    apply pullback.hom_ext <;> simp
  rw [mumfordPicardMap_app, RigidifiedLineBundleClass.toLineBundleClass_pullback,
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
  rw [toLineBundleClass_mumfordPicardMap_app_eq_pullback, mumfordClass_eq_pairing,
    LineBundleClass.pullback_pairing, whiskerRight_fst, whiskerRight_snd,
    LineBundleClass.pairing_def, Hom.one_def]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- The Mumford family takes the unit point to the trivial rigidified line-bundle class. -/
@[simp]
theorem mumfordPicardMap_app_one (L : InvertibleSheaf G.left) (T : Over S) :
    ConcreteCategory.hom (C := Type (u + 1)) (X := ULift.{u + 1} (T ⟶ G))
      (Y := ToType ((rigidifiedPicardFunctor G.hom η[G].left
        (η[G].w.trans Over.tensorUnit_hom)).obj (op T)))
      ((mumfordPicardMap L).app (op T)) ⟨(1 : T ⟶ G)⟩ =
      (1 : RigidifiedLineBundleClass
        (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)) := by
  have h : ((1 : T ⟶ G) ▷ G) = snd T G ≫ lift (toUnit G ≫ η[G]) (𝟙 G) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [whiskerRight_fst, Category.assoc, lift_fst, Hom.one_def,
        comp_toUnit_assoc]
    · simp only [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id]
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)
  rw [toLineBundleClass_mumfordPicardMap_app_eq_pullback,
    RigidifiedLineBundleClass.toLineBundleClass_one, h, Over.comp_left,
    ← LineBundleClass.pullback_comp]
  simp only [Over.lift_left, Over.comp_left, Over.toUnit_left, Over.id_left,
    pullback_lift_unit_id_mumfordClass, LineBundleClass.pullback_one]

/-- The Mumford family of a line bundle pulled back from the base takes every point to the
trivial rigidified line-bundle class. -/
@[simp]
theorem mumfordPicardMap_app_pullback_hom (L : InvertibleSheaf S) {T : Over S} (a : T ⟶ G) :
    ConcreteCategory.hom (C := Type (u + 1)) (X := ULift.{u + 1} (T ⟶ G))
      (Y := ToType ((rigidifiedPicardFunctor G.hom η[G].left
        (η[G].w.trans Over.tensorUnit_hom)).obj (op T)))
      ((mumfordPicardMap ((InvertibleSheaf.pullback G.hom).obj L)).app (op T)) ⟨a⟩ = 1 := by
  -- Use the explicit class group instance so `toLineBundleClass_one` can rewrite.
  change _ = (1 : RigidifiedLineBundleClass
    (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T))
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)
  rw [toLineBundleClass_mumfordPicardMap_app_eq_pullback,
    RigidifiedLineBundleClass.toLineBundleClass_one, ← LineBundleClass.pullback_mk,
    mumfordClass_pullback_hom, LineBundleClass.pullback_one]

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
