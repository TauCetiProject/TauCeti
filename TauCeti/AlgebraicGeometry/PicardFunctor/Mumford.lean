/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Mumford.Basic
public import TauCeti.AlgebraicGeometry.PicardFunctor.BaseChange

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

/-- The Mumford family depends only on the line-bundle class of its input. -/
theorem mumfordPicardMap_congr {L M : InvertibleSheaf G.left}
    (h : LineBundleClass.mk L = LineBundleClass.mk M) :
    mumfordPicardMap L = mumfordPicardMap M := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_mumfordPicardMap, uliftYonedaEquiv_mumfordPicardMap]
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) G)
  simp only [RigidifiedLineBundleClass.toLineBundleClass_mk,
    mumfordRigidifiedLineBundle_eq, mk_mumfordLineBundle, h]

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

/-- At a point `a`, the Mumford family for `f^*L` is the pullback along `id × f` of the
Mumford family for `L` at `a ≫ f`. -/
theorem mumfordPicardMap_app_pullback {H : Over S} [MonObj H] (f : G ⟶ H) [IsMonHom f]
    (L : InvertibleSheaf H.left) {T : Over S} (a : T ⟶ G) :
    (mumfordPicardMap ((InvertibleSheaf.pullback f.left).obj L)).app (op T) ⟨a⟩ =
      RigidifiedLineBundleClass.pullback (h := (T ◁ f).left) (g := 𝟙 T.left) (by
        rw [baseChangeSection_eq_lift_left η[G], baseChangeSection_eq_lift_left η[H],
          Category.id_comp, ← Over.comp_left]
        apply congrArg (fun k : T ⟶ T ⊗ H ↦ k.left)
        simp only [lift_whiskerLeft, Category.assoc, IsMonHom.one_hom])
        ((mumfordPicardMap L).app (op T) ⟨a ≫ f⟩) := by
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) T)
  have h : (a ▷ G) ≫ (f ⊗ₘ f) = (T ◁ f) ≫ (a ≫ f) ▷ H := by
    rw [whiskerRight_comp_tensorHom, tensorHom_def']
  refine Eq.trans ?_ (RigidifiedLineBundleClass.toLineBundleClass_pullback _ _).symm
  simp only [toLineBundleClass_mumfordPicardMap_app_eq_pullback, ← LineBundleClass.pullback_mk,
    ← pullback_mumfordClass, LineBundleClass.pullback_comp, ← Over.comp_left, h]

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
  simp only [pullback_lift_unit_id_mumfordClass, LineBundleClass.pullback_one]

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


section BaseChange

variable {S S' : Scheme.{u}} {G : Over S} [MonObj G] (g : S' ⟶ S)

private def mumfordBaseChangeOverIso :
    (Over.pullback g).obj G ≅ Over.mk (pullback.fst g G.hom) :=
  Over.isoMk (pullbackSymmetry _ _) (by simp)

private abbrev transportedMonObj : MonObj (Over.mk (pullback.fst g G.hom)) :=
  letI := Functor.monObjObj (F := Over.pullback g) G
  MonObj.ofIso (mumfordBaseChangeOverIso g)

private theorem mumfordBaseChange_one :
    (transportedMonObj (G := G) g).one =
      Over.homMk (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g))
        (baseChangeSection_fst ..) := by
  apply Over.OverMorphism.ext
  have hε : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ pullback.snd (𝟙 S) g =
      𝟙 S' := by simp
  have hε' : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ pullback.fst (𝟙 S) g = g := by
    calc
      _ = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          (pullback.fst (𝟙 S) g ≫ 𝟙 S) := by simp
      _ = g := by
        rw [pullback.condition, ← Category.assoc, hε]
        simp
  -- Expose the transported unit so both sides can be compared by their pullback projections.
  change (Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map η[G] ≫
    (mumfordBaseChangeOverIso g).hom).left = _
  apply pullback.hom_ext
  · simpa [mumfordBaseChangeOverIso] using
      (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g)).symm
  · simpa [mumfordBaseChangeOverIso, hε'] using
      (baseChangeSection_snd G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g)).symm

/-- The monoid structure on `S' ×_S G`, with the base-changed unit as its section. Use this
structure to evaluate the Mumford family in the domain of the rigidified Picard comparison. -/
abbrev mumfordBaseChangeMonObj : MonObj (Over.mk (pullback.fst g G.hom)) :=
  letI := Functor.monObjObj (F := Over.pullback g) G
  let m := MonObj.ofIso (Over.isoMk (pullbackSymmetry G.hom g)
    (by simp) : (Over.pullback g).obj G ≅ Over.mk (pullback.fst g G.hom))
  { m with
    one := Over.homMk
      (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g))
      (baseChangeSection_fst ..)
    one_mul := by
      have eq := mumfordBaseChange_one (G := G) g
      change m.one = _ at eq
      simpa only [eq] using m.one_mul
    mul_one := by
      have eq := mumfordBaseChange_one (G := G) g
      change m.one = _ at eq
      simpa only [eq] using m.mul_one }

attribute [local instance] mumfordBaseChangeMonObj

private theorem mumfordBaseChange_mul :
    μ[Over.mk (pullback.fst g G.hom)].left ≫ pullback.snd g G.hom =
      pullback.map _ _ _ _ (pullback.snd g G.hom) (pullback.snd g G.hom) g
        pullback.condition pullback.condition ≫ μ[G].left := by
  -- The multiplication first swaps the factors back, then uses the product comparison.
  change (((mumfordBaseChangeOverIso g).inv ⊗ₘ (mumfordBaseChangeOverIso g).inv) ≫
      Functor.LaxMonoidal.μ (Over.pullback g) G G ≫ (Over.pullback g).map μ[G] ≫
      (mumfordBaseChangeOverIso g).hom).left ≫ _ = _
  simp only [Over.comp_left, Category.assoc, mumfordBaseChangeOverIso, Over.isoMk_hom_left,
    pullbackSymmetry_hom_comp_snd, Over.pullback_map_left, pullback.lift_fst]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.μ_pullback_left_fst_fst, Over.tensorHom_left,
      pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Over.mk_hom,
      Over.isoMk_inv_left, pullbackSymmetry_inv_comp_fst]
  · simp only [Category.assoc, Over.μ_pullback_left_fst_snd, Over.tensorHom_left,
      pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Over.mk_hom,
      Over.isoMk_inv_left, pullbackSymmetry_inv_comp_fst]

private theorem pullback_toLineBundleClass_mumfordPicardMap_app_baseChange
    (L : InvertibleSheaf G.left) {T : Over S'} (a : T ⟶ Over.mk (pullback.fst g G.hom))
    (a₀ : (Over.map g).obj T ⟶ G) (ha₀ : a₀.left = a.left ≫ pullback.snd g G.hom) :
    LineBundleClass.pullback (pullbackRightPullbackFstIso g G.hom T.hom).inv
      (RigidifiedLineBundleClass.toLineBundleClass
        ((mumfordPicardMap ((InvertibleSheaf.pullback (pullback.snd g G.hom)).obj L)).app
          (op T) ⟨a⟩)) =
      RigidifiedLineBundleClass.toLineBundleClass
        ((mumfordPicardMap L).app (op ((Over.map g).obj T)) ⟨a₀⟩) := by
  let G' : Over S' := Over.mk (pullback.fst g G.hom)
  let q := (pullbackRightPullbackFstIso g G.hom T.hom).inv
  rw [toLineBundleClass_mumfordPicardMap_app, toLineBundleClass_mumfordPicardMap_app]
  simp only [← LineBundleClass.pullback_mk, div_eq_mul_inv, LineBundleClass.pullback_mul,
    LineBundleClass.pullback_inv, LineBundleClass.pullback_comp]
  have hfst : q ≫ (fst T G' ≫ a).left ≫ pullback.snd g G.hom =
      (fst ((Over.map g).obj T) G ≫ a₀).left := by
    simp [q, G', ha₀]
  have hsnd : q ≫ (snd T G').left ≫ pullback.snd g G.hom =
      (snd ((Over.map g).obj T) G).left := by
    simp [q, G']
  have hmul : q ≫ ((fst T G' ≫ a) * snd T G').left ≫ pullback.snd g G.hom =
      ((fst ((Over.map g).obj T) G ≫ a₀) * snd ((Over.map g).obj T) G).left := by
    simp only [Hom.mul_def, Over.comp_left, Category.assoc, mumfordBaseChange_mul]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
        G', Over.lift_left, Over.mk_hom]
      exact hfst
    · simp only [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc,
        G', Over.lift_left, Over.mk_hom]
      exact hsnd
  have hone : q ≫ (toUnit (T ⊗ G') ≫ η[G']).left ≫ pullback.snd g G.hom =
      (toUnit (((Over.map g).obj T) ⊗ G) ≫ η[G]).left := by
    have h := baseChangeSection_snd G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom)
      (Over.mk g)
    -- The class uses the terminal map, whose underlying map is the structure morphism.
    change
      q ≫ (pullback.fst T.hom (pullback.fst g G.hom) ≫ T.hom) ≫
        baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g) ≫
        pullback.snd g G.hom =
      (toUnit (((Over.map g).obj T) ⊗ G) ≫ η[G]).left
    simp only [Over.mk_hom] at h
    simp [q, h, Over.comp_left]
  rw [hmul, hfst, hsnd, hone]

/-- The comparison of rigidified Picard functors carries the Mumford family of a pulled-back
bundle to the original Mumford family evaluated at the corresponding point. -/
theorem mumfordPicardMap_app_baseChange (L : InvertibleSheaf G.left) {T : Over S'}
    (a : T ⟶ Over.mk (pullback.fst g G.hom)) :
    (rigidifiedPicardFunctorBaseChangeIso G.hom g η[G].left
      (η[G].w.trans Over.tensorUnit_hom)).hom.app (op T)
      ((mumfordPicardMap ((InvertibleSheaf.pullback (pullback.snd g G.hom)).obj L)).app (op T)
        ⟨a⟩) =
      (mumfordPicardMap L).app (op ((Over.map g).obj T)) ⟨Over.homMk
        (a.left ≫ pullback.snd g G.hom)
        (by
          rw [Category.assoc, ← pullback.condition, ← Category.assoc]
          exact congrArg (fun f ↦ f ≫ g) a.w)⟩ := by
  apply RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) ((Over.map g).obj T))
  let b : RigidifiedLineBundleClass (baseChangeSection (pullback.fst g G.hom)
      (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g))
      (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g)) T) :=
    (mumfordPicardMap ((InvertibleSheaf.pullback (pullback.snd g G.hom)).obj L)).app (op T) ⟨a⟩
  -- Use the explicit class carrier because the functor's object only unfolds to it during
  -- definitional equality checking, so the comparison lemma cannot rewrite the original term.
  change RigidifiedLineBundleClass.toLineBundleClass
      ((rigidifiedPicardFunctorBaseChangeIso G.hom g η[G].left
        (η[G].w.trans Over.tensorUnit_hom)).hom.app (op T) b) = _
  have hb := rigidifiedPicardFunctorBaseChangeIso_hom_app_apply G.hom g η[G].left
    (η[G].w.trans Over.tensorUnit_hom) (op T) b
  refine (congrArg RigidifiedLineBundleClass.toLineBundleClass hb).trans ?_
  rw [RigidifiedLineBundleClass.toLineBundleClass_pullback]
  exact pullback_toLineBundleClass_mumfordPicardMap_app_baseChange g L a _ rfl


end BaseChange

end

end TauCeti.GroupScheme
