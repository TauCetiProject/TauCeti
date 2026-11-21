/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Topology.Category.CompactlyGenerated
public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# Coreflection of `CompactlyGenerated` in `TopCat`

Mathlib defines `CompactlyGenerated.{u, w}` as the full subcategory of `TopCat.{w}` spanned by
`u`-compactly generated spaces (`UCompactlyGeneratedSpace.{u}`), with inclusion
`CompactlyGenerated.compactlyGeneratedToTop`. Mirroring Mathlib's `GeneratedByTopCat.adj`
(`Mathlib.Topology.Convenient.Category`), we construct the right adjoint coreflector
`TopCat.toCompactlyGenerated.{u, w} : TopCat.{w} ⥤ CompactlyGenerated.{u, w}` equipping `X` with
`TopologicalSpace.compactlyGenerated.{u} X`, establish the coreflection `CompactlyGenerated.adj`,
and deduce completeness, cocompleteness, counit characterizations, and map/product functoriality:

* `CompactlyGenerated.equivalenceGeneratedByTopCat` identifies `CompactlyGenerated.{u, w}` with
  `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` over `TopCat.{w}`.
* `CompactlyGenerated.adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w}`
  has invertible unit (`CompactlyGenerated.adjUnitIso`) and identity-on-points counit, giving
  `Coreflective`, `CreatesColimits`, `HasLimits`, `HasColimits`, and
  `CompactlyGenerated.limitIsoToCompactlyGeneratedLimit`.
* `CompactlyGenerated.isIso_counit_app_iff` and `CompactlyGenerated.isHomeomorph_counit_app_iff`
  characterize counit invertibility, specializing to `u`-small Hausdorff compactly coherent (in
  particular weakly locally compact) spaces and colimits of `u`-compactly generated stages (for
  Hausdorff CW complexes, see `TauCeti.Topology.Category.CompactlyGenerated.CWComplex`).
* `TopCat.toCompactlyGeneratedProdRightHomeomorph`,
  `TopCat.toCompactlyGeneratedProdLeftHomeomorph`,
  `TopCat.toCompactlyGeneratedOfContinuousGeneratedBy`, `ContinuousMap.toCompactlyGenerated`, and
  `CompactlyGenerated.continuous_eval_toCompactlyGeneratedContinuousMap`: commutation of `k` with
  `u`-small locally compact Hausdorff products, functoriality of `k` on continuous and
  `CompHaus.{u}`-continuous maps across universes, and ordinary product evaluation continuity on
  `k(C(Y, Z)) × Y` (for homotopy preservation, see
  `TauCeti.Topology.Category.CompactlyGenerated.Homotopy`).

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe u w v v' v₁ v₂ v₃

/-- The coreflector `k : TopCat.{w} ⥤ CompactlyGenerated.{u, w}`, equipping a topological space
`X` with `TopologicalSpace.compactlyGenerated.{u} X` and acting as the identity on underlying
types and maps. -/
@[expose]
def TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w} where
  obj X :=
    { toTop := @TopCat.of X (TopologicalSpace.compactlyGenerated.{u} X)
      is_compactly_generated := TopologicalSpace.uCompactlyGeneratedSpace_compactlyGenerated.{u} X }
  map {X Y} f := InducedCategory.homMk
    (@TopCat.ofHom X Y (TopologicalSpace.compactlyGenerated.{u} X)
      (TopologicalSpace.compactlyGenerated.{u} Y)
      (@ContinuousMap.mk X Y (TopologicalSpace.compactlyGenerated.{u} X)
        (TopologicalSpace.compactlyGenerated.{u} Y) f
        (continuous_from_compactlyGenerated.{u} (t := TopologicalSpace.compactlyGenerated.{u} Y) f
          fun _ g ↦ TopologicalSpace.continuous_to_compactlyGenerated.{u} (f.hom.comp g))))

/-- `TopCat.toCompactlyGenerated` preserves the underlying carrier type definitionally. -/
theorem TopCat.coe_toCompactlyGenerated_obj (X : TopCat.{w}) :
    (TopCat.toCompactlyGenerated.{u, w}.obj X : Type w) = X := rfl

@[simp]
theorem TopCat.toCompactlyGenerated_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    (x : TopCat.toCompactlyGenerated.{u, w}.obj X) :
    TopCat.toCompactlyGenerated.{u, w}.map f x = f x := rfl

instance (X : TopCat.{w}) [T2Space X] : T2Space (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  TopologicalSpace.t2Space_compactlyGenerated.{u} X

instance (X : TopCat.{w}) [Small.{v} X] : Small.{v} (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  ‹Small.{v} X›

instance (X : TopCat.{w}) [IsEmpty X] : IsEmpty (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  ‹IsEmpty X›

instance (X : TopCat.{w}) [Unique X] : Unique (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  ‹Unique X›

instance {α : Sort*} {β : α → Sort*} (X : TopCat.{w}) [DFunLike X α β] :
    DFunLike (TopCat.toCompactlyGenerated.{u, w}.obj X) α β := ‹DFunLike X α β›

namespace CompactlyGenerated

@[simp]
theorem isoOfHomeo_hom_apply {X Y : CompactlyGenerated.{u, w}} (e : X ≃ₜ Y) (x : X) :
    (isoOfHomeo e).hom x = e x := rfl

@[simp]
theorem isoOfHomeo_inv_apply {X Y : CompactlyGenerated.{u, w}} (e : X ≃ₜ Y) (y : Y) :
    (isoOfHomeo e).inv y = e.symm y := rfl

/-- View an object of `CompactlyGenerated.{u, w}` in
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps! obj]
def toGeneratedByTopCat :
    CompactlyGenerated.{u, w} ⥤ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  obj Y := ⟨Y.toTop, inferInstanceAs (IsGeneratedBy (fun K : CompHaus.{u} ↦ K) Y)⟩
  map f := ObjectProperty.homMk f.hom

/-- View an object of `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` in
`CompactlyGenerated.{u, w}`. -/
@[expose, simps! obj_toTop]
def ofGeneratedByTopCat :
    GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) ⥤ CompactlyGenerated.{u, w} where
  obj Y :=
    { toTop := Y.obj
      is_compactly_generated := (Topology.isGeneratedBy_compHaus_iff.{u} Y.obj).1 Y.property }
  map f := InducedCategory.homMk f.hom

/-- `CompactlyGenerated.{u, w}` is equivalent to
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps!]
def equivalenceGeneratedByTopCat :
    CompactlyGenerated.{u, w} ≌ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  functor := toGeneratedByTopCat.{u, w}
  inverse := ofGeneratedByTopCat.{u, w}
  unitIso := NatIso.ofComponents fun Y ↦
    { hom := InducedCategory.homMk (𝟙 Y.toTop), inv := InducedCategory.homMk (𝟙 Y.toTop) }
  counitIso := NatIso.ofComponents fun Y ↦
    { hom := ObjectProperty.homMk (𝟙 Y.obj), inv := ObjectProperty.homMk (𝟙 Y.obj) }

instance : toGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivalenceGeneratedByTopCat.{u, w}.isEquivalence_functor

instance : ofGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivalenceGeneratedByTopCat.{u, w}.isEquivalence_inverse

@[simp]
theorem toGeneratedByTopCat_comp_toTopCat :
    toGeneratedByTopCat.{u, w} ⋙ GeneratedByTopCat.toTopCat = compactlyGeneratedToTop.{u, w} := rfl

@[simp]
theorem ofGeneratedByTopCat_comp_compactlyGeneratedToTop :
    ofGeneratedByTopCat.{u, w} ⋙ compactlyGeneratedToTop.{u, w} = GeneratedByTopCat.toTopCat := rfl

/-- Homeomorphism identifying `TopCat.toCompactlyGenerated.obj X` with
`WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X`, acting as the identity on points. -/
@[expose]
def toCompactlyGeneratedHomeomorphGeneratedBy (X : TopCat.{w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj X ≃ₜ
      WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X where
  toEquiv := (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)).symm
  continuous_toFun :=
    @continuous_from_compactlyGenerated.{u} X _ X.str _ _ fun _ g ↦
      (IsGeneratedBy.equiv_symm_comp_continuous_iff
        (X := fun K : CompHaus.{u} ↦ K) g).2 g.continuous
  continuous_invFun :=
    (@WithGeneratedByTopology.continuous_from_iff _ (fun K : CompHaus.{u} ↦ K) _ X X.str
      (TopCat.toCompactlyGenerated.{u, w}.obj X) _ _).2 fun _ g ↦
      TopologicalSpace.continuous_to_compactlyGenerated.{u} g

@[simp]
theorem toCompactlyGeneratedHomeomorphGeneratedBy_apply (X : TopCat.{w})
    (x : TopCat.toCompactlyGenerated.{u, w}.obj X) :
    toCompactlyGeneratedHomeomorphGeneratedBy.{u, w} X x =
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)).symm x := rfl

@[simp]
theorem toCompactlyGeneratedHomeomorphGeneratedBy_symm_apply (X : TopCat.{w})
    (x : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X) :
    (toCompactlyGeneratedHomeomorphGeneratedBy.{u, w} X).symm x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X) x := rfl

/-- Natural isomorphism comparing `TopCat.toCompactlyGenerated` with
`TopCat.toGeneratedByTopCat ⋙ ofGeneratedByTopCat`. Both functors act as the identity on
underlying types and maps. -/
@[expose]
def toCompactlyGeneratedIsoGeneratedBy :
    TopCat.toCompactlyGenerated.{u, w} ≅
      TopCat.toGeneratedByTopCat (X := fun K : CompHaus.{u} ↦ K) ⋙ ofGeneratedByTopCat.{u, w} :=
  NatIso.ofComponents fun X ↦
    { hom := InducedCategory.homMk
        (TopCat.isoOfHomeo (toCompactlyGeneratedHomeomorphGeneratedBy.{u, w} X)).hom
      inv := InducedCategory.homMk
        (TopCat.isoOfHomeo (toCompactlyGeneratedHomeomorphGeneratedBy.{u, w} X)).inv }

/-- The unit isomorphism `𝟭 CompactlyGenerated ≅ i ⋙ k` of `CompactlyGenerated.adj`. -/
@[expose]
def adjUnitIso :
    𝟭 CompactlyGenerated.{u, w} ≅
      compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w} :=
  NatIso.ofComponents fun Y ↦
    { hom := InducedCategory.homMk
        (@TopCat.ofHom Y Y Y.toTop.str (TopologicalSpace.compactlyGenerated.{u} Y)
          (@ContinuousMap.mk Y Y Y.toTop.str (TopologicalSpace.compactlyGenerated.{u} Y) id
            (continuous_id_iff_le.2 (UCompactlyGeneratedSpace.le_compactlyGenerated.{u} (X := Y)))))
      inv := InducedCategory.homMk
        (@TopCat.ofHom Y Y (TopologicalSpace.compactlyGenerated.{u} Y) Y.toTop.str
          (@ContinuousMap.mk Y Y (TopologicalSpace.compactlyGenerated.{u} Y) Y.toTop.str id
            (continuous_id_iff_le.2 (TopologicalSpace.compactlyGenerated_le.{u} Y)))) }

@[simp]
theorem adjUnitIso_hom_app_apply (Y : CompactlyGenerated.{u, w}) (y : Y) :
    dsimp% only [Functor.id_obj, Functor.comp_obj] (adjUnitIso.{u, w}.hom.app Y y) = y := rfl

@[simp]
theorem adjUnitIso_inv_app_apply (Y : CompactlyGenerated.{u, w}) (y : Y) :
    dsimp% only [Functor.comp_obj, Functor.id_obj] (adjUnitIso.{u, w}.inv.app Y y) = y := rfl

/-- The counit `k ⋙ i ⟶ 𝟭 TopCat` of `CompactlyGenerated.adj`, acting as the identity on
points. -/
@[expose]
def adjCounit :
    TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w} ⟶ 𝟭 TopCat.{w} where
  app X := @TopCat.ofHom X X (TopologicalSpace.compactlyGenerated.{u} X) X.str
    (@ContinuousMap.mk X X (TopologicalSpace.compactlyGenerated.{u} X) X.str id
      (continuous_id_iff_le.2 (TopologicalSpace.compactlyGenerated_le.{u} X)))

@[simp]
theorem adjCounit_app_apply (X : TopCat.{w})
    (x : (TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w}).obj X) :
    dsimp% only [Functor.comp_obj, Functor.id_obj] (adjCounit.{u, w}.app X x) = x := rfl

/-- The coreflection adjunction `i ⊣ k` between `CompactlyGenerated.{u, w}` and `TopCat.{w}`. -/
@[expose, simps]
def adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w} where
  unit := adjUnitIso.{u, w}.hom
  counit := adjCounit.{u, w}
  left_triangle_components _ := by ext; rfl
  right_triangle_components _ := by ext; rfl

@[simp]
theorem adj_homEquiv_apply {Y : CompactlyGenerated.{u, w}} {X : TopCat.{w}}
    (f : compactlyGeneratedToTop.{u, w}.obj Y ⟶ X) (y : Y) :
    adj.{u, w}.homEquiv Y X f y = f y := rfl

@[simp]
theorem adj_homEquiv_symm_apply {Y : CompactlyGenerated.{u, w}} {X : TopCat.{w}}
    (g : Y ⟶ TopCat.toCompactlyGenerated.{u, w}.obj X) (y : Y) :
    (adj.{u, w}.homEquiv Y X).symm g y = g y := rfl

instance : IsIso adj.{u, w}.unit := inferInstanceAs (IsIso adjUnitIso.{u, w}.hom)

instance : compactlyGeneratedToTop.{u, w}.IsLeftAdjoint := adj.{u, w}.isLeftAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.IsRightAdjoint := adj.{u, w}.isRightAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x

/-- `CompactlyGenerated.{u, w}` is a coreflective subcategory of `TopCat.{w}`. -/
instance instCoreflectiveCompactlyGeneratedToTop : Coreflective compactlyGeneratedToTop.{u, w} where
  R := TopCat.toCompactlyGenerated.{u, w}
  adj := adj.{u, w}

instance instCreatesColimitsOfSizeCompactlyGeneratedToTop :
    CreatesColimitsOfSize.{v', v} compactlyGeneratedToTop.{u, w} :=
  comonadicCreatesColimits _

instance {J : Type v} [Category.{v'} J] [Small.{w} J] :
    HasLimitsOfShape J CompactlyGenerated.{u, w} :=
  hasLimitsOfShape_of_coreflective compactlyGeneratedToTop.{u, w}

instance {J : Type v} [Category.{v'} J] [Small.{w} J] :
    HasColimitsOfShape J CompactlyGenerated.{u, w} :=
  hasColimitsOfShape_of_coreflective compactlyGeneratedToTop.{u, w}

instance [UnivLE.{v, w}] : HasLimitsOfSize.{v', v} CompactlyGenerated.{u, w} :=
  hasLimits_of_coreflective compactlyGeneratedToTop.{u, w}

instance [UnivLE.{v, w}] : HasColimitsOfSize.{v', v} CompactlyGenerated.{u, w} :=
  hasColimits_of_coreflective compactlyGeneratedToTop.{u, w}

/-- Limits in `CompactlyGenerated.{u, w}` are computed by taking the limit in `TopCat.{w}` and
applying the coreflector `TopCat.toCompactlyGenerated`. -/
@[expose]
def limitIsoToCompactlyGeneratedLimit {J : Type v} [Category.{v'} J]
    (F : J ⥤ CompactlyGenerated.{u, w}) [HasLimit F]
    [HasLimit (F ⋙ compactlyGeneratedToTop.{u, w})] :
    limit F ≅
      TopCat.toCompactlyGenerated.{u, w}.obj (limit (F ⋙ compactlyGeneratedToTop.{u, w})) :=
  let e : F ≅ F ⋙ compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w} :=
    F.rightUnitor.symm.trans (Functor.isoWhiskerLeft F adjUnitIso.{u, w})
  have : HasLimit (F ⋙ compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w}) :=
    hasLimit_of_iso e
  have : PreservesLimitsOfSize.{v', v} TopCat.toCompactlyGenerated.{u, w} :=
    adj.{u, w}.rightAdjoint_preservesLimits
  (HasLimit.isoOfNatIso e).trans
    (preservesLimitIso TopCat.toCompactlyGenerated.{u, w} (F ⋙ compactlyGeneratedToTop.{u, w})).symm

/-- When `X : TopCat.{w}` is `u`-compactly generated, the counit `kX ⟶ X` is a homeomorphism. -/
@[expose]
def counitHomeomorph (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    TopCat.toCompactlyGenerated.{u, w}.obj X ≃ₜ X where
  toFun := adj.{u, w}.counit.app X
  invFun := adjUnitIso.{u, w}.hom.app { toTop := X }
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (adj.{u, w}.counit.app X).hom.continuous
  continuous_invFun := (adjUnitIso.{u, w}.hom.app { toTop := X }).hom.hom.continuous

@[simp]
theorem counitHomeomorph_apply (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X]
    (x : TopCat.toCompactlyGenerated.{u, w}.obj X) : counitHomeomorph.{u, w} X x = (x : X) := rfl

@[simp]
theorem counitHomeomorph_symm_apply (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] (x : X) :
    ((counitHomeomorph.{u, w} X).symm x : X) = x := rfl

/-- When `X : TopCat.{w}` is `u`-compactly generated, the counit `(k ⋙ i).obj X ⟶ X` is an
isomorphism in `TopCat.{w}`. -/
@[expose]
def counitIso (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    (TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w}).obj X ≅ X :=
  TopCat.isoOfHomeo (counitHomeomorph.{u, w} X)

@[simp]
theorem counitIso_hom (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    (counitIso.{u, w} X).hom = adj.{u, w}.counit.app X := by ext; rfl

instance instIsIsoCounitApp (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    IsIso (adj.{u, w}.counit.app X) := counitIso_hom.{u, w} X ▸ inferInstance

instance (X : TopCat.{w}) :
    IsIso (TopCat.toCompactlyGenerated.{u, w}.map (adjCounit.{u, w}.app X)) := by
  rw [← adj_counit]; infer_instance

/-- The counit `kX ⟶ X` at `X : TopCat.{w}` is an isomorphism in `TopCat` if and only if `X` is
`u`-compactly generated. -/
theorem isIso_counit_app_iff (X : TopCat.{w}) :
    IsIso (adj.{u, w}.counit.app X) ↔ UCompactlyGeneratedSpace.{u} X :=
  ⟨fun _ ↦ let e := TopCat.homeoOfIso (asIso (adj.{u, w}.counit.app X))
    uCompactlyGeneratedSpace_of_coinduced (X := TopCat.toCompactlyGenerated.{u, w}.obj X)
      e.continuous e.coinduced_eq.symm, fun _ ↦ inferInstance⟩

/-- The counit `kX ⟶ X` at `X : TopCat.{w}` is a homeomorphism if and only if `X` is `u`-compactly
generated. -/
theorem isHomeomorph_counit_app_iff (X : TopCat.{w}) :
    IsHomeomorph (adj.{u, w}.counit.app X) ↔ UCompactlyGeneratedSpace.{u} X := by
  rw [← TopCat.isIso_iff_isHomeomorph, isIso_counit_app_iff]

/-- On any `u`-small Hausdorff compactly coherent space (in particular, any `u`-small Hausdorff
weakly locally compact space), the counit `kX ⟶ X` is an isomorphism in `TopCat`. -/
theorem isIso_counit_app_of_compactlyCoherentSpace (X : Type w) [TopologicalSpace X]
    [T2Space X] [CompactlyCoherentSpace X] [Small.{u} X] :
    IsIso (adj.{u, w}.counit.app (TopCat.of X)) := inferInstance

/-- On any colimit cocone in `TopCat` whose stages are `u`-compactly generated, the counit on the
colimit point is an isomorphism. -/
theorem isIso_counit_app_of_isColimit {J : Type v} [Category.{v'} J] {F : J ⥤ TopCat.{w}}
    {c : Cocone F} [∀ j, UCompactlyGeneratedSpace.{u} (F.obj j)] (hc : IsColimit c) :
    IsIso (adj.{u, w}.counit.app c.pt) :=
  have := TauCeti.TopCat.uCompactlyGeneratedSpace_of_isColimit hc; inferInstance

/-- Ordinary product evaluation `k(C(Y, Z)) × Y → Z` is continuous whenever the evaluation source
`Y` is locally compact. -/
theorem continuous_eval_toCompactlyGeneratedContinuousMap (Y : Type v₁) (Z : Type v₂)
    [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace Y] :
    Continuous fun p :
        TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of C(Y, Z)) × Y ↦ p.1 p.2 :=
  (continuous_eval (F := C(Y, Z))).comp <|
    (adj.{u, max v₁ v₂}.counit.app (TopCat.of C(Y, Z))).hom.continuous.prodMap continuous_id

end CompactlyGenerated

/-! ### Functoriality of `k` on maps and locally compact products -/

namespace TopCat

/-- When `L` is a `u`-small locally compact Hausdorff space, refining `X × L` by
`TopCat.toCompactlyGenerated` agrees with refining `X` alone and taking the ordinary topological
product with `L`. -/
@[expose]
def toCompactlyGeneratedProdRightHomeomorph (X : Type v₁) (L : Type v₂)
    [TopologicalSpace X] [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (X × L)) ≃ₜ
      TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X) × L :=
  let e := (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, max v₁ v₂}
      (TopCat.of (X × L))).trans <|
    (Topology.WithGeneratedByTopology.prodRightHomeomorph (fun K : CompHaus.{u} ↦ K) X L).trans <|
      (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, v₁}
        (TopCat.of X)).symm.prodCongr (Homeomorph.refl L)
  let eqvXL := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X × L)
  let eqvX := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)
  { toEquiv := Equiv.refl (X × L)
    continuous_toFun := e.continuous.congr fun p ↦ Prod.ext
      ((eqvX.apply_symm_apply _).trans (congrArg Prod.fst (eqvXL.apply_symm_apply p)))
      (congrArg Prod.snd (eqvXL.apply_symm_apply p))
    continuous_invFun := e.symm.continuous.congr fun p ↦
      (eqvXL.apply_symm_apply _).trans (Prod.ext (eqvX.apply_symm_apply p.1) rfl) }

@[simp]
theorem toCompactlyGeneratedProdRightHomeomorph_apply {X : Type v₁} {L : Type v₂}
    [TopologicalSpace X] [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (X × L))) :
    toCompactlyGeneratedProdRightHomeomorph.{u} X L p = p := rfl

@[simp]
theorem toCompactlyGeneratedProdRightHomeomorph_symm_apply {X : Type v₁} {L : Type v₂}
    [TopologicalSpace X] [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X) × L) :
    (toCompactlyGeneratedProdRightHomeomorph.{u} X L).symm p = p := rfl

/-- When `L` is a `u`-small locally compact Hausdorff space, refining `L × X` by
`TopCat.toCompactlyGenerated` agrees with taking the ordinary topological product of `L` with the
refinement of `X`. -/
@[expose]
def toCompactlyGeneratedProdLeftHomeomorph (L : Type v₁) (X : Type v₂)
    [TopologicalSpace L] [TopologicalSpace X] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (L × X)) ≃ₜ
      L × TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of X) :=
  let e := (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, max v₁ v₂}
      (TopCat.of (L × X))).trans <|
    (Topology.WithGeneratedByTopology.prodLeftHomeomorph (fun K : CompHaus.{u} ↦ K) L X).trans <|
      (Homeomorph.refl L).prodCongr
        (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, v₂} (TopCat.of X)).symm
  let eqvLX := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := L × X)
  let eqvX := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)
  { toEquiv := Equiv.refl (L × X)
    continuous_toFun := e.continuous.congr fun p ↦ Prod.ext
      (congrArg Prod.fst (eqvLX.apply_symm_apply p))
      ((eqvX.apply_symm_apply _).trans (congrArg Prod.snd (eqvLX.apply_symm_apply p)))
    continuous_invFun := e.symm.continuous.congr fun p ↦
      (eqvLX.apply_symm_apply _).trans (Prod.ext rfl (eqvX.apply_symm_apply p.2)) }

@[simp]
theorem toCompactlyGeneratedProdLeftHomeomorph_apply {L : Type v₁} {X : Type v₂}
    [TopologicalSpace L] [TopologicalSpace X] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (L × X))) :
    toCompactlyGeneratedProdLeftHomeomorph.{u} L X p = p := rfl

@[simp]
theorem toCompactlyGeneratedProdLeftHomeomorph_symm_apply {L : Type v₁} {X : Type v₂}
    [TopologicalSpace L] [TopologicalSpace X] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : L × TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of X)) :
    (toCompactlyGeneratedProdLeftHomeomorph.{u} L X).symm p = p := rfl

/-- Any `CompHaus.{u}`-continuous map `A → B` induces a morphism `kA ⟶ kB` in
`CompactlyGenerated.{u, w}` acting identically on underlying points. -/
@[expose]
def toCompactlyGeneratedOfContinuousGeneratedBy {A B : Type w}
    [TopologicalSpace A] [TopologicalSpace B]
    (φ : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) A B) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of A) ⟶
      TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of B) :=
  InducedCategory.homMk <| @TopCat.ofHom A B (TopologicalSpace.compactlyGenerated.{u} A)
    (TopologicalSpace.compactlyGenerated.{u} B) <|
    @ContinuousMap.mk A B (TopologicalSpace.compactlyGenerated.{u} A)
      (TopologicalSpace.compactlyGenerated.{u} B) φ
      (continuous_from_compactlyGenerated.{u} (t := TopologicalSpace.compactlyGenerated.{u} B) φ
        fun _ g ↦ TopologicalSpace.continuous_to_compactlyGenerated.{u} ⟨φ ∘ g, φ.prop g⟩)

@[simp]
theorem toCompactlyGeneratedOfContinuousGeneratedBy_apply {A B : Type w}
    [TopologicalSpace A] [TopologicalSpace B]
    (φ : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) A B)
    (a : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of A)) :
    toCompactlyGeneratedOfContinuousGeneratedBy.{u} φ a = φ a := rfl

end TopCat

namespace ContinuousMap

section ToCompactlyGenerated

variable {X : Type v₁} {Y : Type v₂} {Z : Type v₃}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Apply the compact-generation coreflector `k` to a continuous map `C(X, Y)`, with `X` and `Y` in
possibly distinct universes. -/
@[expose]
def toCompactlyGenerated (f : C(X, Y)) :
    C(TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X),
      TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of Y)) where
  toFun := f
  continuous_toFun :=
    continuous_from_compactlyGenerated.{u} (t := TopologicalSpace.compactlyGenerated.{u} Y) f
      fun _ g ↦ TopologicalSpace.continuous_to_compactlyGenerated.{u} (f.comp g)

@[simp]
theorem toCompactlyGenerated_apply (f : C(X, Y))
    (x : TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    f.toCompactlyGenerated.{u} x = f x := rfl

@[simp]
theorem toCompactlyGenerated_id :
    (ContinuousMap.id X).toCompactlyGenerated.{u} =
      ContinuousMap.id (TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) := rfl

@[simp]
theorem toCompactlyGenerated_comp (g : C(Y, Z)) (f : C(X, Y)) :
    (g.comp f).toCompactlyGenerated.{u} =
      g.toCompactlyGenerated.{u}.comp f.toCompactlyGenerated.{u} := rfl

end ToCompactlyGenerated

end ContinuousMap

end
