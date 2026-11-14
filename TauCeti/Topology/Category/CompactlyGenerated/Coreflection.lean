/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.CompactlyGenerated
public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# Coreflection of `CompactlyGenerated` in `TopCat`

Mathlib defines `CompactlyGenerated.{u, w}` as the full subcategory of `TopCat.{w}` spanned by
`u`-compactly generated spaces (`UCompactlyGeneratedSpace.{u}`), with inclusion functor
`CompactlyGenerated.compactlyGeneratedToTop`. Here we construct the right adjoint coreflector
`TopCat.toCompactlyGenerated.{u, w} : TopCat.{w} ⥤ CompactlyGenerated.{u, w}` equipping each
space `X` with `TopologicalSpace.compactlyGenerated.{u} X` without changing its underlying type or
maps, establish the coreflection `CompactlyGenerated.adj`, and deduce completeness, cocompleteness,
and counit comparisons:

* `CompactlyGenerated.equivalenceGeneratedByTopCat` identifies `CompactlyGenerated.{u, w}` with
  `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` over `TopCat.{w}`.
* `CompactlyGenerated.adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w}`
  has invertible unit (`CompactlyGenerated.adjUnitIso`) and identity-on-points counit, making
  `CompactlyGenerated.{u, w}` a coreflective subcategory of `TopCat.{w}` that creates colimits and
  possesses all small limits and colimits (`CompactlyGenerated.limitIsoToCompactlyGeneratedLimit`
  computes limits in `TopCat` followed by `TopCat.toCompactlyGenerated`).
* The counit at `X : TopCat.{w}` is an isomorphism (equivalently, a homeomorphism) if and only if
  `X` is `u`-compactly generated (`CompactlyGenerated.isIso_counit_app_iff`,
  `CompactlyGenerated.isHomeomorph_counit_app_iff`). In particular, it is an isomorphism on every
  `u`-small Hausdorff weakly locally compact space (such as a point or `unitInterval`), on every
  Hausdorff CW complex, and on every colimit in `TopCat` of `u`-compactly generated stages.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Math. Z. 119
  (1971), 11–28.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix A.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe u w v v'

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
          fun S g ↦ by
            let p : (Σ (i : (T : CompHaus.{u}) × C(T, Y)), i.fst) → Y := fun ⟨⟨_, i⟩, s⟩ ↦ i s
            suffices ∀ (i : (T : CompHaus.{u}) × C(T, Y)),
                Continuous[inferInstance, TopologicalSpace.compactlyGenerated.{u} Y]
                  (fun a : i.fst ↦ p ⟨i, a⟩) from
              this ⟨S, f.hom.comp g⟩
            rw [← @continuous_sigma_iff]
            exact continuous_coinduced_rng)))

/-- `TopCat.toCompactlyGenerated` preserves the underlying carrier type definitionally. -/
theorem TopCat.coe_toCompactlyGenerated_obj (X : TopCat.{w}) :
    (TopCat.toCompactlyGenerated.{u, w}.obj X : Type w) = X :=
  rfl

@[simp]
theorem TopCat.toCompactlyGenerated_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    (x : TopCat.toCompactlyGenerated.{u, w}.obj X) :
    TopCat.toCompactlyGenerated.{u, w}.map f x = f x :=
  rfl

instance (X : TopCat.{w}) [T2Space X] : T2Space (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  TopologicalSpace.t2Space_compactlyGenerated.{u} X

instance (X : TopCat.{w}) [Small.{v} X] : Small.{v} (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  ‹Small.{v} X›

instance (X : TopCat.{w}) [IsEmpty X] : IsEmpty (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  ‹IsEmpty X›

instance (X : TopCat.{w}) [Unique X] : Unique (TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  ‹Unique X›

instance {α : Sort*} {β : α → Sort*} (X : TopCat.{w}) [DFunLike X α β] :
    DFunLike (TopCat.toCompactlyGenerated.{u, w}.obj X) α β :=
  ‹DFunLike X α β›

namespace CompactlyGenerated

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
    { hom := InducedCategory.homMk (𝟙 Y.toTop)
      inv := InducedCategory.homMk (𝟙 Y.toTop) }
  counitIso := NatIso.ofComponents fun Y ↦
    { hom := ObjectProperty.homMk (𝟙 Y.obj)
      inv := ObjectProperty.homMk (𝟙 Y.obj) }

instance : toGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivalenceGeneratedByTopCat.{u, w}.isEquivalence_functor

instance : ofGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivalenceGeneratedByTopCat.{u, w}.isEquivalence_inverse

@[simp]
theorem toGeneratedByTopCat_comp_toTopCat :
    toGeneratedByTopCat.{u, w} ⋙ GeneratedByTopCat.toTopCat = compactlyGeneratedToTop.{u, w} :=
  rfl

@[simp]
theorem ofGeneratedByTopCat_comp_compactlyGeneratedToTop :
    ofGeneratedByTopCat.{u, w} ⋙ compactlyGeneratedToTop.{u, w} = GeneratedByTopCat.toTopCat :=
  rfl

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
      (TopCat.toCompactlyGenerated.{u, w}.obj X) _ _).2 fun S g ↦ by
      let p : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
      suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
          Continuous[inferInstance, TopologicalSpace.compactlyGenerated.{u} X]
            (fun a : i.fst ↦ p ⟨i, a⟩) from
        this ⟨S, g⟩
      rw [← @continuous_sigma_iff]
      exact continuous_coinduced_rng

@[simp]
theorem toCompactlyGeneratedHomeomorphGeneratedBy_apply (X : TopCat.{w})
    (x : TopCat.toCompactlyGenerated.{u, w}.obj X) :
    toCompactlyGeneratedHomeomorphGeneratedBy.{u, w} X x =
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)).symm x :=
  rfl

@[simp]
theorem toCompactlyGeneratedHomeomorphGeneratedBy_symm_apply (X : TopCat.{w})
    (x : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X) :
    (toCompactlyGeneratedHomeomorphGeneratedBy.{u, w} X).symm x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X) x :=
  rfl

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
            (continuous_id_iff_le.2
              (UCompactlyGeneratedSpace.le_compactlyGenerated.{u} (X := Y)))))
      inv := InducedCategory.homMk
        (@TopCat.ofHom Y Y (TopologicalSpace.compactlyGenerated.{u} Y) Y.toTop.str
          (@ContinuousMap.mk Y Y (TopologicalSpace.compactlyGenerated.{u} Y) Y.toTop.str id
            (continuous_id_iff_le.2 (TopologicalSpace.compactlyGenerated_le.{u} Y)))) }

@[simp]
theorem adjUnitIso_hom_app_apply (Y : CompactlyGenerated.{u, w}) (y : Y) :
    dsimp% only [Functor.id_obj, Functor.comp_obj] (adjUnitIso.{u, w}.hom.app Y y) = y :=
  rfl

@[simp]
theorem adjUnitIso_inv_app_apply (Y : CompactlyGenerated.{u, w}) (y : Y) :
    dsimp% only [Functor.comp_obj, Functor.id_obj] (adjUnitIso.{u, w}.inv.app Y y) = y :=
  rfl

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
    dsimp% only [Functor.comp_obj, Functor.id_obj] (adjCounit.{u, w}.app X x) = x :=
  rfl

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
    adj.{u, w}.homEquiv Y X f y = f y :=
  rfl

@[simp]
theorem adj_homEquiv_symm_apply {Y : CompactlyGenerated.{u, w}} {X : TopCat.{w}}
    (g : Y ⟶ TopCat.toCompactlyGenerated.{u, w}.obj X) (y : Y) :
    (adj.{u, w}.homEquiv Y X).symm g y = g y :=
  rfl

instance : IsIso adj.{u, w}.unit :=
  inferInstanceAs (IsIso adjUnitIso.{u, w}.hom)

instance : compactlyGeneratedToTop.{u, w}.IsLeftAdjoint :=
  adj.{u, w}.isLeftAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.IsRightAdjoint :=
  adj.{u, w}.isRightAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.Faithful where
  map_injective h := by
    ext x
    exact ConcreteCategory.congr_hom h x

/-- `CompactlyGenerated.{u, w}` is a coreflective subcategory of `TopCat.{w}`. -/
instance instCoreflectiveCompactlyGeneratedToTop : Coreflective compactlyGeneratedToTop.{u, w} where
  R := TopCat.toCompactlyGenerated.{u, w}
  adj := adj.{u, w}

instance instCreatesColimitsCompactlyGeneratedToTop :
    CreatesColimits compactlyGeneratedToTop.{u, w} :=
  comonadicCreatesColimits _

instance : HasLimits CompactlyGenerated.{u, w} :=
  hasLimits_of_coreflective compactlyGeneratedToTop.{u, w}

instance : HasColimits CompactlyGenerated.{u, w} :=
  hasColimits_of_hasColimits_createsColimits compactlyGeneratedToTop.{u, w}

/-- Limits in `CompactlyGenerated.{u, w}` are computed by taking the limit in `TopCat.{w}` and
applying the coreflector `TopCat.toCompactlyGenerated`. -/
def limitIsoToCompactlyGeneratedLimit {J : Type v} [Category.{v'} J]
    (F : J ⥤ CompactlyGenerated.{u, w}) [HasLimit F]
    [HasLimit (F ⋙ compactlyGeneratedToTop.{u, w})] :
    limit F ≅
      TopCat.toCompactlyGenerated.{u, w}.obj (limit (F ⋙ compactlyGeneratedToTop.{u, w})) := by
  let e : F ≅ F ⋙ compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w} :=
    F.rightUnitor.symm.trans (Functor.isoWhiskerLeft F adjUnitIso.{u, w})
  have : HasLimit (F ⋙ compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w}) :=
    hasLimit_of_iso e
  have : PreservesLimitsOfSize.{v', v} TopCat.toCompactlyGenerated.{u, w} :=
    adj.{u, w}.rightAdjoint_preservesLimits
  exact (HasLimit.isoOfNatIso e).trans
    (preservesLimitIso TopCat.toCompactlyGenerated.{u, w}
      (F ⋙ compactlyGeneratedToTop.{u, w})).symm

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
    (x : TopCat.toCompactlyGenerated.{u, w}.obj X) :
    counitHomeomorph.{u, w} X x = (x : X) :=
  rfl

@[simp]
theorem counitHomeomorph_symm_apply (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] (x : X) :
    ((counitHomeomorph.{u, w} X).symm x : X) = x :=
  rfl

/-- When `X : TopCat.{w}` is `u`-compactly generated, the counit `(k ⋙ i).obj X ⟶ X` is an
isomorphism in `TopCat.{w}`. -/
@[expose]
def counitIso (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    (TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w}).obj X ≅ X :=
  TopCat.isoOfHomeo (counitHomeomorph.{u, w} X)

@[simp]
theorem counitIso_hom (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    (counitIso.{u, w} X).hom = adj.{u, w}.counit.app X := by
  ext
  rfl

instance instIsIsoCounitApp (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    IsIso (adj.{u, w}.counit.app X) := by
  rw [← counitIso_hom]
  infer_instance

/-- The counit `kX ⟶ X` at `X : TopCat.{w}` is an isomorphism in `TopCat` if and only if `X` is
`u`-compactly generated. -/
theorem isIso_counit_app_iff (X : TopCat.{w}) :
    IsIso (adj.{u, w}.counit.app X) ↔ UCompactlyGeneratedSpace.{u} X := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e := TopCat.homeoOfIso (asIso (adj.{u, w}.counit.app X))
  exact uCompactlyGeneratedSpace_of_coinduced (X := TopCat.toCompactlyGenerated.{u, w}.obj X)
    e.continuous e.coinduced_eq.symm

/-- The counit `kX ⟶ X` at `X : TopCat.{w}` is a homeomorphism if and only if `X` is `u`-compactly
generated. -/
theorem isHomeomorph_counit_app_iff (X : TopCat.{w}) :
    IsHomeomorph (adj.{u, w}.counit.app X) ↔ UCompactlyGeneratedSpace.{u} X := by
  rw [← TopCat.isIso_iff_isHomeomorph, isIso_counit_app_iff]

/-- On any `u`-small Hausdorff weakly locally compact space, the counit `kX ⟶ X` is an isomorphism
in `TopCat`. -/
theorem isIso_counit_app_of_weaklyLocallyCompactSpace (X : Type w) [TopologicalSpace X]
    [T2Space X] [WeaklyLocallyCompactSpace X] [Small.{u} X] :
    IsIso (adj.{u, w}.counit.app (TopCat.of X)) :=
  inferInstance

/-- On any Hausdorff CW complex `C : Set X`, the counit `kC ⟶ C` is an isomorphism in `TopCat` for
every test universe `u`. -/
theorem isIso_counit_app_of_cwComplex {X : Type w} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] :
    IsIso (adj.{u, w}.counit.app (TopCat.of C)) :=
  inferInstance

/-- On any Hausdorff space carrying a CW structure on `Set.univ`, the counit `kX ⟶ X` is an
isomorphism in `TopCat` for every test universe `u`. -/
theorem isIso_counit_app_of_cwComplex_univ (X : Type w) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] :
    IsIso (adj.{u, w}.counit.app (TopCat.of X)) :=
  inferInstance

/-- On any colimit cocone in `TopCat` whose stages are `u`-compactly generated, the counit on the
colimit point is an isomorphism. -/
theorem isIso_counit_app_of_isColimit {J : Type v} [Category.{v'} J] {F : J ⥤ TopCat.{w}}
    {c : Cocone F} [∀ j, UCompactlyGeneratedSpace.{u} (F.obj j)] (hc : IsColimit c) :
    IsIso (adj.{u, w}.counit.app c.pt) := by
  have : UCompactlyGeneratedSpace.{u} c.pt :=
    TauCeti.TopCat.uCompactlyGeneratedSpace_of_isColimit hc
  infer_instance

/-- The counit `k(*) ⟶ *` on `PUnit` is an isomorphism in `TopCat`. -/
theorem isIso_counit_app_punit :
    IsIso (adj.{u, w}.counit.app (TopCat.of PUnit.{w + 1})) :=
  inferInstance

/-- The counit `k(I) ⟶ I` on `unitInterval` is an isomorphism in `TopCat` for every test universe
`u`. -/
theorem isIso_counit_app_unitInterval :
    IsIso (adj.{u, 0}.counit.app (TopCat.of unitInterval)) :=
  inferInstance

end CompactlyGenerated

end
