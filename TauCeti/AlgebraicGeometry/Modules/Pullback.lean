/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement

/-!
# Pullback and restriction of modules on schemes

For a scheme morphism `f : X ⟶ Y` and an open `V ⊆ Y`, restricting the pullback `f^* M` to
`f⁻¹ V` agrees with pulling back the restriction `M|_V` along `f ∣_ V`. This compatibility lets
local properties of modules, expressed on open covers, be transported along scheme morphisms.

Mathlib states quasi-coherence, finite type, finite presentation and local freeness of an
`𝒪_Y`-module `M` through local data on the site of opens of `Y`: a cover `V i` of `Y` together
with generating sections or presentations of the restrictions `M.over (V i)` to the slice sites.
Read on these slice sites, pullback along `f` is a colimit-preserving functor
`Scheme.Modules.pullbackOver f V` which preserves the structure sheaf and sends `M.over V` to
`(f^* M).over (f⁻¹ V)`. It therefore carries local generators and local presentations of `M` on
the cover `V i` to local generators and local presentations of `f^* M` on the cover `f⁻¹ (V i)`,
preserving finiteness of the index types and invertibility of the generating morphisms.
Consequently all four properties are stable under arbitrary pullback. The transport of
presentations follows Mathlib's `SheafOfModules.QuasicoherentData.pushforward`, which carries
presentations along a colimit-preserving functor by `SheafOfModules.Presentation.map`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.restrictPullbackObjIso` identifies these two restricted
  pullbacks;
* `AlgebraicGeometry.Scheme.Modules.pullbackOver`: pullback read on the slice sites over `V` and
  `f⁻¹ V`, with `pullbackOverUnitIso` and `pullbackOverObjIso` comparing it with the structure
  sheaves and with the pullback of `𝒪_Y`-modules;
* `SheafOfModules.LocalGeneratorsData.pullback` and `SheafOfModules.QuasicoherentData.pullback`:
  local generators and quasi-coherent data carried along `f`;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback` and
  `AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback`: pullback preserves quasi-coherent,
  finite type, finitely presented and locally free modules.

## References

* The Stacks Project, *Sheaves of Modules*, sections *Quasi-coherent modules*, *Modules of finite
  type*, *Modules of finite presentation* and *Locally free sheaves*.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe w u

noncomputable section

variable {X Y : Scheme.{u}}

section Over

variable (f : X ⟶ Y)

/-- Pullback commutes with restriction to opens: for an open `V ⊆ Y`, the restriction of
`f^* M` to the preimage `f⁻¹ V` is the pullback of `M|_V` along `f ∣_ V : f⁻¹ V ⟶ V`. -/
def restrictPullbackObjIso (V : Y.Opens) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ V).ι ≅ (pullback (f ∣_ V)).obj (M.restrict V.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫ (pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    ((pullbackComp (f ∣_ V) V.ι).app M).symm ≪≫
    (pullback (f ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).app M).symm

variable (V : Y.Opens)

/-- Pullback along `f` read on slice sites: sheaves of modules over the slice of `Y` at an open
`V` are identified with `𝒪_V`-modules, pulled back along `f ∣_ V : f⁻¹ V ⟶ V`, and read as
sheaves of modules over the slice of `X` at `f⁻¹ V`. -/
def pullbackOver : SheafOfModules (Y.ringCatSheaf.over V) ⥤
    SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ V)) :=
  (overEquiv V).functor ⋙ pullback (f ∣_ V) ⋙ (overEquiv (f ⁻¹ᵁ V)).inverse

instance : (pullbackOver f V).IsLeftAdjoint := by
  unfold pullbackOver
  infer_instance

/-- Pullback read on slice sites preserves the structure sheaf. -/
def pullbackOverUnitIso :
    SheafOfModules.unit _ ≅ (pullbackOver f V).obj (SheafOfModules.unit _) :=
  -- Mathlib's invertibility of `pullbackObjUnitToUnit` is stated for pushforwards known to be
  -- right adjoints; the adjunction is recorded for `Scheme.Modules.pushforward`.
  let : (SheafOfModules.pushforward.{u} (f ∣_ V).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward (f ∣_ V)).IsRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ V).toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  (overEquiv (f ⁻¹ᵁ V)).unitIso.app _ ≪≫
    (overEquiv (f ⁻¹ᵁ V)).inverse.mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ V).toRingCatSheafHom)).symm

/-- Pullback read on slice sites computes the restriction of the pullback: it sends `M.over V`
to `(f^* M).over (f⁻¹ V)`. -/
def pullbackOverObjIso (M : Y.Modules) :
    (pullbackOver f V).obj (M.over V) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ V) :=
  ((overEquiv (f ⁻¹ᵁ V)).inverse.mapIso
      ((overFunctorEquiv (f ⁻¹ᵁ V)).app _ ≪≫ restrictPullbackObjIso f V M ≪≫
        (pullback (f ∣_ V)).mapIso ((overFunctorEquiv V).app M).symm)).symm ≪≫
    ((overEquiv (f ⁻¹ᵁ V)).unitIso.app _).symm

end Over

/-- Local generators of an `𝒪_Y`-module `M` on a cover `V i` of `Y`, carried along `f` to local
generators of `f^* M` on the cover `f⁻¹ (V i)` of `X`. -/
@[expose, simps I X]
def _root_.SheafOfModules.LocalGeneratorsData.pullback {M : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M) (f : X ⟶ Y) :
    SheafOfModules.LocalGeneratorsData.{w} (R := X.ringCatSheaf) ((pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := by
    have hq := (Opens.coversTop_iff _ _).mp q.coversTop
    rw [Opens.coversTop_iff, IsOpenCover, ← Scheme.Hom.preimage_iSup, hq.iSup_eq_top,
      Scheme.Hom.preimage_top]
  generators i :=
    (q.generators i).mapIso (pullbackOver f (q.X i)) (pullbackOverUnitIso f _)
      (pullbackOverObjIso f _ M)

/-- Carrying local generators along a morphism of schemes preserves finiteness. -/
instance {M : Y.Modules} (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M)
    [q.IsFiniteType] (f : X ⟶ Y) : (q.pullback f).IsFiniteType where
  isFiniteType i := SheafOfModules.GeneratingSections.isFiniteType_mapIso (q.generators i)
    (pullbackOver f (q.X i)) (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)
    (hσ := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i)

/-- Carrying locally free data along a morphism of schemes gives locally free data. -/
instance {M : Y.Modules} (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M)
    [q.IsLocallyFreeData] (f : X ⟶ Y) : (q.pullback f).IsLocallyFreeData where
  isIso i :=
    have := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
    SheafOfModules.GeneratingSections.isIso_mapIso_π (q.generators i)
      (pullbackOver f (q.X i)) (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)

/-- Quasi-coherent data of an `𝒪_Y`-module `M` on a cover `V i` of `Y`, carried along `f` to
quasi-coherent data of `f^* M` on the cover `f⁻¹ (V i)` of `X`. -/
@[expose, simps I X]
def _root_.SheafOfModules.QuasicoherentData.pullback {M : Y.Modules}
    (q : SheafOfModules.QuasicoherentData.{w} (R := Y.ringCatSheaf) M) (f : X ⟶ Y) :
    SheafOfModules.QuasicoherentData.{w} (R := X.ringCatSheaf) ((pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := (q.localGeneratorsData.pullback f).coversTop
  presentation i :=
    ((q.presentation i).map (pullbackOver f (q.X i)) (pullbackOverUnitIso f _)).ofIsIso
      (pullbackOverObjIso f _ M).hom

/-- Carrying finite quasi-coherent data along a morphism of schemes gives finite quasi-coherent
data. -/
instance {M : Y.Modules} (q : SheafOfModules.QuasicoherentData.{w} (R := Y.ringCatSheaf) M)
    [q.IsFinitePresentation] (f : X ⟶ Y) : (q.pullback f).IsFinitePresentation where
  isFinite_presentation i :=
    have := SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation (q := q) i
    SheafOfModules.instIsFiniteOfIsIso (pullbackOverObjIso f _ M).hom _

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
instance isQuasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  ((SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.pullback
    f).isQuasicoherent

/-- The pullback of a module of finite type along a morphism of schemes is of finite type. -/
instance isFiniteType_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  obtain ⟨q, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  exact SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf) ⟨q.pullback f, inferInstance⟩

/-- The pullback of a finitely presented module along a morphism of schemes is finitely
presented. -/
instance isFinitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, _⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  exact SheafOfModules.IsFinitePresentation.mk (R := X.ringCatSheaf) ⟨q.pullback f, inferInstance⟩

/-- The pullback of a locally free module along a morphism of schemes is locally free. -/
instance isLocallyFree_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsLocallyFree] :
    ((pullback f).obj M).IsLocallyFree := by
  obtain ⟨q, _⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  exact (q.pullback f).isLocallyFree

end

end AlgebraicGeometry.Scheme.Modules
