/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Restriction

/-!
# Pullback of quasi-coherent, finitely presented, and locally free sheaves on ringed spaces

Let `(f, φ) : (X, R) → (Y, S)` be a morphism of ringed spaces, given by a continuous map
`f : X ⟶ Y` and a morphism of sheaves of rings `φ : S ⟶ f_* R`. Using the slice-site pullback
`SheafOfModules.pullbackOver φ V` and its compatibilities with the unit sheaf and slice
restriction (`pullbackOverUnitIso`, `pullbackOverObjIso`), local generators and local
presentations of an `S`-module sheaf `M` over an open cover `{V_i}` of `Y` transport to local
generators and local presentations of `f^* M` over the preimage cover `{f⁻¹(V_i)}` of `X`.

Since `pullbackOver φ V` is a left adjoint, this transport preserves finiteness of generating
families, finiteness of presentations, and invertibility of the generating morphism. Consequently,
pullback of module sheaves along any morphism of ringed spaces preserves quasi-coherence, finite
type, finite presentation, local freeness, and finite local freeness. Via
`Opens.sheafOfModulesRestrictIsoPullback`, open-subspace restriction `U.sheafOfModulesRestrict R`
preserves all five properties as well.

## Main declarations

* `SheafOfModules.LocalGeneratorsData.pullback`: transports local generators of `M` along `(f, φ)`
  to local generators of `(pullback φ).obj M`, preserving `IsFiniteType` and `IsLocallyFreeData`.
* `SheafOfModules.QuasicoherentData.pullback`: transports quasi-coherent presentation data of `M`
  along `(f, φ)` to quasi-coherent presentation data of `(pullback φ).obj M`, preserving
  `IsFinitePresentation`.
* `SheafOfModules.isQuasicoherent_pullback`, `SheafOfModules.isFiniteType_pullback`,
  `SheafOfModules.isFinitePresentation_pullback`, `SheafOfModules.isLocallyFree_pullback`, and
  `SheafOfModules.isFiniteLocallyFree_pullback`: ringed-space pullback preserves quasi-coherent,
  finite-type, finitely presented, locally free, and finite locally free module sheaves.
* `TopologicalSpace.Opens.isQuasicoherent_sheafOfModulesRestrict`,
  `TopologicalSpace.Opens.isFiniteType_sheafOfModulesRestrict`,
  `TopologicalSpace.Opens.isFinitePresentation_sheafOfModulesRestrict`,
  `TopologicalSpace.Opens.isLocallyFree_sheafOfModulesRestrict`, and
  `TopologicalSpace.Opens.isFiniteLocallyFree_sheafOfModulesRestrict`: open-subspace restriction
  preserves all five properties.

## References

* [The Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
-/

public section

open CategoryTheory TopologicalSpace

universe w u

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}

/-- Local generators of an `S`-module sheaf `M` on an open cover `q.X` of `Y`, carried along a
ringed-space morphism `(f, φ)` to local generators of `(pullback φ).obj M` on the preimage open
cover `i ↦ (Opens.map f).obj (q.X i)` of `X`. Its body is exposed so that the dependent
`generators` field over the preimage cover reduces without `cast`. -/
@[expose, simps I X generators]
def LocalGeneratorsData.pullback {M : SheafOfModules.{u} S}
    (q : LocalGeneratorsData.{w} (R := S) M)
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] :
    LocalGeneratorsData.{w} (R := R) ((SheafOfModules.pullback.{u} φ).obj M) where
  I := q.I
  X i := (Opens.map f).obj (q.X i)
  coversTop := Opens.coversTop_map f q.coversTop
  generators i :=
    (q.generators i).mapIso (pullbackOver φ (q.X i)) (pullbackOverUnitIso φ (q.X i))
      (pullbackOverObjIso φ (q.X i) M)

/-- Carrying local generators along a morphism of ringed spaces preserves finite type. -/
instance LocalGeneratorsData.isFiniteType_pullback {M : SheafOfModules.{u} S}
    (q : LocalGeneratorsData.{w} (R := S) M) [q.IsFiniteType]
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] :
    (q.pullback φ).IsFiniteType where
  isFiniteType i :=
    let _ := LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
    GeneratingSections.isFiniteType_mapIso (q.generators i)
      (pullbackOver φ (q.X i)) (pullbackOverUnitIso φ (q.X i)) (pullbackOverObjIso φ (q.X i) M)

/-- Carrying locally free data along a morphism of ringed spaces preserves `IsLocallyFreeData`. -/
instance LocalGeneratorsData.isLocallyFreeData_pullback {M : SheafOfModules.{u} S}
    (q : LocalGeneratorsData.{w} (R := S) M) [q.IsLocallyFreeData]
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] :
    (q.pullback φ).IsLocallyFreeData where
  isIso i :=
    have := LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
    GeneratingSections.isIso_mapIso_π (q.generators i)
      (pullbackOver φ (q.X i)) (pullbackOverUnitIso φ (q.X i)) (pullbackOverObjIso φ (q.X i) M)

/-- Quasi-coherent presentation data of an `S`-module sheaf `M` on an open cover `q.X` of `Y`,
carried along a ringed-space morphism `(f, φ)` to quasi-coherent presentation data of
`(pullback φ).obj M` on the preimage open cover `i ↦ (Opens.map f).obj (q.X i)` of `X`. Its body
is exposed so that the dependent `presentation` field over the preimage cover reduces without
`cast`. -/
@[expose, simps I X presentation]
def QuasicoherentData.pullback {M : SheafOfModules.{u} S}
    (q : QuasicoherentData.{w} (R := S) M)
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] :
    QuasicoherentData.{w} (R := R) ((SheafOfModules.pullback.{u} φ).obj M) where
  I := q.I
  X i := (Opens.map f).obj (q.X i)
  coversTop := Opens.coversTop_map f q.coversTop
  presentation i :=
    ((q.presentation i).map (pullbackOver φ (q.X i)) (pullbackOverUnitIso φ (q.X i))).ofIsIso
      (pullbackOverObjIso φ (q.X i) M).hom

/-- Carrying finite quasi-coherent presentation data along a morphism of ringed spaces preserves
`IsFinitePresentation`. -/
instance QuasicoherentData.isFinitePresentation_pullback {M : SheafOfModules.{u} S}
    (q : QuasicoherentData.{w} (R := S) M) [q.IsFinitePresentation]
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] :
    (q.pullback φ).IsFinitePresentation where
  isFinite_presentation i :=
    have := QuasicoherentData.IsFinitePresentation.isFinite_presentation (q := q) i
    instIsFiniteOfIsIso (pullbackOverObjIso φ (q.X i) M).hom _

section Preservation

variable (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
  [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  (M : SheafOfModules.{u} S)

/-- Pullback along a morphism of ringed spaces preserves quasi-coherence. -/
instance isQuasicoherent_pullback [M.IsQuasicoherent] :
    ((pullback.{u} φ).obj M).IsQuasicoherent :=
  ((IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.pullback φ).isQuasicoherent

/-- Pullback along a morphism of ringed spaces preserves modules of finite type. -/
instance isFiniteType_pullback [M.IsFiniteType] :
    ((pullback.{u} φ).obj M).IsFiniteType := by
  obtain ⟨q, _⟩ := IsFiniteType.exists_localGeneratorsData (M := M)
  exact (q.pullback φ).isFiniteType

/-- Pullback along a morphism of ringed spaces preserves finitely presented modules
(Stacks Project, Tag 01BQ). -/
instance isFinitePresentation_pullback [M.IsFinitePresentation] :
    ((pullback.{u} φ).obj M).IsFinitePresentation := by
  obtain ⟨q, _⟩ := IsFinitePresentation.exists_quasicoherentData M
  exact IsFinitePresentation.mk (R := R) ⟨q.pullback φ, inferInstance⟩

/-- Pullback along a morphism of ringed spaces preserves locally free modules. -/
instance isLocallyFree_pullback [M.IsLocallyFree] :
    ((pullback.{u} φ).obj M).IsLocallyFree := by
  obtain ⟨q, _⟩ := IsLocallyFree.exists_isLocallyFreeData (M := M)
  exact (q.pullback φ).isLocallyFree

/-- Pullback along a morphism of ringed spaces preserves finite locally free modules. -/
theorem isFiniteLocallyFree_pullback (hM : isFiniteLocallyFree S M) :
    isFiniteLocallyFree R ((pullback.{u} φ).obj M) := by
  obtain ⟨hLF, hFP⟩ := hM
  exact ⟨inferInstance, inferInstance⟩

end Preservation

end SheafOfModules

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})
  (M : SheafOfModules.{u} R)

/-- Open-subspace restriction of module sheaves preserves quasi-coherence. -/
instance isQuasicoherent_sheafOfModulesRestrict [M.IsQuasicoherent] :
    ((U.sheafOfModulesRestrict.{u} R).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (U.sheafRestrict.obj R)).prop_of_iso
    ((U.sheafOfModulesRestrictIsoPullback.{u} R).app M).symm
    (SheafOfModules.isQuasicoherent_pullback (U.sheafInclusionHom RingCat.{u} R) M)

/-- Open-subspace restriction of module sheaves preserves finite type. -/
instance isFiniteType_sheafOfModulesRestrict [M.IsFiniteType] :
    ((U.sheafOfModulesRestrict.{u} R).obj M).IsFiniteType :=
  haveI := SheafOfModules.isFiniteType_pullback (U.sheafInclusionHom RingCat.{u} R) M
  SheafOfModules.IsFiniteType.of_iso (R := U.sheafRestrict.obj R)
    ((U.sheafOfModulesRestrictIsoPullback.{u} R).app M).symm

/-- Open-subspace restriction of module sheaves preserves finite presentation. -/
instance isFinitePresentation_sheafOfModulesRestrict [M.IsFinitePresentation] :
    ((U.sheafOfModulesRestrict.{u} R).obj M).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation (U.sheafRestrict.obj R)).prop_of_iso
    ((U.sheafOfModulesRestrictIsoPullback.{u} R).app M).symm
    (SheafOfModules.isFinitePresentation_pullback (U.sheafInclusionHom RingCat.{u} R) M)

/-- Open-subspace restriction of module sheaves preserves local freeness. -/
instance isLocallyFree_sheafOfModulesRestrict [M.IsLocallyFree] :
    ((U.sheafOfModulesRestrict.{u} R).obj M).IsLocallyFree :=
  (SheafOfModules.isLocallyFree (U.sheafRestrict.obj R)).prop_of_iso
    ((U.sheafOfModulesRestrictIsoPullback.{u} R).app M).symm
    (SheafOfModules.isLocallyFree_pullback (U.sheafInclusionHom RingCat.{u} R) M)

/-- Open-subspace restriction of module sheaves preserves finite local freeness. -/
theorem isFiniteLocallyFree_sheafOfModulesRestrict (hM : SheafOfModules.isFiniteLocallyFree R M) :
    SheafOfModules.isFiniteLocallyFree (U.sheafRestrict.obj R)
      ((U.sheafOfModulesRestrict.{u} R).obj M) := by
  obtain ⟨hLF, hFP⟩ := hM
  exact ⟨inferInstance, inferInstance⟩

end TopologicalSpace.Opens

end
