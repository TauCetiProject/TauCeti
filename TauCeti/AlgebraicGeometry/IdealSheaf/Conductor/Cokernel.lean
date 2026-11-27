/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic
public import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
public import TauCeti.AlgebraicGeometry.Modules.StructureSheafSequence
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.Topology.KrullDimension.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The conductor as the annihilator of the structure-sheaf cokernel

For a finite morphism of schemes `f : X ⟶ Y`, let `Q = coker(𝒪_Y ⟶ f_* 𝒪_X)` be the cokernel of
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`. By
`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardSectionsEquiv` and
`AlgebraicGeometry.Scheme.Hom.isFiniteType_cokernel_unitToPushforwardObjUnit`, `Q` is quasicoherent
of finite type and its sections over every affine open `U` of `Y` identify `Γ(Y, U)`-linearly with
`Γ(X, f ⁻¹ᵁ U) ⧸ Γ(Y, U)`.

Hence its annihilator ideal sheaf `Ann(Q)` is the conductor `f.conductor`
(`annihilator_cokernel_unitToPushforwardObjUnit`), and `Q` is canonically isomorphic to the
pushforward of its pullback to the conductor closed subscheme `V(f.conductor)`
(`cokernelUnitToPushforwardIsoPushforward`).

Geometrically, the support of `f.conductor` is contained in the centre `f.centre` outside which `f`
is an isomorphism (`support_conductor_subset_centre`), with equality when `f` is
scheme-theoretically dominant (`support_conductor_eq_centre`). For a finite modification of a
Noetherian scheme `Y` of Krull dimension at most one, possibly reducible, the conductor closed
subscheme therefore has strictly smaller Krull dimension, since its support contains no irreducible
component of `Y`, hence is an Artinian (and in particular
affine) scheme (`isArtinianScheme_conductor_subscheme`); when `f` is also scheme-theoretically
dominant, `f` is an isomorphism if and only if `Γ(Q, ⊤)` vanishes
(`subsingleton_globalSections_cokernel_unitToPushforwardObjUnit_iff_isIso`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.annihilator_cokernel_unitToPushforwardObjUnit`: the annihilator
  ideal sheaf of `coker(𝒪_Y ⟶ f_* 𝒪_X)` is `f.conductor`.
* `AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardIsoPushforward`: canonical presentation
  of `coker(𝒪_Y ⟶ f_* 𝒪_X)` as a pushforward from `f.conductor.subscheme`.
* `AlgebraicGeometry.Scheme.Hom.support_conductor_eq_centre` and
  `AlgebraicGeometry.Scheme.Hom.conductor_eq_top_iff_isIso`: for a finite scheme-theoretically
  dominant morphism, `supp(f.conductor) = f.centre`, and `f.conductor = ⊤ ↔ IsIso f`.
* `AlgebraicGeometry.Scheme.Hom.isArtinianScheme_conductor_subscheme` and
  `AlgebraicGeometry.Scheme.Hom.isFinite_conductor_subschemeι_comp`: for a finite modification in
  dimension at most one, `f.conductor.subscheme` is Artinian, and finite over any locally Artinian
  base over which `Y` is locally of finite type.
* `Hom.subsingleton_globalSections_cokernel_unitToPushforwardObjUnit_iff_isIso`:
  for a finite scheme-theoretically dominant modification of a Noetherian scheme of dimension at
  most one, `Subsingleton Γ(coker(𝒪_Y ⟶ f_* 𝒪_X), ⊤) ↔ IsIso f`.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter IV, §1, Proposition 1.
* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Exercise 1.8.
* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- **The conductor is the annihilator of the structure-sheaf cokernel.** For a finite morphism
`f : X ⟶ Y`, the annihilator ideal sheaf of `coker(𝒪_Y ⟶ f_* 𝒪_X)` is the conductor ideal sheaf
`f.conductor`. -/
@[simp]
theorem annihilator_cokernel_unitToPushforwardObjUnit
    [(cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      Y.Modules).IsQuasicoherent]
    (hM : ∀ U : Y.affineOpens, Module.Finite Γ(Y, U)
      Γ(cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom), U)) :
    Scheme.Modules.annihilator
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) hM =
      f.conductor := by
  apply Scheme.IdealSheafData.ext
  funext U
  let := (f.app U.val).hom.toAlgebra
  rw [Scheme.Modules.annihilator_ideal, f.conductor_ideal U,
    TauCeti.Algebra.conductor_eq_annihilator]
  exact (f.cokernelUnitToPushforwardSectionsEquiv U.property).annihilator_eq

/-- If `i : Z ⟶ Y` is a closed immersion whose ideal sheaf is contained in `f.conductor`, then the
adjunction unit on `coker(𝒪_Y ⟶ f_* 𝒪_X)` is an isomorphism, presenting the cokernel as a
pushforward from `Z`. -/
theorem isIso_unit_app_cokernel_unitToPushforwardObjUnit_of_ker_le_conductor
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (hi : i.ker ≤ f.conductor) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))) := by
  have : (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      Y.Modules).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  refine Scheme.Modules.isIso_unit_app_of_ker_ideal_le_annihilator i
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) fun U ↦ ?_
  rw [← Scheme.Modules.annihilator_ideal
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
      (fun V ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ V.val V.property) U,
    f.annihilator_cokernel_unitToPushforwardObjUnit]
  exact Scheme.IdealSheafData.le_def.mp hi U

/-- The adjunction unit on `coker(𝒪_Y ⟶ f_* 𝒪_X)` for the conductor closed subscheme is an
isomorphism. -/
instance isIso_unit_app_cokernel_unitToPushforwardObjUnit_conductor_subschemeι :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f.conductor.subschemeι).unit.app
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))) :=
  f.isIso_unit_app_cokernel_unitToPushforwardObjUnit_of_ker_le_conductor f.conductor.subschemeι
    f.conductor.ker_subschemeι.le

/-- **Scheme-theoretic support on the conductor.** For a finite morphism `f : X ⟶ Y`, the cokernel
`coker(𝒪_Y ⟶ f_* 𝒪_X)` is canonically isomorphic to the pushforward of its pullback to the
conductor closed subscheme `V(f.conductor)`. -/
def cokernelUnitToPushforwardIsoPushforward :
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : Y.Modules) ≅
      (Scheme.Modules.pushforward f.conductor.subschemeι).obj
        ((Scheme.Modules.pullback f.conductor.subschemeι).obj
          (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))) :=
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction f.conductor.subschemeι).unit.app
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)))

/-- The forward map of `cokernelUnitToPushforwardIsoPushforward` is the unit of the
pullback-pushforward adjunction along `f.conductor.subschemeι`. -/
@[simp]
theorem cokernelUnitToPushforwardIsoPushforward_hom :
    f.cokernelUnitToPushforwardIsoPushforward.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f.conductor.subschemeι).unit.app
        (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  rfl

/-- The support of the conductor of a finite morphism is contained in its centre, the complement
of the largest open over which the morphism is an isomorphism. -/
theorem support_conductor_subset_centre : (f.conductor.support : Set Y) ⊆ f.centre := by
  intro y hy
  by_contra hyc
  have hyi : y ∈ f.isoLocus := by rwa [centre_def, Set.mem_compl_iff, not_not] at hyc
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVi⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyi f.isoLocus.isOpen
  have : IsIso (f ∣_ V) := f.le_isoLocus_iff.mp hVi
  have : IsIso (f.app V) := (isIso_morphismRestrict_iff_isIso_app f hV).mp inferInstance
  exact f.notMem_support_conductor_iff.mpr
    ⟨⟨V, hV⟩, hyV, (ConcreteCategory.bijective_of_isIso (f.app V)).surjective⟩ hy

/-- Over any open `U` where `f` restricts to an isomorphism, no point lies in the support of the
conductor of `f`. -/
theorem notMem_support_conductor_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)]
    {y : Y} (hy : y ∈ U) : y ∉ f.conductor.support := fun hyc ↦
  (f.mem_centre_iff.mp (f.support_conductor_subset_centre hyc)) U hy inferInstance

/-- **The support of the conductor is the centre.** For a finite scheme-theoretically dominant
morphism `f : X ⟶ Y`, the support of `f.conductor` is precisely `f.centre`, the set of points over
which `f` fails to be an isomorphism: over an affine open `V`, the pullback `Γ(Y, V) → Γ(X, f⁻¹ V)`
is already injective, so it is surjective if and only if `f ∣_ V` is an isomorphism. -/
theorem support_conductor_eq_centre [IsSchemeTheoreticallyDominant f] :
    (f.conductor.support : Set Y) = f.centre := by
  refine Set.Subset.antisymm f.support_conductor_subset_centre fun y hyc ↦ ?_
  by_contra hy
  obtain ⟨V, hyV, hsurj⟩ := f.notMem_support_conductor_iff.mp hy
  have : IsIso (f.app V.val) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨f.app_injective V.val, hsurj⟩
  have : IsIso (f ∣_ V.val) := (isIso_morphismRestrict_iff_isIso_app f V.property).mpr inferInstance
  exact (f.mem_centre_iff.mp hyc) V.val hyV inferInstance

/-- **The conductor detects isomorphisms among finite scheme-theoretically dominant morphisms.**
A finite scheme-theoretically dominant morphism is an isomorphism if and only if its conductor is
the unit ideal sheaf. -/
theorem conductor_eq_top_iff_isIso [IsSchemeTheoreticallyDominant f] :
    f.conductor = ⊤ ↔ IsIso f := by
  refine ⟨fun h ↦ ?_, fun _ ↦ f.conductor_eq_top⟩
  rw [← f.centre_eq_empty_iff, ← f.support_conductor_eq_centre, h]
  simp

section Modification

variable [IsModification f]

/-- For a finite modification of a nonempty scheme, the support of the conductor is not the whole
target: the dense open over which the morphism is an isomorphism is nonempty and disjoint from the
conductor support. -/
theorem support_conductor_ne_top_of_isModification [Nonempty Y] : f.conductor.support ≠ ⊤ := by
  obtain ⟨U, hU, -, _⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨y, hy⟩ := hU.nonempty
  intro htop
  exact f.notMem_support_conductor_of_isIso_morphismRestrict hy (htop ▸ trivial)

/-- For a finite modification of a locally Noetherian scheme `Y`, the conductor closed subscheme
has strictly smaller Krull dimension:
`topologicalKrullDim f.conductor.subscheme + 1 ≤ topologicalKrullDim Y`. No irreducible component
of `Y` lies in the support of the conductor: its generic point lies in every dense open of `Y`, in
particular in one over which `f` is an isomorphism. -/
theorem topologicalKrullDim_conductor_subscheme_add_one_le [IsLocallyNoetherian Y] :
    topologicalKrullDim f.conductor.subscheme + 1 ≤ topologicalKrullDim Y := by
  refine Topology.IsInducing.topologicalKrullDim_add_one_le_of_forall_not_subset
    f.conductor.subschemeι.isClosedEmbedding.isInducing fun C hC hCsub ↦ ?_
  obtain ⟨U, hU, -, _⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  let C' : irreducibleComponents Y := ⟨C, hC⟩
  let η := genericPoints.ofComponent C'
  have hηU : (η : Y) ∈ U := U.genericPoints_subset_of_dense hU η.property
  rw [f.conductor.subschemeι.isClosedEmbedding.isClosed_range.closure_eq,
    f.conductor.range_subschemeι] at hCsub
  exact f.notMem_support_conductor_of_isIso_morphismRestrict hηU
    (hCsub (genericPoints.isGenericPoint_ofComponent C').mem)

/-- For a finite modification of a locally Noetherian scheme of Krull dimension at most one, the
conductor closed subscheme has Krull dimension at most zero. -/
theorem topologicalKrullDim_conductor_subscheme_le_zero [IsLocallyNoetherian Y]
    (hY : topologicalKrullDim Y ≤ 1) :
    topologicalKrullDim f.conductor.subscheme ≤ 0 := by
  have h := f.topologicalKrullDim_conductor_subscheme_add_one_le.trans hY
  exact ENat.WithBot.add_le_add_natCast_right_iff (c := 1).mp (by simpa using h)

/-- For a finite modification of a locally Noetherian scheme of Krull dimension at most one, the
conductor closed subscheme is locally Artinian. -/
theorem isLocallyArtinian_conductor_subscheme [IsLocallyNoetherian Y]
    (hY : topologicalKrullDim Y ≤ 1) :
    IsLocallyArtinian f.conductor.subscheme := by
  have : IsLocallyNoetherian f.conductor.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian f.conductor.subschemeι
  exact .of_topologicalKrullDim_le_zero (f.topologicalKrullDim_conductor_subscheme_le_zero hY)

/-- **The conductor closed subscheme on a one-dimensional scheme is Artinian.** For a finite
modification of a Noetherian scheme of Krull dimension at most one, the conductor closed subscheme
is an Artinian scheme (and therefore finite, discrete, and affine). -/
theorem isArtinianScheme_conductor_subscheme [IsNoetherian Y]
    (hY : topologicalKrullDim Y ≤ 1) :
    IsArtinianScheme f.conductor.subscheme :=
  have := f.isLocallyArtinian_conductor_subscheme hY
  have : CompactSpace f.conductor.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace f.conductor.subschemeι
  {}

/-- If `Y` is a Noetherian scheme of dimension at most one and `g : Y ⟶ S` is locally of finite
type over a locally Artinian base `S` (such as `Spec k` for a field `k`), then for any finite
modification `f : X ⟶ Y` the conductor closed subscheme of `f` is finite over `S`. -/
theorem isFinite_conductor_subschemeι_comp [IsNoetherian Y]
    (hY : topologicalKrullDim Y ≤ 1) {S : Scheme.{u}} [IsLocallyArtinian S] (g : Y ⟶ S)
    [LocallyOfFiniteType g] :
    IsFinite (f.conductor.subschemeι ≫ g) := by
  have := f.isArtinianScheme_conductor_subscheme hY
  have : LocallyQuasiFinite (f.conductor.subschemeι ≫ g) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (f.conductor.subschemeι ≫ g)
      fun _ ↦ Set.toFinite _
  exact .of_locallyQuasiFinite _

/-- **Vanishing of the global conductor-cokernel sections detects isomorphisms.** Let `f : X ⟶ Y`
be a finite scheme-theoretically dominant modification of a Noetherian scheme `Y` of Krull
dimension at most one. Because `coker(𝒪_Y ⟶ f_* 𝒪_X)` is pushed forward from the
affine Artinian scheme `V(f.conductor)`, its global sections vanish if and only if `f` is an
isomorphism. -/
theorem subsingleton_globalSections_cokernel_unitToPushforwardObjUnit_iff_isIso
    [IsSchemeTheoreticallyDominant f] [IsNoetherian Y] (hY : topologicalKrullDim Y ≤ 1) :
    Subsingleton Γ(cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom), ⊤) ↔
      IsIso f := by
  have : (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      Y.Modules).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  let i := f.conductor.subschemeι
  let G : f.conductor.subscheme.Modules := (Scheme.Modules.pullback i).obj
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
  let etop := Scheme.Modules.sectionsLinearEquiv f.cokernelUnitToPushforwardIsoPushforward ⊤
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : IsArtinianScheme f.conductor.subscheme := f.isArtinianScheme_conductor_subscheme hY
    have : G.IsQuasicoherent := inferInstance
    have : Subsingleton Γ(G, ⊤) := etop.symm.injective.subsingleton
    have hzeroG : IsZero G := G.isZero_of_subsingleton_sections_top
    have hzeroQ : IsZero (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
        Y.Modules) :=
      ((Scheme.Modules.pushforward i).map_isZero hzeroG).of_iso
        f.cokernelUnitToPushforwardIsoPushforward
    refine f.conductor_eq_top_iff_isIso.mp ?_
    rw [← f.annihilator_cokernel_unitToPushforwardObjUnit
      (fun V ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ V.val V.property)]
    exact Scheme.Modules.annihilator_eq_top_of_subsingleton_sections _ _ fun U ↦
      ModuleCat.subsingleton_of_isZero ((Scheme.Modules.sectionsFunctor U.val).map_isZero hzeroQ)
  · have hker : i.ker = ⊤ := f.conductor.ker_subschemeι.trans f.conductor_eq_top
    have : IsEmpty f.conductor.subscheme := i.ker_eq_top_iff_isEmpty.mp hker
    have : IsEmpty (i ⁻¹ᵁ ⊤ : f.conductor.subscheme.Opens) := ⟨fun ⟨x, _⟩ ↦ IsEmpty.false x⟩
    have : Subsingleton Γ((Scheme.Modules.pushforward i).obj G, ⊤) :=
      ⟨fun s t ↦ Scheme.Modules.section_ext_of_isEmpty (M := G) (U := i ⁻¹ᵁ ⊤) s t⟩
    exact etop.toEquiv.subsingleton

end Modification

end AlgebraicGeometry.Scheme.Hom

end
