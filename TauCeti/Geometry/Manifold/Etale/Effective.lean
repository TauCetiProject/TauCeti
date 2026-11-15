/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid
public import TauCeti.Geometry.Manifold.Groupoid.Unit
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Trivial

import TauCeti.Geometry.Manifold.Etale.IneffectiveKernel
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The smooth structure of the effective quotient

For an étale `C^n` groupoid `C` whose objects are a `C^n` manifold modelled on `I`, this file
equips `TauCeti.EffectiveQuotient C` and its total arrow space
`Quiver.Total (TauCeti.EffectiveQuotient C)` with `C^n` manifold structures making the effective
quotient an étale `C^n` groupoid:

* Object charts are pulled back along `(TauCeti.EffectiveQuotient.objHomeomorph C).symm`, so
  `TauCeti.EffectiveQuotient.objDiffeomorph` identifies `C` with `EffectiveQuotient C` by a `C^n`
  diffeomorphism.
* Arrow charts (`TauCeti.EffectiveQuotient.chartedSpaceArrows`) are pulled back from objects along
  the effective source map via `IsLocalHomeomorph.chartedSpaceComap`. Any `C^n` manifold structure
  on the effective arrow space for which source is a `C^n` local diffeomorphism is compatible with
  these charts (`TauCeti.EffectiveQuotient.compatible_chartedSpaceArrows`).
* Source, the quotient projection `mapTotal`, and target are `C^n` local diffeomorphisms, and
  units, inversion and smooth families of composable arrows are `C^n`.
* When `C` is a Hausdorff proper étale `C^n` groupoid (`1 ≤ n`) over a boundaryless `RCLike`
  Banach manifold, `TauCeti.isClosed_ineffectiveArrows` implies that the effective arrow space is
  Hausdorff (`TauCeti.EffectiveQuotient.t2Space_arrows`). Together with
  `TauCeti.EffectiveQuotient.isProperMap_source_target`,
  `TauCeti.EffectiveQuotient.secondCountableTopology_arrows` and
  `TauCeti.EffectiveQuotient.ineffectiveKernel_eq_bot`, this makes `EffectiveQuotient C` a
  Hausdorff (and second-countable when `C` is) effective proper étale `C^n` presentation with the
  same coarse space.

For a discrete group `K` acting trivially on a manifold `N`, the effective quotient of the trivial
gerbe `ActionCategory K N` is `C^n`-diffeomorphic on both objects and total arrows to the smooth
unit groupoid `Discrete N`, and `TauCeti.ActionGroupoid.exists_trivial_gerbe_effective_reduction`
verifies that all hypotheses of smooth proper étale effective reduction are jointly satisfied for
every finite group `K` and Hausdorff boundaryless `C^n` manifold `N`.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public noncomputable section

open CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace EffectiveQuotient

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  (n : ℕ∞ω)
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)]

variable (C) in
/-- Object charts of the effective quotient, pulled back from `C` along `(objHomeomorph C).symm`. -/
instance instChartedSpaceObjects : ChartedSpace H (EffectiveQuotient C) :=
  (objHomeomorph C).symm.pullbackChartedSpace

/-- Objects of the effective quotient of a `C^n` manifold form a `C^n` manifold. -/
instance instIsManifoldObjects [IsManifold I n C] : IsManifold I n (EffectiveQuotient C) :=
  Homeomorph.pullback_isManifold I n (objHomeomorph C).symm

variable (C) in
/-- Objects of the effective quotient are `C^n`-diffeomorphic to the objects of `C`. -/
def objDiffeomorph : C ≃ₘ^n⟮I, I⟯ EffectiveQuotient C :=
  ((objHomeomorph C).symm.pullbackDiffeomorph I n).symm

@[simp]
theorem objDiffeomorph_apply (x : C) :
    objDiffeomorph I n C x = (toEffectiveQuotient C).obj x := by
  simp [objDiffeomorph]

@[simp]
theorem objDiffeomorph_symm_apply (y : EffectiveQuotient C) :
    (objDiffeomorph I n C).symm y = (objEquiv C).symm y := by
  rw [← Diffeomorph.coe_toEquiv]
  simp [objDiffeomorph]

/-- The object projection `toEffectiveQuotient.obj` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_toEffectiveQuotient_obj :
    IsLocalDiffeomorph I I n (toEffectiveQuotient C).obj := by
  convert (objDiffeomorph I n C).isLocalDiffeomorph using 1
  funext x
  exact (objDiffeomorph_apply I n x).symm

/-- A map into `EffectiveQuotient C` is `C^n` if and only if its preimage in `C` is `C^n`. -/
theorem contMDiff_objects_iff {f : P → EffectiveQuotient C} :
    ContMDiff I'' I n f ↔ ContMDiff I'' I n fun z ↦ (objEquiv C).symm (f z) := by
  simp [← (objDiffeomorph I n C).symm.contMDiff_diffeomorph_comp_iff le_rfl, Function.comp_def]

variable [IsTopologicalGroupoid C]

/-- Arrow charts on `Quiver.Total (EffectiveQuotient C)`, pulled back from `EffectiveQuotient C`
along the local homeomorphism `source`. -/
@[instance_reducible]
def chartedSpaceArrows
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    ChartedSpace H (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).chartedSpaceComap

/-- Total arrows of the effective quotient of an étale groupoid on a `C^n` object manifold form a
`C^n` manifold. -/
theorem isManifold_arrows [IsManifold I n C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsManifold I n (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).isManifold_chartedSpaceComap

/-- Any `C^n` manifold structure on `Quiver.Total (EffectiveQuotient C)` making `source` a `C^n`
local diffeomorphism is compatible with `chartedSpaceArrows hs`. -/
theorem compatible_chartedSpaceArrows [IsManifold I n C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    [c : ChartedSpace H (Quiver.Total (EffectiveQuotient C))]
    [IsManifold I n (Quiver.Total (EffectiveQuotient C))]
    (hsc : IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C)) :
    ∀ e ∈ c.atlas, ∀ e' ∈ (chartedSpaceArrows (H := H) hs).atlas,
      e.symm.trans e' ∈ contDiffGroupoid n I :=
  (isLocalHomeomorph_source hs).compatible_chartedSpaceComap hsc

/-- The source map of the effective quotient is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  (isLocalHomeomorph_source hs).isLocalDiffeomorph_chartedSpaceComap

/-- A map into `Quiver.Total (EffectiveQuotient C)` is `C^n` if and only if it is continuous and
its sources depend `C^n` on the parameter. -/
theorem contMDiff_arrows_iff
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {f : P → Quiver.Total (EffectiveQuotient C)} :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I'' I n f ↔ Continuous f ∧ ContMDiff I'' I n fun z ↦ (f z).left :=
  (isLocalHomeomorph_source hs).contMDiff_chartedSpaceComap_iff

/-- Units of the effective quotient form a `C^n` section of the source map. -/
theorem contMDiff_unit
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I I n fun y : EffectiveQuotient C ↦
      (⟨y, y, 𝟙 y⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let _ := isTopologicalGroupoid hs
  let _ := chartedSpaceArrows (H := H) hs
  exact (contMDiff_arrows_iff I n hs).mpr ⟨IsTopologicalGroupoid.continuous_unit, contMDiff_id⟩

/-- Smooth families of composable arrows in the effective quotient compose to a `C^n` family. -/
theorem contMDiff_comp
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {a b : P → Quiver.Total (EffectiveQuotient C)} :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I'' I n a → ContMDiff I'' I n b →
      (h : ∀ z, (a z).right = (b z).left) →
      ContMDiff I'' I n fun z ↦ (a z).comp (b z) (h z) := by
  let _ := isTopologicalGroupoid hs
  let _ := chartedSpaceArrows (H := H) hs
  intro ha hb h
  have hsource : ContMDiff I'' I n fun z ↦ ((a z).comp (b z) (h z)).left := by
    simpa only [Quiver.Total.comp_left, Function.comp_def] using
      (isLocalDiffeomorph_source I n hs).contMDiff.comp ha
  exact (contMDiff_arrows_iff I n hs).mpr
    ⟨IsTopologicalGroupoid.continuous_comp.comp ((ha.continuous.prodMk hb.continuous).subtype_mk h),
      hsource⟩

section SourceDiffeomorph

variable [ChartedSpace H' (Quiver.Total C)]

/-- When the source of `C` is a `C^n` local diffeomorphism, the quotient projection `mapTotal` onto
effective arrows is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_mapTotal
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph J I n (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  let _ := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro a
  have hcomp : IsLocalDiffeomorphAt J I n
      ((Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) ∘
        (toEffectiveQuotient C).toPrefunctor.mapTotal) a := by
    have h := (hs a).comp (hg := isLocalDiffeomorph_toEffectiveQuotient_obj I n a.left)
    simpa only [Function.comp_def, Prefunctor.mapTotal_left, Functor.toPrefunctor_obj] using h
  exact hcomp.of_comp_left
    (isLocalDiffeomorph_source I n hs.isLocalHomeomorph _)
    isQuotientMap_mapTotal.continuous.continuousAt

/-- When both source and target of `C` are `C^n` local diffeomorphisms, the target map of
`EffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let _ := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro α
  obtain ⟨a, rfl⟩ := mapTotal_surjective α
  have hcomp : IsLocalDiffeomorphAt J I n
      ((Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) ∘
        (toEffectiveQuotient C).toPrefunctor.mapTotal) a := by
    have h := (ht a).comp (hg := isLocalDiffeomorph_toEffectiveQuotient_obj I n a.right)
    simpa only [Function.comp_def, Prefunctor.mapTotal_right, Functor.toPrefunctor_obj] using h
  exact hcomp.of_comp_right (isLocalDiffeomorph_mapTotal I J n hs a)

/-- When both source and target of `C` are `C^n` local diffeomorphisms, inversion of effective
arrows is `C^n`. -/
theorem contMDiff_inverse
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n fun α : Quiver.Total (EffectiveQuotient C) ↦
      (⟨α.right, α.left, inv α.hom⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let _ := isTopologicalGroupoid hs.isLocalHomeomorph
  let _ := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (contMDiff_arrows_iff I n hs.isLocalHomeomorph).mpr
    ⟨IsTopologicalGroupoid.continuous_inverse, (isLocalDiffeomorph_target I J n hs ht).contMDiff⟩

/-- Inversion of effective arrows as a `C^n` diffeomorphism. -/
def inverseDiffeomorph
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    Quiver.Total (EffectiveQuotient C) ≃ₘ^n⟮I, I⟯ Quiver.Total (EffectiveQuotient C) :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  { toFun := fun α ↦ ⟨α.right, α.left, inv α.hom⟩
    invFun := fun α ↦ ⟨α.right, α.left, inv α.hom⟩
    left_inv := fun α ↦ by simp
    right_inv := fun α ↦ by simp
    contMDiff_toFun := contMDiff_inverse I J n hs ht
    contMDiff_invFun := contMDiff_inverse I J n hs ht }

@[simp]
theorem inverseDiffeomorph_apply
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (α : Quiver.Total (EffectiveQuotient C)) :
    inverseDiffeomorph I J n hs ht α = ⟨α.right, α.left, inv α.hom⟩ :=
  (rfl)

end SourceDiffeomorph

end Smooth

section Hausdorff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)] {n : ℕ∞ω}

/-- **Hausdorffness of the smooth effective arrow space.** In a topological groupoid with Hausdorff
arrow space, boundaryless object charts over a complete `RCLike` normed space, proper source-target
map, and `C^n` local diffeomorphisms for source and target (`1 ≤ n`), the effective arrow space
`Quiver.Total (EffectiveQuotient C)` is Hausdorff. -/
theorem t2Space_arrows
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hn : 1 ≤ n) :
    T2Space (Quiver.Total (EffectiveQuotient C)) :=
  t2Space_arrows_of_isClosed hs.isLocalHomeomorph
    (isClosed_ineffectiveArrows hp hs ht IsTopologicalGroupoid.continuous_unit
      IsTopologicalGroupoid.continuous_comp hn)

end Hausdorff

end EffectiveQuotient

namespace ActionGroupoid

section TrivialSmooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {K N : Type*} [Group K] [MulAction K N] [TopologicalSpace K] [DiscreteTopology K]
  [TopologicalSpace N] [ChartedSpace H N]

omit [TopologicalSpace K] [DiscreteTopology K] in
/-- A trivial action on a manifold acts by `C^n` maps. -/
theorem contMDiffConstSMul_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) :
    ContMDiffConstSMul I n K N :=
  ⟨fun k ↦ by
    convert contMDiff_id (I := I) (n := n) using 1
    funext x
    exact htriv k x⟩

variable (K N) in
omit [DiscreteTopology K] in
/-- On objects, `EffectiveQuotient (ActionCategory K N)` is `C^n`-diffeomorphic to `Discrete N`. -/
def effectiveQuotientObjDiffeomorphDiscrete :
    EffectiveQuotient (ActionCategory K N) ≃ₘ^n⟮I, I⟯ Discrete N :=
  (EffectiveQuotient.objDiffeomorph I n (ActionCategory K N)).symm.trans
    ((objectDiffeomorph I n K N).trans (UnitGroupoid.objectDiffeomorph I n N).symm)

omit [DiscreteTopology K] in
@[simp]
theorem effectiveQuotientObjDiffeomorphDiscrete_toEquiv :
    (effectiveQuotientObjDiffeomorphDiscrete I n K N).toEquiv =
      (effectiveQuotientObjHomeomorphDiscrete K N).toEquiv := by
  ext y
  obtain ⟨a, rfl⟩ : ∃ a, (toEffectiveQuotient (ActionCategory K N)).obj a = y :=
    ⟨_, toEffectiveQuotient_obj_objEquiv_symm y⟩
  simp [effectiveQuotientObjDiffeomorphDiscrete]

omit [DiscreteTopology K] in
@[simp]
theorem effectiveQuotientObjDiffeomorphDiscrete_apply
    (y : EffectiveQuotient (ActionCategory K N)) :
    effectiveQuotientObjDiffeomorphDiscrete I n K N y =
      ⟨((EffectiveQuotient.objEquiv (ActionCategory K N)).symm y).back⟩ := by
  rw [← Diffeomorph.coe_toEquiv, effectiveQuotientObjDiffeomorphDiscrete_toEquiv]
  simp

omit [DiscreteTopology K] in
@[simp]
theorem effectiveQuotientObjDiffeomorphDiscrete_symm_apply (x : Discrete N) :
    (effectiveQuotientObjDiffeomorphDiscrete I n K N).symm x =
      (discreteToEffectiveQuotient K N).obj x := by
  rw [← Diffeomorph.toEquiv_coe_symm, effectiveQuotientObjDiffeomorphDiscrete_toEquiv]
  simp

/-- **Smooth effective reduction of a trivial gerbe.** On total arrow manifolds, the effective
quotient of `ActionCategory K N` is `C^n`-diffeomorphic to the smooth unit groupoid
`Quiver.Total (Discrete N)`. -/
def effectiveQuotientArrowDiffeomorphDiscrete (htriv : ∀ (k : K) (x : N), k • x = x) :
    letI := continuousSMul_of_smul_eq_self htriv
    letI : IsTopologicalGroup K :=
      { continuous_mul := continuous_of_discreteTopology
        continuous_inv := continuous_of_discreteTopology }
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    Quiver.Total (EffectiveQuotient (ActionCategory K N)) ≃ₘ^n⟮I, I⟯ Quiver.Total (Discrete N) := by
  let _ := continuousSMul_of_smul_eq_self htriv
  let _ : IsTopologicalGroup K :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  let _ := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
  refine
    { (effectiveQuotientArrowHomeomorphDiscrete htriv).toEquiv with
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · refine (UnitGroupoid.contMDiff_arrows_iff I n).mpr
      ⟨(effectiveQuotientArrowHomeomorphDiscrete htriv).continuous, ?_⟩
    convert (effectiveQuotientObjDiffeomorphDiscrete I n K N).contMDiff.comp
      (EffectiveQuotient.isLocalDiffeomorph_source I n (isLocalHomeomorph_source K N)).contMDiff
      using 1
    funext α
    obtain ⟨⟨a, b, f⟩, rfl⟩ := EffectiveQuotient.mapTotal_surjective α
    simp [Prefunctor.mapTotal]
  · refine (EffectiveQuotient.contMDiff_arrows_iff I n (isLocalHomeomorph_source K N)).mpr
      ⟨(effectiveQuotientArrowHomeomorphDiscrete htriv).symm.continuous, ?_⟩
    convert (effectiveQuotientObjDiffeomorphDiscrete I n K N).symm.contMDiff.comp
      (UnitGroupoid.isLocalDiffeomorph_source I n N).contMDiff using 1
    funext β
    rcases β with ⟨⟨x⟩, ⟨y⟩, ψ⟩
    have hxy : x = y := Discrete.eq_of_hom ψ
    subst y
    simp [Prefunctor.mapTotal]

@[simp]
theorem effectiveQuotientArrowDiffeomorphDiscrete_apply
    (htriv : ∀ (k : K) (x : N), k • x = x)
    (α : Quiver.Total (EffectiveQuotient (ActionCategory K N))) :
    letI := continuousSMul_of_smul_eq_self htriv
    letI : IsTopologicalGroup K :=
      { continuous_mul := continuous_of_discreteTopology
        continuous_inv := continuous_of_discreteTopology }
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    effectiveQuotientArrowDiffeomorphDiscrete I n htriv α =
      (effectiveQuotientToDiscrete htriv).toPrefunctor.mapTotal α :=
  effectiveQuotientArrowHomeomorphDiscrete_apply htriv α

@[simp]
theorem effectiveQuotientArrowDiffeomorphDiscrete_symm_apply
    (htriv : ∀ (k : K) (x : N), k • x = x)
    (β : Quiver.Total (Discrete N)) :
    letI := continuousSMul_of_smul_eq_self htriv
    letI : IsTopologicalGroup K :=
      { continuous_mul := continuous_of_discreteTopology
        continuous_inv := continuous_of_discreteTopology }
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    (effectiveQuotientArrowDiffeomorphDiscrete I n htriv).symm β =
      (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal β :=
  effectiveQuotientArrowHomeomorphDiscrete_symm_apply htriv β

end TrivialSmooth

section TrivialRealization

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  (n : ℕ∞ω) (K N : Type*) [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H N] [IsManifold I n N]

/-- **Joint satisfiability of smooth proper étale effective reduction.** Equipping any Hausdorff
boundaryless `C^n` Banach manifold `N` (`1 ≤ n`) with the trivial action of any finite discrete
group `K` via `MulAction.compHom N (1 : K →* Equiv.Perm N)` yields a Hausdorff proper étale `C^n`
groupoid `ActionCategory K N` whose effective quotient is a Hausdorff proper étale `C^n` groupoid
`C^n`-diffeomorphic on objects and arrows to `Discrete N`, with coarse space homeomorphic to `N`,
while `ActionCategory K N` itself is not equivalent to `EffectiveQuotient (ActionCategory K N)`
whenever `K` is nontrivial and `N` is nonempty. -/
theorem exists_trivial_gerbe_effective_reduction (hn : 1 ≤ n) :
    letI : MulAction K N := MulAction.compHom N (1 : K →* Equiv.Perm N)
    letI := continuousSMul_of_smul_eq_self (K := K) (N := N) (fun _ _ ↦ rfl)
    letI : IsTopologicalGroup K :=
      { continuous_mul := continuous_of_discreteTopology
        continuous_inv := continuous_of_discreteTopology }
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    T2Space (Quiver.Total (ActionCategory K N)) ∧
      IsProperMap (fun f : Quiver.Total (ActionCategory K N) ↦ (f.left, f.right)) ∧
      T2Space (Quiver.Total (EffectiveQuotient (ActionCategory K N))) ∧
      IsProperMap
        (fun α : Quiver.Total (EffectiveQuotient (ActionCategory K N)) ↦ (α.left, α.right)) ∧
      IsManifold I n (EffectiveQuotient (ActionCategory K N)) ∧
      IsManifold I n (Quiver.Total (EffectiveQuotient (ActionCategory K N))) ∧
      Nonempty (EffectiveQuotient (ActionCategory K N) ≃ₘ^n⟮I, I⟯ Discrete N) ∧
      Nonempty
        (Quiver.Total (EffectiveQuotient (ActionCategory K N)) ≃ₘ^n⟮I, I⟯
          Quiver.Total (Discrete N)) ∧
      Nonempty
        (_root_.Quotient (isIsomorphicSetoid (EffectiveQuotient (ActionCategory K N))) ≃ₜ N) ∧
      ([Nontrivial K] → [Nonempty N] →
        IsEmpty (ActionCategory K N ≌ EffectiveQuotient (ActionCategory K N))) := by
  let _ : MulAction K N := MulAction.compHom N (1 : K →* Equiv.Perm N)
  have htriv : ∀ (k : K) (x : N), k • x = x := fun _ _ ↦ rfl
  let _ := continuousSMul_of_smul_eq_self htriv
  let _ : IsTopologicalGroup K :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  let _ := contMDiffConstSMul_of_smul_eq_self I n htriv
  let _ := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
  have hp : IsProperMap fun f : Quiver.Total (ActionCategory K N) ↦ (f.left, f.right) :=
    isProperMap_source_target_of_smul_eq_self htriv
  refine ⟨inferInstance, hp,
    EffectiveQuotient.t2Space_arrows hp (isLocalDiffeomorph_source I n K N)
      (isLocalDiffeomorph_target I n K N) hn,
    EffectiveQuotient.isProperMap_source_target hp,
    inferInstance,
    EffectiveQuotient.isManifold_arrows I n (isLocalHomeomorph_source K N),
    ⟨effectiveQuotientObjDiffeomorphDiscrete I n K N⟩,
    ⟨effectiveQuotientArrowDiffeomorphDiscrete I n htriv⟩,
    ⟨effectiveQuotientCoarseHomeomorphOfSMulEqSelf htriv⟩,
    isEmpty_equivalence_effectiveQuotient_of_smul_eq_self htriv⟩

end TrivialRealization

end ActionGroupoid

end TauCeti
