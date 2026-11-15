/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Linearization
public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective

import TauCeti.Geometry.Manifold.Etale.IneffectiveKernel
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Smooth effective quotient presentations, linear slices, and trivial gerbes

Let `C` be an étale topological groupoid whose object space carries a `C^n` manifold structure.
This file equips the effective quotient `TauCeti.EffectiveQuotient C` with its `C^n` étale
manifold structure, relates its isotropy and principal locus to linear-ball charts, and constructs
the smooth trivial-gerbe reduction `G ⋉ M ⇒ M`.

1. **Smooth structure of the effective quotient.** The object charts of `EffectiveQuotient C` are
   pulled back from `C` along `EffectiveQuotient.objHomeomorph`, making the object projection a
   `C^n` diffeomorphism (`TauCeti.EffectiveQuotient.objDiffeomorph`). The arrow charts
   (`TauCeti.EffectiveQuotient.chartedSpaceArrows`) are pulled back from the objects along the
   source local homeomorphism. When `C` has `C^n` arrow charts for which the source is a local
   diffeomorphism and the target is `C^n`, the arrow quotient map `mapTotal` is a surjective `C^n`
   local diffeomorphism (`TauCeti.EffectiveQuotient.isLocalDiffeomorph_mapTotal`), source and target
   on `EffectiveQuotient C` are `C^n` local diffeomorphisms, and unit, inversion, and composition
   are `C^n`. On boundaryless complete `RCLike` manifolds with `1 ≤ n`, properness and Hausdorff
   arrows of `C` make the arrow manifold of `EffectiveQuotient C` Hausdorff as well
   (`TauCeti.EffectiveQuotient.t2Space_arrows_of_isLocalDiffeomorph`).

2. **Smooth trivial gerbes.** When a discrete group `G` acts trivially on a `C^n` manifold `M`
   (for instance via `MulAction.ofEndHom 1`), `ActionCategory G M` is a `C^n` étale groupoid with
   constant ineffective kernel `G`, and both the object manifold and the arrow manifold of
   `EffectiveQuotient (ActionCategory G M)` are `C^n`-diffeomorphic to `M`
   (`TauCeti.ActionGroupoid.effectiveQuotientObjDiffeomorph`,
   `TauCeti.ActionGroupoid.effectiveQuotientArrowDiffeomorphOfSmulEqSelf`).

3. **Faithful effective isotropy and fixed subspaces in linear-ball charts.** In a retained-arrow
   linear-ball chart `Aut x ⋉ B ⥤ C` centred at `x`, both `σ.toMonoidHom.ker` and the permutation
   kernel `(MulAction.toPermHom (Aut x) B).ker` equal `ineffectiveKernel hs x`
   (`TauCeti.ker_eq_ineffectiveKernel_of_linear_chart`,
   `TauCeti.ker_toPermHom_eq_ineffectiveKernel_of_linear_chart`). Hence `σ` descends to a faithful
   linear representation `TauCeti.effectiveLinearRepresentation` of
   `Aut ((toEffectiveQuotient C).obj x)` on `E`, every `g ∉ ineffectiveKernel hs x` fixes a proper
   linear subspace, and the principal locus in `B` is the complement of those proper fixed subspaces
   (`TauCeti.exists_linear_ball_principal_locus`).

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
-/

public noncomputable section

open CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti.EffectiveQuotient

section SmoothStructure

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)]

/-- The object charts of the effective quotient, pulled back from `C` along the inverse object
homeomorphism. -/
instance instChartedSpaceObjects : ChartedSpace H (EffectiveQuotient C) :=
  (objHomeomorph C).symm.pullbackChartedSpace

/-- The objects of the effective quotient of a `C^n` object manifold form a `C^n` manifold. -/
instance instIsManifoldObjects [IsManifold I n C] : IsManifold I n (EffectiveQuotient C) :=
  (objHomeomorph C).symm.pullback_isManifold I n

/-- The object projection `toEffectiveQuotient C` as a `C^n` diffeomorphism. -/
def objDiffeomorph : C ≃ₘ^n⟮I, I⟯ EffectiveQuotient C :=
  ((objHomeomorph C).symm.pullbackDiffeomorph I n).symm

@[simp]
theorem objDiffeomorph_apply (x : C) :
    objDiffeomorph I n x = (toEffectiveQuotient C).obj x := by
  simp [objDiffeomorph]

@[simp]
theorem coe_objDiffeomorph :
    ⇑(objDiffeomorph I n (C := C)) = (toEffectiveQuotient C).obj :=
  funext (objDiffeomorph_apply I n)

@[simp]
theorem objDiffeomorph_symm_apply (y : EffectiveQuotient C) :
    (objDiffeomorph I n).symm y = (objEquiv C).symm y := by
  apply (objDiffeomorph I n).injective
  simp

@[simp]
theorem coe_objDiffeomorph_symm :
    ⇑(objDiffeomorph I n (C := C)).symm = (objEquiv C).symm :=
  funext (objDiffeomorph_symm_apply I n)

/-- The projection to the effective quotient is `C^n` on objects. -/
theorem contMDiff_toEffectiveQuotient_obj :
    ContMDiff I I n (toEffectiveQuotient C).obj :=
  coe_objDiffeomorph I n (C := C) ▸ (objDiffeomorph I n (C := C)).contMDiff

/-- The projection to the effective quotient is a `C^n` local diffeomorphism on objects. -/
theorem isLocalDiffeomorph_toEffectiveQuotient_obj :
    IsLocalDiffeomorph I I n (toEffectiveQuotient C).obj :=
  coe_objDiffeomorph I n (C := C) ▸ (objDiffeomorph I n (C := C)).isLocalDiffeomorph

/-- A map into the objects of `EffectiveQuotient C` is `C^n` precisely when its underlying map into
`C` is `C^n`. -/
theorem contMDiff_objects_iff {f : M → EffectiveQuotient C} :
    ContMDiff J I n f ↔ ContMDiff J I n fun z ↦ (objEquiv C).symm (f z) := by
  simp [← (objDiffeomorph I n (C := C)).symm.contMDiff_diffeomorph_comp_iff le_rfl,
    Function.comp_def]

section Etale

variable [IsTopologicalGroupoid C]

/-- The arrow charts of the effective quotient of an étale topological groupoid, pulled back from
its object charts along the source local homeomorphism. -/
@[instance_reducible]
def chartedSpaceArrows
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    ChartedSpace H (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).chartedSpaceComap

/-- When `C` is a `C^n` manifold, the arrow charts of `EffectiveQuotient C` form a `C^n`
manifold. -/
theorem isManifold_arrows [IsManifold I n C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsManifold I n (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).isManifold_chartedSpaceComap

/-- The source map of `EffectiveQuotient C` is a `C^n` local diffeomorphism for its pulled-back
arrow charts. -/
theorem isLocalDiffeomorph_source
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  (isLocalHomeomorph_source hs).isLocalDiffeomorph_chartedSpaceComap

/-- A map into the arrows of `EffectiveQuotient C` is `C^n` if and only if it is continuous and its
composite with the source map is `C^n`. -/
theorem contMDiff_arrows_iff
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {f : M → Quiver.Total (EffectiveQuotient C)} :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff J I n f ↔ Continuous f ∧ ContMDiff J I n fun z ↦ (f z).left :=
  (isLocalHomeomorph_source hs).contMDiff_chartedSpaceComap_iff

/-- The unit map of `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_unit
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I I n fun y : EffectiveQuotient C ↦
      (⟨y, y, 𝟙 y⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := chartedSpaceArrows (H := H) hs
  exact (contMDiff_arrows_iff I n hs).mpr ⟨(isTopologicalGroupoid hs).continuous_unit, contMDiff_id⟩

/-- Composition of `C^n` families of composable arrows in `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_comp
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {a b : M → Quiver.Total (EffectiveQuotient C)} :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff J I n a → ContMDiff J I n b → (h : ∀ z, (a z).right = (b z).left) →
      ContMDiff J I n fun z ↦ (a z).comp (b z) (h z) := by
  let := chartedSpaceArrows (H := H) hs
  intro ha hb h
  refine (contMDiff_arrows_iff I n hs).mpr
    ⟨(isTopologicalGroupoid hs).continuous_comp.comp
      ((ha.continuous.prodMk hb.continuous).subtype_mk h), ?_⟩
  simpa only [Quiver.Total.comp_left, Function.comp_def] using
    (isLocalDiffeomorph_source I n hs).contMDiff.comp ha

section SmoothArrows

variable [ChartedSpace H' (Quiver.Total C)]

/-- When the source of `C` is a `C^n` local diffeomorphism, the quotient projection `mapTotal` onto
the arrows of `EffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_mapTotal
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph J I n (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro a
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.left ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) a :=
    (hs a).comp (hg := isLocalDiffeomorph_toEffectiveQuotient_obj I n a.left)
  exact hcomp.of_comp_left
    (isLocalDiffeomorph_source I n hs.isLocalHomeomorph _)
    isQuotientMap_mapTotal.continuous.continuousAt

/-- The quotient projection `mapTotal` onto the arrows of `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_mapTotal
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff J I n (toEffectiveQuotient C).toPrefunctor.mapTotal :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  (isLocalDiffeomorph_mapTotal I n hs).contMDiff

/-- Universal smoothness property of the effective arrow manifold: for `m ≤ n`, a map out of
`Quiver.Total (EffectiveQuotient C)` is `C^m` if and only if its composite with `mapTotal` is
`C^m`. -/
theorem contMDiff_from_arrows_iff {E'' H'' P : Type*} [NormedAddCommGroup E'']
    [NormedSpace 𝕜 E''] [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
    [TopologicalSpace P] [ChartedSpace H'' P] {m : ℕ∞ω} (hm : m ≤ n)
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    {g : Quiver.Total (EffectiveQuotient C) → P} :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I K m g ↔ ContMDiff J K m (g ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  ((isLocalDiffeomorph_mapTotal I n hs).contMDiff_comp_iff mapTotal_surjective hm).symm

/-- When the source of `C` is a `C^n` local diffeomorphism and the target of `C` is `C^n`, the
target map of `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_target
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (contMDiff_from_arrows_iff I n le_rfl hs).mpr
    ((contMDiff_toEffectiveQuotient_obj I n).comp ht)

/-- When the source of `C` is a `C^n` local diffeomorphism and the target of `C` is `C^n`, arrow
inversion on `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_inverse
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n fun a : Quiver.Total (EffectiveQuotient C) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (contMDiff_arrows_iff I n hs.isLocalHomeomorph).mpr
    ⟨(isTopologicalGroupoid hs.isLocalHomeomorph).continuous_inverse, contMDiff_target I n hs ht⟩

/-- Arrow inversion on `EffectiveQuotient C` as a `C^n` diffeomorphism. -/
def inverseDiffeomorph
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    Quiver.Total (EffectiveQuotient C) ≃ₘ^n⟮I, I⟯ Quiver.Total (EffectiveQuotient C) :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  { toFun a := ⟨a.right, a.left, inv a.hom⟩
    invFun a := ⟨a.right, a.left, inv a.hom⟩
    left_inv a := by simp
    right_inv a := by simp
    contMDiff_toFun := contMDiff_inverse I n hs ht
    contMDiff_invFun := contMDiff_inverse I n hs ht }

@[simp]
theorem inverseDiffeomorph_apply
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C))
    (a : Quiver.Total (EffectiveQuotient C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    inverseDiffeomorph I n hs ht a = ⟨a.right, a.left, inv a.hom⟩ :=
  (rfl)

@[simp]
theorem inverseDiffeomorph_symm
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    (inverseDiffeomorph I n hs ht).symm = inverseDiffeomorph I n hs ht :=
  (rfl)

/-- When the source of `C` is a `C^n` local diffeomorphism and the target of `C` is `C^n`, the
target map of `EffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact fun a ↦ ((inverseDiffeomorph I n hs ht).isLocalDiffeomorph a).comp
    (hg := isLocalDiffeomorph_source I n hs.isLocalHomeomorph _)

end SmoothArrows

/-- When every arrow of `C` is ineffective, the source map is a `C^n` diffeomorphism from the arrow
manifold of `EffectiveQuotient C` onto its object manifold, with inverse the unit map. -/
def arrowDiffeomorphObjectsOfIneffectiveArrowsEqUniv
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (h : ineffectiveArrows C = univ) :
    letI := chartedSpaceArrows (H := H) hs
    Quiver.Total (EffectiveQuotient C) ≃ₘ^n⟮I, I⟯ EffectiveQuotient C :=
  letI := chartedSpaceArrows (H := H) hs
  { toFun := Quiver.Total.left
    invFun y := ⟨y, y, 𝟙 y⟩
    left_inv a := by
      simpa using (arrowHomeomorphObjectsOfIneffectiveArrowsEqUniv hs h).symm_apply_apply a
    right_inv _ := rfl
    contMDiff_toFun := (isLocalDiffeomorph_source I n hs).contMDiff
    contMDiff_invFun := contMDiff_unit I n hs }

@[simp]
theorem arrowDiffeomorphObjectsOfIneffectiveArrowsEqUniv_apply
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (h : ineffectiveArrows C = univ) (a : Quiver.Total (EffectiveQuotient C)) :
    letI := chartedSpaceArrows (H := H) hs
    arrowDiffeomorphObjectsOfIneffectiveArrowsEqUniv I n hs h a = a.left :=
  (rfl)

@[simp]
theorem arrowDiffeomorphObjectsOfIneffectiveArrowsEqUniv_symm_apply
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (h : ineffectiveArrows C = univ) (y : EffectiveQuotient C) :
    letI := chartedSpaceArrows (H := H) hs
    (arrowDiffeomorphObjectsOfIneffectiveArrowsEqUniv I n hs h).symm y = ⟨y, y, 𝟙 y⟩ :=
  (rfl)

end Etale

end SmoothStructure

section HausdorffArrows

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [T2Space (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- In a proper étale topological groupoid with Hausdorff arrow space and boundaryless object
charts over a complete `RCLike` normed space, if source and target are `C^n` local diffeomorphisms
with `1 ≤ n`, then the arrow space of `EffectiveQuotient C` is Hausdorff. -/
theorem t2Space_arrows_of_isLocalDiffeomorph
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) (hn : 1 ≤ n) :
    T2Space (Quiver.Total (EffectiveQuotient C)) := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  exact t2Space_arrows hs.isLocalHomeomorph
    (isClosed_ineffectiveArrows hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp hn)

end HausdorffArrows

end TauCeti.EffectiveQuotient

namespace TauCeti.ActionGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  (G M : Type*) [Group G] [MulAction G M] [TopologicalSpace M] [ChartedSpace H M]

variable {G M} in
/-- A trivial action on a charted space is `C^n` (for instance `MulAction.ofEndHom 1`, where
`htriv` is `fun _ _ ↦ rfl`). -/
theorem contMDiffConstSMul_of_smul_eq_self (htriv : ∀ (g : G) (x : M), g • x = x) :
    ContMDiffConstSMul I n G M :=
  ⟨fun g ↦ contMDiff_id.congr (htriv g)⟩

section Discrete

variable [TopologicalSpace G]

/-- The object manifold of `EffectiveQuotient (ActionCategory G M)` is `C^n`-diffeomorphic to
`M`. -/
def effectiveQuotientObjDiffeomorph :
    EffectiveQuotient (ActionCategory G M) ≃ₘ^n⟮I, I⟯ M :=
  (EffectiveQuotient.objDiffeomorph I n (C := ActionCategory G M)).symm.trans
    (objectDiffeomorph I n G M)

@[simp]
theorem effectiveQuotientObjDiffeomorph_toEffectiveQuotient_obj (a : ActionCategory G M) :
    effectiveQuotientObjDiffeomorph I n G M ((toEffectiveQuotient (ActionCategory G M)).obj a) =
      a.back := by
  simp [effectiveQuotientObjDiffeomorph]

@[simp]
theorem effectiveQuotientObjDiffeomorph_symm_apply (x : M) :
    (effectiveQuotientObjDiffeomorph I n G M).symm x =
      (toEffectiveQuotient (ActionCategory G M)).obj (ActionCategory.objEquiv G M x) := by
  apply (effectiveQuotientObjDiffeomorph I n G M).injective
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply,
    effectiveQuotientObjDiffeomorph_toEffectiveQuotient_obj]
  rfl

variable {G M} [DiscreteTopology G] [ContinuousSMul G M]

/-- **Smooth trivial-gerbe reduction.** When a discrete group `G` acts trivially on a `C^n`
manifold `M`, the arrow manifold of `EffectiveQuotient (ActionCategory G M)` is `C^n`-diffeomorphic
to `M`: dividing out the constant ineffective kernel `G` collapses the gerbe `G ⋉ M` to the unit
groupoid `M ⇒ M`. -/
def effectiveQuotientArrowDiffeomorphOfSmulEqSelf (htriv : ∀ (g : G) (x : M), g • x = x) :
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source G M)
    Quiver.Total (EffectiveQuotient (ActionCategory G M)) ≃ₘ^n⟮I, I⟯ M :=
  letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source G M)
  (EffectiveQuotient.arrowDiffeomorphObjectsOfIneffectiveArrowsEqUniv I n
    (isLocalHomeomorph_source G M) (ineffectiveArrows_eq_univ_of_smul_eq_self htriv)).trans
      (effectiveQuotientObjDiffeomorph I n G M)

@[simp]
theorem effectiveQuotientArrowDiffeomorphOfSmulEqSelf_mapTotal
    (htriv : ∀ (g : G) (x : M), g • x = x) (f : Quiver.Total (ActionCategory G M)) :
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source G M)
    effectiveQuotientArrowDiffeomorphOfSmulEqSelf I n htriv
      ((toEffectiveQuotient (ActionCategory G M)).toPrefunctor.mapTotal f) = f.left.back := by
  let := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source G M)
  simp [effectiveQuotientArrowDiffeomorphOfSmulEqSelf, Prefunctor.mapTotal]

@[simp]
theorem effectiveQuotientArrowDiffeomorphOfSmulEqSelf_symm_apply
    (htriv : ∀ (g : G) (x : M), g • x = x) (x : M) :
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source G M)
    (effectiveQuotientArrowDiffeomorphOfSmulEqSelf I n htriv).symm x =
      ⟨(toEffectiveQuotient (ActionCategory G M)).obj (ActionCategory.objEquiv G M x),
        (toEffectiveQuotient (ActionCategory G M)).obj (ActionCategory.objEquiv G M x), 𝟙 _⟩ := by
  let := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source G M)
  simp [effectiveQuotientArrowDiffeomorphOfSmulEqSelf]

end Discrete

end TauCeti.ActionGroupoid

namespace TauCeti

section LinearActionChart

variable {𝕜 G E C : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]

/-- In a fully faithful linear action chart `F : G ⋉ B ⥤ C` lying over an injective map `f : B → C`,
the stabilizer isomorphism carries `σ.toMonoidHom.ker ∩ stabilizer G v` onto
`ineffectiveKernel hs (f v)`. -/
theorem map_stabilizerMulEquivAutOfChart_ker
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (σ : ContRepresentation 𝕜 G E) (B : TopologicalSpace.Opens E) [MulAction G B]
    (hval : ∀ (g : G) (v : B), (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f)
    {F : ActionCategory G B ⥤ C} [F.Full] [F.Faithful] (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : G, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv G B).symm (g, v)).hom⟩ : Quiver.Total C))
    (v : B) :
    (σ.toMonoidHom.ker.subgroupOf (MulAction.stabilizer G v)).map
      (stabilizerMulEquivAutOfChart hobj v).toMonoidHom = ineffectiveKernel hs (f v) := by
  rw [← σ.germKernel_eq_ker_of_val_smul B hval v]
  exact map_stabilizerMulEquivAutOfChart_germKernel hs hf hobj hσ v

/-- In a fully faithful linear action chart `F : G ⋉ B ⥤ C`, an object `f v` lies in the principal
locus `ineffectiveKernel hs (f v) = ⊤` precisely when `v` avoids the proper fixed subspaces of all
`g ∉ σ.toMonoidHom.ker`. -/
theorem ineffectiveKernel_eq_top_iff_forall_notMem_eqLocus
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (σ : ContRepresentation 𝕜 G E) (B : TopologicalSpace.Opens E) [MulAction G B]
    (hval : ∀ (g : G) (v : B), (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f)
    {F : ActionCategory G B ⥤ C} [F.Full] [F.Faithful] (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : G, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv G B).symm (g, v)).hom⟩ : Quiver.Total C))
    (v : B) :
    ineffectiveKernel hs (f v) = ⊤ ↔
      ∀ g ∉ σ.toMonoidHom.ker,
        (v : E) ∉ LinearMap.eqLocus (σ g).toLinearMap LinearMap.id := by
  rw [ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs hf hobj hσ v]
  exact σ.stabilizer_eq_germKernel_iff_of_val_smul B hval v

/-- In a retained-arrow linear isotropy chart `Aut x ⋉ B ⥤ C` centred at `z` over `x`, the kernel of
the linear representation `σ : ContRepresentation 𝕜 (Aut x) E` is `ineffectiveKernel hs x`. -/
theorem ker_eq_ineffectiveKernel_of_linear_chart
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} (σ : ContRepresentation 𝕜 (Aut x) E) (B : TopologicalSpace.Opens E)
    [MulAction (Aut x) B] (hval : ∀ (g : Aut x) (v : B), (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f) (z : B)
    {F : ActionCategory (Aut x) B ⥤ C} (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ : Quiver.Total C) =
        ⟨x, x, g.asIso.hom⟩) :
    σ.toMonoidHom.ker = ineffectiveKernel hs x := by
  rw [← σ.germKernel_eq_ker_of_val_smul B hval z]
  ext g
  have hmem := mem_ineffectiveArrows_map_iff_mem_germKernel hf hobj
    ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom (hσ _)
  have hback : (ActionCategory.objEquiv (Aut x) B z).back = z := rfl
  rw [hcentre g, ← mem_ineffectiveKernel, ActionCategory.totalEquiv_symm_apply_hom_hom,
    ActionCategory.totalEquiv_symm_apply_left, hback] at hmem
  exact hmem.symm

/-- In a retained-arrow linear isotropy chart `Aut x ⋉ B ⥤ C` centred at `z` over `x`, the kernel of
the permutation action of `Aut x` on `B` is `ineffectiveKernel hs x`. Thus
`Aut x ⧸ ineffectiveKernel hs x` acts faithfully on `B` via
`TauCeti.instFaithfulSMulQuotientKerToPermHom`. -/
theorem ker_toPermHom_eq_ineffectiveKernel_of_linear_chart
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} (σ : ContRepresentation 𝕜 (Aut x) E) (B : TopologicalSpace.Opens E)
    [MulAction (Aut x) B] (hval : ∀ (g : Aut x) (v : B), (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f) (z : B)
    {F : ActionCategory (Aut x) B ⥤ C} (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ : Quiver.Total C) =
        ⟨x, x, g.asIso.hom⟩) :
    (MulAction.toPermHom (Aut x) B).ker = ineffectiveKernel hs x := by
  have : Nonempty B := ⟨z⟩
  rw [σ.ker_toPermHom_eq_ker_of_val_smul B hval,
    ker_eq_ineffectiveKernel_of_linear_chart hs σ B hval hf z hobj hσ hcentre]

/-- Given a linear isotropy representation `σ : ContRepresentation 𝕜 (Aut x) E` whose kernel
contains `ineffectiveKernel hs x`, `σ` descends to a linear representation of the effective isotropy
group `Aut ((toEffectiveQuotient C).obj x)` on `E`. -/
def effectiveLinearRepresentation
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} (σ : ContRepresentation 𝕜 (Aut x) E)
    (hker : ineffectiveKernel hs x ≤ σ.toMonoidHom.ker) :
    ContRepresentation 𝕜 (Aut ((toEffectiveQuotient C).obj x)) E :=
  ⟨(QuotientGroup.lift (ineffectiveKernel hs x) σ.toMonoidHom hker).comp
    (quotientIneffectiveKernelMulEquivAut hs x).symm.toMonoidHom⟩

@[simp]
theorem effectiveLinearRepresentation_mapAut
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} (σ : ContRepresentation 𝕜 (Aut x) E)
    (hker : ineffectiveKernel hs x ≤ σ.toMonoidHom.ker) (g : Aut x) :
    effectiveLinearRepresentation hs σ hker ((toEffectiveQuotient C).mapAut x g) = σ g := by
  change (QuotientGroup.lift (ineffectiveKernel hs x) σ.toMonoidHom hker)
    ((quotientIneffectiveKernelMulEquivAut hs x).symm ((toEffectiveQuotient C).mapAut x g)) = σ g
  rw [← quotientIneffectiveKernelMulEquivAut_mk hs x g, MulEquiv.symm_apply_apply,
    QuotientGroup.lift_mk, ContRepresentation.toMonoidHom_apply]

/-- When `σ.toMonoidHom.ker = ineffectiveKernel hs x`, the descended representation of the effective
isotropy group `Aut ((toEffectiveQuotient C).obj x)` on `E` is faithful. -/
theorem injective_effectiveLinearRepresentation
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} (σ : ContRepresentation 𝕜 (Aut x) E)
    (hker : σ.toMonoidHom.ker = ineffectiveKernel hs x) :
    Function.Injective (effectiveLinearRepresentation hs σ hker.symm.le) := by
  intro e₁ e₂ h
  obtain ⟨g₁, rfl⟩ := mapAut_toEffectiveQuotient_surjective x e₁
  obtain ⟨g₂, rfl⟩ := mapAut_toEffectiveQuotient_surjective x e₂
  rw [effectiveLinearRepresentation_mapAut, effectiveLinearRepresentation_mapAut] at h
  have h' : σ.toMonoidHom g₁ = σ.toMonoidHom g₂ := h
  have hmem : g₁⁻¹ * g₂ ∈ ineffectiveKernel hs x := by
    rw [← hker, MonoidHom.mem_ker, map_mul, ← h', ← map_mul, inv_mul_cancel, map_one]
  rw [← ker_mapAut_toEffectiveQuotient hs x, MonoidHom.mem_ker, map_mul, map_inv,
    inv_mul_eq_one] at hmem
  exact hmem

end LinearActionChart

section LinearBallPrincipalLocus

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I n C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [T2Space (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- **Faithful effective linear slice and fixed-subspace principal locus.** Around every object `x`
of a Hausdorff proper étale real `C^n` groupoid (`1 ≤ n`), inside any neighbourhood `s ∈ 𝓝 x`,
there is a retained-arrow linear-ball chart `Aut x ⋉ B ⥤ C` in which:
* both `σ.toMonoidHom.ker` and `(MulAction.toPermHom (Aut x) B).ker` equal
  `ineffectiveKernel hs.isLocalHomeomorph x`, so the effective isotropy
  `Aut ((toEffectiveQuotient C).obj x)` acts faithfully on `E` and on `B`;
* every `g ∉ ineffectiveKernel hs.isLocalHomeomorph x` fixes a proper linear subspace
  `LinearMap.eqLocus (σ g).toLinearMap LinearMap.id < ⊤`;
* a point `f v` lies in the principal locus `ineffectiveKernel hs.isLocalHomeomorph (f v) = ⊤`
  precisely when `v` avoids those proper fixed subspaces. -/
theorem exists_linear_ball_principal_locus
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hn : 1 ≤ n) (x : C) {s : Set C} (hsx : s ∈ 𝓝 x) :
    ∃ (ι : Fintype (Aut x)), letI := ι;
    ∃ (σ : ContRepresentation ℝ (Aut x) E) (c : ℝ) (B : TopologicalSpace.Opens E)
      (_ : MulAction (Aut x) B) (f : B → C) (z : B)
      (F : ActionCategory (Aut x) B ⥤ C),
      0 < c ∧ (B : Set E) = σ.toRepresentation.sumOfConjugatesInnerSublevel c ∧
      (z : E) = 0 ∧ f z = x ∧
      (∀ g : Aut x, ∀ v : B, (g • v : B).val = σ g v) ∧
      ContMDiffConstSMul 𝓘(ℝ, E) n (Aut x) B ∧
      IsOpenEmbedding f ∧ IsLocalDiffeomorph 𝓘(ℝ, E) I n f ∧ range f ⊆ s ∧
      (∀ a, F.obj a = f a.back) ∧ F.Full ∧ F.Faithful ∧
      σ.toMonoidHom.ker = ineffectiveKernel hs.isLocalHomeomorph x ∧
      (MulAction.toPermHom (Aut x) B).ker = ineffectiveKernel hs.isLocalHomeomorph x ∧
      (∀ g ∉ ineffectiveKernel hs.isLocalHomeomorph x,
        LinearMap.eqLocus (σ g).toLinearMap LinearMap.id < ⊤) ∧
      ∀ v : B,
        ineffectiveKernel hs.isLocalHomeomorph (f v) = ⊤ ↔
          ∀ g ∉ ineffectiveKernel hs.isLocalHomeomorph x,
            (v : E) ∉ LinearMap.eqLocus (σ g).toLinearMap LinearMap.id := by
  obtain ⟨ι, σ, c, B, actB, f, z, F, hc, hB, hz, hfz, hval, hsmul, hfopen, hfdiff, hrange,
      hobj, hFull, hFaithful, hopen, -, hcentre⟩ :=
    exists_linear_ball_isotropy_chart hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp hn x hsx
  let : MulAction (Aut x) B := actB
  have : F.Full := hFull
  have : F.Faithful := hFaithful
  have hker : σ.toMonoidHom.ker = ineffectiveKernel hs.isLocalHomeomorph x :=
    ker_eq_ineffectiveKernel_of_linear_chart hs.isLocalHomeomorph σ B hval hfopen.injective z
      hobj hopen hcentre
  have hperm : (MulAction.toPermHom (Aut x) B).ker = ineffectiveKernel hs.isLocalHomeomorph x :=
    ker_toPermHom_eq_ineffectiveKernel_of_linear_chart hs.isLocalHomeomorph σ B hval
      hfopen.injective z hobj hopen hcentre
  refine ⟨ι, σ, c, B, actB, f, z, F, hc, hB, hz, hfz, hval, hsmul, hfopen, hfdiff, hrange,
    hobj, hFull, hFaithful, hker, hperm, fun g hg ↦ ?_, fun v ↦ ?_⟩
  · rw [σ.eqLocus_lt_top_iff_notMem_ker, hker]
    exact hg
  · rw [ineffectiveKernel_eq_top_iff_forall_notMem_eqLocus hs.isLocalHomeomorph σ B hval
      hfopen.injective hobj hopen v, hker]

end LinearBallPrincipalLocus

end TauCeti
