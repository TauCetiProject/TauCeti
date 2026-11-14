/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.IneffectiveKernel
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Principal

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The smooth effective quotient presentation

Given an étale topological groupoid `C` whose objects form a `C^n` manifold modelled on `I`, its
effective quotient `TauCeti.EffectiveQuotient C` inherits canonical `C^n` manifold structures on
objects and on total arrows:

* On objects, `TauCeti.EffectiveQuotient.instChartedSpaceObjects` pulls the object charts of `C`
  back along the canonical homeomorphism `TauCeti.EffectiveQuotient.objHomeomorph`, making the
  object projection `(TauCeti.toEffectiveQuotient C).obj` a `C^n` diffeomorphism
  (`TauCeti.EffectiveQuotient.objDiffeomorph`).
* On total arrows, `TauCeti.EffectiveQuotient.chartedSpaceArrows` pulls the object charts back
  along the locally homeomorphic source `Quiver.Total.left` via
  `IsLocalHomeomorph.chartedSpaceComap`. For these charts the effective source is a `C^n` local
  diffeomorphism (`TauCeti.EffectiveQuotient.isLocalDiffeomorph_source`), and up to equivalence of
  atlases this is the only `C^n` manifold structure on effective arrows with that property
  (`TauCeti.EffectiveQuotient.compatible_chartedSpaceArrows`).

When the original arrow space is also charted so that source and target on `C` are `C^n` local
diffeomorphisms, the arrow quotient map `(TauCeti.toEffectiveQuotient C).toPrefunctor.mapTotal`
and the effective target, unit, inversion and composition maps are all `C^n` local diffeomorphisms,
with inversion a `C^n` diffeomorphism (`TauCeti.EffectiveQuotient.inverseDiffeomorph`).

Finally, when `1 ≤ n`, the object model is boundaryless over a complete `RCLike` normed space, the
original arrow space is Hausdorff, and the source-target map is proper, the identity principle
closes the ineffective arrows (`TauCeti.isClosed_ineffectiveArrows`) and hence makes the effective
arrow space Hausdorff (`TauCeti.EffectiveQuotient.t2Space_arrows`). Together with properness and
second countability from `TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology` and the
dense open principal stratum from `TauCeti.Topology.CategoryTheory.Groupoid.Effective.Principal`,
this upgrades effective reduction to a `C^n` Hausdorff proper étale presentation.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1.
-/

public section

open CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace EffectiveQuotient

section Objects

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [ChartedSpace H C]

/-- The objects of the effective quotient carry the charted-space structure pulled back from the
objects of `C` along `(objHomeomorph C).symm`. -/
instance instChartedSpaceObjects : ChartedSpace H (EffectiveQuotient C) :=
  (objHomeomorph C).symm.pullbackChartedSpace

/-- The objects of the effective quotient form a `C^n` manifold whenever the objects of `C` do. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n C] :
    IsManifold I n (EffectiveQuotient C) :=
  (objHomeomorph C).symm.pullback_isManifold I n

/-- The object projection `C → EffectiveQuotient C` as a `C^n` diffeomorphism. -/
def objDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (C : Type*) [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
    [ChartedSpace H C] :
    C ≃ₘ^n⟮I, I⟯ EffectiveQuotient C :=
  ((objHomeomorph C).symm.pullbackDiffeomorph I n).symm

@[simp]
theorem objDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : C) :
    objDiffeomorph I n C x = (toEffectiveQuotient C).obj x := by
  simp [objDiffeomorph]

@[simp]
theorem objDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (x : EffectiveQuotient C) :
    (objDiffeomorph I n C).symm x = (objEquiv C).symm x := by
  apply (objDiffeomorph I n C).injective
  simp

@[simp]
theorem objDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objDiffeomorph I n C).toHomeomorph = objHomeomorph C := by
  ext x
  simp

/-- The object map of `toEffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_toEffectiveQuotient_obj {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (toEffectiveQuotient C).obj := by
  have h := (objDiffeomorph I n C).isLocalDiffeomorph
  have heq : ⇑(objDiffeomorph I n C) = (toEffectiveQuotient C).obj :=
    funext (objDiffeomorph_apply I n)
  rwa [heq] at h

end Objects

section Arrows

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- For an étale topological groupoid `C`, the total arrows of `EffectiveQuotient C` carry the
charted-space structure pulled back from objects along the locally homeomorphic source. -/
@[instance_reducible]
noncomputable def chartedSpaceArrows
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    ChartedSpace H (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).chartedSpaceComap

/-- When the objects of `C` form a `C^n` manifold, so do the total arrows of
`EffectiveQuotient C`. -/
theorem isManifold_arrows [IsManifold I n C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsManifold I n (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).isManifold_chartedSpaceComap

/-- The source map of `EffectiveQuotient C` is a `C^n` local diffeomorphism for the pulled-back
arrow charts. -/
theorem isLocalDiffeomorph_source
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  (isLocalHomeomorph_source hs).isLocalDiffeomorph_chartedSpaceComap

/-- The source map of `EffectiveQuotient C` is `C^n` for the pulled-back arrow charts. -/
theorem contMDiff_source
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  (isLocalHomeomorph_source hs).contMDiff_chartedSpaceComap

section UniversalProperty

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : N → Quiver.Total (EffectiveQuotient C)} {s : Set N} {z : N}

/-- A map into `Quiver.Total (EffectiveQuotient C)` is `C^n` within `s` at `z` if and only if it is
continuous within `s` at `z` and its composite with the effective source is `C^n` within `s` at
`z`. -/
theorem contMDiffWithinAt_arrows_iff
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiffWithinAt J I n f s z ↔
      ContinuousWithinAt f s z ∧ ContMDiffWithinAt J I n (Quiver.Total.left ∘ f) s z :=
  (isLocalHomeomorph_source hs).contMDiffWithinAt_chartedSpaceComap_iff

/-- A map into `Quiver.Total (EffectiveQuotient C)` is `C^n` at `z` if and only if it is continuous
at `z` and its composite with the effective source is `C^n` at `z`. -/
theorem contMDiffAt_arrows_iff
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiffAt J I n f z ↔
      ContinuousAt f z ∧ ContMDiffAt J I n (Quiver.Total.left ∘ f) z :=
  (isLocalHomeomorph_source hs).contMDiffAt_chartedSpaceComap_iff

/-- A map into `Quiver.Total (EffectiveQuotient C)` is `C^n` on `s` if and only if it is continuous
on `s` and its composite with the effective source is `C^n` on `s`. -/
theorem contMDiffOn_arrows_iff
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiffOn J I n f s ↔
      ContinuousOn f s ∧ ContMDiffOn J I n (Quiver.Total.left ∘ f) s :=
  (isLocalHomeomorph_source hs).contMDiffOn_chartedSpaceComap_iff

/-- A map into `Quiver.Total (EffectiveQuotient C)` is `C^n` if and only if it is continuous and
its composite with the effective source is `C^n`. -/
theorem contMDiff_arrows_iff
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff J I n f ↔ Continuous f ∧ ContMDiff J I n (Quiver.Total.left ∘ f) :=
  (isLocalHomeomorph_source hs).contMDiff_chartedSpaceComap_iff

end UniversalProperty

/-- Any `C^n` manifold structure on `Quiver.Total (EffectiveQuotient C)` for which the effective
source is a `C^n` local diffeomorphism is compatible with `chartedSpaceArrows`. -/
theorem compatible_chartedSpaceArrows [IsManifold I n C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    [c : ChartedSpace H (Quiver.Total (EffectiveQuotient C))]
    [IsManifold I n (Quiver.Total (EffectiveQuotient C))]
    (hsc : IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C)) :
    ∀ e ∈ c.atlas, ∀ e' ∈ (chartedSpaceArrows (H := H) hs).atlas,
      e.symm.trans e' ∈ contDiffGroupoid n I :=
  (isLocalHomeomorph_source hs).compatible_chartedSpaceComap hsc

/-- The unit map of `EffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_unit
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    IsLocalDiffeomorph I I n
      fun x : EffectiveQuotient C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := isTopologicalGroupoid hs
  let := chartedSpaceArrows (H := H) hs
  exact IsTopologicalGroupoid.isLocalDiffeomorph_unit (isLocalDiffeomorph_source hs)

/-- The unit map of `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_unit
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I I n
      fun x : EffectiveQuotient C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := chartedSpaceArrows (H := H) hs
  exact (isLocalDiffeomorph_unit hs).contMDiff

section SmoothArrows

variable [ChartedSpace H' (Quiver.Total C)]

/-- When the source of `C` is a `C^n` local diffeomorphism, the total-arrow quotient map to
`EffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_mapTotal
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph J I n (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro a
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.left ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) a := by
    have heq : Quiver.Total.left ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal =
        (toEffectiveQuotient C).obj ∘ Quiver.Total.left :=
      funext fun b ↦ Prefunctor.mapTotal_left _ b
    rw [heq]
    exact (hs a).comp (hg := isLocalDiffeomorph_toEffectiveQuotient_obj a.left)
  exact hcomp.of_comp_left (isLocalDiffeomorph_source hs.isLocalHomeomorph _)
    isQuotientMap_mapTotal.continuous.continuousAt

/-- When the source of `C` is a `C^n` local diffeomorphism, the total-arrow quotient map to
`EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_mapTotal
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff J I n (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (isLocalDiffeomorph_mapTotal hs).contMDiff

/-- When source and target on `C` are `C^n` local diffeomorphisms, the target map of
`EffectiveQuotient C` is also a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro b
  obtain ⟨a, rfl⟩ := mapTotal_surjective b
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.right ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) a := by
    have heq : Quiver.Total.right ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal =
        (toEffectiveQuotient C).obj ∘ Quiver.Total.right :=
      funext fun c ↦ Prefunctor.mapTotal_right _ c
    rw [heq]
    exact (ht a).comp (hg := isLocalDiffeomorph_toEffectiveQuotient_obj a.right)
  exact hcomp.of_comp_right (isLocalDiffeomorph_mapTotal hs a)

/-- When source and target on `C` are `C^n` local diffeomorphisms, the target map of
`EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_target
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (isLocalDiffeomorph_target hs ht).contMDiff

/-- Inversion on the total arrows of `EffectiveQuotient C` is a `C^n` local diffeomorphism when
source and target on `C` are `C^n` local diffeomorphisms. -/
theorem isLocalDiffeomorph_inverse
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph I I n
      fun a : Quiver.Total (EffectiveQuotient C) ↦
        (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact IsTopologicalGroupoid.isLocalDiffeomorph_inverse
    (isLocalDiffeomorph_source hs.isLocalHomeomorph) (isLocalDiffeomorph_target hs ht)

/-- Inversion on the total arrows of `EffectiveQuotient C` is `C^n` when source and target on `C`
are `C^n` local diffeomorphisms. -/
theorem contMDiff_inverse
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n
      fun a : Quiver.Total (EffectiveQuotient C) ↦
        (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (isLocalDiffeomorph_inverse hs ht).contMDiff

/-- Inversion on the total arrows of `EffectiveQuotient C` is a `C^n` diffeomorphism when source
and target on `C` are `C^n` local diffeomorphisms. -/
noncomputable def inverseDiffeomorph
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    Quiver.Total (EffectiveQuotient C) ≃ₘ^n⟮I, I⟯ Quiver.Total (EffectiveQuotient C) :=
  letI := isTopologicalGroupoid hs.isLocalHomeomorph
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  IsTopologicalGroupoid.inverseDiffeomorph
    (isLocalDiffeomorph_source hs.isLocalHomeomorph) (isLocalDiffeomorph_target hs ht)

@[simp]
theorem inverseDiffeomorph_apply
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (a : Quiver.Total (EffectiveQuotient C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    inverseDiffeomorph hs ht a = ⟨a.right, a.left, inv a.hom⟩ := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  simp [inverseDiffeomorph]

@[simp]
theorem inverseDiffeomorph_symm_apply
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (a : Quiver.Total (EffectiveQuotient C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    (inverseDiffeomorph hs ht).symm a = ⟨a.right, a.left, inv a.hom⟩ := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  simp [inverseDiffeomorph]

@[simp]
theorem inverseDiffeomorph_toHomeomorph
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := isTopologicalGroupoid hs.isLocalHomeomorph
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    (inverseDiffeomorph hs ht).toHomeomorph =
      IsTopologicalGroupoid.inverseHomeomorph (EffectiveQuotient C) := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  simp [inverseDiffeomorph]

/-- Composition of composable pairs in `EffectiveQuotient C` is a `C^n` local diffeomorphism when
source and target on `C` are `C^n` local diffeomorphisms. -/
theorem isLocalDiffeomorph_comp
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := isTopologicalGroupoid hs.isLocalHomeomorph
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    letI := IsTopologicalGroupoid.composablePairsChartedSpace (H' := H)
      (isLocalHomeomorph_source hs.isLocalHomeomorph)
    IsLocalDiffeomorph I I n
      fun p : {p : Quiver.Total (EffectiveQuotient C) × Quiver.Total (EffectiveQuotient C) //
        p.1.right = p.2.left} ↦ p.1.1.comp p.1.2 p.2 := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact IsTopologicalGroupoid.isLocalDiffeomorph_comp
    (isLocalDiffeomorph_source hs.isLocalHomeomorph) (isLocalDiffeomorph_target hs ht)

/-- Composition of composable pairs in `EffectiveQuotient C` is `C^n` when source and target on `C`
are `C^n` local diffeomorphisms. -/
theorem contMDiff_comp
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := isTopologicalGroupoid hs.isLocalHomeomorph
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    letI := IsTopologicalGroupoid.composablePairsChartedSpace (H' := H)
      (isLocalHomeomorph_source hs.isLocalHomeomorph)
    ContMDiff I I n
      fun p : {p : Quiver.Total (EffectiveQuotient C) × Quiver.Total (EffectiveQuotient C) //
        p.1.right = p.2.left} ↦ p.1.1.comp p.1.2 p.2 := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  let := IsTopologicalGroupoid.composablePairsChartedSpace (H' := H)
    (isLocalHomeomorph_source hs.isLocalHomeomorph)
  exact (isLocalDiffeomorph_comp hs ht).contMDiff

end SmoothArrows

end Arrows

section Hausdorff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)]

/-- **Hausdorffness of the smooth effective arrow space.** In a proper étale topological groupoid
with Hausdorff arrow space, boundaryless object charts over a complete `RCLike` normed space, and
`C^n` locally diffeomorphic source and target (`1 ≤ n`), the total arrows of `EffectiveQuotient C`
form a Hausdorff space. -/
theorem t2Space_arrows
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hn : 1 ≤ n) :
    T2Space (Quiver.Total (EffectiveQuotient C)) := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  exact t2Space_arrows_of_isClosed_ineffectiveArrows hs.isLocalHomeomorph
    (isClosed_ineffectiveArrows hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp hn)

end Hausdorff

end EffectiveQuotient

end TauCeti
