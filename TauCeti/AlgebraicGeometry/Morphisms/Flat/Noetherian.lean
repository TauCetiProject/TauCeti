/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.RingTheory.Flat.Noetherian

/-!
# Faithfully flat descent of local Noetherianity

Local Noetherianity descends along fpqc covering families. Over each affine open of the base,
a finite affine refinement gives a single affine faithfully flat cover, where Noetherianity
is a ring-theoretic property. In particular, one can test local Noetherianity on a smooth
surjective cover, even when the cover morphism is not quasi-compact.

## References

* [Stacks Project, Tag 034C](https://stacks.math.columbia.edu/tag/034C) for the fppf case.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u v

namespace IsLocallyNoetherian

variable {Y : Scheme.{u}}

open Scheme in
/-- Local Noetherianity descends along a quasi-compact covering family of flat morphisms. -/
theorem of_flat_quasiCompactCover (𝒰 : Y.Cover.{v} (Scheme.precoverage @Flat))
    [QuasiCompactCover 𝒰.toPreZeroHypercover] (h : ∀ i, IsLocallyNoetherian (𝒰.X i)) :
    IsLocallyNoetherian Y := by
  refine (isLocallyNoetherian_iff_openCover Y.affineCover).mpr fun i ↦ ?_
  -- Restrict the cover to an affine chart and refine by finitely many affine opens.
  have : Scheme.IsJointlySurjectivePreserving (@Flat : MorphismProperty Scheme.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  have : (Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})).IsStableUnderBaseChange :=
    instIsStableUnderBaseChangePrecoverageOfIsJointlySurjectivePreservingOfIsStableUnderBaseChange
      (P := @Flat)
  have : MorphismProperty.RespectsLeft (@Flat : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    ⟨fun i _ f _ ↦ Flat.comp i f⟩
  let ι := Y.affineCover.f i
  let 𝒱 : (Y.affineCover.X i).Cover.{v} (Scheme.precoverage @Flat) := 𝒰.pullback₁ ι
  have : QuasiCompactCover 𝒱.toPreZeroHypercover :=
    inferInstanceAs (QuasiCompactCover (𝒰.toPreZeroHypercover.pullback₁ ι))
  obtain ⟨𝒲, r, hfinite, hr⟩ := QuasiCompactCover.exists_hom (P := @Flat) 𝒱
  -- The disjoint union of the refinement is affine and locally Noetherian.
  have : Finite 𝒲.cover.I₀ := hfinite
  let _ : Fintype 𝒲.I₀ := Fintype.ofFinite 𝒲.I₀
  have : Small.{u} 𝒲.cover.I₀ := small_of_injective (Fintype.equivFin 𝒲.I₀).injective
  have hAffine : ∀ j : 𝒲.cover.I₀, IsAffine (𝒲.cover.X j) :=
    fun j ↦ inferInstanceAs (IsAffine (Spec (𝒲.X j)))
  have : IsAffine (∐ 𝒲.cover.X) := instIsAffineSigmaObjScheme (g := 𝒲.cover.X)
  have hNoeth (j : 𝒲.I₀) : IsLocallyNoetherian (𝒲.cover.X j) := by
    have := h (r.s₀ j)
    have := hr j
    have : IsOpenImmersion (𝒰.pullbackHom ι (r.s₀ j)) :=
      inferInstanceAs (IsOpenImmersion (pullback.snd ι (𝒰.f (r.s₀ j))))
    exact isLocallyNoetherian_of_isOpenImmersion (r.h₀ j ≫ 𝒰.pullbackHom ι (r.s₀ j))
  have : ∀ j : 𝒲.cover.I₀, Flat (𝒲.cover.f j) := fun j ↦ 𝒲.cover.map_prop j
  have : IsLocallyNoetherian (∐ 𝒲.cover.X) :=
    (isLocallyNoetherian_iff_openCover (sigmaOpenCover 𝒲.cover.X)).mpr fun j ↦ hNoeth j
  have : Scheme.JointlySurjective (Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  let p : (∐ 𝒲.cover.X) ⟶ Y.affineCover.X i := Sigma.desc 𝒲.cover.f
  have : Surjective p := Surjective.sigmaDesc_of_union_range_eq_univ 𝒲.cover.iUnion_range
  have : Flat p := inferInstanceAs (Flat (Sigma.desc 𝒲.cover.f))
  -- The map on global sections is faithfully flat, so its source ring is Noetherian.
  have hp := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := p)).mp
    ⟨inferInstance, inferInstance⟩
  algebraize [p.appTop.hom]
  have : IsNoetherianRing Γ(∐ 𝒲.cover.X, ⊤) := component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ(Y.affineCover.X i, ⊤) :=
    IsNoetherianRing.of_faithfullyFlat Γ(∐ 𝒲.cover.X, ⊤)
  exact isLocallyNoetherian_of_isOpenImmersion (Y.affineCover.X i).isoSpec.hom

/-- A surjective, open flat morphism from a locally Noetherian scheme has locally Noetherian
target. No quasi-compactness of the morphism is required. -/
theorem of_flat_of_surjective_of_isOpenMap {X : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsLocallyNoetherian X] (hf : IsOpenMap f) : IsLocallyNoetherian Y := by
  let 𝒰 : Y.Cover.{0} (Scheme.precoverage @Flat) := f.cover (P := @Flat) inferInstance
  have : Scheme.JointlySurjective (Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  have : QuasiCompactCover 𝒰.toPreZeroHypercover := .of_isOpenMap (𝒰 := 𝒰) (fun _ ↦ hf)
  exact of_flat_quasiCompactCover 𝒰 fun _ ↦ inferInstanceAs (IsLocallyNoetherian X)

end IsLocallyNoetherian

/-- Local Noetherianity can be tested on a smooth surjective cover. -/
theorem Scheme.Hom.isLocallyNoetherian_iff_of_smooth_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [Surjective f] : IsLocallyNoetherian X ↔ IsLocallyNoetherian Y :=
  ⟨fun _ ↦ .of_flat_of_surjective_of_isOpenMap f f.isOpenMap,
    fun _ ↦ LocallyOfFiniteType.isLocallyNoetherian f⟩

end AlgebraicGeometry
