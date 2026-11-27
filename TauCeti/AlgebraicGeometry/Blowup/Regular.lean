/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Scheme.Regular.Descent
import TauCeti.RingTheory.Ideal.AffineBlowup.Regular
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo

/-!
# Blowing up a regular surface at a point

Let `A` be a regular local ring of dimension two. The blowup `Proj A[𝔪t]` of `Spec A` at its
closed point is covered by the two affine charts `Spec A[𝔪/x]` and `Spec A[𝔪/y]`, for `x, y`
generating the maximal ideal `𝔪` (`TauCeti.AlgebraicGeometry.iSup_opensRange_affineBlowupι`), and
both charts are regular rings
(`TauCeti.IsRegularLocalRing.isRegularRing_affineBlowup_maximalIdeal`). So the blowup is a regular
scheme.

This globalizes. Let `I` be an ideal sheaf on a scheme `X` and `x` a point whose local ring
`𝒪_{X,x}` is regular of dimension two, such that `I` generates the maximal ideal of `𝒪_{X,x}`;
for instance `I` is the ideal sheaf of the closure of `x` with its reduced structure. Over an affine
open `U ∋ x`, the blowup of `X` along `I` is `Proj Γ(X, U)[I(U)t]`, and its base change along the
flat localization `Γ(X, U) → 𝒪_{X,x}` is the blowup of `Spec 𝒪_{X,x}` at its closed point, since
blowing up commutes with flat base change
(`TauCeti.AlgebraicGeometry.isPullback_affineBlowup_of_flat`). Every point of the blowup over `x`
is the image of a point of this regular scheme, and regularity descends along flat morphisms
(`AlgebraicGeometry.Scheme.Hom.isRegularLocalRing_stalk_of_flat`). Away from its centre the blowup
is an isomorphism, so the blowup of a regular scheme along an ideal sheaf that is the maximal ideal
of a two-dimensional local ring at every point of its support is regular. In particular, so is the
blowup of a regular scheme at a closed point with two-dimensional local ring. These are the
blowups of regular arithmetic surfaces, such as regular models of curves over a discrete valuation
ring, at closed points of the special fibre.

## Main results

* `TauCeti.AlgebraicGeometry.isRegular_proj_grade_maximalIdeal`: the blowup of the spectrum of a
  two-dimensional regular local ring at its closed point is regular.
* `Scheme.IdealSheafData.isRegularLocalRing_stalk_blowup_of_stalkIdeal_eq_maximalIdeal`: the
  blowup of a scheme along an ideal sheaf that generates the maximal ideal of a regular
  two-dimensional local ring has regular local rings at the points over that point.
* `Scheme.IdealSheafData.isRegular_blowup_of_stalkIdeal_eq_maximalIdeal`: the blowup of a regular
  scheme along an ideal sheaf that generates the maximal ideal of a two-dimensional local ring at
  every point of its support is regular.
* `TauCeti.AlgebraicGeometry.isRegular_blowup_vanishingIdeal_closure_singleton`: the blowup of a
  regular scheme at a closed point with two-dimensional local ring is regular.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.1
  (blowing up), where blowups of regular schemes along regular centres are shown to be regular.
-/

public section

open CategoryTheory IsLocalRing reesAlgebra

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **The blowup of a regular surface at a closed point is regular, locally.** The blowup
`Proj A[𝔪t]` of the spectrum of a regular local ring `A` of dimension two at its closed point is a
regular scheme. -/
theorem isRegular_proj_grade_maximalIdeal (hdim : ringKrullDim A = 2) :
    IsRegular (Proj (grade (maximalIdeal A))) := by
  obtain ⟨x, y, hxy⟩ := IsRegularLocalRing.exists_span_pair_eq_maximalIdeal hdim
  let s : Fin 2 → A := ![x, y]
  have hs : Ideal.span (Set.range s) = maximalIdeal A := by
    rw [Matrix.range_cons_cons_empty, hxy]
  have hmem (i : Fin 2) : s i ∈ maximalIdeal A := hs ▸ Ideal.subset_span ⟨i, rfl⟩
  have hreg : ∀ i : Fin 2,
      IsRegularRing ((maximalIdeal A).affineBlowup (s i) (Localization.Away (s i))) :=
    Fin.forall_fin_two.mpr
      ⟨IsRegularLocalRing.isRegularRing_affineBlowup_maximalIdeal hdim hxy (Localization.Away x),
        IsRegularLocalRing.isRegularRing_affineBlowup_maximalIdeal hdim
          (by rw [Set.pair_comm, hxy] : Ideal.span {y, x} = _) (Localization.Away y)⟩
  -- The charts of `x` and `y` cover the blowup.
  have htop := iSup_opensRange_affineBlowupι hs
  let 𝒰 : (Proj (grade (maximalIdeal A))).OpenCover :=
    .mkOfCovers (Fin 2)
      (fun i ↦ Spec (.of ((maximalIdeal A).affineBlowup (s i) (Localization.Away (s i)))))
      (fun i ↦ affineBlowupι (Localization.Away (s i)) (hmem i))
      (fun z ↦ by
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (htop.ge (by trivial : z ∈ ⊤))
        exact ⟨i, Scheme.Hom.mem_opensRange.mp hi⟩)
  exact (isRegular_iff_openCover 𝒰).mpr fun i ↦ have := hreg i; isRegular_Spec _

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry Limits

variable {X : Scheme.{u}}

/-- **Blowing up a regular point of a surface gives regular points over it.** Let `I` be an ideal
sheaf on a scheme `X` and `x` a point whose local ring is regular of dimension two, at which `I`
generates the maximal ideal. Every local ring of the blowup of `X` along `I` at a point over `x` is
regular. -/
theorem isRegularLocalRing_stalk_blowup_of_stalkIdeal_eq_maximalIdeal (I : X.IdealSheafData)
    {x : X} [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (hI : I.stalkIdeal x = maximalIdeal (X.presheaf.stalk x)) {z : I.blowup}
    (hz : I.blowupToBase z = x) : IsRegularLocalRing (I.blowup.presheaf.stalk z) := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  -- The point `z` lies on the chart of the blowup over the affine open `U ∋ x`.
  obtain ⟨z, rfl⟩ : z ∈ Set.range (I.blowupChart hU) := by
    rw [← Scheme.Hom.coe_opensRange, I.opensRange_blowupChart hU, SetLike.mem_coe,
      Scheme.Hom.mem_preimage, hz]
    exact hxU
  refine (isRegularLocalRing_stalk_iff_of_isOpenImmersion (I.blowupChart hU) z).mpr ?_
  -- Base change the chart along the flat localization `Γ(X, U) → 𝒪_{X,x}`.
  let B := X.presheaf.stalk x
  let : Algebra Γ(X, U) B := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime B (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : Module.Flat Γ(X, U) B :=
    IsLocalization.flat B (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  -- There the centre becomes the closed point of `Spec 𝒪_{X,x}`, so the blowup is regular.
  have hJ : (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) B) = maximalIdeal B := by
    rw [RingHom.algebraMap_toAlgebra, ← I.stalkIdeal_eq_map ⟨U, hU⟩ x hxU, hI]
  have : IsRegular (Proj (grade ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) B)))) :=
    hJ ▸ isRegular_proj_grade_maximalIdeal hdim
  -- A point of the base-changed blowup over `z` and the closed point of `Spec 𝒪_{X,x}`.
  let c : Spec (.of B) := closedPoint B
  have h : Proj.toSpecCoeff (grade (I.ideal ⟨U, hU⟩)) z =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B)) c := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← I.blowupChart_blowupToBase hU, Scheme.Hom.comp_apply, hz,
      ← Scheme.Hom.comp_apply, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_closedPoint]
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback z c h
  let φ := affineBlowupBaseChangeHom (I.ideal ⟨U, hU⟩) B
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  -- Regularity descends along the flat projection of the base change.
  have hφ : (φ ≫ pullback.fst _ _) (inv φ w) = z := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, hw]
  exact hφ ▸ (φ ≫ pullback.fst _ _).isRegularLocalRing_stalk_of_flat (inv φ w)

/-- **Blowing up regular points of a surface keeps it regular.** Let `I` be an ideal sheaf on a
regular scheme `X` that, at every point of its support, generates the maximal ideal of a local
ring of dimension two. Then the blowup of `X` along `I` is regular. -/
theorem isRegular_blowup_of_stalkIdeal_eq_maximalIdeal [IsRegular X] (I : X.IdealSheafData)
    (hI : ∀ x ∈ I.support, I.stalkIdeal x = maximalIdeal (X.presheaf.stalk x))
    (hdim : ∀ x ∈ I.support, ringKrullDim (X.presheaf.stalk x) = 2) : IsRegular I.blowup := by
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  refine ⟨fun z ↦ ?_⟩
  by_cases hz : I.blowupToBase z ∈ I.support
  · exact I.isRegularLocalRing_stalk_blowup_of_stalkIdeal_eq_maximalIdeal (hdim _ hz) (hI _ hz) rfl
  -- Away from the support of `I`, the blowup is an isomorphism onto the regular scheme `X`.
  have hzV : I.blowupToBase z ∈ I.support.compl := by
    rwa [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_compl, Set.mem_compl_iff, SetLike.mem_coe]
  exact (I.blowupToBase.isRegularLocalRing_stalk_iff_of_isOpenImmersion_morphismRestrict _
    hzV).mpr inferInstance

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.IdealSheafData

/-- **The blowup of a regular surface at a closed point is regular.** Let `x` be a closed point of a
regular scheme `X` whose local ring has dimension two. The blowup of `X` at `x`, with its reduced
structure, is regular. -/
theorem isRegular_blowup_vanishingIdeal_closure_singleton {X : Scheme.{u}} [IsRegular X] {x : X}
    (hx : IsClosed {x}) (hdim : ringKrullDim (X.presheaf.stalk x) = 2) :
    IsRegular (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).blowup := by
  have hsupp (y : X) (hy : y ∈ (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).support) :
      y = x := by
    rwa [← SetLike.mem_coe, coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
      hx.closure_eq] at hy
  refine isRegular_blowup_of_stalkIdeal_eq_maximalIdeal _ (fun y hy ↦ ?_)
    (fun y hy ↦ hsupp y hy ▸ hdim)
  obtain rfl : x = y := (hsupp y hy).symm
  -- On an affine open `U ∋ x`, the ideal of the closure of `x` is the prime of `x`, which
  -- generates the maximal ideal of the localization `𝒪_{X,x}`.
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [stalkIdeal_eq_map _ ⟨U, hU⟩ x hxU, vanishingIdeal_closure_singleton_ideal x ⟨U, hU⟩ hxU,
    ← X.presheaf.stalk_open_algebraMap ⟨x, hxU⟩]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

end TauCeti.AlgebraicGeometry
