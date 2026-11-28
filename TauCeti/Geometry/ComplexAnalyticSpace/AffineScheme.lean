/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.ComplexAnalyticSpace.Basic
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Analytic models of affine complex schemes

For an ideal of multivariate complex polynomials, `Ideal.toComplexAnalyticSpace`
extends the ideal to holomorphic functions and takes the associated closed analytic subspace.
The comparison `Ideal.toSpecQuotient` is induced by polynomial evaluation on
global sections, via Mathlib's `LocallyRingedSpace.toΓSpec`. It is a morphism over
`Spec (ULift ℂ)` in every universe. The analytic structure sheaf uses the extended ideal,
so the construction retains the equations of nonreduced schemes.

See SGA 1, Exposé XII, Theorem and Definition 1.1, for the affine construction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TauCeti TopCat.Presheaf TopologicalSpace
open scoped ContDiff Manifold

universe u

variable {n : ℕ}

local notation "𝒫" => MvPolynomial (Fin n) ℂ
local notation "𝒰" => (⊤ : Opens (Fin n → ℂ))
local notation "𝓕" => TopCat.Sheaf.presheaf (C := CommRingCat)
  (holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) 𝒰)
local notation "𝓗" => Functor.obj (D := CommRingCat) 𝓕 (op ⊤)

namespace TauCeti.ComplexAnalyticSpace

/-- Polynomial evaluation as global holomorphic functions on complex affine space. -/
def polynomialToHolomorphic (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ]
      (holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (⊤ : Opens (Fin n → ℂ))).presheaf.obj (op ⊤) :=
  MvPolynomial.aeval fun i ↦
    holomorphicStructureSheaf.ofContMDiff (fun x ↦ x.val.val i)
      (((ContinuousLinearMap.proj (R := ℂ) i : (Fin n → ℂ) →L[ℂ] ℂ).contDiff.contMDiff).comp
        (contMDiff_subtypeVal.comp contMDiff_subtypeVal))

/-- The holomorphic section attached to a polynomial evaluates to its value at each point. -/
-- Index on evaluation across the unexposed section carrier and its dependent opens.
@[simp]
theorem polynomialToHolomorphic_apply (p : 𝒫) (x : 𝒰) :
    holomorphicStructureSheaf.toFun (no_index 𝓘(ℂ, Fin n → ℂ)) (no_index 𝒰) (no_index (op ⊤))
      (no_index (polynomialToHolomorphic n p)) (no_index ⟨x, trivial⟩) =
        MvPolynomial.eval x.val p := by
  let evaluation : 𝓗 →+* ℂ :=
    (holomorphicStructureSheaf.eval _ _ x).comp ((𝓕).germ ⊤ x (Opens.mem_top x)).hom
  have heval (f : 𝓗) : evaluation f = f ⟨x, trivial⟩ :=
    holomorphicStructureSheaf.eval_germ _ _ _ _ (Opens.mem_top x) f
  have hconst : evaluation.comp (algebraMap ℂ 𝓗) = RingHom.id ℂ := by
    ext c
    exact (heval _).trans (holomorphicStructureSheaf.algebraMap_apply _ _ _)
  rw [← heval, polynomialToHolomorphic, MvPolynomial.map_aeval, hconst]
  congr 3
  ext i
  exact (heval _).trans (holomorphicStructureSheaf.ofContMDiff_apply _ _ _)

end TauCeti.ComplexAnalyticSpace

open TauCeti.ComplexAnalyticSpace

namespace Ideal

/-- Extend the polynomial ideal to the global holomorphic functions on complex affine space. -/
def toHolomorphic (I : Ideal 𝒫) : Ideal 𝓗 :=
  I.map (polynomialToHolomorphic n).toRingHom

/-- The defining ideal of the affine model is the image ideal under polynomial evaluation. -/
@[simp]
theorem toHolomorphic_def (I : Ideal 𝒫) :
    toHolomorphic I = I.map (polynomialToHolomorphic n).toRingHom :=
  (rfl)

/-- The extended ideal cuts out the common zeros of the original polynomial equations. -/
-- The generic zero-locus membership simp lemma already rewrites the left-hand side.
theorem mem_zeroLocus_toHolomorphic {I : Ideal 𝒫} {x : 𝒰} :
    x ∈ closedAnalyticSubspace.zeroLocus (toHolomorphic I) ↔
      ∀ p ∈ I, MvPolynomial.eval x.val p = 0 := by
  have hspan : toHolomorphic I =
      Ideal.span ((polynomialToHolomorphic n).toRingHom '' (I : Set 𝒫)) := by
    rw [toHolomorphic_def]
    simpa only [Ideal.span_eq] using
      Ideal.map_span (polynomialToHolomorphic n).toRingHom (I : Set 𝒫)
  rw [hspan, closedAnalyticSubspace.zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_image]
  exact forall₂_congr fun p _ ↦ (congrArg (· = 0) (polynomialToHolomorphic_apply p x)).to_iff

/-- The affine analytic space cut out by all equations in the polynomial ideal `I`. -/
def toComplexAnalyticSpace (I : Ideal 𝒫) : ComplexAnalyticSpace.{u} :=
  ⟨closedAnalyticSubspace.toOver (toHolomorphic I),
    isComplexAnalyticSpace_toOver
      (Ideal.FG.map (IsNoetherian.noetherian I) (polynomialToHolomorphic n).toRingHom)⟩

/-- The underlying locally ringed space over `Spec (ULift ℂ)` is the closed analytic model of
the extended polynomial ideal. -/
@[simp]
theorem toComplexAnalyticSpace_obj (I : Ideal 𝒫) :
    (toComplexAnalyticSpace.{u} I).obj =
      closedAnalyticSubspace.toOver.{u} (toHolomorphic I) :=
  (rfl)

/-- The map from the polynomial quotient to the global sections of the closed analytic model. -/
def polynomialQuotientToSections (I : Ideal 𝒫) :
    (𝒫 ⧸ I) →+* (closedAnalyticSubspace (toHolomorphic I)).presheaf.obj (op ⊤) :=
  Ideal.Quotient.lift I
    ((TopCat.Presheaf.quotientIdealSheaf.restrictRingHom 𝓕 (toHolomorphic I)
      (closedAnalyticSubspace.zeroLocus (toHolomorphic I)) ⊤).comp
      (polynomialToHolomorphic n).toRingHom)
    (by
      intro p hp
      let Z := closedAnalyticSubspace.zeroLocus (toHolomorphic I)
      let W : Opens (TopCat.of Z) := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ ⊤
      refine quotientIdealSheaf.ext (F := 𝓕) (J := toHolomorphic I) (Z := Z) (W := W) fun z ↦ ?_
      have h := quotientIdealSheaf.sectionsEquiv_restrictRingHom_apply
        (F := 𝓕) (J := toHolomorphic I) (Z := Z) ⊤ (polynomialToHolomorphic n p) z
      have hz : _ = (0 : _ ⧸ _) := Ideal.Quotient.eq_zero_iff_mem.mpr
        (germ_mem_stalkIdeal (Ideal.mem_map_of_mem (polynomialToHolomorphic n).toRingHom hp)
          z.val.val)
      have hzero := map_zero (quotientIdealSheaf.sectionsEquiv 𝓕 (toHolomorphic I) Z W)
      exact h.trans (hz.trans (congrArg (fun a ↦ a.val z) hzero).symm))

/-- On a polynomial class the section is the restriction of the associated holomorphic function. -/
@[simp]
theorem polynomialQuotientToSections_mk (I : Ideal 𝒫) (p : 𝒫) :
    polynomialQuotientToSections I (Ideal.Quotient.mk I p) =
      TopCat.Presheaf.quotientIdealSheaf.restrictRingHom 𝓕 (toHolomorphic I)
        (closedAnalyticSubspace.zeroLocus (toHolomorphic I)) ⊤
        (polynomialToHolomorphic n p) :=
  Ideal.Quotient.lift_mk _ _ _

/-- Polynomial classes of constants restrict to the constant sections. -/
@[simp]
theorem polynomialQuotientToSections_algebraMap (I : Ideal 𝒫) (c : ℂ) :
    polynomialQuotientToSections I (algebraMap ℂ (𝒫 ⧸ I) c) =
      closedAnalyticSubspace.constRingHom (toHolomorphic I) c := by
  rw [← Ideal.Quotient.mk_algebraMap, polynomialQuotientToSections_mk, AlgHom.commutes,
    closedAnalyticSubspace.constRingHom_apply]

/-- The canonical map from the analytic model to the spectrum of the polynomial quotient, over
`Spec (ULift ℂ)`. The map is induced by restriction of polynomial functions to the analytic
quotient. -/
def toSpecQuotient (I : Ideal 𝒫) :
    (toComplexAnalyticSpace.{u} I).obj ⟶
      Over.mk (Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom (algebraMap ℂ (𝒫 ⧸ I)).ulift)) :=
  let A := closedAnalyticSubspace (toHolomorphic I)
  let f : CommRingCat.of (ULift.{u} (𝒫 ⧸ I)) ⟶ LocallyRingedSpace.Γ.obj (op A.ulift.{u}) :=
    CommRingCat.ofHom (polynomialQuotientToSections I).ulift ≫ A.uliftΓIso.{u}.inv
  Over.homMk (A.ulift.{u}.toΓSpec ≫ Spec.locallyRingedSpaceMap f) (by
    have h : CommRingCat.ofHom (algebraMap ℂ (𝒫 ⧸ I)).ulift ≫
          CommRingCat.ofHom (polynomialQuotientToSections I).ulift =
        CommRingCat.ofHom (closedAnalyticSubspace.constRingHom
          (toHolomorphic I)).ulift := by
      ext c
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        RingHom.ulift_apply, polynomialQuotientToSections_algebraMap]
    have hcomp : CommRingCat.ofHom (algebraMap ℂ (𝒫 ⧸ I)).ulift ≫ f =
        CommRingCat.ofHom (closedAnalyticSubspace.constRingHom
          (toHolomorphic I)).ulift ≫ A.uliftΓIso.{u}.inv :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ A.uliftΓIso.{u}.inv) h)
    calc
      _ = A.ulift.{u}.toΓSpec ≫ Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom (algebraMap ℂ (𝒫 ⧸ I)).ulift ≫ f) :=
        (Category.assoc _ _ _).trans
          (congrArg (A.ulift.{u}.toΓSpec ≫ ·) (Spec.locallyRingedSpaceMap_comp _ _).symm)
      _ = _ := by
        rw [hcomp]
        exact (closedAnalyticSubspace.toOver_hom _).symm)

/-- The comparison morphism is induced by the map from the polynomial quotient to global
sections of the analytic model. -/
@[simp]
theorem toSpecQuotient_left (I : Ideal 𝒫) :
    (toSpecQuotient.{u} I).left =
      eqToHom (congrArg Over.left (toComplexAnalyticSpace_obj.{u} I)) ≫
        (closedAnalyticSubspace (toHolomorphic I)).ulift.{u}.toΓSpec ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom (polynomialQuotientToSections I).ulift ≫
            (closedAnalyticSubspace (toHolomorphic I)).uliftΓIso.{u}.inv) :=
  (Category.id_comp _).symm

end Ideal
