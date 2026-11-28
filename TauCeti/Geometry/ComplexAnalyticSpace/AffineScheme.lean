/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.ComplexAnalyticSpace.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Polynomial.ClosedSubspace
import TauCeti.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Analytic models of affine complex schemes

For an ideal of multivariate complex polynomials, `Ideal.toComplexAnalyticSpace`
extends the ideal to holomorphic functions and takes the associated closed analytic subspace.
The comparison `Ideal.toSpecQuotient` is induced by polynomial evaluation on
global sections, via Mathlib's `LocallyRingedSpace.toΓSpec`. It follows the lifted construction
in `TauCeti.closedAnalyticSubspace.toOver` using the polynomial-quotient section map
in place of the constant-section map. It is a morphism over
`Spec (ULift ℂ)` in every universe. The analytic structure sheaf uses the extended ideal,
so the construction retains the equations of nonreduced schemes.
`Ideal.toSpecQuotient_mem_asIdeal_iff` computes the image prime by vanishing, and
`Ideal.toSpecQuotient_Γ` computes the pullback on global sections using
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_toΓSpec_comp`.

See SGA 1, Exposé XII, Theorem and Definition 1.1, for the affine construction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TauCeti TauCeti.ComplexAnalyticSpace
open TopCat.Presheaf TopologicalSpace
open scoped Manifold

universe u

variable {n : ℕ}

local notation "𝒫" => MvPolynomial (Fin n) ℂ
local notation "𝒰" => (⊤ : Opens (Fin n → ℂ))
local notation "𝓕" => TopCat.Sheaf.presheaf (C := CommRingCat)
  (holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) 𝒰)

namespace Ideal

/-- The affine analytic space cut out by all equations in the polynomial ideal `I`. -/
def toComplexAnalyticSpace (I : Ideal 𝒫) : ComplexAnalyticSpace.{u} :=
  ComplexAnalyticSpace.ofClosedAnalyticSubspace (toHolomorphic I)
    (by
      rw [toHolomorphic_def]
      exact Ideal.FG.map (IsNoetherian.noetherian I) (polynomialToHolomorphic n).toRingHom)

/-- The underlying locally ringed space over `Spec (ULift ℂ)` is the closed analytic model of
the extended polynomial ideal. -/
@[simp]
theorem toComplexAnalyticSpace_obj (I : Ideal 𝒫) :
    (toComplexAnalyticSpace.{u} I).obj =
      closedAnalyticSubspace.toOver.{u} (toHolomorphic I) :=
  ComplexAnalyticSpace.ofClosedAnalyticSubspace_obj _ _

/-- The locally ringed space of the affine analytic model is the universe-lifted closed
subspace cut out by the extended ideal. -/
theorem toComplexAnalyticSpace_left (I : Ideal 𝒫) :
    (toComplexAnalyticSpace.{u} I).obj.left =
      (closedAnalyticSubspace (toHolomorphic I)).ulift.{u} :=
  (congrArg Over.left (toComplexAnalyticSpace_obj.{u} I)).trans
    (closedAnalyticSubspace.toOver_left _)

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
  eqToHom (toComplexAnalyticSpace_obj.{u} I) ≫
  Over.homMk (A.ulift.{u}.toΓSpec ≫ Spec.locallyRingedSpaceMap f) (by
    have h₀ : CommRingCat.ofHom (algebraMap ℂ (𝒫 ⧸ I)) ≫
        CommRingCat.ofHom (polynomialQuotientToSections I) =
          CommRingCat.ofHom (closedAnalyticSubspace.constRingHom (toHolomorphic I)) := by
      ext c
      exact polynomialQuotientToSections_algebraMap I c
    have h := congrArg (CommRingCat.uliftFunctor.{u}.map) h₀
    rw [Functor.map_comp] at h
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
        rw [hcomp, closedAnalyticSubspace.toOver_hom])

/-- The comparison morphism is induced by the map from the polynomial quotient to global
sections of the analytic model. -/
theorem toSpecQuotient_left (I : Ideal 𝒫) :
    (toSpecQuotient.{u} I).left =
      eqToHom (toComplexAnalyticSpace_left.{u} I) ≫
        (closedAnalyticSubspace (toHolomorphic I)).ulift.{u}.toΓSpec ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom (polynomialQuotientToSections I).ulift ≫
            (closedAnalyticSubspace (toHolomorphic I)).uliftΓIso.{u}.inv) := by
  rw [toSpecQuotient, Over.comp_left, Over.eqToHom_left]
  exact congrArg (eqToHom (toComplexAnalyticSpace_left.{u} I) ≫ ·)
    (Over.homMk_left _ _)

/-- The points of the affine analytic model are the universe lift of its complex zero locus. -/
def toComplexAnalyticSpaceHomeomorph (I : Ideal 𝒫) :
    (toComplexAnalyticSpace.{u} I).obj.left ≃ₜ ULift.{u} (closedAnalyticSubspace.zeroLocus
      (toHolomorphic I)) :=
  TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso
    (eqToIso (toComplexAnalyticSpace_left.{u} I)))

/-- The zero-locus homeomorphism acts by the canonical transport on the carrier.
Use this equation explicitly when working with the transport. -/
theorem toComplexAnalyticSpaceHomeomorph_apply (I : Ideal 𝒫)
    (x : (toComplexAnalyticSpace.{u} I).obj.left) :
    toComplexAnalyticSpaceHomeomorph I x =
      (eqToHom (toComplexAnalyticSpace_left.{u} I)).base x :=
  (rfl)

/-- A polynomial class belongs to the comparison point's prime ideal exactly when the
polynomial vanishes at the analytic point. -/
-- Match the membership expression before `simp` normalizes its subterms.
@[simp↓]
theorem toSpecQuotient_mem_asIdeal_iff (I : Ideal 𝒫)
    (x : (toComplexAnalyticSpace.{u} I).obj.left) (p : 𝒫) :
    ULift.up (Ideal.Quotient.mk I p) ∈ ((toSpecQuotient I).left.base x).asIdeal ↔
      MvPolynomial.eval (toComplexAnalyticSpaceHomeomorph I x).down.val.val p = 0 := by
  let A := closedAnalyticSubspace (toHolomorphic I)
  let z := (toComplexAnalyticSpaceHomeomorph I x).down
  let f : CommRingCat.of (ULift.{u} (𝒫 ⧸ I)) ⟶ LocallyRingedSpace.Γ.obj (op A.ulift.{u}) :=
    CommRingCat.ofHom (polynomialQuotientToSections I).ulift ≫ A.uliftΓIso.{u}.inv
  rw [toSpecQuotient_left, LocallyRingedSpace.comp_base]
  -- The spectrum map is comap, and the source transport is the homeomorphism on points.
  change f (ULift.up (Ideal.Quotient.mk I p)) ∈
    (A.ulift.{u}.toΓSpecFun (ULift.up z)).asIdeal ↔ MvPolynomial.eval z.val.val p = 0
  refine not_iff_not.mp ((A.ulift.{u}.notMem_prime_iff_unit_in_stalk _ (ULift.up z)).trans ?_)
  refine (isUnit_map_iff
    (closedAnalyticSubspace.toOverStalkEquiv (toHolomorphic I) z) _).symm.trans ?_
  let J := stalkIdeal 𝓕 (toHolomorphic I) z.val
  have : Nontrivial ((𝓕).stalk z.val ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (closedAnalyticSubspace.stalkIdeal_ne_top_iff.mpr z.property)
  have : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let g := polynomialQuotientToSections I (Ideal.Quotient.mk I p)
  have hfg : f (ULift.up (Ideal.Quotient.mk I p)) = ULift.up g := by
    exact (CommRingCat.comp_apply _ _ _).trans (A.uliftΓIso_inv_apply _)
  have hg := closedAnalyticSubspace.toOverStalkEquiv_germ
    (J := toHolomorphic I) (z := z) (W := ⊤) (Opens.mem_top _) (ULift.up g)
  have hclass : (quotientIdealSheaf.sectionsEquiv 𝓕 (toHolomorphic I) _ ⊤ g).val
      ⟨z, Opens.mem_top _⟩ = Ideal.Quotient.mk _ ((𝓕).germ ⊤ z.val (Opens.mem_top _)
        (polynomialToHolomorphic n p)) :=
    (congrArg (fun s ↦ (quotientIdealSheaf.sectionsEquiv 𝓕 (toHolomorphic I) _ ⊤ s).val
      ⟨z, Opens.mem_top _⟩) (polynomialQuotientToSections_mk I p)).trans
      (quotientIdealSheaf.sectionsEquiv_restrictRingHom_apply (F := 𝓕)
        (J := toHolomorphic I) (Z := closedAnalyticSubspace.zeroLocus (toHolomorphic I))
        ⊤ (polynomialToHolomorphic n p) ⟨z, trivial⟩)
  have hclass' := (congrArg (fun s ↦ closedAnalyticSubspace.toOverStalkEquiv
    (toHolomorphic I) z (A.ulift.{u}.presheaf.Γgerm (ULift.up z) s)) hfg).trans (hg.trans hclass)
  refine (congrArg IsUnit hclass').to_iff.trans ((isUnit_map_iff (Ideal.Quotient.mk J) _).trans ?_)
  exact (holomorphicStructureSheaf.isUnit_stalk_iff _ _ _).trans (not_congr
    (congrArg (· = 0) ((holomorphicStructureSheaf.eval_germ _ _ _ _ (Opens.mem_top _) _).trans
      (p.polynomialToHolomorphic_apply z.val))).to_iff)

/-- After the spectrum and universe-lift identifications, pullback on global sections is
restriction of polynomial classes to the affine analytic model. -/
theorem toSpecQuotient_Γ (I : Ideal 𝒫) :
    Scheme.SpecΓIdentity.inv.app (CommRingCat.of (ULift.{u} (𝒫 ⧸ I))) ≫
      LocallyRingedSpace.Γ.map
        (eqToHom ((toComplexAnalyticSpace_left.{u} I).symm) ≫
          (toSpecQuotient.{u} I).left).op ≫
      (closedAnalyticSubspace (toHolomorphic I)).uliftΓIso.{u}.hom =
        CommRingCat.ofHom (polynomialQuotientToSections I).ulift := by
  let A := closedAnalyticSubspace (toHolomorphic I)
  let f : CommRingCat.of (ULift.{u} (𝒫 ⧸ I)) ⟶ LocallyRingedSpace.Γ.obj (op A.ulift.{u}) :=
    CommRingCat.ofHom (polynomialQuotientToSections I).ulift ≫ A.uliftΓIso.{u}.inv
  have hleft : eqToHom ((toComplexAnalyticSpace_left.{u} I).symm) ≫
      (toSpecQuotient.{u} I).left = A.ulift.{u}.toΓSpec ≫ Spec.locallyRingedSpaceMap f := by
    simp only [toSpecQuotient_left, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, f, A]
  rw [hleft]
  have hcancel : f ≫ A.uliftΓIso.{u}.hom =
      CommRingCat.ofHom (polynomialQuotientToSections I).ulift :=
    A.uliftΓIso.{u}.eq_comp_inv.mp rfl
  exact (A.ulift.{u}.Γ_map_toΓSpec_comp_assoc f _).trans hcancel

end Ideal
