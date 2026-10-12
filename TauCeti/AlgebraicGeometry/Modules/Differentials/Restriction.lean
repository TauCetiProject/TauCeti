/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Basic

/-!
# Restriction of relative differentials

The sheaf of relative differentials commutes with restriction along an open immersion over
an affine base. The canonical isomorphism sends the differential of a local function to the
differential of its restriction. This permits affine computations of differentials to be used
on arbitrary schemes. The isomorphism is `relativeDifferentialsRestrictIso`, characterized by
`relativeDifferentialsRestrictIso_hom_app_d` and `relativeDifferentialsRestrictIso_inv_app_d`.

## References

* The Stacks Project, Section 29.33, Lemma 29.33.3 (Tag 01UM).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [hf : f.IsOver (Spec (.of R))]

/-- A derivation of the structure sheaf of `X` induces a derivation into its pushforward on
`Y`, by differentiating the pullbacks of local functions. -/
def pushforwardDerivation {M : X.Modules} (d : M.Derivation R) :
    ((Scheme.Modules.pushforward f).obj M).Derivation R where
  d {U} := d.d.comp (f.app U.unop).hom.toAddMonoidHom
  d_mul a b := by
    -- The pushforward restricts scalars along `f.app`; expose that action and composition.
    change d.d (f.app _ (a * b)) = f.app _ a • d.d (f.app _ b) +
      f.app _ b • d.d (f.app _ a)
    rw [map_mul, d.d_mul]
  d_map {U V} i a := by
    -- The underlying presheaf of the pushforward is precomposition by preimage on opens.
    change d.d (f.app V.unop (Y.presheaf.map i a)) =
      M.val.map ((TopologicalSpace.Opens.map f.base).map i.unop).op (d.d (f.app U.unop a))
    rw [← ConcreteCategory.comp_apply, f.naturality i, ConcreteCategory.comp_apply,
      d.d_map]
    rfl
  d_app {U} r := by
    -- The composition in the field `d` is an additive-hom composition.
    change d.d (f.app U.unop ((Y.baseRingToStructurePresheaf R).app U r)) = 0
    rw [Scheme.Modules.app_baseRingToStructurePresheaf]
    exact d.d_app r

/-- The pushed derivation differentiates the pullback of a local function. -/
@[simp]
lemma pushforwardDerivation_d {M : X.Modules} (d : M.Derivation R)
    (U : Y.Opens) (a : Γ(Y, U)) :
    (pushforwardDerivation R f d).d a = d.d (f.app U a) :=
  (rfl)

/-- On an open immersion, a derivation restricts by identifying the functions on each open
with the functions on its image. -/
def restrictDerivation [IsOpenImmersion f] {M : Y.Modules} (d : M.Derivation R) :
    (M.restrict f).Derivation R where
  d {U} := d.d.comp (f.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul a b := by
    -- Restriction restricts scalars along `appIso.inv`, and `d` is a composed additive map.
    change d.d ((f.appIso _).inv (a * b)) =
      (f.appIso _).inv a • d.d ((f.appIso _).inv b) +
      (f.appIso _).inv b • d.d ((f.appIso _).inv a)
    rw [map_mul, d.d_mul]
  d_map {U V} i a := by
    -- Restriction uses the image functor on opens and the inverse ring isomorphisms.
    change d.d ((f.appIso V.unop).inv (X.presheaf.map i a)) =
      M.val.map (f.opensFunctor.map i.unop).op (d.d ((f.appIso U.unop).inv a))
    rw [← ConcreteCategory.comp_apply, f.appIso_inv_naturality i,
      ConcreteCategory.comp_apply, d.d_map]
    rfl
  d_app {U} r := by
    -- The identity base functor and the additive composition reduce to this local equation.
    change d.d ((f.appIso U.unop).inv ((X.baseRingToStructurePresheaf R).app U r)) = 0
    have h : (f.appIso U.unop).inv
        ((X.baseRingToStructurePresheaf R).app U r) =
        (Y.baseRingToStructurePresheaf R).app (op (f ''ᵁ U.unop)) r := by
      apply_fun (f.appIso U.unop).hom using
        (f.appIso U.unop).commRingCatIsoToRingEquiv.injective
      rw [Iso.inv_hom_id_apply]
      rw [Scheme.Hom.appIso_hom, ConcreteCategory.comp_apply,
        Scheme.Modules.app_baseRingToStructurePresheaf]
      exact (X.baseRingToStructurePresheaf R).naturality_apply
        (eqToHom (f.preimage_image_eq U.unop).symm).op r
    rw [h]
    exact d.d_app r

/-- A restricted derivation differentiates the corresponding function on the image open. -/
@[simp]
lemma restrictDerivation_d [IsOpenImmersion f] {M : Y.Modules} (d : M.Derivation R)
    (U : X.Opens) (a : Γ(X, U)) :
    (restrictDerivation R f d).d a = d.d ((f.appIso U).inv a) :=
  (rfl)

variable [IsOpenImmersion f]

private def restrictionHom : (Y.relativeDifferentials R).restrict f ⟶
    X.relativeDifferentials R :=
  ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).symm
    ((Y.relativeDifferentialsHomEquiv R _).symm
      (pushforwardDerivation R f (X.universalDerivation R)))

private def restrictionInv : X.relativeDifferentials R ⟶
    (Y.relativeDifferentials R).restrict f :=
  (X.relativeDifferentialsHomEquiv R _).symm
    (restrictDerivation R f (Y.universalDerivation R))

include hf in
private lemma restrictionInv_app_d (U : X.Opens) (a : Γ(X, U)) :
    (restrictionInv R f).app U ((X.universalDerivation R).d a) =
      (Y.universalDerivation R).d ((f.appIso U).inv a) := by
  exact congrArg (fun d ↦ d.d a)
    (X.relativeDifferentialsHomEquiv_symm_fac R
      (restrictDerivation R f (Y.universalDerivation R)))

private lemma restrictionHom_app_d (U : X.Opens) (a : Γ(Y, f ''ᵁ U)) :
    (restrictionHom R f).app U ((Y.universalDerivation R).d a) =
      (X.universalDerivation R).d ((f.appIso U).hom a) := by
  let g : Y.relativeDifferentials R ⟶
      (Scheme.Modules.pushforward f).obj (X.relativeDifferentials R) :=
    (Y.relativeDifferentialsHomEquiv R _).symm
      (pushforwardDerivation R f (X.universalDerivation R))
  have hg (W : Y.Opens) (b : Γ(Y, W)) :
      g.app W ((Y.universalDerivation R).d b) =
        (X.universalDerivation R).d (f.app W b) :=
    congrArg (fun d ↦ d.d b)
      (Y.relativeDifferentialsHomEquiv_symm_fac R
        (pushforwardDerivation R f (X.universalDerivation R)))
  -- The adjunct is restriction of `g` followed by the counit, whose local map identifies
  -- `f⁻¹(f(U))` with `U`; the identity cannot rewrite through the presheaf/module wrappers.
  change (X.relativeDifferentials R).presheaf.map
      (eqToHom (f.preimage_image_eq U).symm).op
        (g.app (f ''ᵁ U) ((Y.universalDerivation R).d a)) = _
  rw [hg]
  exact ((X.universalDerivation R).d_map
    (eqToHom (f.preimage_image_eq U).symm).op (f.app (f ''ᵁ U) a)).symm.trans
      (congrArg (X.universalDerivation R).d
        (ConcreteCategory.congr_hom (f.appIso_hom U) a).symm)

/-- Relative differentials commute with restriction along an open immersion over `Spec R`.
The inverse sends `d a` on `X` to the differential of the corresponding function on `Y`.
-/
def relativeDifferentialsRestrictIso : (Y.relativeDifferentials R).restrict f ≅
    X.relativeDifferentials R where
  hom := restrictionHom R f
  inv := restrictionInv R f
  hom_inv_id := by
    apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
    apply Y.relativeDifferentials_hom_ext R
    intro U a
    -- The adjunction evaluates the restricted composite after restricting the local function
    -- to the image of its preimage; expose these evaluation maps to use the derivative laws.
    change (restrictionInv R f).app (f ⁻¹ᵁ U.unop)
        ((restrictionHom R f).app (f ⁻¹ᵁ U.unop)
          ((Y.relativeDifferentials R).val.map
            (homOfLE (f.image_preimage_le U.unop)).op ((Y.universalDerivation R).d a))) =
      (Y.relativeDifferentials R).val.map
        (homOfLE (f.image_preimage_le U.unop)).op ((Y.universalDerivation R).d a)
    have hd := (Y.universalDerivation R).d_map
      (homOfLE (f.image_preimage_le U.unop)).op a
    refine (congrArg (fun z ↦ (restrictionInv R f).app (f ⁻¹ᵁ U.unop)
      ((restrictionHom R f).app (f ⁻¹ᵁ U.unop) z)) hd.symm).trans ?_
    refine Eq.trans ?_ hd
    rw [restrictionHom_app_d, restrictionInv_app_d, Iso.hom_inv_id_apply]
  inv_hom_id := by
    apply X.relativeDifferentials_hom_ext R
    intro U a
    -- Evaluation of a composite of sheaf morphisms is composition of the section maps.
    change (restrictionHom R f).app U.unop
        ((restrictionInv R f).app U.unop ((X.universalDerivation R).d a)) =
      (X.universalDerivation R).d a
    rw [restrictionInv_app_d, restrictionHom_app_d, Iso.inv_hom_id_apply]

/-- The restriction comparison carries the differential of a function on `Y` to the
differential of that function on `X`. -/
lemma relativeDifferentialsRestrictIso_hom_app_d (U : X.Opens) (a : Γ(Y, f ''ᵁ U)) :
    (relativeDifferentialsRestrictIso R f).hom.app U ((Y.universalDerivation R).d a) =
      (X.universalDerivation R).d ((f.appIso U).hom a) :=
  restrictionHom_app_d R f U a

/-- The inverse restriction comparison sends `d a` to the differential of the corresponding
function on the image open. -/
@[simp]
lemma relativeDifferentialsRestrictIso_inv_app_d (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsRestrictIso R f).inv.app U ((X.universalDerivation R).d a) =
      (Y.universalDerivation R).d ((f.appIso U).inv a) :=
  restrictionInv_app_d R f U a

end

end TauCeti.AlgebraicGeometry
