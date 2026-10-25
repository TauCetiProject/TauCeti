/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Basic

/-!
# Naturality of principal parts under divisor inclusions

For `D ≤ E`, the quotients of the function field by the stalks of `𝒪(D)` map to those for
`𝒪(E)`. These maps define the natural morphism between the sheaves of principal parts, compatible
with the maps from the rational-function sheaf.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 7.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  {D E : SchemeWeilDivisor X}

private def principalPartsMapApp (h : D ≤ E) (U : X.Opens) :
    Γ(principalParts D, U) →+ Γ(principalParts E, U) :=
  (principalPartsSectionsEquiv E U).symm.toAddMonoidHom.comp <|
    (DFinsupp.mapRange.addMonoidHom fun (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) ↦
      (principalPartMapOfLE h x.1).toAddMonoidHom).comp
      (principalPartsSectionsEquiv D U).toAddMonoidHom

private lemma principalPartsMapApp_apply (h : D ≤ E) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv E U (principalPartsMapApp h U s) x =
      principalPartMapOfLE h x.1 (principalPartsSectionsEquiv D U s x) := by
  simp only [principalPartsMapApp, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe]
  -- Reduce the additive-hom wrappers, then cancel the public section equivalence.
  change principalPartsSectionsEquiv E U ((principalPartsSectionsEquiv E U).symm _) x = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The map of principal-parts sheaves induced by `D ≤ E`, taking each local quotient class
to the class of the same rational function. -/
def principalPartsHomOfLE (h : D ≤ E) : principalParts D ⟶ principalParts E :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (principalPartsMapApp h U.unop)
      naturality {U V} i := by
        ext s
        apply (principalPartsSectionsEquiv E V.unop).injective
        apply DFinsupp.ext
        intro x
        -- The additive-category wrapper is reduced only to expose the application equation.
        change principalPartsSectionsEquiv E V.unop
            (principalPartsMapApp h V.unop ((principalParts D).presheaf.map i s)) x =
          principalPartsSectionsEquiv E V.unop
            ((principalParts E).presheaf.map i (principalPartsMapApp h U.unop s)) x
        erw [principalPartsMapApp_apply, principalParts_presheaf_map_apply,
          principalParts_presheaf_map_apply, principalPartsMapApp_apply] }
    (by
      intro U r s
      apply (principalPartsSectionsEquiv E U.unop).injective
      apply DFinsupp.ext
      intro x
      -- Reduce the additive-category wrapper before using the public scalar equation.
      change principalPartsSectionsEquiv E U.unop
          (principalPartsMapApp h U.unop ((show Γ(X, U.unop) from r) •
            (show Γ(principalParts D, U.unop) from s))) x =
        principalPartsSectionsEquiv E U.unop
          ((show Γ(X, U.unop) from r) • principalPartsMapApp h U.unop s) x
      erw [principalPartsMapApp_apply, principalPartsSectionsEquiv_smul_apply,
        principalPartsSectionsEquiv_smul_apply, principalPartsMapApp_apply, map_smul])⟩

/-- Evaluation of the principal-parts morphism is the local quotient map. -/
@[simp]
lemma principalPartsHomOfLE_app_apply (h : D ≤ E) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv E U ((principalPartsHomOfLE h).app U s) x =
      principalPartMapOfLE h x.1 (principalPartsSectionsEquiv D U s x) :=
  principalPartsMapApp_apply h U s x

/-- The principal-parts map for an equality inclusion is the identity. -/
@[simp]
lemma principalPartsHomOfLE_refl (D : SchemeWeilDivisor X) :
    principalPartsHomOfLE (le_refl D) = 𝟙 (principalParts D) := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  apply (principalPartsSectionsEquiv D U).injective
  apply DFinsupp.ext
  intro x
  simp only [Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply,
    principalPartsHomOfLE_app_apply]
  induction principalPartsSectionsEquiv D U s x using Submodule.Quotient.induction_on with
  | _ f => simp only [principalPartMapOfLE_mk]

/-- Principal-parts maps compose along inclusions of divisors. -/
@[reassoc (attr := simp)]
lemma principalPartsHomOfLE_comp {F : SchemeWeilDivisor X} (h : D ≤ E) (h' : E ≤ F) :
    principalPartsHomOfLE h ≫ principalPartsHomOfLE h' =
      principalPartsHomOfLE (h.trans h') := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  apply (principalPartsSectionsEquiv F U).injective
  apply DFinsupp.ext
  intro x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    principalPartsHomOfLE_app_apply]
  induction principalPartsSectionsEquiv D U s x using Submodule.Quotient.induction_on with
  | _ f => simp only [principalPartMapOfLE_mk]

/-- Taking principal parts commutes with enlargement of the divisor. -/
@[reassoc (attr := simp)]
lemma toPrincipalParts_principalPartsHomOfLE (h : D ≤ E) :
    toPrincipalParts D ≫ principalPartsHomOfLE h = toPrincipalParts E := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  apply (principalPartsSectionsEquiv E U).injective
  apply DFinsupp.ext
  intro x
  have : Nonempty U := ⟨⟨x.1, x.2⟩⟩
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    principalPartsHomOfLE_app_apply, toPrincipalParts_app_apply, principalPartAt_eq,
    principalPartMapOfLE_mk]

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
