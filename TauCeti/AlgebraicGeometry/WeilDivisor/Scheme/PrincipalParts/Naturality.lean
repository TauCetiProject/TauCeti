/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Basic

/-!
# Naturality of principal parts

For `D ≤ E`, the quotients of the function field by the stalks of `𝒪(D)` map to those for
`𝒪(E)`. These maps define the natural morphism between the sheaves of principal parts, compatible
with the maps from the rational-function sheaf. `principalPartsShortComplexMap` extends any
commuting square between divisor sheaves and rational functions to their resolutions when
the map from rational functions to the source principal parts is epimorphic.

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
      (principalPartMapOfLE h x.val).toAddMonoidHom).comp
      (principalPartsSectionsEquiv D U).toAddMonoidHom

private lemma principalPartsMapApp_apply (h : D ≤ E) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv E U (principalPartsMapApp h U s) x =
      principalPartMapOfLE h x.val (principalPartsSectionsEquiv D U s x) := by
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
      principalPartMapOfLE h x.val (principalPartsSectionsEquiv D U s x) :=
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
    principalPartsHomOfLE_app_apply, principalPartMapOfLE_refl, LinearMap.id_apply]

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
  exact principalPartMapOfLE_comp_apply h h' x.val _

/-- Taking principal parts commutes with enlargement of the divisor. -/
@[reassoc (attr := simp)]
lemma toPrincipalParts_principalPartsHomOfLE (h : D ≤ E) :
    toPrincipalParts D ≫ principalPartsHomOfLE h = toPrincipalParts E := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  apply (principalPartsSectionsEquiv E U).injective
  apply DFinsupp.ext
  intro x
  have : Nonempty U := ⟨⟨x.val, x.property⟩⟩
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    principalPartsHomOfLE_app_apply, toPrincipalParts_app_apply, principalPartAt_eq,
    principalPartMapOfLE_mk]

variable [Epi (toPrincipalParts D)]

/-- A commuting square between divisor sheaves and the rational-function sheaf induces a map
on principal parts, by the cokernel property of the principal-parts resolution. -/
def principalPartsMap (φ : sheaf D ⟶ sheaf E)
    (ψ : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E) : principalParts D ⟶ principalParts E :=
  have : Epi (principalPartsShortComplex D).g := ‹Epi (toPrincipalParts D)›
  (principalPartsShortComplex_exact D).desc (ψ ≫ toPrincipalParts E) (by
    simp only [principalPartsShortComplex]
    rw [← Category.assoc, hcomm, Category.assoc, sheafι_toPrincipalParts, Limits.comp_zero]
    rfl)

/-- The induced map on principal parts commutes with the rational-function map. -/
@[reassoc (attr := simp)]
lemma toPrincipalParts_principalPartsMap (φ : sheaf D ⟶ sheaf E)
    (ψ : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E) :
    toPrincipalParts D ≫ principalPartsMap φ ψ hcomm = ψ ≫ toPrincipalParts E := by
  have : Epi (principalPartsShortComplex D).g := ‹Epi (toPrincipalParts D)›
  exact (principalPartsShortComplex_exact D).g_desc _ _

/-- The identity square induces the identity on principal parts. -/
@[simp]
lemma principalPartsMap_id (D : SchemeWeilDivisor X) [Epi (toPrincipalParts D)] :
    principalPartsMap (𝟙 (sheaf D)) (𝟙 _) (by simp) = 𝟙 (principalParts D) := by
  apply (cancel_epi (toPrincipalParts D)).1
  simp

/-- The map on principal parts respects composition of commuting squares. -/
@[reassoc (attr := simp)]
lemma principalPartsMap_comp {F : SchemeWeilDivisor X} [Epi (toPrincipalParts E)]
    (φ : sheaf D ⟶ sheaf E) (φ' : sheaf E ⟶ sheaf F)
    (ψ ψ' : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E)
    (hcomm' : sheafι E ≫ ψ' = φ' ≫ sheafι F) :
    principalPartsMap φ ψ hcomm ≫ principalPartsMap φ' ψ' hcomm' =
      principalPartsMap (φ ≫ φ') (ψ ≫ ψ') (by
        rw [← Category.assoc, hcomm, Category.assoc, hcomm', ← Category.assoc]) := by
  apply (cancel_epi (toPrincipalParts D)).1
  simp

/-- The square between divisor and rational-function sheaves extends to a morphism of
principal-parts resolutions. -/
def principalPartsShortComplexMap (φ : sheaf D ⟶ sheaf E)
    (ψ : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E) :
    principalPartsShortComplex D ⟶ principalPartsShortComplex E where
  τ₁ := φ
  τ₂ := ψ
  τ₃ := principalPartsMap φ ψ hcomm
  comm₁₂ := by simpa only [principalPartsShortComplex] using hcomm.symm
  comm₂₃ := by simpa only [principalPartsShortComplex] using
    (toPrincipalParts_principalPartsMap φ ψ hcomm).symm

/-- The divisor-sheaf component of the induced resolution map is the given morphism. -/
@[simp]
lemma principalPartsShortComplexMap_τ₁ (φ : sheaf D ⟶ sheaf E)
    (ψ : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E) :
    (principalPartsShortComplexMap φ ψ hcomm).τ₁ = φ := (rfl)

/-- The rational-function component of the induced resolution map is the given morphism. -/
@[simp]
lemma principalPartsShortComplexMap_τ₂ (φ : sheaf D ⟶ sheaf E)
    (ψ : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E) :
    (principalPartsShortComplexMap φ ψ hcomm).τ₂ = ψ := (rfl)

/-- The principal-parts component is the map induced by the commuting square. -/
@[simp]
lemma principalPartsShortComplexMap_τ₃ (φ : sheaf D ⟶ sheaf E)
    (ψ : Scheme.rationalFunctions X ⟶ Scheme.rationalFunctions X)
    (hcomm : sheafι D ≫ ψ = φ ≫ sheafι E) :
    (principalPartsShortComplexMap φ ψ hcomm).τ₃ =
      principalPartsMap φ ψ hcomm := (rfl)

/-- For a divisor inclusion and the identity on rational functions, the induced map is the
local quotient map defining `principalPartsHomOfLE`. -/
@[simp]
lemma principalPartsMap_ofLE (h : D ≤ E)
    (hcomm : sheafι D ≫ 𝟙 _ = sheafHomOfLE h ≫ sheafι E) :
    principalPartsMap (sheafHomOfLE h) (𝟙 _) hcomm = principalPartsHomOfLE h := by
  apply (cancel_epi (toPrincipalParts D)).1
  simp

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
