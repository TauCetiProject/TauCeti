/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Basic

/-!
# Naturality of principal parts

A family of linear maps of local principal parts, one at each codimension-one point, defines a
morphism of principal-parts sheaves (`principalPartsHomMk`). For `D ≤ E`, the quotients of the
function field by the stalks of `𝒪(D)` map to those for `𝒪(E)`, giving `principalPartsHomOfLE`;
for a nonzero rational function `g`, multiplication by `g` maps them to those for
`𝒪(D - div g)`, giving `principalPartsMul`. Both are compatible with the maps from the
rational-function sheaf. `principalPartsShortComplexMap` extends any
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

private def principalPartsMapApp
    (φ : ∀ x : CodimensionOnePoint X,
      PrincipalPart D x →ₗ[X.presheaf.stalk (x : X)] PrincipalPart E x) (U : X.Opens) :
    Γ(principalParts D, U) →+ Γ(principalParts E, U) :=
  (principalPartsSectionsEquiv E U).symm.toAddMonoidHom.comp <|
    (DFinsupp.mapRange.addMonoidHom fun (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) ↦
      (φ x.val).toAddMonoidHom).comp
      (principalPartsSectionsEquiv D U).toAddMonoidHom

private lemma principalPartsMapApp_apply
    (φ : ∀ x : CodimensionOnePoint X,
      PrincipalPart D x →ₗ[X.presheaf.stalk (x : X)] PrincipalPart E x) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv E U (principalPartsMapApp φ U s) x =
      φ x.val (principalPartsSectionsEquiv D U s x) := by
  simp only [principalPartsMapApp, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe]
  -- Reduce the additive-hom wrappers, then cancel the public section equivalence.
  change principalPartsSectionsEquiv E U ((principalPartsSectionsEquiv E U).symm _) x = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The morphism of principal-parts sheaves given by a family of linear maps of local principal
parts, one at each codimension-one point. A section, a finitely supported family of local
principal parts, is mapped pointwise. -/
def principalPartsHomMk
    (φ : ∀ x : CodimensionOnePoint X,
      PrincipalPart D x →ₗ[X.presheaf.stalk (x : X)] PrincipalPart E x) :
    principalParts D ⟶ principalParts E :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (principalPartsMapApp φ U.unop)
      naturality {U V} i := by
        ext s
        apply (principalPartsSectionsEquiv E V.unop).injective
        apply DFinsupp.ext
        intro x
        -- The additive-category wrapper is reduced only to expose the application equation.
        change principalPartsSectionsEquiv E V.unop
            (principalPartsMapApp φ V.unop ((principalParts D).presheaf.map i s)) x =
          principalPartsSectionsEquiv E V.unop
            ((principalParts E).presheaf.map i (principalPartsMapApp φ U.unop s)) x
        erw [principalPartsMapApp_apply, principalParts_presheaf_map_apply,
          principalParts_presheaf_map_apply, principalPartsMapApp_apply] }
    (by
      intro U r s
      apply (principalPartsSectionsEquiv E U.unop).injective
      apply DFinsupp.ext
      intro x
      -- Reduce the additive-category wrapper before using the public scalar equation.
      change principalPartsSectionsEquiv E U.unop
          (principalPartsMapApp φ U.unop ((show Γ(X, U.unop) from r) •
            (show Γ(principalParts D, U.unop) from s))) x =
        principalPartsSectionsEquiv E U.unop
          ((show Γ(X, U.unop) from r) • principalPartsMapApp φ U.unop s) x
      erw [principalPartsMapApp_apply, principalPartsSectionsEquiv_smul_apply,
        principalPartsSectionsEquiv_smul_apply, principalPartsMapApp_apply, map_smul])⟩

/-- Evaluation of `principalPartsHomMk φ` at a codimension-one point is `φ` there. -/
@[simp]
lemma principalPartsHomMk_app_apply
    (φ : ∀ x : CodimensionOnePoint X,
      PrincipalPart D x →ₗ[X.presheaf.stalk (x : X)] PrincipalPart E x) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv E U ((principalPartsHomMk φ).app U s) x =
      φ x.val (principalPartsSectionsEquiv D U s x) :=
  principalPartsMapApp_apply φ U s x

/-- The map of principal-parts sheaves induced by `D ≤ E`, taking each local quotient class
to the class of the same rational function. -/
def principalPartsHomOfLE (h : D ≤ E) : principalParts D ⟶ principalParts E :=
  principalPartsHomMk (principalPartMapOfLE h)

/-- Evaluation of the principal-parts morphism is the local quotient map. -/
@[simp]
lemma principalPartsHomOfLE_app_apply (h : D ≤ E) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv E U ((principalPartsHomOfLE h).app U s) x =
      principalPartMapOfLE h x.val (principalPartsSectionsEquiv D U s x) :=
  principalPartsHomMk_app_apply _ U s x

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

section Mul

variable (g : Additive X.functionFieldˣ)

/-- Multiplying by a nonzero rational function `g` carries the stalk of `𝒪_X(D)` at `x` into
the stalk of `𝒪_X(D - div g)`, since it adds `ord_x g` to every order of vanishing. -/
lemma mul_mem_stalkSubmodule_sub_principalDivisor {x : CodimensionOnePoint X}
    {f : X.functionField} (hf : f ∈ stalkSubmodule D x) :
    ((Additive.toMul g : X.functionFieldˣ) : X.functionField) * f ∈
      stalkSubmodule (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) x := by
  rw [mem_stalkSubmodule] at hf ⊢
  rcases eq_or_ne f 0 with rfl | h0
  · exact Or.inl (mul_zero _)
  refine Or.inr ?_
  have hf' := hf.resolve_left h0
  rw [coeff_sub_principalDivisor, Scheme.ord_mul (Units.ne_zero _) h0]
  omega

/-- Multiplication by a nonzero rational function `g` on the local principal parts at `x`,
`K(X) / 𝒪_X(D)_x → K(X) / 𝒪_X(D - div g)_x`. -/
def principalPartMapOfMul (D : SchemeWeilDivisor X) (x : CodimensionOnePoint X) :
    PrincipalPart D x →ₗ[X.presheaf.stalk (x : X)]
      PrincipalPart (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) x :=
  Submodule.mapQ _ _
    (LinearMap.mulLeft (X.presheaf.stalk (x : X))
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField))
    fun _ hf ↦ mul_mem_stalkSubmodule_sub_principalDivisor g hf

/-- Multiplication by `g` sends the class of `f` to the class of `g * f`. -/
@[simp]
lemma principalPartMapOfMul_mk (D : SchemeWeilDivisor X) (x : CodimensionOnePoint X)
    (f : X.functionField) :
    principalPartMapOfMul g D x (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (((Additive.toMul g : X.functionFieldˣ) : X.functionField) * f) :=
  (Submodule.mapQ_apply (x := f) ..).trans (congrArg _ (LinearMap.mulLeft_apply ..))

/-- Multiplication by a nonzero rational function `g`, as a morphism of principal-parts sheaves
`principalParts D ⟶ principalParts (D - div g)`. It is the map induced on the cokernels of the
principal-parts resolutions by `SchemeWeilDivisor.sheafMul`
(`SchemeWeilDivisor.principalPartsMap_sheafMul`). -/
def principalPartsMul (D : SchemeWeilDivisor X) :
    principalParts D ⟶
      principalParts (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) :=
  principalPartsHomMk (principalPartMapOfMul g D)

/-- Evaluation of the multiplication morphism is multiplication of local principal parts. -/
@[simp]
lemma principalPartsMul_app_apply (D : SchemeWeilDivisor X) (U : X.Opens)
    (s : Γ(principalParts D, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartsSectionsEquiv _ U ((principalPartsMul g D).app U s) x =
      principalPartMapOfMul g D x.val (principalPartsSectionsEquiv D U s x) :=
  principalPartsHomMk_app_apply _ U s x

/-- Taking principal parts commutes with multiplication by `g`. -/
@[reassoc (attr := simp)]
lemma toPrincipalParts_principalPartsMul (D : SchemeWeilDivisor X) :
    toPrincipalParts D ≫ principalPartsMul g D =
      Scheme.rationalFunctionsMul X ((Additive.toMul g : X.functionFieldˣ) : X.functionField) ≫
        toPrincipalParts _ := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  apply (principalPartsSectionsEquiv _ U).injective
  apply DFinsupp.ext
  intro x
  have : Nonempty U := ⟨⟨x.val, x.property⟩⟩
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    principalPartsMul_app_apply, toPrincipalParts_app_apply, principalPartAt_eq,
    principalPartMapOfMul_mk, Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app]

end Mul

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

/-- The square formed by `SchemeWeilDivisor.sheafMul` and multiplication on rational functions
induces multiplication on principal parts. -/
@[simp]
lemma principalPartsMap_sheafMul (g : Additive X.functionFieldˣ)
    (hcomm : sheafι D ≫ Scheme.rationalFunctionsMul X
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      sheafMul g D ≫ sheafι _) :
    principalPartsMap (sheafMul g D) _ hcomm = principalPartsMul g D := by
  apply (cancel_epi (toPrincipalParts D)).1
  simp

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
