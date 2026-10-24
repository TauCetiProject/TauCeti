/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.RestrictScalars
public import TauCeti.CategoryTheory.Preadditive.Equivalence

/-!
# Invariance of `K₀^gr(proj A)`, `G₀^gr(mod A)` and the graded Cartan map

Let `e : GradedModuleCat 𝒜 ≌ GradedModuleCat ℬ` be an equivalence of graded module categories
which commutes with the grading shifts, and which preserves and reflects finite generation and
projectivity of underlying modules. Equivalences of abelian categories are exact, so `e`
restricts to graded exact equivalences between the finite graded modules and between the finite
graded projectives over the two sides. On graded Grothendieck groups it induces
`ℤ[q,q⁻¹]`-linear isomorphisms

```text
K₀^gr(proj A) ≃ K₀^gr(proj B),   G₀^gr(mod A) ≃ G₀^gr(mod B),
```

both sending the class of `M` to the class of `e.functor.obj M`, and these intertwine the two
graded Cartan maps. In particular the graded Cartan map of `A` is bijective if and only if that
of `B` is.

The motivating instance is restriction of scalars along a graded algebra isomorphism
`e : A ≃ₐ[k] B`, one with `e a ∈ ℬᵢ ↔ a ∈ 𝒜ᵢ`
(`TauCeti.GradedModuleCat.restrictScalarsEquivalenceOfAlgEquiv`). It commutes with the shift on
the nose, and it preserves and reflects finite generation and projectivity, so the graded
Grothendieck groups and the bijectivity of the graded Cartan map are invariants of the graded
isomorphism class of the algebra. This is the graded counterpart of
`TauCeti/Algebra/Category/ModuleCat/CartanMap/Morita.lean`.

The finiteness and projectivity hypotheses on a general equivalence are stated explicitly, as
equalities of object properties; for restriction of scalars along a graded isomorphism they are
`TauCeti.GradedModuleCat.gradedFiniteModules_inverseImage_restrictScalars` and
`TauCeti.GradedModuleCat.gradedFiniteProjectiveModules_inverseImage_restrictScalars`.

## Main definitions

* `CategoryTheory.Equivalence.gradedModuleExactEquiv`: an equivalence of graded module categories
  commuting with the shifts, as a graded exact equivalence of the canonical graded exact
  structures.
* `CategoryTheory.Equivalence.gradedFiniteModulesLaurentK0Equiv` and
  `CategoryTheory.Equivalence.gradedFiniteProjectiveModulesLaurentK0Equiv`: the induced
  isomorphisms `G₀^gr(mod A) ≃ G₀^gr(mod B)` and `K₀^gr(proj A) ≃ K₀^gr(proj B)`.

## Main results

* `CategoryTheory.Equivalence.gradedCartanMap_comp_gradedFiniteProjectiveModulesLaurentK0Equiv`:
  the two graded Cartan maps commute with the induced isomorphisms.
* `CategoryTheory.Equivalence.gradedCartanMap_bijective_iff`: the graded Cartan map of `A` is
  bijective if and only if that of `B` is.
* `TauCeti.GradedModuleCat.gradedCartanMap_bijective_iff_of_algEquiv`: the same for a graded
  algebra isomorphism.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Section 2.2, for change of rings between graded module categories.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 2,
  for the invariance of `K₀` of a ring under ring isomorphisms and Morita equivalences.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.ObjectProperty TauCeti

universe uk uA uB

namespace CategoryTheory.Equivalence

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {B : Type uB} [Ring B] [Algebra k B] {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}
  (e : GradedModuleCat.{uA} 𝒜 ≌ GradedModuleCat.{uB} ℬ)

/-- An equivalence of graded module categories commuting with the grading shifts is a graded
exact equivalence for the canonical exact structures: an equivalence of abelian categories
preserves all finite limits and colimits. -/
@[expose]
def gradedModuleExactEquiv
    (σ : (GradedModuleCat.shift 𝒜).functor ⋙ e.functor ≅
      e.functor ⋙ (GradedModuleCat.shift ℬ).functor) :
    GradedExactEquiv (gradedModuleCanonicalExactStructure 𝒜)
      (gradedModuleCanonicalExactStructure ℬ) where
  equiv := e
  isConflationExact := (GradedConflationExact.abelian e.functor σ).isConflationExact
  inverse_isConflationExact := by
    rw [GradedExactStructure.abelian_toExactStructure,
      GradedExactStructure.abelian_toExactStructure]
    exact ExactStructure.isConflationExact_abelian e.inverse
  commShift := (GradedConflationExact.abelian e.functor σ).commShift

/-- The underlying equivalence of `CategoryTheory.Equivalence.gradedModuleExactEquiv` is `e`. -/
@[simp]
theorem gradedModuleExactEquiv_equiv
    (σ : (GradedModuleCat.shift 𝒜).functor ⋙ e.functor ≅
      e.functor ⋙ (GradedModuleCat.shift ℬ).functor) :
    (e.gradedModuleExactEquiv σ).equiv = e :=
  (rfl)

variable (σ : (GradedModuleCat.shift 𝒜).functor ⋙ e.functor ≅
  e.functor ⋙ (GradedModuleCat.shift ℬ).functor)

section Finite

variable (hfin : (gradedFiniteModules ℬ).inverseImage e.functor = gradedFiniteModules 𝒜)

/-- **Invariance of `G₀^gr(mod A)`.** An equivalence of graded module categories commuting with
the shifts and preserving and reflecting finite generation induces a `ℤ[q,q⁻¹]`-linear
isomorphism of the graded Grothendieck groups of finite graded modules, sending `[M]` to
`[e.functor.obj M]`. -/
def gradedFiniteModulesLaurentK0Equiv :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) ≃ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uB} (gradedFiniteModulesExactStructure ℬ) :=
  LaurentK0.mapEquiv <| (e.gradedModuleExactEquiv σ).congrFullSubcategory
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift hfin

/-- The isomorphism `G₀^gr(mod A) ≃ G₀^gr(mod B)` sends `[M]` to `[e.functor.obj M]`. -/
@[simp]
theorem gradedFiniteModulesLaurentK0Equiv_of (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    e.gradedFiniteModulesLaurentK0Equiv σ hfin
        (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) =
      LaurentK0.of.{uB} (gradedFiniteModulesExactStructure ℬ)
        ((e.congrFullSubcategory hfin).functor.obj M) :=
  (LaurentK0.mapEquiv_of.{uA, uB} _ M).trans <|
    congrArg (fun F ↦ LaurentK0.of.{uB} (gradedFiniteModulesExactStructure ℬ) (F.functor.obj M))
      (GradedExactEquiv.congrFullSubcategory_equiv _ _ _ _ _ hfin)

/-- The inverse isomorphism `G₀^gr(mod B) ≃ G₀^gr(mod A)` sends `[N]` to `[e.inverse.obj N]`. -/
@[simp]
theorem gradedFiniteModulesLaurentK0Equiv_symm_of (M : (gradedFiniteModules ℬ).FullSubcategory) :
    (e.gradedFiniteModulesLaurentK0Equiv σ hfin).symm
        (LaurentK0.of.{uB} (gradedFiniteModulesExactStructure ℬ) M) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ((e.congrFullSubcategory hfin).inverse.obj M) :=
  (LaurentK0.mapEquiv_symm_of.{uA, uB} _ M).trans <|
    congrArg (fun F ↦ LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (F.inverse.obj M))
      (GradedExactEquiv.congrFullSubcategory_equiv _ _ _ _ _ hfin)

end Finite

section Projective

variable (hproj :
  (gradedFiniteProjectiveModules ℬ).inverseImage e.functor = gradedFiniteProjectiveModules 𝒜)

/-- **Invariance of `K₀^gr(proj A)`.** An equivalence of graded module categories commuting with
the shifts and preserving and reflecting finitely generated projective underlying modules
induces a `ℤ[q,q⁻¹]`-linear isomorphism of the graded Grothendieck groups of finite graded
projectives, sending `[P]` to `[e.functor.obj P]`. -/
def gradedFiniteProjectiveModulesLaurentK0Equiv :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ≃ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uB} (gradedFiniteProjectiveModulesExactStructure ℬ) :=
  LaurentK0.mapEquiv <| (e.gradedModuleExactEquiv σ).congrFullSubcategory
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift
    gradedFiniteProjectiveModules_gradedAbelian_shift hproj

/-- The isomorphism `K₀^gr(proj A) ≃ K₀^gr(proj B)` sends `[P]` to `[e.functor.obj P]`. -/
@[simp]
theorem gradedFiniteProjectiveModulesLaurentK0Equiv_of
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    e.gradedFiniteProjectiveModulesLaurentK0Equiv σ hproj
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) =
      LaurentK0.of.{uB} (gradedFiniteProjectiveModulesExactStructure ℬ)
        ((e.congrFullSubcategory hproj).functor.obj P) :=
  (LaurentK0.mapEquiv_of.{uA, uB} _ P).trans <|
    congrArg
      (fun F ↦ LaurentK0.of.{uB} (gradedFiniteProjectiveModulesExactStructure ℬ) (F.functor.obj P))
      (GradedExactEquiv.congrFullSubcategory_equiv _ _ _ _ _ hproj)

/-- The inverse isomorphism `K₀^gr(proj B) ≃ K₀^gr(proj A)` sends `[Q]` to `[e.inverse.obj Q]`. -/
@[simp]
theorem gradedFiniteProjectiveModulesLaurentK0Equiv_symm_of
    (P : (gradedFiniteProjectiveModules ℬ).FullSubcategory) :
    (e.gradedFiniteProjectiveModulesLaurentK0Equiv σ hproj).symm
        (LaurentK0.of.{uB} (gradedFiniteProjectiveModulesExactStructure ℬ) P) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ((e.congrFullSubcategory hproj).inverse.obj P) :=
  (LaurentK0.mapEquiv_symm_of.{uA, uB} _ P).trans <|
    congrArg
      (fun F ↦ LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (F.inverse.obj P))
      (GradedExactEquiv.congrFullSubcategory_equiv _ _ _ _ _ hproj)

end Projective

section Cartan

variable (hfin : (gradedFiniteModules ℬ).inverseImage e.functor = gradedFiniteModules 𝒜)
  (hproj :
    (gradedFiniteProjectiveModules ℬ).inverseImage e.functor = gradedFiniteProjectiveModules 𝒜)

/-- **Invariance of the graded Cartan map.** The graded Cartan maps of the two sides are
intertwined by the isomorphisms of graded Grothendieck groups induced by `e`. -/
theorem gradedCartanMap_comp_gradedFiniteProjectiveModulesLaurentK0Equiv :
    gradedCartanMap ℬ ∘ₗ (e.gradedFiniteProjectiveModulesLaurentK0Equiv σ hproj).toLinearMap =
      (e.gradedFiniteModulesLaurentK0Equiv σ hfin).toLinearMap ∘ₗ gradedCartanMap 𝒜 :=
  LaurentK0.hom_ext _ fun ⟨M, hM⟩ ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      gradedFiniteProjectiveModulesLaurentK0Equiv_of, gradedCartanMap_of hM,
      gradedFiniteModulesLaurentK0Equiv_of]
    -- `gradedCartanMap_of` is stated for `⟨X.obj, X.property⟩`, which is `X` by structure eta.
    refine (gradedCartanMap_of
      ((e.congrFullSubcategory hproj).functor.obj ⟨M, hM⟩).property).trans ?_
    exact congrArg _ (ObjectProperty.FullSubcategory.ext (by simp))

/-- Pointwise form of
`CategoryTheory.Equivalence.gradedCartanMap_comp_gradedFiniteProjectiveModulesLaurentK0Equiv`. -/
@[simp]
theorem gradedCartanMap_gradedFiniteProjectiveModulesLaurentK0Equiv
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :
    gradedCartanMap ℬ (e.gradedFiniteProjectiveModulesLaurentK0Equiv σ hproj x) =
      e.gradedFiniteModulesLaurentK0Equiv σ hfin (gradedCartanMap 𝒜 x) :=
  LinearMap.congr_fun (e.gradedCartanMap_comp_gradedFiniteProjectiveModulesLaurentK0Equiv σ hfin
    hproj) x

include σ hfin hproj in
/-- **Bijectivity of the graded Cartan map is invariant** under equivalences of graded module
categories commuting with the shifts and preserving finiteness and projectivity. -/
theorem gradedCartanMap_bijective_iff :
    Function.Bijective (gradedCartanMap 𝒜) ↔ Function.Bijective (gradedCartanMap ℬ) := by
  have h : ⇑(gradedCartanMap ℬ) = ⇑(e.gradedFiniteModulesLaurentK0Equiv σ hfin) ∘
      ⇑(gradedCartanMap 𝒜) ∘ ⇑(e.gradedFiniteProjectiveModulesLaurentK0Equiv σ hproj).symm := by
    ext x
    rw [Function.comp_apply, Function.comp_apply,
      ← gradedCartanMap_gradedFiniteProjectiveModulesLaurentK0Equiv e σ hfin hproj,
      LinearEquiv.apply_symm_apply]
  rw [h, EquivLike.comp_bijective, EquivLike.bijective_comp]

end Cartan

end CategoryTheory.Equivalence

namespace TauCeti.GradedModuleCat

universe u

variable {k : Type uk} [CommRing k] {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, e a ∈ ℬ i ↔ a ∈ 𝒜 i)

/-- Restriction of scalars along a graded algebra isomorphism pulls the finite graded
`𝒜`-modules back to the finite graded `ℬ`-modules. -/
theorem gradedFiniteModules_inverseImage_restrictScalars :
    (gradedFiniteModules 𝒜).inverseImage (restrictScalarsEquivalenceOfAlgEquiv.{u} e he).functor =
      gradedFiniteModules ℬ := by
  ext M
  rw [prop_inverseImage_iff, gradedFiniteModules_iff, gradedFiniteModules_iff]
  exact restrictScalars_finite_iff e he M

/-- Restriction of scalars along a graded algebra isomorphism pulls the finite graded
`𝒜`-projectives back to the finite graded `ℬ`-projectives. -/
theorem gradedFiniteProjectiveModules_inverseImage_restrictScalars :
    (gradedFiniteProjectiveModules 𝒜).inverseImage
        (restrictScalarsEquivalenceOfAlgEquiv.{u} e he).functor =
      gradedFiniteProjectiveModules ℬ := by
  ext M
  rw [prop_inverseImage_iff, gradedFiniteProjectiveModules_iff, gradedFiniteProjectiveModules_iff]
  exact and_congr (restrictScalars_finite_iff e he M) (restrictScalars_projective_iff e he M)

include e he in
/-- **Bijectivity of the graded Cartan map is a graded isomorphism invariant**: for a graded
algebra isomorphism `e : A ≃ₐ[k] B`, the graded Cartan map of `A` is bijective if and only if that
of `B` is. -/
theorem gradedCartanMap_bijective_iff_of_algEquiv :
    Function.Bijective (gradedCartanMap 𝒜) ↔ Function.Bijective (gradedCartanMap ℬ) :=
  ((restrictScalarsEquivalenceOfAlgEquiv e he).gradedCartanMap_bijective_iff
    (restrictScalarsShiftIso _ _) (gradedFiniteModules_inverseImage_restrictScalars e he)
    (gradedFiniteProjectiveModules_inverseImage_restrictScalars e he)).symm

end TauCeti.GradedModuleCat
