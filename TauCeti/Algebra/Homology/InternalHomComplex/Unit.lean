/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import TauCeti.Algebra.Homology.CochainComplex.TensorUnit
public import TauCeti.Algebra.Homology.InternalHomComplex.Basic
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic

/-!
# The internal Hom complex represents the Hom complex

Let `C` be a closed monoidal preadditive category with countable products. Applying the functor
`Hom(T, -)` degreewise to the internal Hom complex `𝓗om^•(K, L)` gives Mathlib's Hom complex of
`K ⊗ T` and `L` (`CochainComplex.linearCoyonedaInternalHomComplexIso`). For the monoidal unit
`T = 𝟙_ C` this identifies the "global sections" `Hom(𝟙, 𝓗om^•(K, L))` of the internal Hom
complex with the Hom complex `CochainComplex.linearHomComplex ℤ K L`
(`CochainComplex.globalSectionsInternalHomComplexIso`). When `C` is the category of
`𝒪_X`-modules on a scheme `X`, `Hom(𝒪_X, M)` is the module of global sections of `M`
(Mathlib's `SheafOfModules.unitHomEquiv`), so this is the statement that the global sections of
the Hom complex of complexes of `𝒪_X`-modules of [Stacks, Section 20.41 (0A8K)] form the Hom
complex of complexes of abelian groups.

The internal Hom complex out of the unit placed in degree `0` is the target complex:
`𝓗om^•(𝟙[0], L) ≅ L` (`CochainComplex.internalHomComplexSingleUnitIso`).

## Main definitions

* `CochainComplex.linearCoyonedaInternalHomComplexIso`: `Hom(T, 𝓗om^•(K, L))` is the Hom complex
  of `K ⊗ T` and `L`.
* `CochainComplex.globalSectionsInternalHomComplexIso`: `Hom(𝟙, 𝓗om^•(K, L))` is the Hom complex
  of `K` and `L`.
* `CochainComplex.internalHomComplexSingleUnitIso`: `𝓗om^•(𝟙[0], L) ≅ L`.

## References

* [Stacks Project, Section 20.41 (0A8K)](https://stacks.math.columbia.edu/tag/0A8K).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed CochainComplex.HomComplex Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C]

section Coyoneda

variable (K L : CochainComplex C ℤ) (T : C)

/-- Applying `Hom(T, -)` degreewise to the internal Hom complex `𝓗om^•(K, L)` gives the Hom
complex of `K ⊗ T` and `L`; in degree `n` this is `CochainComplex.internalHomComplexHomEquiv`. -/
def linearCoyonedaInternalHomComplexIso :
    (((linearCoyoneda ℤ C).obj (op T)).mapHomologicalComplex _).obj (internalHomComplex K L) ≅
      linearHomComplex ℤ (((tensorRight T).mapHomologicalComplex _).obj K) L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (internalHomComplexHomEquiv K L T n).toIntLinearEquiv.toModuleIso)
    (fun n m _ ↦ by
      ext φ
      exact (internalHomComplexHomEquiv_comp_d φ m).symm)

/-- The forward component of `linearCoyonedaInternalHomComplexIso` sends a morphism to its
cochain. -/
lemma linearCoyonedaInternalHomComplexIso_hom_f_apply (n : ℤ)
    (φ : T ⟶ (internalHomComplex K L).X n) :
    (dsimp% ((linearCoyonedaInternalHomComplexIso K L T).hom.f n).hom φ) =
      internalHomComplexHomEquiv K L T n φ :=
  (rfl)

end Coyoneda

section Unit

variable (K L : CochainComplex C ℤ)

/-- The global sections `Hom(𝟙, 𝓗om^•(K, L))` of the internal Hom complex are the Hom complex of
`K` and `L`: a morphism `𝟙 ⟶ 𝓗om^n(K, L)` is a degree `n` cochain `K ≅ K ⊗ 𝟙 ⟶ L`. -/
def globalSectionsInternalHomComplexIso :
    (((linearCoyoneda ℤ C).obj (op (𝟙_ C))).mapHomologicalComplex _).obj
        (internalHomComplex K L) ≅ linearHomComplex ℤ K L :=
  linearCoyonedaInternalHomComplexIso K L (𝟙_ C) ≪≫
    ((TauCeti.linearHomComplexFunctor ℤ).mapIso (tensorRightUnitIso K).symm.op).app L

/-- The cochain attached to a global section `𝟙 ⟶ 𝓗om^n(K, L)`. -/
lemma globalSectionsInternalHomComplexIso_hom_f_apply (n : ℤ)
    (φ : 𝟙_ C ⟶ (internalHomComplex K L).X n) :
    (dsimp% ((globalSectionsInternalHomComplexIso K L).hom.f n).hom φ) =
      (Cochain.ofHom (tensorRightUnitIso K).inv).comp (internalHomComplexHomEquiv K L _ n φ)
        (zero_add n) :=
  TauCeti.linearHomComplexPrecomp_f_apply (tensorRightUnitIso K).inv L n
    (internalHomComplexHomEquiv K L _ n φ)

end Unit

section Single

variable [HasZeroObject C] (L : CochainComplex C ℤ)

/-- Morphisms `T ⟶ 𝓗om^n(𝟙[0], L)` are morphisms `T ⟶ L^n`. -/
private def singleUnitHomEquiv (T : C) (n : ℤ) :
    (T ⟶ (internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L).X n) ≃+ (T ⟶ L.X n) :=
  ((internalHomComplexHomEquiv _ L T n).trans
    { toFun z := (Cochain.ofHom (singleUnitTensorIso T).inv).comp z (zero_add n)
      invFun z := (Cochain.ofHom (singleUnitTensorIso T).hom).comp z (zero_add n)
      left_inv z := by
        dsimp only
        rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
          Iso.hom_inv_id, Cochain.id_comp]
      right_inv z := by
        dsimp only
        rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
          Iso.inv_hom_id, Cochain.id_comp]
      map_add' z z' := Cochain.comp_add _ z z' (zero_add n) }).trans
    (Cochain.fromSingleEquiv (zero_add n))

private lemma singleUnitHomEquiv_comp {T' T : C} (g : T' ⟶ T) {n : ℤ}
    (φ : T ⟶ (internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L).X n) :
    singleUnitHomEquiv L T' n (g ≫ φ) = g ≫ singleUnitHomEquiv L T n φ := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (singleUnitTensorIso T).inv).comp (internalHomComplexHomEquiv _ L T n φ)
      (zero_add n)) n (zero_add n)
  have hφ : singleUnitHomEquiv L T n φ = f := by
    rw [← Cochain.fromSingleEquiv_fromSingleMk f (zero_add n), hf]
    rfl
  rw [hφ]
  -- Unfold the composite AddEquiv to reach the cochain to which the naturality lemmas apply.
  -- There is no application lemma for this proof-specific equivalence.
  change Cochain.fromSingleEquiv (zero_add n) ((Cochain.ofHom (singleUnitTensorIso T').inv).comp
    (internalHomComplexHomEquiv _ L T' n (g ≫ φ)) (zero_add n)) = _
  rw [internalHomComplexHomEquiv_comp, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    singleUnitTensorIso_inv_naturality, Cochain.comp_assoc_of_first_is_zero_cochain, ← hf,
    ← Cochain.fromSingleMk_precomp, Cochain.fromSingleEquiv_fromSingleMk]

private lemma singleUnitHomEquiv_comp_d {T : C} {n : ℤ}
    (φ : T ⟶ (internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L).X n) (m : ℤ) :
    singleUnitHomEquiv L T m (φ ≫ (internalHomComplex _ L).d n m) =
      singleUnitHomEquiv L T n φ ≫ L.d n m := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (singleUnitTensorIso T).inv).comp (internalHomComplexHomEquiv _ L T n φ)
      (zero_add n)) n (zero_add n)
  have hφ : singleUnitHomEquiv L T n φ = f := by
    rw [← Cochain.fromSingleEquiv_fromSingleMk f (zero_add n), hf]
    rfl
  rw [hφ]
  -- Unfold the composite AddEquiv to expose the cochain differential; the differential lemmas
  -- apply to this cochain rather than to the proof-specific equivalence.
  change Cochain.fromSingleEquiv (zero_add m) ((Cochain.ofHom (singleUnitTensorIso T).inv).comp
    (internalHomComplexHomEquiv _ L T m (φ ≫ (internalHomComplex _ L).d n m)) (zero_add m)) = _
  rw [internalHomComplexHomEquiv_comp_d, ← δ_ofHom_comp, ← hf,
    Cochain.δ_fromSingleMk f (zero_add n) m m (zero_add m), Cochain.fromSingleEquiv_fromSingleMk]

/-- The degree `n` term of `𝓗om^•(𝟙[0], L)` is `L^n`, by the Yoneda lemma applied to
`singleUnitHomEquiv`. -/
private def singleUnitXIso (n : ℤ) :
    (internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L).X n ≅ L.X n :=
  Yoneda.ext _ _ (fun φ ↦ singleUnitHomEquiv L _ n φ) (fun ψ ↦ (singleUnitHomEquiv L _ n).symm ψ)
    (fun φ ↦ AddEquiv.symm_apply_apply _ φ) (fun ψ ↦ AddEquiv.apply_symm_apply _ ψ)
    (fun g φ ↦ singleUnitHomEquiv_comp L g φ)

private lemma comp_singleUnitXIso_hom {T : C} {n : ℤ}
    (φ : T ⟶ (internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L).X n) :
    φ ≫ (singleUnitXIso L n).hom = singleUnitHomEquiv L T n φ := by
  -- The forward map of an isomorphism given by `Yoneda.ext` is the image of the identity.
  have h : (singleUnitXIso L n).hom = singleUnitHomEquiv L _ n (𝟙 _) := rfl
  rw [h, ← singleUnitHomEquiv_comp, Category.comp_id]

/-- The internal Hom complex out of the monoidal unit placed in degree `0` is the target:
`𝓗om^•(𝟙[0], L) ≅ L`. In degree `n` a morphism `T ⟶ 𝓗om^n(𝟙[0], L)` is a degree `n` cochain
`𝟙[0] ⊗ T ≅ T[0] ⟶ L`, that is, a morphism `T ⟶ L^n`. -/
def internalHomComplexSingleUnitIso :
    internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L ≅ L :=
  HomologicalComplex.Hom.isoOfComponents (singleUnitXIso L)
    (fun n m _ ↦ by
      rw [comp_singleUnitXIso_hom, ← Category.id_comp (singleUnitXIso L n).hom,
        comp_singleUnitXIso_hom, ← singleUnitHomEquiv_comp_d, Category.id_comp])

/-- The isomorphism `𝓗om^•(𝟙[0], L) ≅ L` sends a morphism `T ⟶ 𝓗om^n(𝟙[0], L)` to the degree `0`
component `T ≅ 𝟙 ⊗ T ⟶ L^n` of its cochain, where `𝟙` is identified with the degree `0` term of
`𝟙[0]`. -/
lemma comp_internalHomComplexSingleUnitIso_hom_f {T : C} {n : ℤ}
    (φ : T ⟶ (internalHomComplex ((singleFunctor C 0).obj (𝟙_ C)) L).X n) :
    φ ≫ (internalHomComplexSingleUnitIso L).hom.f n =
      (λ_ T).inv ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ▷ T ≫
        (internalHomComplexHomEquiv _ L T n φ).v 0 n (zero_add n) := by
  -- The components of an isomorphism built by `isoOfComponents` are the given isomorphisms.
  have h : (internalHomComplexSingleUnitIso L).hom.f n = (singleUnitXIso L n).hom := rfl
  rw [h, comp_singleUnitXIso_hom]
  simp only [singleUnitHomEquiv, AddEquiv.trans_apply, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [Cochain.fromSingleEquiv_apply, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    singleUnitTensorIso_inv_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Single

end CochainComplex
