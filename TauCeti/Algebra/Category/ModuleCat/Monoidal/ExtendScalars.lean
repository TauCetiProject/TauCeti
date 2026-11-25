/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation

/-!
# The composition isomorphisms of extension of scalars are monoidal

For morphisms of commutative rings `f₁₂ : R₁ →+* R₂` and `f₂₃ : R₂ →+* R₃`, Mathlib's
`ModuleCat.extendScalarsComp f₁₂ f₂₃` identifies extension of scalars along `f₂₃.comp f₁₂` with
the composite of the two extensions of scalars. This file shows that it is a monoidal natural
isomorphism for the monoidal structures of `ModuleCat.extendScalars`
(`Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`). Its conjugate along the
extension–restriction adjunctions is the composition isomorphism of restriction of scalars, which
is monoidal for the induced lax monoidal structures; the oplax tensor comparisons, inverse to the
tensor comparisons, transfer along conjugation
(`CategoryTheory.Adjunction.app_tensor_comp_δ_of_conjugateEquiv`).

Extension of scalars along a ring morphism `f₁₃` that is only propositionally equal to
`f₂₃.comp f₁₂`, such as the structure map of an algebra `S` over `K` compared with the composite
`K → R → S` of the structure map of `R` and a morphism of algebras, is handled by
`ModuleCat.extendScalarsComp'`, the counterpart of Mathlib's `ModuleCat.restrictScalarsComp'`.
Its associativity and unit coherences are those of Mathlib's `ModuleCat.extendScalars_assoc` and
`ModuleCat.extendScalars_comp_id`.

## Main declarations

* `ModuleCat.conjugateEquiv_extendScalarsComp_hom`: the conjugate of `extendScalarsComp` is the
  inverse of `restrictScalarsComp`.
* `ModuleCat.extendScalarsComp'`: extension of scalars along a ring morphism equal to a composite.
* `ModuleCat.extendScalarsComp'_assoc` and `ModuleCat.extendScalarsComp'_hom_comp_id`: its
  coherences.
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

namespace ModuleCat

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₁₃ : R₁ →+* R₃) (h : f₁₃ = f₂₃.comp f₁₂)

/-- The comparison of restriction of scalars along a composite with the composite of restrictions
of scalars is compatible with their lax monoidal structures. -/
instance : NatTrans.IsMonoidal (restrictScalarsComp'.{u} f₁₂ f₂₃ f₁₃ h).inv where
  unit := by
    ext
    subst h
    simp only [restrictScalarsComp'_inv_app, Functor.comp_obj]
    -- `restrictScalars_η` is stated in `dsimp%` normal form, which `rw` cannot match here.
    erw [restrictScalars_η, restrictScalars_η, restrictScalars_η]
    rfl
  tensor M N := by
    refine MonoidalCategory.tensor_ext fun m n ↦ ?_
    subst h
    have h₁ := restrictScalars_μ_tmul f₁₂ _ _ m n
    have h₂ := restrictScalars_μ_tmul f₂₃ M N m n
    have h₃ := restrictScalars_μ_tmul (f₂₃.comp f₁₂) M N m n
    dsimp at h₁ h₂ h₃ ⊢
    rw [h₁]
    exact h₂.trans h₃.symm

/-- The conjugate of the composition isomorphism of extension of scalars is the inverse of the
composition isomorphism of restriction of scalars. -/
theorem conjugateEquiv_extendScalarsComp_hom :
    conjugateEquiv ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
      (extendRestrictScalarsAdj (f₂₃.comp f₁₂)) (extendScalarsComp.{u} f₁₂ f₂₃).hom =
        (restrictScalarsComp f₁₂ f₂₃).inv := by
  rw [extendScalarsComp, ← conjugateIsoEquiv_apply_hom, Equiv.apply_symm_apply, Iso.symm_hom]

/-- The composition isomorphism of extension of scalars is a monoidal natural isomorphism. -/
instance : NatTrans.IsMonoidal (extendScalarsComp.{u} f₁₂ f₂₃).hom :=
  NatTrans.IsMonoidal.of_tensor _ fun M N ↦ by
    rw [← cancel_mono (δ (extendScalars f₁₂ ⋙ extendScalars f₂₃) M N), Category.assoc,
      Category.assoc, Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _
        (conjugateEquiv_extendScalarsComp_hom f₁₂ f₂₃),
      Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- Extension of scalars along a ring morphism `f₁₃` equal to a composite `f₂₃.comp f₁₂` is the
composite of the two extensions of scalars. -/
noncomputable def extendScalarsComp' :
    extendScalars.{u, u, u} f₁₃ ≅ extendScalars.{u, u, u} f₁₂ ⋙ extendScalars.{u, u, u} f₂₃ :=
  eqToIso (congrArg extendScalars h) ≪≫ extendScalarsComp f₁₂ f₂₃

/-- For the composite itself, `extendScalarsComp'` is `extendScalarsComp`. -/
@[simp]
theorem extendScalarsComp'_rfl :
    extendScalarsComp' f₁₂ f₂₃ (f₂₃.comp f₁₂) rfl = extendScalarsComp f₁₂ f₂₃ := by
  simp [extendScalarsComp']

/-- `extendScalarsComp'` is a monoidal natural isomorphism. -/
instance : NatTrans.IsMonoidal (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom := by
  subst h
  rw [extendScalarsComp'_rfl]
  infer_instance

section Coherence

variable {R₄ : Type u} [CommRing R₄] (f₃₄ : R₃ →+* R₄) (f₂₄ : R₂ →+* R₄) (f₁₄ : R₁ →+* R₄)

/-- The isomorphisms `extendScalarsComp'` are associative. -/
@[reassoc]
theorem extendScalarsComp'_assoc (h₁₄ : f₁₄ = f₃₄.comp f₁₃) (h₂₄ : f₂₄ = f₃₄.comp f₂₃)
    (h₁₄' : f₁₄ = f₂₄.comp f₁₂) :
    (extendScalarsComp' f₁₃ f₃₄ f₁₄ h₁₄).hom ≫
      Functor.whiskerRight (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom _ =
        (extendScalarsComp' f₁₂ f₂₄ f₁₄ h₁₄').hom ≫
          Functor.whiskerLeft _ (extendScalarsComp' f₂₃ f₃₄ f₂₄ h₂₄).hom ≫
            (Functor.associator _ _ _).inv := by
  subst h h₂₄ h₁₄
  simp only [extendScalarsComp'_rfl]
  exact extendScalars_assoc f₁₂ f₂₃ f₃₄

end Coherence

variable {f₂₂ : R₂ →+* R₂} (hf₂₂ : f₂₂ = RingHom.id R₂)

/-- Extension of scalars along a ring endomorphism equal to the identity is isomorphic to the
identity functor. -/
noncomputable def extendScalarsId' : extendScalars.{u, u, u} f₂₂ ≅ 𝟭 _ :=
  eqToIso (congrArg extendScalars hf₂₂) ≪≫ extendScalarsId R₂

/-- Extension of scalars along a morphism followed by a ring endomorphism equal to the identity
is extension of scalars along the morphism. -/
theorem extendScalarsComp'_hom_comp_id (h₁₂ : f₁₂ = f₂₂.comp f₁₂) :
    (extendScalarsComp' f₁₂ f₂₂ f₁₂ h₁₂).hom ≫
      Functor.whiskerLeft _ (extendScalarsId' hf₂₂).hom ≫ (Functor.rightUnitor _).hom = 𝟙 _ := by
  subst hf₂₂
  rw [extendScalarsId', Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp]
  exact extendScalars_comp_id f₁₂

end ModuleCat
