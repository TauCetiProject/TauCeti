/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import TauCeti.Algebra.Category.ModuleCat.ExtendScalars.Comp
public import TauCeti.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation

/-!
# The composition isomorphisms of extension of scalars are monoidal

For morphisms of commutative rings `f₁₂ : R₁ →+* R₂` and `f₂₃ : R₂ →+* R₃`, Mathlib's
`ModuleCat.extendScalarsComp f₁₂ f₂₃` identifies extension of scalars along `f₂₃.comp f₁₂` with
the composite of the two extensions of scalars. This file shows that it is a monoidal natural
isomorphism for the monoidal structures of `ModuleCat.extendScalars`
(`Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`). Its conjugate along the
extension–restriction adjunctions is the composition isomorphism of restriction of scalars
(`ModuleCat.conjugateEquiv_extendScalarsComp_hom`), which is monoidal for the induced lax
monoidal structures; the oplax tensor comparisons, inverse to the tensor comparisons, transfer
along conjugation (`CategoryTheory.Adjunction.app_tensor_comp_δ_of_conjugateEquiv`).

The same holds for the variant `ModuleCat.extendScalarsComp'` along a ring morphism only
propositionally equal to a composite, and hence for the comparison isomorphisms
`CategoryTheory.Functor.scalarExtensionCompIso` and
`CategoryTheory.Functor.scalarExtensionIsoOfIso` of scalar extensions of lax monoidal
module-valued functors (`TauCeti.Algebra.Category.ModuleCat.ExtendScalars.Comp`).
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe u u₁ u₂ v₁ v₂

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

/-- The composition isomorphism of extension of scalars is a monoidal natural isomorphism. -/
instance : NatTrans.IsMonoidal (extendScalarsComp.{u} f₁₂ f₂₃).hom :=
  NatTrans.IsMonoidal.of_tensor _ fun M N ↦ by
    rw [← cancel_mono (δ (extendScalars f₁₂ ⋙ extendScalars f₂₃) M N), Category.assoc,
      Category.assoc, Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _
        (conjugateEquiv_extendScalarsComp_hom f₁₂ f₂₃),
      Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- `extendScalarsComp'` is a monoidal natural isomorphism. -/
instance : NatTrans.IsMonoidal (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom := by
  subst h
  rw [extendScalarsComp'_rfl]
  infer_instance

end ModuleCat

namespace CategoryTheory.Functor

variable {K : Type u} [CommRing K] {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- `scalarExtensionCompIso` is a monoidal natural isomorphism. -/
instance (ω : C ⥤ ModuleCat.{u} K) [ω.LaxMonoidal] {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (f : R →ₐ[K] S) :
    NatTrans.IsMonoidal (ω.scalarExtensionCompIso f).hom :=
  inferInstanceAs (NatTrans.IsMonoidal ((Functor.associator _ _ _).hom ≫ whiskerLeft ω
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).inv))

/-- `scalarExtensionIsoOfIso` is a monoidal natural isomorphism. -/
instance {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {ω : C ⥤ ModuleCat.{u} K} [ω.LaxMonoidal] {ω' : D ⥤ ModuleCat.{u} K} [ω'.LaxMonoidal]
    (ι : F ⋙ ω' ≅ ω) [NatTrans.IsMonoidal ι.hom] (R : Type u) [CommRing R] [Algebra K R] :
    NatTrans.IsMonoidal (scalarExtensionIsoOfIso F ι R).hom :=
  inferInstanceAs (NatTrans.IsMonoidal ((Functor.associator _ _ _).inv ≫
    whiskerRight ι.hom (ModuleCat.extendScalars (algebraMap K R))))

end CategoryTheory.Functor
