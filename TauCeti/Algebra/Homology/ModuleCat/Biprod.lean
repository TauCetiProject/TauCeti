/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Basis.Prod
public import TauCeti.Algebra.Category.ModuleCat.Biproducts

/-!
# Biproducts of complexes of modules

A short complex `K ⟶ L₁ ⊞ L₂ ⟶ N` of homological complexes of modules whose maps are
`biprod.lift a₁ a₂` and `biprod.desc b₁ b₂` is short exact as soon as, in each degree and under
given identifications of the terms with modules, the linear maps `(a₁, a₂) : K → L₁ × L₂` and
`b₁ + b₂ : L₁ × L₂ → N` form a short exact sequence of modules
(`HomologicalComplex.moduleCat_shortExact_biprod`). Mayer–Vietoris sequences have this shape.

The comparison uses `ModuleCat.inl_comp_biprodIsoProd_hom` and
`ModuleCat.inr_comp_biprodIsoProd_hom` from `TauCeti.Algebra.Category.ModuleCat.Biproducts`:
under Mathlib's identification `ModuleCat.biprodIsoProd` of the biproduct of two modules with
their product, the biproduct inclusions are `LinearMap.inl` and `LinearMap.inr`. Along the same
identification, bases of `K.X i` and `L.X i` give the basis `HomologicalComplex.biprodXBasis` of
`(K ⊞ L).X i`, made of their images under the two biproduct inclusions; this is how a direct sum
of based complexes is based.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 1.3.
-/

public section

open CategoryTheory Limits

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L₁ L₂ N : HomologicalComplex (ModuleCat.{v} R) c}
  {K' L₁' L₂' N' : ι → Type v} [∀ i, AddCommGroup (K' i)] [∀ i, Module R (K' i)]
  [∀ i, AddCommGroup (L₁' i)] [∀ i, Module R (L₁' i)] [∀ i, AddCommGroup (L₂' i)]
  [∀ i, Module R (L₂' i)] [∀ i, AddCommGroup (N' i)] [∀ i, Module R (N' i)]

/-- A short complex `K ⟶ L₁ ⊞ L₂ ⟶ N` of complexes of modules, with maps `biprod.lift a₁ a₂` and
`biprod.desc b₁ b₂`, is short exact when, in each degree and under identifications of the terms
with modules `K' i`, `L₁' i`, `L₂' i`, `N' i` carrying the components to linear maps `a₁' i`,
`a₂' i`, `b₁' i`, `b₂' i`, the pair map `(a₁' i).prod (a₂' i)` is injective, the sum map
`(b₁' i).coprod (b₂' i)` is surjective, and the two are exact. -/
theorem moduleCat_shortExact_biprod {a₁ : K ⟶ L₁} {a₂ : K ⟶ L₂} {b₁ : L₁ ⟶ N} {b₂ : L₂ ⟶ N}
    (w : biprod.lift a₁ a₂ ≫ biprod.desc b₁ b₂ = 0)
    (eK : ∀ i, K.X i ≅ ModuleCat.of R (K' i)) (eL₁ : ∀ i, L₁.X i ≅ ModuleCat.of R (L₁' i))
    (eL₂ : ∀ i, L₂.X i ≅ ModuleCat.of R (L₂' i)) (eN : ∀ i, N.X i ≅ ModuleCat.of R (N' i))
    (a₁' : ∀ i, K' i →ₗ[R] L₁' i) (a₂' : ∀ i, K' i →ₗ[R] L₂' i)
    (b₁' : ∀ i, L₁' i →ₗ[R] N' i) (b₂' : ∀ i, L₂' i →ₗ[R] N' i)
    (ha₁ : ∀ i, a₁.f i ≫ (eL₁ i).hom = (eK i).hom ≫ ModuleCat.ofHom (a₁' i))
    (ha₂ : ∀ i, a₂.f i ≫ (eL₂ i).hom = (eK i).hom ≫ ModuleCat.ofHom (a₂' i))
    (hb₁ : ∀ i, b₁.f i ≫ (eN i).hom = (eL₁ i).hom ≫ ModuleCat.ofHom (b₁' i))
    (hb₂ : ∀ i, b₂.f i ≫ (eN i).hom = (eL₂ i).hom ≫ ModuleCat.ofHom (b₂' i))
    (hexact : ∀ i, Function.Exact ((a₁' i).prod (a₂' i)) ((b₁' i).coprod (b₂' i)))
    (hinj : ∀ i, Function.Injective ((a₁' i).prod (a₂' i)))
    (hsurj : ∀ i, Function.Surjective ((b₁' i).coprod (b₂' i))) :
    (ShortComplex.mk (biprod.lift a₁ a₂) (biprod.desc b₁ b₂) w).ShortExact := by
  -- In each degree, transport the short exact sequence of modules along the identification of
  -- `(L₁ ⊞ L₂).X i` with the product module `L₁' i × L₂' i`.
  refine shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  let e₂ := biprodXIso L₁ L₂ i ≪≫ biprod.mapIso (eL₁ i) (eL₂ i) ≪≫ ModuleCat.biprodIsoProd _ _
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk (eK i).symm e₂.symm (eN i).symm ?_ ?_)
    (ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero _ _ (hexact i).linearMap_comp_eq_zero) (hexact i)
      (hinj i) (hsurj i))
  -- The two squares commute: compare components of the biproducts.
  · rw [← cancel_mono (biprodXIso L₁ L₂ i).hom]
    apply biprod.hom_ext
    · rw [← cancel_mono (eL₁ i).hom]
      ext x
      simp [e₂, ha₁, reassoc_of% ModuleCat.biprodIsoProd_inv_comp_fst]
    · rw [← cancel_mono (eL₂ i).hom]
      ext x
      simp [e₂, ha₂, reassoc_of% ModuleCat.biprodIsoProd_inv_comp_snd]
  · rw [← cancel_mono (eN i).hom]
    refine (cancel_epi (ModuleCat.biprodIsoProd (.of R (L₁' i)) (.of R (L₂' i))).hom).mp ?_
    apply biprod.hom_ext'
    · ext x
      simp [e₂, hb₁]
    · ext x
      simp [e₂, hb₂]

section Basis

variable {L : HomologicalComplex (ModuleCat.{v} R) c} {i : ι} {κ σ : Type*}

/-- The basis of the term `(K ⊞ L).X i` of a biproduct of complexes of modules made of the images
of a basis `b` of `K.X i` under `biprod.inl`, followed by the images of a basis `b'` of `L.X i`
under `biprod.inr`. -/
noncomputable def biprodXBasis (b : Module.Basis κ R (K.X i)) (b' : Module.Basis σ R (L.X i)) :
    Module.Basis (κ ⊕ σ) R ((K ⊞ L).X i) :=
  (b.prod b').map (biprodXIso K L i ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.symm

variable (b : Module.Basis κ R (K.X i)) (b' : Module.Basis σ R (L.X i))

@[simp]
theorem biprodXBasis_inl (k : κ) :
    biprodXBasis b b' (.inl k) = ((biprod.inl : K ⟶ K ⊞ L).f i).hom (b k) := by
  have h : ((biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprodXIso K L i ≪≫ ModuleCat.biprodIsoProd _ _).hom) =
      ModuleCat.ofHom (LinearMap.inl R _ _) := by
    rw [← inl_biprodXIso_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      ModuleCat.inl_comp_biprodIsoProd_hom]
  rw [biprodXBasis, Module.Basis.map_apply, LinearEquiv.symm_apply_eq, Iso.toLinearEquiv_apply,
    ← ModuleCat.comp_apply, h]
  simp

@[simp]
theorem biprodXBasis_inr (k : σ) :
    biprodXBasis b b' (.inr k) = ((biprod.inr : L ⟶ K ⊞ L).f i).hom (b' k) := by
  have h : ((biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprodXIso K L i ≪≫ ModuleCat.biprodIsoProd _ _).hom) =
      ModuleCat.ofHom (LinearMap.inr R _ _) := by
    rw [← inr_biprodXIso_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      ModuleCat.inr_comp_biprodIsoProd_hom]
  rw [biprodXBasis, Module.Basis.map_apply, LinearEquiv.symm_apply_eq, Iso.toLinearEquiv_apply,
    ← ModuleCat.comp_apply, h]
  simp

end Basis

end HomologicalComplex
