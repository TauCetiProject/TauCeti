/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Descending a coaction through a coalgebra inclusion

A linear factorization of a coaction through an injective coalgebra map inherits
coassociativity and the counit law, provided the relevant tensor maps remain injective.
Over a field, a comodule therefore descends uniquely exactly when its coaction lands in
the image of the smaller coefficient coalgebra. This gives the extension criterion for
rational representations whose coefficients lie in a coordinate subbialgebra.

The construction uses `LinearMap.codRestrictOfInjective` and the existing comodule
corestriction. See Sweedler, *Hopf Algebras*, Chapter 2, for coalgebra corestriction.
-/

public section

open scoped TensorProduct

open TauCeti TauCeti.Comodule

variable {R C D M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid D] [Module R D] [Coalgebra R D]
  [AddCommMonoid M] [Module R M] [Comodule R D M]

namespace CoalgHom

/-- A linear factorization of a coaction through a coalgebra map is a coaction if
tensoring twice with that map is injective. -/
@[implicit_reducible]
def comoduleOfFactor (f : C →ₗc[R] D) (ρ : M →ₗ[R] M ⊗[R] C)
    (hi : Function.Injective
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (TensorProduct.map f.toLinearMap f.toLinearMap)))
    (hρ : f.toLinearMap.lTensor M ∘ₗ ρ = coact (R := R) (C := D)) :
    Comodule R C M where
  coact := ρ
  coassoc := by
    ext m
    apply hi
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hm : f.toLinearMap.lTensor M (ρ m) = coact (R := R) (C := D) m := by
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hρ m
    rw [← f.assoc_rTensor_lTensor_comp ρ, hρ, ← f.comul_lTensor_lTensor, hm,
      coassoc_apply]
  lTensor_counit_comp_coact := by
    ext m
    have hm : f.toLinearMap.lTensor M (ρ m) = coact (R := R) (C := D) m := by
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hρ m
    rw [LinearMap.comp_apply, ← f.counit_lTensor_lTensor, hm]
    exact LinearMap.congr_fun lTensor_counit_comp_coact m

/-- The descended coaction is the specified linear factorization. -/
@[simp]
theorem comoduleOfFactor_coact (f : C →ₗc[R] D) (ρ : M →ₗ[R] M ⊗[R] C)
    (hi : Function.Injective
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (TensorProduct.map f.toLinearMap f.toLinearMap)))
    (hρ : f.toLinearMap.lTensor M ∘ₗ ρ = coact (R := R) (C := D)) :
    (comoduleOfFactor f ρ hi hρ).coact = ρ := (rfl)

/-- Over flat modules, a coaction descends uniquely through a coalgebra inclusion
exactly when it takes values in the tensor product with that coalgebra.
In particular, no finiteness assumptions are needed over a field. -/
theorem existsUnique_comoduleFactor_iff [Module.Flat R M] [Module.Flat R C]
    [Module.Flat R D] (f : C →ₗc[R] D) (hf : Function.Injective f) :
    (∃! σ : Comodule R C M,
      f.toLinearMap.lTensor M ∘ₗ σ.coact = coact (R := R) (C := D)) ↔
      ∀ m, coact (R := R) (C := D) m ∈ LinearMap.range (f.toLinearMap.lTensor M) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap (M := M) f.toLinearMap hf
  constructor
  · rintro ⟨σ, hσ, _⟩ m
    exact ⟨σ.coact m, LinearMap.congr_fun hσ m⟩
  · intro h
    let ρ := LinearMap.codRestrictOfInjective (coact (R := R) (C := D) (M := M))
      (f.toLinearMap.lTensor M) hi h
    have hρ : f.toLinearMap.lTensor M ∘ₗ ρ = coact (R := R) (C := D) :=
      LinearMap.codRestrictOfInjective_comp _ _ _ _
    have hi₂ := TensorProduct.map_injective_of_flat_flat _ _ hf hf
    have hi₃ := Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ hi₂
    refine ⟨comoduleOfFactor f ρ hi₃ hρ, hρ, ?_⟩
    intro σ hσ
    apply Comodule.ext
    ext m
    apply hi
    exact (LinearMap.congr_fun hσ m).trans (LinearMap.congr_fun hρ m).symm

/-- A coaction factoring through a coalgebra map corestricts to the original
comodule structure. The tensor map in corestriction is `f.toLinearMap.lTensor M`. -/
theorem corestrict_eq_of_factor (f : C →ₗc[R] D) (σ : Comodule R C M)
    (hσ : f.toLinearMap.lTensor M ∘ₗ σ.coact = coact (R := R) (C := D)) :
    (letI := σ; Corestrict f) = (inferInstance : Comodule R D M) := by
  apply Comodule.ext
  rw [corestrict_coact, corestrictCoact_eq_lTensor]
  exact hσ

end CoalgHom
