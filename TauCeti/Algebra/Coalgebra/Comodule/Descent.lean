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
    have hmap (z : M ⊗[R] C) :
        TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
            (TensorProduct.assoc R M C C (ρ.rTensor C z)) =
          TensorProduct.assoc R M D D
            ((coact (R := R) (C := D) (M := M)).rTensor D
              (f.toLinearMap.lTensor M z)) := by
      induction z using TensorProduct.inductionOn with
      | tmul m c =>
        simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
        rw [← LinearMap.congr_fun hρ m, LinearMap.comp_apply]
        induction ρ m using TensorProduct.inductionOn with
        | tmul x d => simp
        | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hcomul (z : M ⊗[R] C) :
        TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
            (Coalgebra.comul.lTensor M z) =
          Coalgebra.comul.lTensor M (f.toLinearMap.lTensor M z) := by
      induction z using TensorProduct.inductionOn with
      | tmul m c => simp [CoalgHomClass.map_comp_comul_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    ext m
    apply hi
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hm : f.toLinearMap.lTensor M (ρ m) = coact (R := R) (C := D) m :=
      LinearMap.congr_fun hρ m
    rw [hmap, hcomul, hm, coassoc_apply]
  lTensor_counit_comp_coact := by
    have hc : Coalgebra.counit.lTensor M ∘ₗ f.toLinearMap.lTensor M =
        (Coalgebra.counit (R := R) (A := C)).lTensor M := by
      ext m c
      simp
    rw [← hc, LinearMap.comp_assoc, hρ, lTensor_counit_comp_coact]

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

end CoalgHom
