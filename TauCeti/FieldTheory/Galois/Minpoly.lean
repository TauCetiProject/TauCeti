/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# The minimal polynomial of a primitive element of a Galois extension

Let `L/K` be a finite Galois extension and let `x` generate `L` over `K`. The Galois group acts
freely on `x`, so the conjugates `σ x` for `σ ∈ Gal(L/K)` are exactly the roots of `minpoly K x`,
each once, and

`(minpoly K x).map (algebraMap K L) = ∏ σ : Gal(L/K), (X - C (σ x))`.

Differentiating and evaluating at `x` kills every summand with a factor `X - C x` and leaves

`(minpoly K x)' (x) = ∏_{σ ≠ 1} (x - σ x)`.

This is the form in which the derivative of the minimal polynomial enters the theory of the
different: for a Galois extension of local fields it expresses the different exponent as a sum
of valuations `v (σ x - x)` over the nontrivial automorphisms.

## Main results

* `TauCeti.minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top`: the minimal polynomial of a primitive
  element is, in `L[X]`, the product of `X - C (σ x)` over the Galois group.
* `TauCeti.aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top`: its derivative at `x` is the
  product of `x - σ x` over the nontrivial automorphisms.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6 and Chapter IV, §1.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The image in `L[X]` of the minimal polynomial of a primitive element `x` of a finite Galois
extension `L/K` is `∏ σ : Gal(L/K), (X - C (σ x))`. -/
theorem minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top {x : L} (hx : K⟮x⟯ = ⊤) :
    (minpoly K x).map (algebraMap K L) = ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) := by
  classical
  -- An automorphism is determined by its value at the generator `x`.
  have hinj : Function.Injective fun σ : L ≃ₐ[K] L ↦ σ x := fun σ τ h ↦
    AlgEquiv.coe_toAlgHom_injective <| AlgHom.ext_of_adjoin_eq_top
      ((adjoin_eq_top_iff_of_isAlgebraic fun y _ ↦ IsAlgebraic.of_finite K y).1 hx)
      (Set.eqOn_singleton.2 h)
  -- The conjugacy class of `x` is its Galois orbit.
  have hcarrier : (ConjRootClass.mk K x).carrier.toFinset =
      Finset.univ.image fun σ : L ≃ₐ[K] L ↦ σ x := by
    ext y
    simp [ConjRootClass.mem_carrier, isConjRoot_iff_exists_algEquiv]
  rw [← ConjRootClass.minpoly_mk, ConjRootClass.minpoly.map_eq_prod, hcarrier,
    Finset.prod_image fun σ _ τ _ h ↦ hinj h]

/-- The derivative of the minimal polynomial of a primitive element `x` of a finite Galois
extension, evaluated at `x`, is `∏_{σ ≠ 1} (x - σ x)`. -/
theorem aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top [DecidableEq (L ≃ₐ[K] L)] {x : L}
    (hx : K⟮x⟯ = ⊤) :
    aeval x (derivative (minpoly K x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - σ x) := by
  classical
  -- `x` is the root of the linear factor indexed by the identity automorphism.
  have hmem : x ∈ Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) Finset.univ.val :=
    Multiset.mem_map.2 ⟨1, Finset.mem_univ _, AlgEquiv.one_apply x⟩
  -- Erasing that root from the multiset of conjugates erases the identity from the index set.
  have herase : (Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) Finset.univ.val).erase x =
      Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) (Finset.univ.erase (1 : L ≃ₐ[K] L)).val := by
    rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ (Finset.mem_univ 1), AlgEquiv.one_apply]
  -- The product over the Galois group is the product of `X - C a` over the multiset of conjugates.
  have hprod : ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) =
      (Multiset.map (fun a : L ↦ X - C a)
        (Multiset.map (fun σ : L ≃ₐ[K] L ↦ σ x) Finset.univ.val)).prod := by
    rw [Multiset.map_map]; rfl
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map,
    minpoly_map_eq_prod_X_sub_C_of_adjoin_eq_top hx, hprod,
    eval_multiset_prod_X_sub_C_derivative hmem, herase, Multiset.map_map]
  rfl

end TauCeti
