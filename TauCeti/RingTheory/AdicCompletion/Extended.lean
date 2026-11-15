/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Module adic completion vs. completion along an extended ideal

Let `S` be a commutative `R`-algebra, `I` an ideal of `R`, and `M` an `S`-module with compatible
`R`-scalar action (`[IsScalarTower R S M]`). As `R`-submodules of `M`, the filtrations
`I ^ n • (⊤ : Submodule R M)` and `(I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)` coincide by
`Submodule.restrictScalars_map_smul_eq`. Passing to inverse limits identifies the module completion
`AdicCompletion I M` over `R` with the completion `AdicCompletion (I.map (algebraMap R S)) M` along
the extended ideal `I S`, without any Noetherian or finite-generation hypotheses.

This comparison bridges module-level exactness results (such as `AdicCompletion.map_injective` and
`AdicCompletion.map_exact` for `R`-linear maps completed along `I`) with ring-level functoriality
(`AdicCompletion.mapₐ` on `AdicCompletion (I.map (algebraMap R S)) S`).

## Main definitions and results

* `AdicCompletion.mapAlgebraMapLinearEquiv`: the canonical `R`-linear isomorphism
  `AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M`.
* `AdicCompletion.mapAlgebraMapLinearEquiv_of` and
  `AdicCompletion.mapAlgebraMapLinearEquiv_symm_of`: compatibility with `AdicCompletion.of`.
* `AdicCompletion.mapAlgebraMapLinearEquiv_map_restrictScalars`: naturality for `S`-linear maps.
* `AdicCompletion.mapAlgebraMapLinearEquiv_map_algebraLinearMap`: for `M = S`, intertwines
  `AdicCompletion.map I (Algebra.linearMap R S)` with `AdicCompletion.mapₐ (Algebra.ofId R S)`.
* `AdicCompletion.mapAlgebraMapLinearEquiv_map_algHom`: for `f : S →ₐ[R] S'`, intertwines
  `AdicCompletion.map I f.toLinearMap` with `AdicCompletion.mapₐ f`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 8.7.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 10.13.
-/

public section

namespace AdicCompletion

section Module

variable {R : Type*} [CommRing R] (I : Ideal R) (S M : Type*) [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

private theorem pow_smul_top_eq_restrictScalars_map_pow (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) =
      (((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)).restrictScalars R) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
  rfl

private noncomputable def quotLevelEquiv (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_restrictScalars_map_pow I S M n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

private theorem transitionMap_quotLevelEquiv {m n : ℕ} (hmn : m ≤ n)
    (q : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    transitionMap (I.map (algebraMap R S)) M hmn (quotLevelEquiv I S M n q) =
      quotLevelEquiv I S M m (transitionMap I M hmn q) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q; rfl

private theorem transitionMap_quotLevelEquiv_symm {m n : ℕ} (hmn : m ≤ n)
    (q : M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :
    transitionMap I M hmn ((quotLevelEquiv I S M n).symm q) =
      (quotLevelEquiv I S M m).symm (transitionMap (I.map (algebraMap R S)) M hmn q) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q; rfl

/-- Completing an `S`-module `M` as an `R`-module along `I` is canonically `R`-linearly isomorphic
to completing `M` as an `S`-module along the extended ideal `I.map (algebraMap R S)`. -/
noncomputable def mapAlgebraMapLinearEquiv :
    AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M :=
  LinearEquiv.ofLinearMap
    { toFun := fun x ↦ ⟨fun n ↦ quotLevelEquiv I S M n (x.val n),
        fun hmn ↦ by rw [transitionMap_quotLevelEquiv, x.property hmn]⟩
      map_add' := fun x y ↦ ext fun n ↦ map_add (quotLevelEquiv I S M n) (x.val n) (y.val n)
      map_smul' := fun r x ↦ ext fun n ↦ by
        simp only [RingHom.id_apply, val_smul_apply]
        exact map_smul (quotLevelEquiv I S M n) r (x.val n) }
    { toFun := fun y ↦ ⟨fun n ↦ (quotLevelEquiv I S M n).symm (y.val n),
        fun hmn ↦ by rw [transitionMap_quotLevelEquiv_symm, y.property hmn]⟩
      map_add' := fun x y ↦ ext fun n ↦ map_add (quotLevelEquiv I S M n).symm (x.val n) (y.val n)
      map_smul' := fun r x ↦ ext fun n ↦ by
        simp only [RingHom.id_apply, val_smul_apply]
        exact map_smul (quotLevelEquiv I S M n).symm r (x.val n) }
    (LinearMap.ext fun y ↦ ext fun n ↦ (quotLevelEquiv I S M n).apply_symm_apply (y.val n))
    (LinearMap.ext fun x ↦ ext fun n ↦ (quotLevelEquiv I S M n).symm_apply_apply (x.val n))

private theorem val_mapAlgebraMapLinearEquiv (n : ℕ) (x : AdicCompletion I M) :
    (mapAlgebraMapLinearEquiv I S M x).val n = quotLevelEquiv I S M n (x.val n) :=
  rfl

/-- `mapAlgebraMapLinearEquiv` commutes with `AdicCompletion.of`. -/
@[simp]
theorem mapAlgebraMapLinearEquiv_of (m : M) :
    mapAlgebraMapLinearEquiv I S M (of I M m) = of (I.map (algebraMap R S)) M m :=
  ext fun _ ↦ rfl

/-- The inverse of `mapAlgebraMapLinearEquiv` commutes with `AdicCompletion.of`. -/
@[simp]
theorem mapAlgebraMapLinearEquiv_symm_of (m : M) :
    (mapAlgebraMapLinearEquiv I S M).symm (of (I.map (algebraMap R S)) M m) = of I M m :=
  ext fun _ ↦ rfl

/-- `mapAlgebraMapLinearEquiv` commutes with completions of `S`-linear maps. -/
theorem mapAlgebraMapLinearEquiv_map_restrictScalars {N : Type*} [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N) (x : AdicCompletion I M) :
    mapAlgebraMapLinearEquiv I S N (map I (f.restrictScalars R) x) =
      map (I.map (algebraMap R S)) f (mapAlgebraMapLinearEquiv I S M x) := by
  refine ext fun n ↦ ?_
  rw [val_mapAlgebraMapLinearEquiv, map_val_apply, map_val_apply, val_mapAlgebraMapLinearEquiv]
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x.val n); rw [← hm]; rfl

end Module

section Algebra

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
  (I : Ideal R)

/-- On an `R`-algebra `S`, `mapAlgebraMapLinearEquiv` intertwines the module-level completion of
`Algebra.linearMap R S` with `AdicCompletion.mapₐ (Algebra.ofId R S)`. -/
@[simp]
theorem mapAlgebraMapLinearEquiv_map_algebraLinearMap
    (hle : I ≤ (I.map (algebraMap R S)).comap (Algebra.ofId R S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))
    (x : AdicCompletion I R) :
    mapAlgebraMapLinearEquiv I S S (map I (Algebra.linearMap R S) x) =
      mapₐ (Algebra.ofId R S) hle x := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_mapₐ, ← factor_eval_eq_evalₐ _ _ (le_of_eq (Ideal.mul_top _)),
    ← factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _)), eval_apply, eval_apply,
    val_mapAlgebraMapLinearEquiv, map_val_apply]
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val n); rw [← hr]; rfl

/-- An `R`-algebra homomorphism `f : S →ₐ[R] S'` maps `I.map (algebraMap R S)` into
`I.map (algebraMap R S')`, and `mapAlgebraMapLinearEquiv` intertwines `map I f.toLinearMap` with
`mapₐ f`. -/
theorem mapAlgebraMapLinearEquiv_map_algHom (f : S →ₐ[R] S')
    (hf : I.map (algebraMap R S) ≤ (I.map (algebraMap R S')).comap f :=
      Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Ideal.mem_comap.mpr
        (Ideal.mem_comap.mpr ((f.commutes r).symm ▸ Ideal.mem_map_of_mem (algebraMap R S') hr)))
    (x : AdicCompletion I S) :
    mapAlgebraMapLinearEquiv I S' S' (map I f.toLinearMap x) =
      mapₐ f hf (mapAlgebraMapLinearEquiv I S S x) := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_mapₐ, ← factor_eval_eq_evalₐ _ _ (le_of_eq (Ideal.mul_top _)),
    ← factor_eval_eq_evalₐ _ _ (le_of_eq (Ideal.mul_top _)), eval_apply, eval_apply,
    val_mapAlgebraMapLinearEquiv, val_mapAlgebraMapLinearEquiv, map_val_apply]
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x.val n); rw [← hs]; rfl

end Algebra

end AdicCompletion
