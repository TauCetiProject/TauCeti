/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.LinearAlgebra.Submodule.Quotient
public import TauCeti.RingTheory.AdicCompletion.AlgHom

import TauCeti.RingTheory.AdicCompletion.Exactness

/-!
# Module adic completion vs. completion along an extended ideal

Let `S` be a commutative `R`-algebra, `I` an ideal of `R`, and `M` an `S`-module with
`[IsScalarTower R S M]`. Since `I ^ n • (⊤ : Submodule R M)` and
`(I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)` agree as `R`-submodules
(`Submodule.restrictScalars_map_smul_eq`), `AdicCompletion I M` and
`AdicCompletion (I.map (algebraMap R S)) M` are canonically `R`-linearly isomorphic without
Noetherian or finite-generation hypotheses. This bridges module-level exactness with
`AdicCompletion.mapₐ`, yielding Artin–Rees injectivity `AdicCompletion.mapₐ_ofId_injective`.

## Main definitions and results

* `AdicCompletion.mapAlgebraMapLinearEquiv`: `AdicCompletion I M ≃ₗ[R] AdicCompletion (I S) M`,
  characterized on arbitrary coordinates by `val_mapAlgebraMapLinearEquiv` and
  `val_mapAlgebraMapLinearEquiv_symm`, on Cauchy sequences by `val_mapAlgebraMapLinearEquiv_mk`
  and `val_mapAlgebraMapLinearEquiv_symm_mk`, and on `AdicCompletion.of` by
  `mapAlgebraMapLinearEquiv_of` and `mapAlgebraMapLinearEquiv_symm_of`.
* `AdicCompletion.mapAlgebraMapLinearEquiv_map_restrictScalars`,
  `AdicCompletion.mapAlgebraMapLinearEquiv_map_algebraLinearMap`, and
  `AdicCompletion.mapAlgebraMapLinearEquiv_map_algHom`: naturality for `S`-linear maps,
  `Algebra.linearMap R S`, and `R`-algebra homomorphisms.
* `AdicCompletion.mapₐ_ofId_injective`: injectivity of `AdicCompletion.mapₐ (Algebra.ofId R S)` for
  a module-finite faithful extension `S` of a Noetherian ring `R`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 6.
* H. Matsumura, *Commutative Ring Theory*, §8.
-/

public section

namespace AdicCompletion

section Module

variable {R : Type*} [CommRing R] (I : Ideal R) (S M : Type*) [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Completing an `S`-module `M` as an `R`-module along `I` is canonically `R`-linearly isomorphic
to completing `M` as an `S`-module along the extended ideal `I.map (algebraMap R S)`. -/
noncomputable def mapAlgebraMapLinearEquiv :
    AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M :=
  let e (n : ℕ) :=
    Submodule.quotEquivOfEqRestrictScalars (I ^ n • ⊤ : Submodule R M)
      ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)
      (by rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
        Submodule.restrictScalars_top])
  { toFun := fun x ↦ ⟨fun n ↦ e n (x.val n), fun {m n} hmn ↦ by
      dsimp only
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
      have hx : x.val m = transitionMap I M hmn (x.val n) := (x.property hmn).symm
      simp [e, hx, ← ha]⟩
    invFun := fun y ↦ ⟨fun n ↦ (e n).symm (y.val n), fun {m n} hmn ↦ by
      dsimp only
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
      have hy : y.val m = transitionMap (I.map (algebraMap R S)) M hmn (y.val n) :=
        (y.property hmn).symm
      simp [e, hy, ← ha]⟩
    map_add' := fun x y ↦ ext fun n ↦ map_add (e n) (x.val n) (y.val n)
    map_smul' := fun r x ↦ ext fun n ↦ map_smul (e n) r (x.val n)
    left_inv := fun x ↦ ext fun n ↦ (e n).symm_apply_apply (x.val n)
    right_inv := fun y ↦ ext fun n ↦ (e n).apply_symm_apply (y.val n) }

/-- The `n`-th coordinate of `mapAlgebraMapLinearEquiv I S M x` transports `x.val n` along
`Submodule.quotEquivOfEqRestrictScalars`. -/
@[simp] theorem val_mapAlgebraMapLinearEquiv (x : AdicCompletion I M) (n : ℕ) :
    (mapAlgebraMapLinearEquiv I S M x).val n =
      Submodule.quotEquivOfEqRestrictScalars (I ^ n • ⊤ : Submodule R M)
        ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)
        (by rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
          Submodule.restrictScalars_top]) (x.val n) :=
  (rfl)

/-- The `n`-th coordinate of `(mapAlgebraMapLinearEquiv I S M).symm y` transports `y.val n`
backward along `Submodule.quotEquivOfEqRestrictScalars`. -/
@[simp] theorem val_mapAlgebraMapLinearEquiv_symm
    (y : AdicCompletion (I.map (algebraMap R S)) M) (n : ℕ) :
    ((mapAlgebraMapLinearEquiv I S M).symm y).val n =
      (Submodule.quotEquivOfEqRestrictScalars (I ^ n • ⊤ : Submodule R M)
        ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)
        (by rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
          Submodule.restrictScalars_top])).symm (y.val n) :=
  (rfl)

/-- On a Cauchy sequence `c`, the `n`-th coordinate of `mapAlgebraMapLinearEquiv I S M (mk I M c)`
is the class of `c n` modulo `(I.map (algebraMap R S)) ^ n • ⊤`. -/
theorem val_mapAlgebraMapLinearEquiv_mk (c : AdicCauchySequence I M) (n : ℕ) :
    (mapAlgebraMapLinearEquiv I S M (mk I M c)).val n = Submodule.Quotient.mk (c n) := by
  simp

/-- On a Cauchy sequence `c`, the `n`-th coordinate of
`(mapAlgebraMapLinearEquiv I S M).symm (mk (I.map (algebraMap R S)) M c)` is `c n` mod `I ^ n • ⊤`.
-/
theorem val_mapAlgebraMapLinearEquiv_symm_mk
    (c : AdicCauchySequence (I.map (algebraMap R S)) M) (n : ℕ) :
    ((mapAlgebraMapLinearEquiv I S M).symm (mk (I.map (algebraMap R S)) M c)).val n =
      Submodule.Quotient.mk (c n) := by
  simp

/-- `mapAlgebraMapLinearEquiv` commutes with `AdicCompletion.of`. -/
@[simp] theorem mapAlgebraMapLinearEquiv_of (m : M) :
    mapAlgebraMapLinearEquiv I S M (of I M m) = of (I.map (algebraMap R S)) M m :=
  ext fun _ ↦ by simp

/-- The inverse of `mapAlgebraMapLinearEquiv` commutes with `AdicCompletion.of`. -/
@[simp] theorem mapAlgebraMapLinearEquiv_symm_of (m : M) :
    (mapAlgebraMapLinearEquiv I S M).symm (of (I.map (algebraMap R S)) M m) = of I M m :=
  ext fun _ ↦ by simp

/-- `mapAlgebraMapLinearEquiv` commutes with completions of `S`-linear maps. -/
theorem mapAlgebraMapLinearEquiv_map_restrictScalars {N : Type*} [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N) (x : AdicCompletion I M) :
    mapAlgebraMapLinearEquiv I S N (map I (f.restrictScalars R) x) =
      map (I.map (algebraMap R S)) f (mapAlgebraMapLinearEquiv I S M x) := by
  refine ext fun n ↦ ?_
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  simp [← hm]

end Module

section Algebra

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
  (I : Ideal R)

/-- On an `R`-algebra `S`, `mapAlgebraMapLinearEquiv` intertwines the module-level completion of
`Algebra.linearMap R S` with `AdicCompletion.mapₐ (Algebra.ofId R S)`. -/
@[simp] theorem mapAlgebraMapLinearEquiv_map_algebraLinearMap (x : AdicCompletion I R) :
    mapAlgebraMapLinearEquiv I S S (map I (Algebra.linearMap R S) x) =
      mapₐ (Algebra.ofId R S)
        (fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap R S) hx)) x := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_mapₐ, ← factor_eval_eq_evalₐ _ _ ((Ideal.smul_eq_mul _ _).trans_le Ideal.mul_le_left),
    ← factor_eval_eq_evalₐ I x ((Ideal.smul_eq_mul _ _).trans_le Ideal.mul_le_left),
    eval_apply, eval_apply, val_mapAlgebraMapLinearEquiv, map_val_apply]
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  rw [← hr, LinearMap.reduceModIdeal_apply, Submodule.quotEquivOfEqRestrictScalars_mk,
    ← Submodule.mkQ_apply, Submodule.factor_mk, ← Submodule.mkQ_apply, Submodule.factor_mk]
  simp

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
  rw [evalₐ_mapₐ, ← factor_eval_eq_evalₐ _ _ ((Ideal.smul_eq_mul _ _).trans_le Ideal.mul_le_left),
    ← factor_eval_eq_evalₐ _ _ ((Ideal.smul_eq_mul _ _).trans_le Ideal.mul_le_left),
    eval_apply, eval_apply, val_mapAlgebraMapLinearEquiv, val_mapAlgebraMapLinearEquiv,
    map_val_apply]
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  rw [← hs, LinearMap.reduceModIdeal_apply, Submodule.quotEquivOfEqRestrictScalars_mk,
    Submodule.quotEquivOfEqRestrictScalars_mk]
  simp [Ideal.Quotient.factor_mk]

/-- For a module-finite faithful extension `S` of a Noetherian ring `R` and any ideal `I` of `R`,
`AdicCompletion I R →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S` is injective. -/
theorem mapₐ_ofId_injective [FaithfulSMul R S] [IsNoetherianRing R] [Module.Finite R S]
    (hle : I ≤ (I.map (algebraMap R S)).comap (Algebra.ofId R S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap R S) hx)) :
    Function.Injective (mapₐ (Algebra.ofId R S) hle) := by
  let f := Algebra.linearMap R S
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective R S
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  have hmap : Function.Injective (map I f) :=
    map_injective_of_comap_pow_smul_top_le (k := k) fun n r hr ↦ by
      rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R R),
        Submodule.map_smul'', Submodule.map_top]
      refine (smul_mono_right _ inf_le_right : I ^ n • (I ^ k • ⊤ ⊓ LinearMap.range f) ≤ _) ?_
      have hnk : I ^ (n + k) • ⊤ ⊓ LinearMap.range f = I ^ n • (I ^ k • ⊤ ⊓ LinearMap.range f) := by
        simpa only [Nat.add_sub_cancel] using hk (n + k) (Nat.le_add_left k n)
      exact hnk ▸ ⟨Submodule.mem_comap.mp hr, ⟨r, rfl⟩⟩
  have hcomp : ⇑(mapₐ (Algebra.ofId R S) hle) = ⇑(mapAlgebraMapLinearEquiv I S S) ∘ ⇑(map I f) :=
    funext fun x ↦ (mapAlgebraMapLinearEquiv_map_algebraLinearMap I x).symm
  exact hcomp ▸ (mapAlgebraMapLinearEquiv I S S).injective.comp hmap

end Algebra

end AdicCompletion
