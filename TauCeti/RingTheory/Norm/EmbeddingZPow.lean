/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Weighted products of field norms over embeddings

For a finite separable extension L / K of fields and a separably closed field F with finitely
many ring homomorphisms from K and L, grouping the embeddings σ : L →+* F by their
restriction s = σ ∘ algebraMap K L : K →+* F identifies the fibre over s with L →ₐ[K] F
and rewrites a weighted product of norms as a weighted product over the embeddings of L:

`	ext
∏ s : K →+* F, s (Algebra.norm K x) ^ n s =
  ∏ σ : L →+* F, σ x ^ n (σ.comp (algebraMap K L)).
`

This is proved for both integer exponents (Algebra.prod_ringHom_norm_zpow) and natural-number
exponents (Algebra.prod_ringHom_norm_pow).

## Main results

* Algebra.prod_ringHom_norm_zpow: weighted product of s (Algebra.norm K x) ^ n s for
  
 : (K →+* F) → ℤ.
* Algebra.prod_ringHom_norm_pow: weighted product of s (Algebra.norm K x) ^ n s for
  
 : (K →+* F) → ℕ.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/ClassField/Avatar/HeckeBaseChange.lean (prod_norm_zpow).
-/

public section

namespace Algebra

private lemma algebraMap_norm_eq_prod_algHom
    {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsSepClosed F] (x : L) :
    algebraMap K F (Algebra.norm K x) = ∏ τ : L →ₐ[K] F, τ x := by
  have hsplits : ∀ y : L, ((minpoly K y).map (algebraMap K F)).Splits := fun y ↦
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K y)
  refine (algebraMap F (AlgebraicClosure F)).injective ?_
  rw [map_prod, ← IsScalarTower.algebraMap_apply K F (AlgebraicClosure F),
    Algebra.norm_eq_prod_embeddings (K := K) (L := L) (E := AlgebraicClosure F) x]
  refine (Fintype.prod_equiv
    (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (AlgebraicClosure F) F hsplits)
    _ _ fun τ ↦ ?_).symm
  exact (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply
    (AlgebraicClosure F) F hsplits τ x).symm

/-- For a finite separable extension L / K and a separably closed field F, the weighted product
of s (Algebra.norm K x) ^ n s over all ring homomorphisms s : K →+* F equals the product of
σ x ^ n (σ.comp (algebraMap K L)) over all ring homomorphisms σ : L →+* F. -/
theorem prod_ringHom_norm_zpow
    {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsSepClosed F]
    [Fintype (K →+* F)] [Fintype (L →+* F)]
    (x : L) (n : (K →+* F) → ℤ) :
    ∏ s : K →+* F, s (Algebra.norm K x) ^ n s =
      ∏ σ : L →+* F, σ x ^ n (σ.comp (algebraMap K L)) := by
  classical
  rw [← Fintype.prod_fiberwise fun σ : L →+* F ↦ σ.comp (algebraMap K L)]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  let _ : Algebra K F := s.toAlgebra
  let extensions : {σ : L →+* F // σ.comp (algebraMap K L) = s} ≃ (L →ₐ[K] F) :=
    { toFun σ := ⟨σ.val, RingHom.congr_fun σ.property⟩
      invFun τ := ⟨τ.toRingHom, τ.comp_algebraMap⟩ }
  have hnorm : s (Algebra.norm K x) = ∏ τ : L →ₐ[K] F, τ x :=
    algebraMap_norm_eq_prod_algHom x
  rw [hnorm, ← Finset.prod_zpow]
  exact (Fintype.prod_equiv extensions _ (fun τ ↦ τ x ^ n s)
    fun σ ↦ congrArg (fun t ↦ σ.val x ^ n t) σ.property).symm

/-- For a finite separable extension L / K and a separably closed field F, the weighted product
of s (Algebra.norm K x) ^ n s over all ring homomorphisms s : K →+* F equals the product of
σ x ^ n (σ.comp (algebraMap K L)) over all ring homomorphisms σ : L →+* F, for natural-number
exponents. -/
theorem prod_ringHom_norm_pow
    {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsSepClosed F]
    [Fintype (K →+* F)] [Fintype (L →+* F)]
    (x : L) (n : (K →+* F) → ℕ) :
    ∏ s : K →+* F, s (Algebra.norm K x) ^ n s =
      ∏ σ : L →+* F, σ x ^ n (σ.comp (algebraMap K L)) := by
  simpa only [zpow_natCast] using prod_ringHom_norm_zpow x (fun s ↦ (n s : ℤ))

end Algebra
