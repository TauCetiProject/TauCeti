/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Data.Finsupp.Antidiagonal

/-!
# Disjoint copy embeddings for multivariate power series

Given a variable type X and a finite index type ι, TauCeti.copyEmbedding b : X ↪ X × ι
embeds the variables of one copy as the -th copy in X × ι. Given a family of multi-index
exponents α : ι → X →₀ ℕ, TauCeti.copyExponent α : X × ι →₀ ℕ assembles them into a single
multi-index whose restriction to copy  is α b. The main result
TauCeti.coeff_prod_rename_copyEmbedding shows that the coefficient at copyExponent α of a
product ∏ b, MvPowerSeries.rename (copyEmbedding b) (Ψ b) equals
∏ b, MvPowerSeries.coeff (α b) (Ψ b).

## Main definitions and results

* TauCeti.copyEmbedding: the embedding x ↦ (x, b) of X into X × ι.
* TauCeti.copyExponent: the multi-index ∑ b, (α b).embDomain (copyEmbedding b) on X × ι.
* TauCeti.copyEmbedding_apply: evaluation formula for copyEmbedding.
* TauCeti.copyExponent_apply: evaluating copyExponent α at (x, b) yields α b x.
* TauCeti.coeff_prod_rename_copyEmbedding: the coefficient at copyExponent α of a product of
  power series renamed into disjoint copies factors as the product of their coefficients.

## References

* Provenance: adapted from copyEmbedding, copyExponent, copyExponent_apply, and
  coeff_prod_rename_copyEmbedding in grh/src/New/Derivatives/Sharpness/BoundAttained.lean of
  grh-lean (https://github.com/lsernau/grh-lean, commit
  72fead102f663d5c7a407964a13dc0cf9d977207).
-/

@[expose] public section

namespace TauCeti

open Finset Finsupp MvPowerSeries

variable {X ι : Type*}

/-- The embedding of a variable set X as the -th copy in X × ι. -/
def copyEmbedding (b : ι) : X ↪ X × ι :=
  ⟨fun x ↦ (x, b), fun _ _ h ↦ (Prod.mk.inj h).left⟩

/-- Evaluation of copyEmbedding. -/
@[simp]
theorem copyEmbedding_apply (b : ι) (x : X) : copyEmbedding b x = (x, b) :=
  rfl

/-- The multi-index on X × ι whose component in copy  is α b. -/
noncomputable def copyExponent [Fintype ι] (α : ι → X →₀ ℕ) : X × ι →₀ ℕ :=
  ∑ b : ι, (α b).embDomain (copyEmbedding b)

/-- The component of copyExponent α in copy  at variable x is α b x. -/
@[simp]
theorem copyExponent_apply [Fintype ι] (α : ι → X →₀ ℕ) (x : X) (b : ι) :
    copyExponent α (x, b) = α b x := by
  classical
  rw [copyExponent, finsetSum_apply, sum_eq_single_of_mem b (mem_univ b)]
  · exact embDomain_apply_self (copyEmbedding b) (α b) x
  · exact fun b' _ hb' ↦ embDomain_of_notMem_range _ _ _ fun ⟨x', hx'⟩ ↦
      hb' (Prod.mk.inj hx').right

/-- The coefficient at copyExponent α of a product of multivariate power series renamed into
disjoint copies is the product of their coefficients at α b. -/
theorem coeff_prod_rename_copyEmbedding {R : Type*} [CommSemiring R] [Fintype ι]
    (α : ι → X →₀ ℕ) (Ψ : ι → MvPowerSeries X R) :
    coeff (copyExponent α) (∏ b : ι, rename (copyEmbedding b) (Ψ b)) =
      ∏ b : ι, coeff (α b) (Ψ b) := by
  classical
  let β₀ : ι →₀ X × ι →₀ ℕ :=
    equivFunOnFinite.symm fun b ↦ (α b).embDomain (copyEmbedding b)
  have hβ₀ : β₀ ∈ finsuppAntidiag univ (copyExponent α) :=
    mem_finsuppAntidiag.2 ⟨rfl, fun _ _ ↦ mem_univ _⟩
  rw [coeff_prod, sum_eq_single_of_mem β₀ hβ₀]
  · simp only [β₀, equivFunOnFinite_symm_apply_apply, coeff_embDomain_rename]
  intro β hβ h_ne
  by_contra h_prod
  have h_range (b : ι) : β b ∈ Set.range (mapDomain (copyEmbedding b)) :=
    by_contra fun hb ↦ h_prod (prod_eq_zero (mem_univ b) (coeff_rename_eq_zero _ _ hb))
  choose α' hα' using h_range
  have h_exponent : copyExponent α' = copyExponent α := by
    rw [copyExponent]
    simp only [embDomain_eq_mapDomain, hα']
    exact (mem_finsuppAntidiag.1 hβ).left
  have h_copy (b : ι) : α' b = α b := by
    ext x
    rw [← copyExponent_apply, h_exponent, copyExponent_apply]
  exact h_ne (Finsupp.ext fun b ↦ by
    rw [← hα' b, h_copy b, ← embDomain_eq_mapDomain]
    rfl)

end TauCeti
