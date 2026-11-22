/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp

/-!
# Reindexing products and sums over `Finset.finsuppAntidiag`

Products and sums over `Finset.finsuppAntidiag s n` agree with products and sums over
`Finset.piAntidiag s n` when the summand only reads the underlying function
(`Finset.prod_finsuppAntidiag_eq_prod_piAntidiag`, `Finset.sum_finsuppAntidiag_eq_sum_piAntidiag`).
-/

public section

namespace Finset

/-- Reindexing a product over `Finset.finsuppAntidiag s n` to `Finset.piAntidiag s n` via
coercion of finitely supported functions to ordinary functions. -/
@[to_additive /-- Reindexing a sum over `Finset.finsuppAntidiag s n` to `Finset.piAntidiag s n`
via coercion of finitely supported functions to ordinary functions. -/]
theorem prod_finsuppAntidiag_eq_prod_piAntidiag {ι μ M : Type*} [DecidableEq ι]
    [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] [CommMonoid M]
    (s : Finset ι) (n : μ) (g : (ι → μ) → M) :
    ∏ e ∈ finsuppAntidiag s n, g e = ∏ e ∈ piAntidiag s n, g e := by
  refine prod_bij (fun e _ ↦ (e : ι → μ)) (fun e he ↦ ?_)
    (fun _ _ _ _ h ↦ DFunLike.coe_injective h) (fun e he ↦ ?_) (fun _ _ ↦ rfl)
  · obtain ⟨hsum, hsupp⟩ := mem_finsuppAntidiag.mp he
    exact mem_piAntidiag.mpr ⟨hsum, fun i hi ↦ hsupp (Finsupp.mem_support_iff.mpr hi)⟩
  · obtain ⟨hsum, hsupp⟩ := mem_piAntidiag.mp he
    exact ⟨Finsupp.onFinset s e hsupp,
      mem_finsuppAntidiag.mpr ⟨hsum, Finsupp.support_onFinset_subset⟩, rfl⟩

end Finset
