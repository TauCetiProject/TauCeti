/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AlgebraTower

/-!
# Sums over the embeddings of a separable extension

Let `L / K` be a finite separable extension, `E` an algebraically closed field over `K`, and
`x ∈ L`. As `σ` runs over the `K`-embeddings `L →ₐ[K] E`, the value `σ x` runs over the roots of
the minimal polynomial of `x` in `E`, each root being hit by exactly `[L : K⟮x⟯]` embeddings.
Hence for every function `f : E → M` into an additive commutative monoid,
`∑ σ, f (σ x) = [L : K⟮x⟯] • ∑_{y root of minpoly K x} f y`.

This generalizes Mathlib's `sum_embeddings_eq_finrank_mul`, which is the case `f = id` (stated for
a power basis). With `f = (‖·‖ ^ 2)` and `E = ℂ` it computes the `T₂` norm of an algebraic number
from the roots of its minimal polynomial.

## Main results

* `TauCeti.sum_algHom_apply_eq_finrank_nsmul_sum_map_aroots`: the formula above.
-/

public section

open Module IntermediateField Polynomial

namespace TauCeti

variable {K L E M : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
  [AddCommMonoid M]

/-- For `x` separable over `K`, summing `f` over the images of the generator of `K⟮x⟯` under its
`K`-embeddings into `E` is summing `f` over the roots of `minpoly K x` in `E`. -/
theorem sum_algHom_adjoin_apply_gen_eq_sum_map_aroots {x : L} (hsep : IsSeparable K x)
    [Fintype (K⟮x⟯ →ₐ[K] E)] (f : E → M) :
    ∑ σ : K⟮x⟯ →ₐ[K] E, f (σ (AdjoinSimple.gen K x)) = (((minpoly K x).aroots E).map f).sum := by
  classical
  have hx := hsep.isIntegral
  have hnodup : ((minpoly K x).aroots E).Nodup := nodup_roots ((separable_map _).mpr hsep)
  rw [Fintype.sum_equiv (algHomAdjoinIntegralEquiv K hx) _ (fun y => f y.val)
    (fun σ => by rw [← algHomAdjoinIntegralEquiv_symm_apply_gen K hx, Equiv.symm_apply_apply]),
    Finset.sum_mem_multiset, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnodup]
  exact fun _ => rfl

/-- **Sums over embeddings.** If `L / K` is finite separable and `E` is algebraically closed,
then for every `x : L` and every `f : E → M`, the sum of `f (σ x)` over the `K`-embeddings
`σ : L →ₐ[K] E` is `[L : K⟮x⟯]` times the sum of `f` over the roots of `minpoly K x` in `E`, with
multiplicity.

The proof adapts Mathlib's proof of `sum_embeddings_eq_finrank_mul`
(`Mathlib/RingTheory/Trace/Basic.lean`). -/
theorem sum_algHom_apply_eq_finrank_nsmul_sum_map_aroots [IsAlgClosed E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (f : E → M) (x : L) :
    ∑ σ : L →ₐ[K] E, f (σ x) = finrank K⟮x⟯ L • (((minpoly K x).aroots E).map f).sum := by
  have : Algebra.IsSeparable K⟮x⟯ L := Algebra.isSeparable_tower_top_of_isSeparable K K⟮x⟯ L
  -- Split an embedding of `L` into its restriction `τ` to `K⟮x⟯` (which sends the generator to
  -- `σ x` by definition) and an extension of `τ` to `L`; there are `[L : K⟮x⟯]` extensions.
  rw [← sum_algHom_adjoin_apply_gen_eq_sum_map_aroots (Algebra.IsSeparable.isSeparable K x),
    Fintype.sum_equiv algHomEquivSigma (fun σ : L →ₐ[K] E => f (σ x))
      (fun σ => f (σ.fst (AdjoinSimple.gen K x))) (fun _ => rfl),
    ← Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  let : Algebra K⟮x⟯ E := σ.toRingHom.toAlgebra
  simp_rw [Finset.sum_const, Finset.card_univ, ← AlgHom.card K⟮x⟯ L E]

end TauCeti
