/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.ComplexExtension
import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Extension
import TauCeti.RingTheory.Norm.Embeddings

/-!
# Weighted norms over a nonreal base embedding

For a base field with one infinite place, a nonreal embedding specifies which representative
of each infinite place upstairs to use. On a root of unity the weighted product of these
representatives depends only on the weights modulo the order of the root. When the weights
are all congruent, the product is the corresponding power of the relative norm.
-/

public section

namespace NumberField.ComplexEmbedding.Extension

open NumberField.InfinitePlace NumberField.ComplexEmbedding

/-- A weighted product of the representatives extending `σ`, with weights congruent
modulo an exponent killing `x`, is the corresponding power of the relative norm at `σ`. -/
theorem prod_equivInfinitePlace_symm_apply_zpow_eq_norm_zpow
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Subsingleton (InfinitePlace K)] {σ : K →+* ℂ} (hσ : ¬ IsReal σ)
    {x : L} {n : ℕ} (hx : x ^ n = 1) {weight : InfinitePlace L → ℤ} {a : ℤ}
    (hw : ∀ w, weight w ≡ a [ZMOD (n : ℤ)]) :
    (∏ᶠ w : InfinitePlace L, ((equivInfinitePlace hσ).symm w).val x ^ weight w) =
      σ (Algebra.norm K x) ^ a := by
  have : CharZero K := σ.charZero
  have : IsAlgClosed (Codomain σ) := Complex.isAlgClosed
  let e := (equivAlgHom L σ).symm.trans (equivInfinitePlace hσ)
  rw [← finprod_comp_equiv e, finprod_eq_prod_of_fintype]
  calc
    _ = ∏ f : L →ₐ[K] Codomain σ, Codomain.equiv σ (f x ^ weight (e f)) := by
      refine Finset.prod_congr rfl fun f _ ↦ ?_
      simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, equivAlgHom_symm_apply, map_zpow₀]
    _ = σ (Algebra.norm K x) ^ a := by
      rw [← map_prod, Algebra.prod_embeddings_zpow_eq_norm_zpow_of_modEq hx (fun f ↦ hw (e f)),
        Codomain.equiv_algebraMap, map_zpow₀]

end NumberField.ComplexEmbedding.Extension
