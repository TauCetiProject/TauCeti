/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Basic
public import TauCeti.RingTheory.MvPolynomial.BlockHomogenize

/-!
# Euclidean coefficient height of block homogenizations

Block homogenization within the prescribed degree bounds preserves the Euclidean height of
coefficients. The coefficient vectors are indexed by their nonzero supports: homogenization
only reindexes these coordinates, without repeating or combining them. This permits affine
auxiliary polynomials to be homogenized without changing their Euclidean coefficient-height
bounds.

The equality includes the zero polynomial, whose empty coefficient vector has Euclidean
height zero. No finiteness assumption on the affine variable type is needed.

## References

* J.-H. Evertse, *An explicit version of Faltings' Product Theorem and an improvement of Roth's
  lemma*, Acta Arith. 73 (1995), §1.
-/

public section

namespace MvPolynomial

variable {K B S : Type*} [Field K] [NumberField K] [Fintype B]

/-- Block homogenization preserves the Euclidean height of the coefficient vector when every
supported monomial lies within the block degree bounds. Both coefficient vectors are indexed
by their nonzero supports; the assertion also holds for the zero polynomial. -/
@[simp]
theorem height2_blockHomogenize (b : S → B) (d : B → ℕ) (f : MvPolynomial S K)
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) :
    TauCeti.height2 (fun e : (blockHomogenize b d f).support ↦
      (blockHomogenize b d f).coeff e) =
        TauCeti.height2 (fun e : f.support ↦ f.coeff e) := by
  classical
  let emb : (S →₀ ℕ) ↪ (B ⊕ S →₀ ℕ) :=
    ⟨blockHomogenizeExponent b d, blockHomogenizeExponent_injective b d⟩
  let e : f.support ≃ (blockHomogenize b d f).support :=
    (Finset.equivMap emb f.support).trans
      (Equiv.subtypeEquivRight fun u ↦ by rw [support_blockHomogenize b d hf])
  have hcoeff : (fun u : (blockHomogenize b d f).support ↦
      (blockHomogenize b d f).coeff u) ∘ e = fun u : f.support ↦ f.coeff u := by
    funext u
    exact coeff_blockHomogenizeExponent_blockHomogenize b d f (hf u u.property)
  rw [← hcoeff, TauCeti.height2_comp_equiv]

end MvPolynomial
