/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.NormTwoShell.ChevalleyBasis
public import TauCeti.Algebra.Lie.Sl2.Straightening

/-!
# Opposite-root straightening in the signed shell Lie algebra

The inverse-lift normalization of the shell root vectors makes every pair of opposite roots,
not just the simple roots, an integral `sl₂` triple. Consequently their divided powers satisfy
the rank-one Kostant straightening formula under any Lie homomorphism into an associative
rational algebra. The Cartan binomial uses the actual coroot vector `H_a`; no sign from the
ordered cover remains in it. This supplies the opposite-root collection rule for integral
ordered monomials.

## Main results

* `Matrix.ShellLieAlgebra.isSl2Triple_normalizedRoot`: the normalized opposite-root triple.
* `Matrix.ShellLieAlgebra.dividedPower_normalizedRoot_mul_dividedPower_normalizedRoot_neg`:
  the integral opposite-root straightening identity in any associative rational algebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The normalization is that of `Matrix.ShellLieAlgebra.normalizedRoot`; the collection formula
  is `TauCeti.Sl2.dividedPower_e_mul_dividedPower_f`.
-/

public section

namespace Matrix.ShellLieAlgebra

open TauCeti.Associative

attribute [local instance] TauCeti.moduleNNRat

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
    (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0)

include hoff

/-- Each normalized opposite-root pair and its coroot form an integral `sl₂` triple. -/
theorem isSl2Triple_normalizedRoot (a : B.normTwoShell) :
    letI := lieRing hB hev
    IsSl2Triple (cartan B a) (normalizedRoot B a)
      (normalizedRoot B ⟨-(a : I → ℤ), neg_mem_normTwoShell.mpr a.2⟩) := by
  let _ := lieRing hB hev
  refine
    { h_ne_zero := ?_
      lie_e_f := normalizedRoot_lie_normalizedRoot_of_add_eq_zero hB hev hoff
        (add_neg_cancel _)
      lie_h_e_nsmul := ?_
      lie_h_f_nsmul := ?_ }
  · intro h
    have hz := congrArg (fun x ↦ (equivProd B x).1) h
    exact ne_zero_of_mem_normTwoShell a.2 (by simpa using hz)
  · rw [cartan_lie_normalizedRoot, mem_normTwoShell.mp a.2]
    simp only [two_smul]
  · rw [cartan_lie_normalizedRoot, mulVec_neg, dotProduct_neg,
      mem_normTwoShell.mp a.2, neg_smul]
    simp only [two_smul]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Opposite normalized root divided powers collect into lowering, Cartan-binomial, raising
order, with no extra sign. The identity holds under any integral Lie homomorphism into an
associative rational algebra, without nilpotence or injectivity hypotheses. -/
theorem dividedPower_normalizedRoot_mul_dividedPower_normalizedRoot_neg
    {A : Type*} [Ring A] [Algebra ℚ A]
    (φ : letI := lieRing hB hev; ShellLieAlgebra B →ₗ⁅ℤ⁆ A)
    (a : B.normTwoShell) (m n : ℕ) :
    dividedPower m (φ (normalizedRoot B a)) *
        dividedPower n (φ (normalizedRoot B
          ⟨-(a : I → ℤ), neg_mem_normTwoShell.mpr a.2⟩)) =
      ∑ k ∈ Finset.range (min m n + 1),
        dividedPower (n - k) (φ (normalizedRoot B
            ⟨-(a : I → ℤ), neg_mem_normTwoShell.mpr a.2⟩)) *
          Ring.choose (φ (cartan B a) - (m + n : ℕ) + (2 * k : ℕ)) k *
            dividedPower (m - k) (φ (normalizedRoot B a)) := by
  let _ := lieRing hB hev
  have ht := isSl2Triple_normalizedRoot hB hev hoff a
  exact φ.dividedPower_map_e_mul_dividedPower_map_f
    ht.lie_e_f ht.lie_h_e_nsmul ht.lie_h_f_nsmul m n

end Matrix.ShellLieAlgebra
