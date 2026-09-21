/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.InformationTheory.Coding.EuclideanDual

/-!
# Character sums over linear codes

Let `ψ` be a primitive additive character of a finite commutative ring `R`, with values in a
domain. For a linear code `C ≤ ι → R`, the character `c ↦ ψ (c ⬝ᵥ y)` of `C` is trivial exactly
when `y` lies in the Euclidean dual of `C`, so

  `∑ c ∈ C, ψ (c ⬝ᵥ y) = if y ∈ C⊥ then #C else 0`.

Summing this orthogonality relation against an arbitrary function `f` on words gives the
Poisson summation formula for the finite Fourier transform `f̂ x = ∑ y, ψ (x ⬝ᵥ y) • f y`:

  `∑ c ∈ C, f̂ c = #C • ∑ y ∈ C⊥, f y`.

This is the analytic input of the MacWilliams identity; it is stated for an arbitrary
`f` with values in a module over the target of `ψ` so that it applies to polynomial-valued
weight monomials. Every finite field carries a primitive character with values in a field of
characteristic zero (`AddChar.FiniteField.primitiveChar`), and so does every `ZMod m`
(`AddChar.primitiveZModChar`).

## Main statements

* `Submodule.sum_addChar_dotProduct`: the orthogonality relation for a code and its dual.
* `Submodule.sum_sum_addChar_dotProduct_smul`: the Poisson summation formula.

## References

F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*, North-Holland
(1977), Chapter 5, §2, Lemmas 2 and 11; W. C. Huffman and V. Pless, *Fundamentals of
Error-Correcting Codes*, Cambridge University Press (2003), §7.2.
-/

public section

open Finset

namespace Submodule

variable {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S] [IsDomain S]
  {ψ : AddChar R S} {C : Submodule R (ι → R)}

/-- The orthogonality relation for a linear code and its Euclidean dual: summing a primitive
additive character over the values `c ⬝ᵥ y`, `c ∈ C`, gives `#C` when `y` is dual to `C` and
zero otherwise. -/
theorem sum_addChar_dotProduct [Fintype C] [DecidablePred (· ∈ euclideanDual C)]
    (hψ : ψ.IsPrimitive) (y : ι → R) :
    ∑ c : C, ψ ((c : ι → R) ⬝ᵥ y) = if y ∈ euclideanDual C then (Fintype.card C : S) else 0 := by
  split_ifs with hy
  · simp [mem_euclideanDual.mp hy _ (Subtype.prop _)]
  · obtain ⟨x, hx, hxy⟩ : ∃ x ∈ C, x ⬝ᵥ y ≠ 0 := by simpa using hy
    -- The character `c ↦ ψ (c ⬝ᵥ y)` of the finite group `C` is nontrivial.
    let φ : AddChar C S := ψ.compAddMonoidHom
      { toFun := fun c ↦ (c : ι → R) ⬝ᵥ y
        map_zero' := by simp
        map_add' := fun _ _ ↦ by simp [add_dotProduct] }
    obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp (hψ hxy)
    refine AddChar.sum_eq_zero_of_ne_one (ψ := φ)
      (AddChar.ne_one_iff.mpr ⟨⟨t • x, C.smul_mem t hx⟩, ?_⟩)
    simpa [φ, smul_dotProduct, mul_comm] using ht

/-- The Poisson summation formula for a linear code: the finite Fourier transform
`f̂ x = ∑ y, ψ (x ⬝ᵥ y) • f y` of a function on words, summed over the code `C`, is `#C` times
the sum of `f` over the Euclidean dual of `C`. -/
theorem sum_sum_addChar_dotProduct_smul [DecidableEq ι] [Fintype R] [Fintype C]
    [Fintype (euclideanDual C)] {M : Type*} [AddCommMonoid M] [Module S M] (hψ : ψ.IsPrimitive)
    (f : (ι → R) → M) :
    ∑ c : C, ∑ y, ψ ((c : ι → R) ⬝ᵥ y) • f y =
      Fintype.card C • ∑ y : euclideanDual C, f (y : ι → R) := by
  classical
  rw [sum_comm]
  simp_rw [← sum_smul, sum_addChar_dotProduct hψ, ite_smul, zero_smul, Nat.cast_smul_eq_nsmul]
  rw [← sum_filter, sum_subtype _ fun y ↦ by rw [mem_filter, and_iff_right (mem_univ y)],
    smul_sum]

end Submodule
