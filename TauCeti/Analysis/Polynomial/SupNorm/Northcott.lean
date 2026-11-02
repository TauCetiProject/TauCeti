/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Polynomial.Norm
import TauCeti.Algebra.Polynomial.Card.BoundedCoeff
import Mathlib.Order.CountableDenseLinearOrder

/-!
# Northcott's theorem for integer polynomials and the height gaps

The coefficient sup norm `Polynomial.supNorm` of an integer polynomial is its naive height.
Over `ℤ` only finitely many polynomials have bounded degree and bounded naive height
(`Polynomial.finite_setOf_natDegree_le_supNorm_le`). This fails over `ℚ`, where the constants
`1 / k` all have height at most `1`, and it fails without the degree bound, where the powers
of `X` all have height `1`.

Two consequences make Northcott's theorem usable in Diophantine approximation by algebraic
numbers, where solutions are integer polynomials `P` with `‖P ξ‖` small, or roots `α` with
`‖ξ - α‖` small, compared to a negative power of the height. Fix a degree bound `n` and a
height bound `B`. Then

* there is `δ > 0` such that every integer polynomial `P` of degree at most `n` with
  `0 < ‖P ξ‖ < δ` has naive height above `B`
  (`Polynomial.exists_pos_lt_supNorm_of_norm_aeval_lt`);
* there is `δ > 0` such that every nonzero integer polynomial `Q` of degree at most `n` with a
  root `α ≠ ξ` satisfying `‖ξ - α‖ < δ` has naive height above `B`
  (`Polynomial.exists_pos_lt_supNorm_of_norm_sub_root_lt`).

In both cases the finitely many polynomials of degree at most `n` and height at most `B` give
only finitely many nonzero values at `ξ`, respectively finitely many roots other than `ξ`, and
`δ` is chosen below all of their sizes. These height gaps are what lets an exponent defined by
infinitely many solutions of bounded degree be controlled through their heights.

The value gap holds for `ξ` in an arbitrary normed ring, and the root gap for `ξ` in a normed
commutative domain of characteristic zero, so the statements apply both to real approximation
by real algebraic numbers and to real or complex approximation by complex algebraic numbers.

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.6.

The statements are adapted from Ralf Stephan's `DiophantineApproximation/PolynomialSupNorm.lean`
in [`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/09835cb23557ae5ae0cf55a9c4ab9055f5d60338/DiophantineApproximation/PolynomialSupNorm.lean),
commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0). Here they are restated at the
normed-ring level, and the proofs reuse the bounded-coefficient finiteness of integer
polynomials.
-/

public section

namespace Polynomial

/-- **Northcott's theorem for integer polynomials.** Only finitely many integer polynomials
have degree at most `n` and coefficient sup norm (naive height) at most `B`. -/
theorem finite_setOf_natDegree_le_supNorm_le (n : ℕ) (B : ℝ) :
    {P : ℤ[X] | P.natDegree ≤ n ∧ P.supNorm ≤ B}.Finite := by
  refine (TauCeti.Polynomial.finite_setOf_natDegree_le_abs_intCoeff_le n ⌈B⌉₊).subset ?_
  rintro P ⟨hn, hB⟩
  refine ⟨hn, fun i ↦ ?_⟩
  have h : ((|P.coeff i| : ℤ) : ℝ) ≤ ⌈B⌉₊ := by
    simpa [Int.norm_eq_abs] using (P.le_supNorm i).trans (hB.trans (Nat.le_ceil B))
  exact_mod_cast h

/-- **The height gap for values.** For a degree bound `n` and a height bound `B` there is
`δ > 0` such that every integer polynomial `P` of degree at most `n` with `aeval ξ P ≠ 0` and
`‖aeval ξ P‖ < δ` has coefficient sup norm greater than `B`. -/
theorem exists_pos_lt_supNorm_of_norm_aeval_lt {A : Type*} [NormedRing A] (ξ : A) (n : ℕ)
    (B : ℝ) :
    ∃ δ > 0, ∀ P : ℤ[X], P.natDegree ≤ n → aeval ξ P ≠ 0 → ‖aeval ξ P‖ < δ →
      B < P.supNorm := by
  -- The finitely many polynomials of degree at most `n` and height at most `B` have finitely
  -- many nonzero values at `ξ`; `δ` is chosen below their norms.
  have hfin := ((finite_setOf_natDegree_le_supNorm_le n B).inter_of_left
    {P | aeval ξ P ≠ 0}).image fun P ↦ ‖aeval ξ P‖
  obtain ⟨δ, hδ0, hδ⟩ := Order.exists_between_finsets {0} hfin.toFinset (by
    simp only [Finset.mem_singleton, forall_eq]
    rintro _ hy
    obtain ⟨P, ⟨-, hP⟩, rfl⟩ := hfin.mem_toFinset.1 hy
    exact norm_pos_iff.2 hP)
  refine ⟨δ, hδ0 0 (Finset.mem_singleton_self 0), fun P hn hP hlt ↦ not_le.1 fun hB ↦ ?_⟩
  exact (hδ _ (hfin.mem_toFinset.2 ⟨P, ⟨⟨hn, hB⟩, hP⟩, rfl⟩)).not_gt hlt

/-- **The height gap for roots.** For a degree bound `n` and a height bound `B` there is
`δ > 0` such that every nonzero integer polynomial `Q` of degree at most `n` with a root
`α ≠ ξ` satisfying `‖ξ - α‖ < δ` has coefficient sup norm greater than `B`. -/
theorem exists_pos_lt_supNorm_of_norm_sub_root_lt {A : Type*} [NormedCommRing A] [IsDomain A]
    [CharZero A] (ξ : A) (n : ℕ) (B : ℝ) :
    ∃ δ > 0, ∀ (Q : ℤ[X]) (α : A), Q.natDegree ≤ n → Q ≠ 0 → aeval α Q = 0 → α ≠ ξ →
      ‖ξ - α‖ < δ → B < Q.supNorm := by
  classical
  -- The roots in `A` of the finitely many polynomials of degree at most `n` and height at most
  -- `B` form a finite set; `δ` is chosen below their distances to `ξ`.
  have hroots : (⋃ Q ∈ {Q : ℤ[X] | Q.natDegree ≤ n ∧ Q.supNorm ≤ B}, Q.rootSet A).Finite :=
    (finite_setOf_natDegree_le_supNorm_le n B).biUnion fun Q _ ↦ Q.rootSet_finite A
  have hfin := (hroots.inter_of_left {α | α ≠ ξ}).image fun α ↦ ‖ξ - α‖
  obtain ⟨δ, hδ0, hδ⟩ := Order.exists_between_finsets {0} hfin.toFinset (by
    simp only [Finset.mem_singleton, forall_eq]
    rintro _ hy
    obtain ⟨α, ⟨-, hα⟩, rfl⟩ := hfin.mem_toFinset.1 hy
    exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hα)))
  refine ⟨δ, hδ0 0 (Finset.mem_singleton_self 0), fun Q α hn hQ hα hαξ hlt ↦
    not_le.1 fun hB ↦ ?_⟩
  have hmem : α ∈ ⋃ Q ∈ {Q : ℤ[X] | Q.natDegree ≤ n ∧ Q.supNorm ≤ B}, Q.rootSet A :=
    Set.mem_biUnion (x := Q) ⟨hn, hB⟩ (mem_rootSet.2 ⟨hQ, hα⟩)
  exact (hδ _ (hfin.mem_toFinset.2 ⟨α, ⟨hmem, hαξ⟩, rfl⟩)).not_gt hlt

end Polynomial
