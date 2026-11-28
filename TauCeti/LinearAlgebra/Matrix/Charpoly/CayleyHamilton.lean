/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ

import TauCeti.Algebra.MvPolynomial.Coeff

/-!
# Cayley–Hamilton over commutative semirings

The positive-negative Cayley–Hamilton identity over a commutative semiring is obtained from the
universal characteristic polynomial by splitting its integer coefficients into natural-number
parts.

## Main results

* `Matrix.exists_pow_card_add_sum_eq_sum`: a positive-negative Cayley–Hamilton identity over a
  commutative semiring.
-/

public section

namespace Matrix

variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]

/-- Positive-negative Cayley–Hamilton identity over any commutative semiring, obtained by
splitting the integer coefficients of the universal characteristic polynomial and evaluating at
`A`. -/
theorem exists_pow_card_add_sum_eq_sum (A : Matrix n n R) :
    ∃ c₁ c₂ : Fin (Fintype.card n) → R,
      A ^ Fintype.card n + ∑ j : Fin (Fintype.card n), c₁ j • A ^ (j : ℕ) =
        ∑ j : Fin (Fintype.card n), c₂ j • A ^ (j : ℕ) := by
  let ι : MvPolynomial (n × n) ℕ →+* MvPolynomial (n × n) ℤ :=
    MvPolynomial.map (Nat.castRingHom ℤ)
  let M₀ := mvPolynomialX n n ℕ
  let M := mvPolynomialX n n ℤ
  have hM : ι.mapMatrix M₀ = M :=
    Matrix.ext fun i j => by simp [ι, M₀, M, mvPolynomialX_apply]
  choose p₁ p₂ hp using fun j : Fin (Fintype.card n) =>
    MvPolynomial.exists_map_nat_sub_map_nat_eq (M.charpoly.coeff j)
  have hCH : M ^ Fintype.card n + ∑ j : Fin (Fintype.card n), ι (p₁ j) • M ^ (j : ℕ) =
      ∑ j : Fin (Fintype.card n), ι (p₂ j) • M ^ (j : ℕ) := by
    have h0 := M.aeval_self_charpoly
    have hdeg : M.charpoly.natDegree < Fintype.card n + 1 := by
      rw [M.charpoly_natDegree_eq_dim]
      exact Nat.lt_succ_self _
    rw [Polynomial.aeval_eq_sum_range' hdeg, Finset.sum_range_succ,
      Matrix.charpoly.univ_coeff_card, one_smul, ← Fin.sum_univ_eq_sum_range] at h0
    have hsub : M ^ Fintype.card n +
        ∑ j : Fin (Fintype.card n), (ι (p₁ j) - ι (p₂ j)) • M ^ (j : ℕ) = 0 := by
      simpa only [ι, hp, add_comm] using h0
    simp only [sub_smul, Finset.sum_sub_distrib, ← add_sub_assoc] at hsub
    exact sub_eq_zero.1 hsub
  have hsmul_ι (a : MvPolynomial (n × n) ℕ) (X : Matrix n n (MvPolynomial (n × n) ℕ)) :
      ι.mapMatrix (a • X) = ι a • ι.mapMatrix X :=
    Matrix.ext fun i j => by simp [RingHom.mapMatrix_apply]
  have hnat : M₀ ^ Fintype.card n + ∑ j : Fin (Fintype.card n), p₁ j • M₀ ^ (j : ℕ) =
      ∑ j : Fin (Fintype.card n), p₂ j • M₀ ^ (j : ℕ) := by
    have hEq :
        ι.mapMatrix (M₀ ^ Fintype.card n +
          ∑ j : Fin (Fintype.card n), p₁ j • M₀ ^ (j : ℕ)) =
          ι.mapMatrix (∑ j : Fin (Fintype.card n), p₂ j • M₀ ^ (j : ℕ)) := by
      simpa only [map_add, map_sum, map_pow, hsmul_ι, hM] using hCH
    refine Matrix.ext fun i j =>
      MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using
      congrArg (fun X : Matrix n n _ => X i j) hEq
  let ev : MvPolynomial (n × n) ℕ →+* R :=
    MvPolynomial.eval₂Hom (Nat.castRingHom R) fun q => A q.1 q.2
  have hsmul_ev (a : MvPolynomial (n × n) ℕ) (X : Matrix n n (MvPolynomial (n × n) ℕ)) :
      ev.mapMatrix (a • X) = ev a • ev.mapMatrix X :=
    Matrix.ext fun i j => by simp [RingHom.mapMatrix_apply]
  refine ⟨fun j => ev (p₁ j), fun j => ev (p₂ j), ?_⟩
  have hev : ev.mapMatrix M₀ = A := mvPolynomialX_map_eval₂ _ A
  simpa only [map_add, map_sum, map_pow, hsmul_ev, hev] using congrArg ev.mapMatrix hnat

end Matrix
