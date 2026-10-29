/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Polynomial.Factor
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Heights bound root multiplicities

A root `β` of multiplicity `m` of a polynomial `P` over a number field `K` contributes the
factor `(X - β) ^ m`, whose `m` linear factors each have coefficient height `H(β)`. Gelfond's
inequality bounds the product of the heights of the factors by the height of `P`, which gives

`m * h(β) ≤ h(P) + [K : ℚ] * deg P * log 2`

for relative logarithmic heights. Thus a polynomial of small height cannot vanish to high order
at a point of large height. In terms of indices: if `P ≠ 0`, `r ≥ deg P` and `r * h(β)` is at
least `s⁻¹ * (h(P) + [K : ℚ] * r * log 2)` for some `s > 0`, then the index of `P` at `β` with
weight `r` is at most `s`. This is Roth's lemma in one variable, the base case of the inductive
bound on indices of auxiliary polynomials in the proof of Roth's theorem.

## Main results

* `Polynomial.rootMultiplicity_mul_logHeight₁_le`: `m * h(β) ≤ h(P) + [K : ℚ] * deg P * log 2`.
* `MvPolynomial.weightedIndex_toMvPolynomial_le`: the index form of Roth's lemma in one variable,
  for a univariate polynomial placed in one coordinate.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.4, Lemma 3.4.3.
* The statement of the corresponding lemma in Ralf Stephan's
  `DiophantineApproximation/RothBaseCase.lean` in `rwst/Subspace-Theorems`, snapshot
  `c26d909dc48cf7fe` (Apache 2.0), was consulted for reference; the proof here is independent.
-/

public section

namespace Polynomial

open Height

variable {K : Type*} [Field K] [NumberField K]

/-- **Roth's lemma in one variable**, multiplicity form: the multiplicity of a root `β` of a
polynomial `P` over a number field, times the relative logarithmic height of `β`, is at most
`h(P) + [K : ℚ] * deg P * log 2`. The zero polynomial has root multiplicity zero. -/
theorem rootMultiplicity_mul_logHeight₁_le (P : K[X]) (β : K) :
    (P.rootMultiplicity β : ℝ) * logHeight₁ β ≤
      P.logHeight + Module.finrank ℚ K * P.natDegree * Real.log 2 := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  obtain ⟨R, hR⟩ := pow_rootMultiplicity_dvd P β
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hP (by simpa using hR)
  -- Apply Gelfond's inequality to the `m` linear factors `X - β` together with the cofactor.
  let f : Option (Fin (P.rootMultiplicity β)) → K[X] := fun i ↦ i.elim R fun _ ↦ X - C β
  have hf : ∀ i ∈ Finset.univ, f i ≠ 0 := by
    rintro (_ | _) - <;> simp [f, hR0, X_sub_C_ne_zero]
  have hprod : ∏ i, f i = P := by
    simp only [Fintype.prod_option, Option.elim_none, Option.elim_some, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, f]
    rw [mul_comm, ← hR]
  have h := sum_logHeight_le_logHeight_prod_add Finset.univ f hf
  rw [hprod, Fintype.sum_option] at h
  simp only [Option.elim_none, Option.elim_some, logHeight_X_sub_C, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, f] at h
  linarith [R.logHeight_nonneg]

end Polynomial

namespace MvPolynomial

open Polynomial Height

variable {K : Type*} [Field K] [NumberField K]

/-- **Roth's lemma in one variable**, index form. Let `P ≠ 0` be placed in the coordinate `i`,
with `deg P ≤ r i`. If `r i * h(a i) ≥ s⁻¹ * (h(P) + [K : ℚ] * r i * log 2)` for some `s > 0`,
then the index of `P` at `a` with weights `r` is at most `s`. Heights are relative. Replacing
`log 2` by a larger constant, such as Pottmeyer's `4`, only strengthens the hypothesis. -/
theorem weightedIndex_toMvPolynomial_le {σ : Type*} (r : σ → ℕ) (a : σ → K) (i : σ)
    {P : K[X]} (hP : P ≠ 0) (hr : P.natDegree ≤ r i) {s : ℝ} (hs : 0 < s)
    (h : s⁻¹ * (P.logHeight + Module.finrank ℚ K * r i * Real.log 2) ≤
      r i * logHeight₁ (a i)) :
    weightedIndex r a (P.toMvPolynomial i) ≤ ENNReal.ofReal s := by
  have hD : (0 : ℝ) < Module.finrank ℚ K := mod_cast Module.finrank_pos
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm : (P.rootMultiplicity (a i) : ℝ) * logHeight₁ (a i) ≤
      P.logHeight + Module.finrank ℚ K * r i * Real.log 2 := by
    refine (rootMultiplicity_mul_logHeight₁_le P (a i)).trans ?_
    gcongr
  have h' : P.logHeight + Module.finrank ℚ K * r i * Real.log 2 ≤
      s * (r i * logHeight₁ (a i)) := by
    rwa [inv_mul_le_iff₀ hs] at h
  have hmr : (P.rootMultiplicity (a i) : ℝ) ≤ s * r i := by
    rcases (zero_le_logHeight₁ (a i)).eq_or_lt with h0 | h0
    · -- A point of height zero forces `r i = 0`, so `P` is a nonzero constant.
      rw [← h0, mul_zero, mul_zero] at h'
      have hri : r i = 0 := by
        by_contra hne
        have hr0 : (0 : ℝ) < r i := mod_cast Nat.pos_of_ne_zero hne
        linarith [P.logHeight_nonneg, mul_pos (mul_pos hD hr0) hlog]
      have hdeg : P.natDegree = 0 := by omega
      rw [eq_C_of_natDegree_eq_zero hdeg, rootMultiplicity_C, hri]
      simp
    · nlinarith
  rw [weightedIndex_toMvPolynomial r a i hP]
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hs.le]
  exact ENNReal.ofReal_le_ofReal hmr

end MvPolynomial
