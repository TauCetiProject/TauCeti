/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.HasseDerivBound
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde

/-!
# Entry bounds for confluent Vandermonde matrices

The row of the jet `⟨i, k⟩` of the confluent Vandermonde matrix with nodes `a` is the family
`j ↦ D^[k] (X ^ j) (a i)`, whose entries are bounded by `choose j k · ‖a i‖ ^ (j - k)` in
`TauCeti/Analysis/Polynomial/HasseDerivBound.lean`. This file turns node bounds into row bounds
on the entries of `Matrix.confluentVandermonde a m`, in the form consumed by row-dependent
determinant bounds.

## Main results

* `Matrix.norm_confluentVandermonde_le`: node bounds `‖a i‖ ≤ N i` and bounds `B ρ` on
  `choose j k · N i ^ (j - k)` over the exponents `j < ∑ i, m i` bound the entries of the row
  `ρ = finSigmaFinEquiv ⟨i, k⟩` of `Matrix.confluentVandermonde a m`.
-/

public section

namespace Matrix

variable {R : Type*} [SeminormedRing R] [NormOneClass R] {r : ℕ}

/-- The row bounds of a confluent Vandermonde matrix: if `‖a i‖ ≤ N i` for every node and `B ρ`
bounds `choose j k · N i ^ (j - k)` for every exponent `j < ∑ i, m i`, where
`ρ = finSigmaFinEquiv ⟨i, k⟩`, then `B ρ` bounds every entry of the row `ρ`. -/
theorem norm_confluentVandermonde_le {a : Fin r → R} {m : Fin r → ℕ} {N : Fin r → ℝ}
    (hN : ∀ i, ‖a i‖ ≤ N i) {B : Fin (∑ i, m i) → ℝ}
    (hB : ∀ i (k : Fin (m i)), ∀ j < ∑ i, m i,
      (j.choose k : ℝ) * N i ^ (j - k) ≤ B (finSigmaFinEquiv ⟨i, k⟩))
    (ρ j : Fin (∑ i, m i)) :
    ‖confluentVandermonde a m ρ j‖ ≤ B ρ := by
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [confluentVandermonde_apply, Equiv.symm_apply_apply]
  refine (Polynomial.norm_eval_hasseDeriv_X_pow_le k j (a i)).trans
    (le_trans ?_ (hB i k j j.isLt))
  gcongr
  exact hN i

end Matrix
