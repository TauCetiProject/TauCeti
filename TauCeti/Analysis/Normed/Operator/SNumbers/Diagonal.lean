/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal

/-!
# s-numbers of diagonal operators

For `1 ≤ p ≤ ∞` and a bounded coefficient family `σ` with nonincreasing magnitudes, the diagonal
operator `D_σ = lp.diagonalCLM σ`, `(D_σ x)ᵢ = σᵢ xᵢ`, on the sequence space `ℓ^p` has the same
s-numbers for every strict s-number sequence: `sₙ(D_σ) = |σₙ|`. This holds on `ℓ^p(ℕ, 𝕜)` and on
the finite sequence spaces `ℓ_p^m = ℓ^p(Fin m, 𝕜)`, where moreover `sₙ(D_σ) = 0` for `n ≥ m`. The
operator norm `‖D_σ‖ = sup |σᵢ|` is `lp.norm_diagonalCLM`. For an s-number sequence that is not
strict, `|σₙ|` is still an upper bound.

The upper bound holds for every s-number sequence, since s-numbers are bounded by approximation
numbers and retaining the first `n` coordinates approximates `D_σ` within `|σₙ|`. For the lower
bound, `D_σ` has a left inverse of norm at most `|σₙ|⁻¹` on the span `M` of the first `n + 1`
coordinate vectors (`lp.exists_comp_diagonalCLM_comp_subtypeL_eq_id`). So the identity of `M`,
a space of rank `n + 1`, factors through `D_σ`, and strictness normalizes it at index `n`
(`TauCeti.SNumbers.IsStrictSNumberSequence.le_of_comp_eq_id`). The lower bound needs
strictness: the identity of `ℓ₁^m` is the diagonal operator with all coefficients `1`, and by
Grothendieck's inequality its Hilbert numbers at index `n` are at most a constant times
`(n + 1)^(-1/2)`, hence below `1` for large `n < m`.

The statements fix the index types `ℕ` and `Fin m`, which live in the lowest universe, so that the
sequence spaces lie in the universe of the scalar field, as `TauCeti.SNumbers.SNumberFamily`
requires.

## Main declarations

* `TauCeti.SNumbers.IsStrictSNumberSequence.apply_diagonalCLM`: `sₙ(D_σ) = |σₙ|` on `ℓ^p(ℕ, 𝕜)`.
* `TauCeti.SNumbers.IsStrictSNumberSequence.apply_diagonalCLM_fin`: `sₖ(D_σ) = |σₖ|` on
  `ℓ^p(Fin m, 𝕜)` for `k < m`.
* `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_le`,
  `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_fin_le`: the upper bound `sₙ(D_σ) ≤ |σₙ|`
  for every s-number sequence.
* `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_fin_of_le`: `sₙ(D_σ) = 0` on
  `ℓ^p(Fin m, 𝕜)` for `n ≥ m`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §7.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped lp ENNReal NNReal

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {s : SNumberFamily 𝕜}

namespace IsSNumberSequence

variable (hs : IsSNumberSequence s)
include hs

/-- Every s-number sequence of a diagonal operator on `ℓ^p(ℕ, 𝕜)` with nonincreasing
coefficient magnitudes is bounded by the magnitude of the coefficient of the same index. -/
theorem apply_diagonalCLM_le (d : ℓ^∞(ℕ, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    s (lp.diagonalCLM (p := p) d) n ≤ ‖d n‖₊ :=
  (hs.le_singularValue _ n).trans_eq (lp.singularValue_diagonalCLM d hd n)

/-- Every s-number sequence of a diagonal operator on `ℓ^p(Fin m, 𝕜)` with nonincreasing
coefficient magnitudes is bounded by the magnitude of the coefficient of the same index. -/
theorem apply_diagonalCLM_fin_le {m : ℕ} (d : ℓ^∞(Fin m, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖)
    (k : Fin m) : s (lp.diagonalCLM (p := p) d) k ≤ ‖d k‖₊ :=
  (hs.le_singularValue _ k).trans <| lp.singularValue_diagonalCLM_le d (Fin.card_Iio k).le
    fun i hi ↦ hd (by simpa using hi)

/-- Every s-number sequence of a diagonal operator on `ℓ^p(Fin m, 𝕜)` vanishes from index `m`
on. -/
theorem apply_diagonalCLM_fin_of_le {m n : ℕ} (d : ℓ^∞(Fin m, 𝕜)) (hmn : m ≤ n) :
    s (lp.diagonalCLM (p := p) d) n = 0 :=
  le_antisymm ((hs.le_singularValue _ n).trans <|
    lp.singularValue_diagonalCLM_le d (s := Finset.univ) (by simpa using hmn) (by simp))
    zero_le

end IsSNumberSequence

namespace IsStrictSNumberSequence

variable (hs : IsStrictSNumberSequence s)
include hs

/-- **Strict s-numbers of a diagonal operator.** Every strict s-number sequence of a diagonal
operator on `ℓ^p(ℕ, 𝕜)` with nonincreasing coefficient magnitudes is the sequence of those
magnitudes. -/
theorem apply_diagonalCLM (d : ℓ^∞(ℕ, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    s (lp.diagonalCLM (p := p) d) n = ‖d n‖₊ := by
  refine le_antisymm (hs.toIsSNumberSequence.apply_diagonalCLM_le d hd n) ?_
  rcases eq_zero_or_pos ‖d n‖₊ with h | h
  · exact h.symm ▸ zero_le
  obtain ⟨M, B, hM, hB, hBDA⟩ := lp.exists_comp_diagonalCLM_comp_subtypeL_eq_id (p := p) d
    (Finset.range (n + 1)) h fun i hi ↦ hd (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  exact hs.le_of_comp_eq_id B _ M.subtypeL hBDA (by simp [hM]) <|
    (mul_le_of_le_one_right' (by exact_mod_cast Submodule.norm_subtypeL_le M)).trans hB

/-- **Strict s-numbers of a finite diagonal operator.** Every strict s-number sequence of a
diagonal operator on `ℓ^p(Fin m, 𝕜)` with nonincreasing coefficient magnitudes takes the value
`‖d k‖` at each index `k < m`. -/
theorem apply_diagonalCLM_fin {m : ℕ} (d : ℓ^∞(Fin m, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖)
    (k : Fin m) : s (lp.diagonalCLM (p := p) d) k = ‖d k‖₊ := by
  refine le_antisymm (hs.toIsSNumberSequence.apply_diagonalCLM_fin_le d hd k) ?_
  rcases eq_zero_or_pos ‖d k‖₊ with h | h
  · exact h.symm ▸ zero_le
  obtain ⟨M, B, hM, hB, hBDA⟩ := lp.exists_comp_diagonalCLM_comp_subtypeL_eq_id (p := p) d
    (Finset.Iic k) h fun i hi ↦ hd (Finset.mem_Iic.mp hi)
  exact hs.le_of_comp_eq_id B _ M.subtypeL hBDA (by simp [hM]) <|
    (mul_le_of_le_one_right' (by exact_mod_cast Submodule.norm_subtypeL_le M)).trans hB

end IsStrictSNumberSequence

end TauCeti.SNumbers
