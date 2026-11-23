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

Both bounds hold on any index type, for coefficients in any order: the coefficients outside a set
of at most `n` indices bound `sₙ(D_σ)` from above, and for a strict sequence the coefficients on a
set of more than `n` indices bound it from below. `TauCeti.SNumbers.SNumberFamily` needs the
sequence space in the universe of the scalar field, so these general statements take a scalar
field in the universe `max u v` of an index type `ι : Type v`; the index types `ℕ` and `Fin m`
then work over a scalar field in any universe.

## Main declarations

* `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_le_of_card`,
  `TauCeti.SNumbers.IsStrictSNumberSequence.le_apply_diagonalCLM`: the upper and strict lower
  bounds on an arbitrary index type.
* `TauCeti.SNumbers.IsStrictSNumberSequence.apply_diagonalCLM`: `sₙ(D_σ) = |σₙ|` on `ℓ^p(ℕ, 𝕜)`.
* `TauCeti.SNumbers.IsStrictSNumberSequence.apply_diagonalCLM_fin`: `sₖ(D_σ) = |σₖ|` on
  `ℓ^p(Fin m, 𝕜)` for `k < m`.
* `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_le`,
  `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_fin_le`: the upper bound `sₙ(D_σ) ≤ |σₙ|`
  for every s-number sequence.
* `TauCeti.SNumbers.IsSNumberSequence.apply_diagonalCLM_fin_eq_zero_of_le`: `sₙ(D_σ) = 0` on
  `ℓ^p(Fin m, 𝕜)` for `n ≥ m`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §7.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped lp ENNReal NNReal

universe u v

namespace TauCeti.SNumbers

section General

variable {ι : Type v} {𝕜 : Type (max u v)} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {s : SNumberFamily 𝕜}

/-- Every s-number sequence of a diagonal operator on `ℓ^p(ι, 𝕜)` is bounded at index `n` by
any bound on the coefficients outside a set of at most `n` indices. -/
theorem IsSNumberSequence.apply_diagonalCLM_le_of_card (hs : IsSNumberSequence s)
    (d : ℓ^∞(ι, 𝕜)) {n : ℕ} {t : Finset ι} (ht : t.card ≤ n) {C : ℝ≥0}
    (hC : ∀ i ∉ t, ‖d i‖₊ ≤ C) : s (lp.diagonalCLM (p := p) d) n ≤ C :=
  (hs.le_singularValue _ n).trans (lp.singularValue_diagonalCLM_le d ht hC)

/-- Every strict s-number sequence of a diagonal operator on `ℓ^p(ι, 𝕜)` is bounded below at
index `n` by any lower bound on the coefficients over a set of more than `n` indices. -/
theorem IsStrictSNumberSequence.le_apply_diagonalCLM (hs : IsStrictSNumberSequence s)
    (d : ℓ^∞(ι, 𝕜)) {n : ℕ} {t : Finset ι} (ht : n < t.card) {c : ℝ≥0}
    (hc : ∀ i ∈ t, c ≤ ‖d i‖₊) : c ≤ s (lp.diagonalCLM (p := p) d) n := by
  rcases eq_zero_or_pos c with h | h
  · exact h ▸ zero_le
  obtain ⟨M, B, hM, hB, hBDA⟩ := lp.exists_comp_diagonalCLM_comp_subtypeL_eq_id (p := p) d t h hc
  exact hs.le_of_comp_eq_id B _ M.subtypeL hBDA (by simpa [hM] using ht) <|
    (mul_le_of_le_one_right' (by exact_mod_cast Submodule.norm_subtypeL_le M)).trans hB

end General

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
  hs.apply_diagonalCLM_le_of_card d (Fin.card_Iio k).le fun i hi ↦ hd (by simpa using hi)

/-- Every s-number sequence of a diagonal operator on `ℓ^p(Fin m, 𝕜)` vanishes from index `m`
on. -/
theorem apply_diagonalCLM_fin_eq_zero_of_le {m n : ℕ} (d : ℓ^∞(Fin m, 𝕜)) (hmn : m ≤ n) :
    s (lp.diagonalCLM (p := p) d) n = 0 :=
  le_antisymm (hs.apply_diagonalCLM_le_of_card d (t := Finset.univ) (by simpa using hmn)
    (by simp)) zero_le

end IsSNumberSequence

namespace IsStrictSNumberSequence

variable (hs : IsStrictSNumberSequence s)
include hs

/-- **Strict s-numbers of a diagonal operator.** Every strict s-number sequence of a diagonal
operator on `ℓ^p(ℕ, 𝕜)` with nonincreasing coefficient magnitudes is the sequence of those
magnitudes. -/
theorem apply_diagonalCLM (d : ℓ^∞(ℕ, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    s (lp.diagonalCLM (p := p) d) n = ‖d n‖₊ :=
  le_antisymm (hs.toIsSNumberSequence.apply_diagonalCLM_le d hd n) <|
    hs.le_apply_diagonalCLM d (t := Finset.range (n + 1)) (by simp)
      fun i hi ↦ hd (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **Strict s-numbers of a finite diagonal operator.** Every strict s-number sequence of a
diagonal operator on `ℓ^p(Fin m, 𝕜)` with nonincreasing coefficient magnitudes takes the value
`‖d k‖` at each index `k < m`. -/
theorem apply_diagonalCLM_fin {m : ℕ} (d : ℓ^∞(Fin m, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖)
    (k : Fin m) : s (lp.diagonalCLM (p := p) d) k = ‖d k‖₊ :=
  le_antisymm (hs.toIsSNumberSequence.apply_diagonalCLM_fin_le d hd k) <|
    hs.le_apply_diagonalCLM d (t := Finset.Iic k) (by simp)
      fun i hi ↦ hd (Finset.mem_Iic.mp hi)

end IsStrictSNumberSequence

end TauCeti.SNumbers
