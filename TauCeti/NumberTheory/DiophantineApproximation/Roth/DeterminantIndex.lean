/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.SumEstimate
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Wronskian
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# The index of the determinant in the inductive step of Roth's lemma

Roth's lemma bounds the weighted index `Ind_{a, r}(P)` of a polynomial `P` at a point `a` of
large height. Its inductive step replaces `P` by the determinant

`W = det (∂^(D k + l eᵢ) P)_{k, l < m}`

of Hasse derivatives of `P`, where `m ≤ r i + 1`, and the rows `D k` have weight
`∑ⱼ (D k)ⱼ / rⱼ ≤ c`. If `P = ∑ₖ fₖ · gₖ(Xᵢ)` is separated in the variable `Xᵢ` and the rows do not
differentiate in `Xᵢ`, then `W` is the product of the generalized Wronskian `W_D(f)` and the
Hasse Wronskian of the `gₖ` placed in `Xᵢ` (`MvPolynomial.det_hasseDeriv_sum_mul_toMvPolynomial`).
The heights and degrees of the two factors are controlled, so the induction hypothesis and the
one-variable case bound their indices from above.

This file proves the matching lower bound. The entries of column `l` have index at least
`Ind(P) - c - l / r i`, so the index of `W` is at least the sum of the positive parts of these
numbers over `l < m`. By Pottmeyer's Lemma 3.4.8 (`TauCeti.mul_min_le_sum_max_sub_div`) this sum
is at least `m min (δ / 2) (δ² / 2)` with `δ = Ind(P) - c`. A large index of `P` therefore forces
a large index of one of the two Wronskians.

## Main results

* `TauCeti.ofReal_mul_min_le_weightedIndex_det_hasseDeriv`: the lower bound
  `m min (δ / 2) (δ² / 2) ≤ Ind(W)`, over any commutative ring.
* `TauCeti.ofReal_mul_min_le_weightedIndex_genWronskian_add`: for a separated polynomial over a
  ring without zero divisors, the same lower bound for the sum of the indices of the two
  Wronskians.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.4, proof of Theorem 3.4.1, §3.4.7 and Lemma 3.4.8.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Lemma 6.3.7.
* The column-wise estimate follows the inductive step `MvPolynomial.rothProp_succ` in
  `DiophantineApproximation/RothLemma.lean` of Ralf Stephan's `rwst/Subspace-Theorems`, snapshot
  `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

namespace TauCeti

open MvPolynomial Finset Finsupp
open scoped ENNReal

variable {σ R : Type*} [CommRing R] {m : ℕ}

/-- **The index of the determinant in Roth's lemma.** Let `P` have index at least `t` at `a`
with respect to the weights `r`, let `m ≤ r i + 1`, and let the rows `D k` have weight
`∑ⱼ (D k)ⱼ / rⱼ ≤ c` with `c ≥ 0`. Then the determinant of the Hasse derivatives
`∂^(D k + l eᵢ) P`, for `k, l < m`, has index at least `m min (δ / 2) (δ² / 2)`, where
`δ = t - c`. -/
theorem ofReal_mul_min_le_weightedIndex_det_hasseDeriv {r : σ → ℕ} {a : σ → R}
    {P : MvPolynomial σ R} {i : σ} (hm : m ≤ r i + 1) (D : Fin m → σ →₀ ℕ) {t c : ℝ}
    (hc : 0 ≤ c) (ht : ENNReal.ofReal t ≤ weightedIndex r a P)
    (hD : ∀ k, (D k).weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (m * min ((t - c) / 2) ((t - c) ^ 2 / 2)) ≤
      weightedIndex r a
        (Matrix.of fun k l : Fin m ↦ hasseDeriv (D k + single i (l : ℕ)) P).det := by
  -- The entries of column `l` differentiate `l` more times in `Xᵢ`, at the cost `l / r i`.
  have hcol (k l : Fin m) : ENNReal.ofReal (t - c - l / r i) ≤
      weightedIndex r a (hasseDeriv (D k + single i (l : ℕ)) P) := by
    have hl : (single i (l : ℕ)).weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) =
        ENNReal.ofReal (l / r i) := by
      rw [weight_single, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
      · simp [hl]
      · have hrNat : 0 < r i := by omega
        have hr : (0 : ℝ) < r i := by exact_mod_cast hrNat
        rw [ENNReal.ofReal_div_of_pos hr, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
          div_eq_mul_inv]
    have hw := weightedIndex_le_weightedIndex_hasseDeriv_add r a (D k + single i (l : ℕ)) P
    rw [map_add, hl] at hw
    rw [sub_sub, ENNReal.ofReal_sub _ (by positivity), tsub_le_iff_right,
      ENNReal.ofReal_add hc (by positivity)]
    refine ht.trans (hw.trans ?_)
    gcongr
    exact hD k
  refine le_trans ?_ (le_weightedIndex_det r a _ fun k l ↦ by
    rw [Matrix.of_apply]
    exact hcol k l)
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ ENNReal.ofReal (t - c - l / r i)) m]
  calc ENNReal.ofReal (m * min ((t - c) / 2) ((t - c) ^ 2 / 2))
      ≤ ENNReal.ofReal (∑ l ∈ range m, max (t - c - l / r i) 0) :=
        ENNReal.ofReal_le_ofReal (mul_min_le_sum_max_sub_div hm (t - c))
    _ = ∑ l ∈ range m, ENNReal.ofReal (t - c - l / r i) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ le_max_right _ _]
        simp

/-- **The index of the two Wronskians in Roth's lemma.** Let `P = ∑ₖ fₖ · gₖ(Xᵢ)` over a
ring without zero divisors, where no `fₖ` involves `Xᵢ`, and let the rows `D k` not differentiate
in `Xᵢ`.
Under the hypotheses of `ofReal_mul_min_le_weightedIndex_det_hasseDeriv`, the indices of the
generalized Wronskian `W_D(f)` and of the Hasse Wronskian of the `gₖ` placed in `Xᵢ` add up to at
least `m min (δ / 2) (δ² / 2)`, where `δ = t - c`. -/
theorem ofReal_mul_min_le_weightedIndex_genWronskian_add [NoZeroDivisors R] {r : σ → ℕ}
    {a : σ → R} {i : σ} (hm : m ≤ r i + 1) {D : Fin m → σ →₀ ℕ} (hDi : ∀ k, D k i = 0)
    {f : Fin m → MvPolynomial σ R} (hf : ∀ k, i ∉ (f k).vars) (g : Fin m → Polynomial R)
    {t c : ℝ} (hc : 0 ≤ c)
    (ht : ENNReal.ofReal t ≤ weightedIndex r a (∑ k, f k * (g k).toMvPolynomial i))
    (hD : ∀ k, (D k).weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (m * min ((t - c) / 2) ((t - c) ^ 2 / 2)) ≤
      weightedIndex r a (genWronskian D f) +
        weightedIndex r a ((Polynomial.hasseWronskian g).toMvPolynomial i) := by
  rw [← weightedIndex_mul, ← det_hasseDeriv_sum_mul_toMvPolynomial hDi hf g]
  exact ofReal_mul_min_le_weightedIndex_det_hasseDeriv hm D hc ht hD

end TauCeti
