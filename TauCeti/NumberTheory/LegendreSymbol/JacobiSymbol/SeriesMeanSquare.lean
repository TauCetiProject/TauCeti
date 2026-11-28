/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.PolyaVinogradov

/-!
# Mean squares of Jacobi-symbol series averaged over numerators

When averaging `|∑ n, a n * J(-v | n°)|²` over the numerator `-v`, with `n°` the odd part
of `n`, the pair `m, n` contributes a character sum of modulus `(m * n)°`. More generally,
for any family of odd denominators the pair contributes a character sum at their product.
Square products are bounded trivially; the others admit Pólya–Vinogradov cancellation.
The second-moment bounds apply to finite sums and to absolutely summable weights such as
Gaussian weights in theta series, without requiring distinct denominators.

The application to quadratic twists follows the moment calculation in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207),
notably `New.dirichletCharacter_jacobiSym_ne_one`, `New.norm_sum_jacobiSym_le`, and
`New.sum_sq_thetaSeries_jacobiSym_le`.
-/

public section

open Finset

namespace TauCeti

/-- The sum of `J(-v | b)` for `1 ≤ v ≤ X` is bounded in norm by `X`, and for odd nonsquare
`b` also by the Pólya–Vinogradov bound. The minimum gives one bound usable for all odd `b`. -/
theorem norm_sum_jacobiSym_neg_Icc_le {b : ℕ} (hb : Odd b) (X : ℕ) :
    ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) b : ℂ)‖ ≤
      if IsSquare b then (X : ℝ) else min X (2 * Real.sqrt b * (1 + Real.log b)) := by
  let : NeZero b := ⟨hb.pos.ne'⟩
  let χ := jacobiChar ℂ b
  have hcard : ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) b : ℂ)‖ ≤ X := by
    refine (norm_sum_le_of_le _ (n := fun _ ↦ (1 : ℝ)) fun v _ ↦ ?_).trans_eq (by simp)
    rw [← jacobiChar_intCast]
    exact χ.norm_le_one _
  split_ifs with hsq
  · exact hcard
  · exact le_min hcard (norm_sum_Icc_jacobiSym_neg_le hb hsq X)

/-- In the numerator second moment, each pair of weights costs at most `K` when the
product of its odd denominators is square, and at most the smaller of `K` and the
Pólya–Vinogradov bound otherwise. The indices need not have distinct denominators. -/
theorem _root_.Finset.sum_norm_sq_jacobiSym_neg_le {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (c : ι → ℂ) (hm : ∀ i ∈ S, Odd (m i)) (K : ℕ) :
    ∑ v ∈ Icc 1 K, ‖∑ i ∈ S, c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)‖ ^ 2 ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ *
        (if IsSquare (m i * m j) then (K : ℝ)
          else min K (2 * Real.sqrt (m i * m j : ℕ) * (1 + Real.log (m i * m j : ℕ)))) := by
  -- Keep the signed correlations inside the norm until the numerator sum has been taken.
  let J (v b : ℕ) : ℂ := jacobiSym (-(v : ℤ)) b
  have hexpand (v : ℕ) :
      ‖∑ i ∈ S, c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)‖ ^ 2 =
        (∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) * J v (m i * m j)).re := by
    rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _),
      Complex.normSq_eq_conj_mul_self, mul_comm, map_sum, sum_mul]
    simp_rw [mul_sum]
    congr 1
    refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
    let : NeZero (m i) := ⟨(hm i hi).pos.ne'⟩
    let : NeZero (m j) := ⟨(hm j hj).pos.ne'⟩
    simp [J, jacobiSym.mul_right, mul_assoc, mul_left_comm]
  simp_rw [hexpand]
  rw [← Complex.re_sum, sum_comm (s := Icc 1 K)]
  simp_rw [sum_comm (s := Icc 1 K), ← mul_sum, Complex.re_sum]
  refine sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ ?_
  set b := m i * m j
  have hb : Odd b := (hm i hi).mul (hm j hj)
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_left (norm_sum_jacobiSym_neg_Icc_le hb K) (by positivity)

/-- The numerator second-moment bound for absolutely summable weights. The product-indexed
majorant is summable because each correlation is bounded by `K`. -/
theorem sum_norm_sq_tsum_jacobiSym_neg_le {ι : Type*} (m : ι → ℕ) (c : ι → ℂ)
    (hm : ∀ i, Odd (m i)) (hc : Summable (fun i ↦ ‖c i‖)) (K : ℕ) :
    ∑ v ∈ Icc 1 K, ‖∑' i, c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)‖ ^ 2 ≤
      ∑' p : ι × ι, ‖c p.1‖ * ‖c p.2‖ *
        (if IsSquare (m p.1 * m p.2) then (K : ℝ)
          else min K (2 * Real.sqrt (m p.1 * m p.2 : ℕ) * (1 + Real.log (m p.1 * m p.2 : ℕ)))) := by
  let F (v : ℕ) (i : ι) := c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)
  set B : ι × ι → ℝ := fun p ↦ ‖c p.1‖ * ‖c p.2‖ *
    (if IsSquare (m p.1 * m p.2) then (K : ℝ)
      else min K (2 * Real.sqrt (m p.1 * m p.2 : ℕ) * (1 + Real.log (m p.1 * m p.2 : ℕ))))
  have hB₀ (p) : 0 ≤ B p := by
    have hp : (1 : ℝ) ≤ (m p.1 * m p.2 : ℕ) := by exact_mod_cast ((hm p.1).mul (hm p.2)).pos
    dsimp only [B]
    split_ifs <;> positivity [Real.log_nonneg hp]
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le hB₀ (fun p ↦ ?_)
      ((hc.mul_of_nonneg hc (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_right (K : ℝ))
    dsimp only [B]
    split_ifs
    · rfl
    · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  have hF (v : ℕ) : Summable (F v) := by
    refine hc.of_norm_bounded fun i ↦ ?_
    let : NeZero (m i) := ⟨(hm i).pos.ne'⟩
    dsimp only [F]
    rw [norm_mul, ← jacobiChar_intCast]
    exact mul_le_of_le_one_right (norm_nonneg _) ((jacobiChar ℂ (m i)).norm_le_one _)
  have hlim : Filter.Tendsto
      (fun S : Finset ι ↦ ∑ v ∈ Icc 1 K, ‖∑ i ∈ S, F v i‖ ^ 2) Filter.atTop
      (nhds (∑ v ∈ Icc 1 K, ‖∑' i, F v i‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun v _ ↦ ?_
    have hv : Filter.Tendsto (fun S : Finset ι ↦ ∑ i ∈ S, F v i) Filter.atTop
      (nhds (∑' i, F v i)) := (hF v).hasSum
    exact hv.norm.pow 2
  refine le_of_tendsto' hlim fun S ↦ ?_
  refine (S.sum_norm_sq_jacobiSym_neg_le m c (fun i _ ↦ hm i) K).trans ?_
  rw [← Finset.sum_product S S B]
  exact hB.sum_le_tsum _ fun p _ ↦ hB₀ p

end TauCeti
