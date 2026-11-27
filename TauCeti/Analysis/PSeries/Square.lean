/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.PSeries
public import TauCeti.Data.Nat.Factorization.Square

/-!
# Power weights on pairs with square product

For `s < -1/2`, the weight `(m * n) ^ s` is summable over pairs of natural numbers with square
product, and over pairs for which the `p`-free part of the product is square. Pairs with a zero
coordinate have weight zero in this range. For `p = 2`, the latter sum gives a nonnegative
summable majorant for the square contribution to quadratic-twist second moments.

The estimate corresponds to `New.exists_summable_ge_of_isSquare_ordCompl`, used in
`New.sum_sq_thetaSeries_jacobiSym_le` in `Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at commit `72fead1`.
-/

public section

open Set

namespace TauCeti

/-- The weight `(m * n) ^ s` restricted to pairs with square product is summable for
`s < -1/2`. -/
theorem summable_rpow_isSquare_mul {s : ℝ} (hs : s < -1 / 2) :
    Summable ({q : ℕ × ℕ | IsSquare (q.1 * q.2)}.indicator
      (fun q ↦ ((q.1 : ℝ) * q.2) ^ s)) := by
  let S : Set (ℕ × ℕ) := {q | IsSquare (q.1 * q.2)}
  -- Pick one triple for each pair. The two products determine the pair, so the choice is injective.
  have h (q : S) : ∃ t : ℕ × ℕ × ℕ,
      q.val = (t.1 * t.2.1 ^ 2, t.1 * t.2.2 ^ 2) := by
    obtain ⟨a, b, c, hb, hc⟩ := Nat.isSquare_mul_iff_exists_eq_mul_sq.mp q.property
    exact ⟨(a, b, c), Prod.ext hb hc⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext ((hf x).trans (by rw [hxy, ← hf y]))
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hp₀ (n : ℕ) : 0 ≤ (n : ℝ) ^ (2 * s) := by positivity
  have hprod := hp.mul_of_nonneg (hp.mul_of_nonneg hp hp₀ hp₀) hp₀
    (fun q : ℕ × ℕ ↦ mul_nonneg (hp₀ q.1) (hp₀ q.2))
  refine summable_subtype_iff_indicator.mp ((hprod.comp_injective hinj).congr ?_)
  intro q
  have heq : (q.val.1 : ℝ) * q.val.2 = ((f q).1 * ((f q).2.1 * (f q).2.2) : ℝ) ^ 2 := by
    rw [congrArg Prod.fst (hf q), congrArg Prod.snd (hf q)]
    push_cast
    ring
  simp only [Function.comp_apply]
  rw [heq, ← Real.rpow_natCast_mul (by positivity), Nat.cast_ofNat,
    Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]

end TauCeti

namespace Nat

/-- The weight `(m * n) ^ s` restricted to pairs for which the `p`-free part of `m * n` is
square is summable for `s < -1/2`. For `p = 2` this is the square diagonal of the
Jacobi-symbol second moment; for nonprime `p`, `ordCompl[p]` is the identity. -/
theorem summable_rpow_isSquare_ordCompl (p : ℕ) {s : ℝ} (hs : s < -1 / 2) :
    Summable ({q : ℕ × ℕ | IsSquare (ordCompl[p] (q.1 * q.2))}.indicator
      (fun q ↦ ((q.1 : ℝ) * q.2) ^ s)) := by
  by_cases hp : p.Prime
  swap
  · simpa only [Nat.ordCompl_of_not_prime _ _ hp] using TauCeti.summable_rpow_isSquare_mul hs
  let F : ℕ × ℕ → ℝ := {q : ℕ × ℕ | IsSquare (q.1 * q.2)}.indicator
    (fun q ↦ ((q.1 : ℝ) * q.2) ^ s)
  let g (q : ℕ × ℕ) : ℕ × ℕ := (p * q.1, q.2)
  have hg : Function.Injective g := by
    intro x y h
    have hsnd : (g x).2 = (g y).2 := congrArg Prod.snd h
    exact Prod.ext (mul_left_cancel₀ hp.ne_zero (congrArg Prod.fst h)) hsnd
  have hF : Summable F := TauCeti.summable_rpow_isSquare_mul hs
  have hG := hF.add ((hF.comp_injective hg).mul_left ((p : ℝ) ^ s)⁻¹)
  have hF₀ (q : ℕ × ℕ) : 0 ≤ F q := indicator_apply_nonneg (fun _ ↦ by positivity)
  have hG₀ (q : ℕ × ℕ) : 0 ≤ ((p : ℝ) ^ s)⁻¹ * F (g q) :=
    mul_nonneg (by positivity) (hF₀ _)
  refine hG.of_nonneg_of_le (fun _ ↦ indicator_apply_nonneg (fun _ ↦ by positivity)) ?_
  intro q
  by_cases hq : IsSquare (ordCompl[p] (q.1 * q.2))
  · rw [indicator_of_mem (s := {q : ℕ × ℕ | IsSquare (ordCompl[p] (q.1 * q.2))}) hq]
    rcases (Nat.isSquare_ordCompl_iff hp).mp hq with h | h
    · have hEq : F q = ((q.1 : ℝ) * q.2) ^ s := indicator_of_mem h _
      exact hEq ▸ le_add_of_nonneg_right (hG₀ q)
    · have hEq : F (g q) = ((p : ℝ) * ((q.1 : ℝ) * q.2)) ^ s := by
        have hx : g q ∈ {q : ℕ × ℕ | IsSquare (q.1 * q.2)} := by
          simpa only [mem_ofPred_eq, g, mul_assoc] using h
        simpa only [F, g, Nat.cast_mul, mul_assoc] using
          (indicator_of_mem hx (fun q ↦ ((q.1 : ℝ) * q.2) ^ s))
      have hc : ((p : ℝ) ^ s)⁻¹ * F (g q) = ((q.1 : ℝ) * q.2) ^ s := by
        rw [hEq, Real.mul_rpow (by positivity) (by positivity), ← mul_assoc,
          inv_mul_cancel₀ (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne', one_mul]
      exact hc ▸ le_add_of_nonneg_left (hF₀ q)
  · rw [indicator_of_notMem (s := {q : ℕ × ℕ | IsSquare (ordCompl[p] (q.1 * q.2))}) hq]
    exact add_nonneg (hF₀ q) (hG₀ q)

end Nat
