/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import TauCeti.Data.Rat.NumDenDvd
public import TauCeti.RingTheory.Valuation.LinearIndependent

/-!
# Denominators of rational values of an extended valuation

Let `v` be a real additive valuation on a ring `K` taking integer values on nonzero elements, such
as a discrete valuation normalised at a uniformiser, and let `w` be a real additive valuation on a
`K`-algebra `L` restricting to `v`. A value `w α = q` need not be an integer, and this file bounds
the denominator of a rational value `q` in two ways.

* If `e • w` takes integer values on the nonzero elements of `L`, then `q.den ∣ e`. For a finite
  extension of discretely valued fields, `e • w` is the integral normalisation of the valuation of
  `L` exactly when `e` is the ramification index, so the denominator of the base-normalised
  valuation of an element divides the ramification index.
* The powers `1, α, …, α ^ (q.den - 1)` are linearly independent over `K`, because the values of
  their nonzero multiples lie in the distinct classes `i * q + ℤ`. Hence `q.den ≤ [L : K]`. For an
  element of value `1 / e`, such as a uniformiser of the integral normalisation `e • w`, this is
  the inequality `e ≤ [L : K]` between the ramification index and the degree.

No completeness and no hypothesis on the residue field is used.

## Main results

* `AddValuation.den_dvd_of_map_eq_ratCast`: if `e • w` is integer valued on nonzero elements, the
  denominator of every rational value of `w` divides `e`.
* `AddValuation.linearIndependent_pow_of_map_eq_ratCast`: the first `q.den` powers of an element
  of value `q` are linearly independent over `K`.
* `AddValuation.den_le_finrank_of_map_eq_ratCast`: the denominator of a rational value of `w` is
  at most `[L : K]`.
* `AddValuation.le_finrank_of_map_eq_inv_natCast`: an element of value `1 / e` forces
  `e ≤ [L : K]`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6, in
  particular Proposition 6.8.
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter I, §4 and
  Chapter II, §2.
-/

public section

namespace AddValuation

section Integral

variable {L : Type*} [Ring L] {w : AddValuation L (WithTop ℝ)}

/-- **Denominators of values divide the ramification index.** If `e • w` takes integer values on
the nonzero elements of `L`, the denominator of every rational value `w α = q` divides `e`. For a
valuation extending a base-normalised discrete valuation, `e • w` is the integral normalisation
when `e` is the ramification index. -/
theorem den_dvd_of_map_eq_ratCast {e : ℕ}
    (hL : ∀ y : L, y ≠ 0 → ∃ n : ℤ, w y = ((n / e : ℝ) : WithTop ℝ)) {α : L} {q : ℚ}
    (hα : w α = ((q : ℝ) : WithTop ℝ)) : q.den ∣ e := by
  rcases eq_or_ne e 0 with rfl | he
  · exact dvd_zero _
  have hα₀ : α ≠ 0 := by
    rintro rfl
    simp at hα
  obtain ⟨n, hn⟩ := hL α hα₀
  rw [hα, WithTop.coe_inj] at hn
  exact (Rat.den_dvd_iff_exists_eq_intCast_div he).2 ⟨n, by exact_mod_cast hn⟩

end Integral

section Extension

variable {K L : Type*} [CommRing K] [Ring L] [Algebra K L] {v : AddValuation K (WithTop ℝ)}
  {w : AddValuation L (WithTop ℝ)}

/-- If `w` restricts to a valuation `v` taking integer values on nonzero elements, and `w α = q`
is rational, the powers `α ^ i` for `i < q.den` are linearly independent over `K`. The value of a
nonzero multiple `a • α ^ i` is `v a + i * q`, and these lie in distinct classes modulo `ℤ`. -/
theorem linearIndependent_pow_of_map_eq_ratCast
    (hint : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    (hw : ∀ x, w (algebraMap K L x) = v x) {α : L} {q : ℚ} (hα : w α = ((q : ℝ) : WithTop ℝ)) :
    LinearIndependent K fun i : Fin q.den ↦ α ^ (i : ℕ) := by
  have hval : ∀ (i : ℕ) (a : K), a ≠ 0 →
      ∃ n : ℤ, w (a • α ^ i) = (((n : ℝ) + i * q : ℝ) : WithTop ℝ) := fun i a ha ↦ by
    obtain ⟨n, hn⟩ := hint a ha
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, map_mul, hw, hn, map_pow, hα, ← WithTop.coe_nsmul, ← WithTop.coe_add,
      nsmul_eq_mul]
  refine w.toValuation.linearIndependent_of_map_smul_ne (fun i a ha ↦ ?_)
    fun i j hij a b ha hb ↦ ?_
  · obtain ⟨n, hn⟩ := hval i a ha
    rw [Ne, ← w.toValuation.map_zero, toValuation_apply, toValuation_apply, hn, map_zero]
    exact fun h ↦ WithTop.coe_ne_top (OrderDual.toDual.injective (Multiplicative.ofAdd.injective h))
  · obtain ⟨m, hm⟩ := hval i a ha
    obtain ⟨n, hn⟩ := hval j b hb
    rw [toValuation_apply, toValuation_apply, hm, hn]
    intro h
    have h' : ((m : ℝ) + (i : ℕ) * q : ℝ) = (n : ℝ) + (j : ℕ) * q :=
      WithTop.coe_inj.mp (OrderDual.toDual.injective (Multiplicative.ofAdd.injective h))
    -- The difference `(j - i) * q` of the two values is the integer `m - n`.
    have hq : ((m - n : ℤ) : ℚ) = q * (((j : ℕ) : ℤ) - (i : ℕ) : ℤ) := by
      have : ((m - n : ℤ) : ℝ) = q * (((j : ℕ) : ℤ) - (i : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hdvd := Rat.den_dvd_of_intCast_eq_mul_intCast q hq
    have hlt : (((j : ℕ) : ℤ) - (i : ℕ)).natAbs < ((q.den : ℤ)).natAbs := by
      have := i.isLt
      have := j.isLt
      omega
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
    exact hij (Fin.ext (by omega))

variable [Nontrivial K] [Module.Finite K L]

/-- If `w` restricts to a valuation `v` taking integer values on nonzero elements, the denominator
of a rational value of `w` is at most the degree `[L : K]`. -/
theorem den_le_finrank_of_map_eq_ratCast
    (hint : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    (hw : ∀ x, w (algebraMap K L x) = v x) {α : L} {q : ℚ} (hα : w α = ((q : ℝ) : WithTop ℝ)) :
    q.den ≤ Module.finrank K L := by
  simpa using (linearIndependent_pow_of_map_eq_ratCast hint hw hα).fintype_card_le_finrank

/-- **The ramification index is at most the degree.** If `w` restricts to a valuation `v` taking
integer values on nonzero elements and some element has value `1 / e`, then `e ≤ [L : K]`. When
`e • w` is the integral normalisation of the valuation of `L`, such an element is a uniformiser
and `e` is the ramification index. -/
theorem le_finrank_of_map_eq_inv_natCast
    (hint : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    (hw : ∀ x, w (algebraMap K L x) = v x) {ϖ : L} {e : ℕ}
    (hϖ : w ϖ = (((e : ℝ)⁻¹ : ℝ) : WithTop ℝ)) : e ≤ Module.finrank K L := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact Nat.zero_le _
  have h := den_le_finrank_of_map_eq_ratCast (q := (e : ℚ)⁻¹) hint hw (by rw [hϖ]; push_cast; rfl)
  rwa [Rat.inv_natCast_den_of_pos he] at h

end Extension

end AddValuation

end
