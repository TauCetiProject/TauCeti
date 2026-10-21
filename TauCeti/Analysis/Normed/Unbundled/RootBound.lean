/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Roots of monic polynomials under power-multiplicative seminorms

Let `f` be a nonarchimedean, power-multiplicative ring seminorm on a ring `R`, and let `x : R` be
a root of a monic polynomial `p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `R` itself. Then `f x` is
controlled by the coefficients: some `i < d` satisfies `f x ^ (d - i) ≤ f aᵢ`, and hence

`f x ≤ max_{i < d} f aᵢ ^ (1 / (d - i))`.

This is the ring-seminorm form of the bound of the norm of a root by the spectral value of a
polynomial, `norm_root_le_spectralValue`, which treats coefficients in a normed field and roots in
an algebra over it. Here the coefficients and the root live in the same ring, as in the integral
equations used to bound supremum seminorms of affinoid algebras.

## Main results

* `Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`: some `i < d` satisfies
  `f x ^ (d - i) ≤ f aᵢ`.
* `Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero`:
  `f x ≤ ⨆ i < d, f aᵢ ^ (1 / (d - i))`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.1.2
  and §3.8.1.
-/

public section

namespace Polynomial.Monic

variable {R F : Type*} [Ring R] [FunLike F R ℝ] [RingSeminormClass F R ℝ] {f : F}
  {p : R[X]} {x : R}

/-- A root `x` of a monic polynomial `p` of degree `d` over a nontrivial ring satisfies
`f x ^ (d - i) ≤ f (p.coeff i)` for some `i < d`, for every nonarchimedean power-multiplicative
ring seminorm `f`. -/
theorem exists_apply_pow_le_apply_coeff_of_eval_eq_zero [Nontrivial R] (hp : p.Monic)
    (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    ∃ i < p.natDegree, f x ^ (p.natDegree - i) ≤ f (p.coeff i) := by
  set d := p.natDegree
  have hd : 0 < d := by
    refine Nat.pos_of_ne_zero fun hd ↦ ?_
    rw [hp.natDegree_eq_zero.mp hd, eval_one] at hx
    exact one_ne_zero hx
  by_contra! h
  -- Every lower term `aᵢ xⁱ` is strictly smaller than `xᵈ`, which is impossible in the
  -- ultrametric relation `xᵈ = -∑_{i < d} aᵢ xⁱ`.
  have hx0 : 0 < f x := by
    refine (apply_nonneg f x).lt_of_ne fun h0 ↦ ?_
    have := (apply_nonneg f (p.coeff 0)).trans_lt (h 0 hd)
    rw [← h0, zero_pow (by omega)] at this
    exact lt_irrefl _ this
  have hterm (i : ℕ) (hi : i < d) : f (p.coeff i * x ^ i) < f x ^ d := by
    have hpow : f (x ^ i) ≤ f x ^ i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa using hf_pm.map_one_le_one
      · exact (hf_pm x hi0).le
    calc f (p.coeff i * x ^ i) ≤ f (p.coeff i) * f (x ^ i) := map_mul_le_mul f _ _
      _ ≤ f (p.coeff i) * f x ^ i := by gcongr
      _ < f x ^ (d - i) * f x ^ i := by gcongr; exact h i hi
      _ = f x ^ d := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  obtain ⟨i, hi, hsum⟩ := hf_na.finset_image_add_of_nonempty (fun i ↦ p.coeff i * x ^ i)
    (Finset.nonempty_range_iff.mpr hd.ne')
  have hxd : x ^ d = -∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hx
    exact eq_neg_of_add_eq_zero_right hx
  have := (hsum.trans_lt (hterm i (Finset.mem_range.mp hi))).trans_eq (hf_pm x hd).symm
  rw [hxd, map_neg_eq_map] at this
  exact lt_irrefl _ this

/-- **Root bound for monic polynomials.** A root `x` of a monic polynomial `p` of degree `d`
satisfies `f x ≤ ⨆ i < d, f (p.coeff i) ^ (1 / (d - i))`, for every nonarchimedean
power-multiplicative ring seminorm `f`. -/
theorem apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero (hp : p.Monic) (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    f x ≤ ⨆ i : Fin p.natDegree, f (p.coeff i) ^ (1 / (p.natDegree - i : ℝ)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim x 0, map_zero]
    exact Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (apply_nonneg f _) _
  · obtain ⟨i, hi, hle⟩ := hp.exists_apply_pow_le_apply_coeff_of_eval_eq_zero hf_pm hf_na hx
    refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨i, hi⟩ ?_
    have hdi : (p.natDegree - i : ℝ) = ((p.natDegree - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hi.le]
    rw [one_div, hdi, Real.le_rpow_inv_iff_of_pos (apply_nonneg f x) (apply_nonneg f _)
      (by exact_mod_cast Nat.sub_pos_of_lt hi), Real.rpow_natCast]
    exact hle

end Polynomial.Monic
