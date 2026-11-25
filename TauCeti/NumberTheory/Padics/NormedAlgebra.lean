/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

/-!
# Norms in finite extensions of `ℚ_[p]`

Let `K` be a normed field extension of `ℚ_[p]` of finite degree `n`. The norm of `K` is the
spectral norm, so an element `x` whose minimal polynomial has degree `d` and constant coefficient
`a₀` satisfies `‖x‖ ^ d = ‖a₀‖`. Since `d` divides `n` and `‖a₀‖` is an integer power of `p`, the
`n`-th power of the norm of every nonzero element of `K` is an integer power of `p`.

In any normed field extension of `ℚ_[p]`, an element `π` with `‖π‖ ^ e = ‖p‖` behaves like a
uniformizer: the nonzero terms `aᵢ πⁱ`, `i < e`, have pairwise distinct norms.

## Main results

* `TauCeti.exists_norm_pow_finrank_eq_zpow`: in an extension of `ℚ_[p]` of degree `n`, the `n`-th
  powers of the nonzero norms lie in `p ^ ℤ`.
* `TauCeti.pairwise_norm_smul_pow_ne`: if `‖π‖ ^ e = p⁻¹`, the nonzero terms `aᵢ πⁱ`
  (`aᵢ ∈ ℚ_[p]`, `i < e`) have pairwise distinct norms.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §4.
-/

public section

namespace TauCeti

/-- **Norms in a finite extension of `ℚ_[p]`.** If `K` is a normed field extension of `ℚ_[p]` of
finite degree `n`, then the `n`-th power of the norm of every nonzero element of `K` is an integer
power of `p`. -/
theorem exists_norm_pow_finrank_eq_zpow {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, ‖x‖ ^ Module.finrank ℚ_[p] K = (p : ℝ) ^ m := by
  have hint : IsIntegral ℚ_[p] x := .of_finite ℚ_[p] x
  obtain ⟨k, hk⟩ := minpoly.degree_dvd hint
  refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation * k, ?_⟩
  rw [hk, pow_mul,
    NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero ℚ_[p] hint.isAlgebraic,
    Padic.norm_eq_zpow_neg_valuation (minpoly.coeff_zero_ne_zero hint hx), zpow_mul,
    zpow_natCast]

/-- **Distinct norms of the terms of a `π`-adic expansion.** In a normed field extension of
`ℚ_[p]`, if `‖π‖ ^ e = p⁻¹`, the nonzero terms `aᵢ πⁱ`, `i < e`, of a `ℚ_p`-combination of
powers of `π` have pairwise distinct norms: the norm of `aᵢ πⁱ` is `‖π‖ ^ (e v(aᵢ) + i)`, and
these exponents differ modulo `e`. -/
theorem pairwise_norm_smul_pow_ne {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] {π : K} {e : ℕ} {a : ℕ → ℚ_[p]} {s : Finset ℕ}
    (hπe : ‖π‖ ^ e = (p : ℝ)⁻¹) (hs : ∀ i ∈ s, i < e ∧ a i ≠ 0) :
    (s : Set ℕ).Pairwise fun i j ↦ ‖a i • π ^ i‖ ≠ ‖a j • π ^ j‖ := by
  -- `0 < ‖π‖ < 1` follows from `‖π‖ ^ e = p⁻¹ < 1`.
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have he : e ≠ 0 := by
    rintro rfl
    exact hp1.ne' (by rwa [pow_zero] at hπe)
  have hπ1 : ‖π‖ < 1 := (pow_lt_one_iff_of_nonneg (norm_nonneg π) he).mp (hπe ▸ hp1)
  have hπ0 : 0 < ‖π‖ := lt_of_pow_lt_pow_left₀ e (norm_nonneg π) (by
    rw [zero_pow he, hπe]
    exact inv_pos.mpr (zero_lt_one.trans hp))
  have h_norm (i : ℕ) (ha : a i ≠ 0) : ‖a i • π ^ i‖ = ‖π‖ ^ ((e : ℤ) * (a i).valuation + i) := by
    rw [norm_smul, norm_pow, Padic.norm_eq_zpow_neg_valuation ha, zpow_add₀ hπ0.ne', zpow_mul,
      zpow_natCast, hπe, zpow_natCast, inv_zpow', zpow_neg]
  intro i hi j hj hij h
  obtain ⟨hie, hai⟩ := hs i hi
  obtain ⟨hje, haj⟩ := hs j hj
  rw [h_norm i hai, h_norm j haj, zpow_right_inj₀ hπ0 hπ1.ne] at h
  have h_mod := congrArg (· % (e : ℤ)) h
  simp only [Int.mul_add_emod_self_left] at h_mod
  exact hij (by
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hie),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hje)] at h_mod
    exact_mod_cast h_mod)

end TauCeti
