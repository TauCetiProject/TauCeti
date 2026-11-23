/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# The Koecher support theorem for coefficient families at a Hilbert cusp

Let `F` be a totally real field of degree greater than `1`, with real embeddings `τ_w` indexed by
its infinite places, and let `U` be a subgroup of finite index in the units of `𝓞 F`. At a cusp of
a Hilbert modular variety, the Fourier coefficients `a(ξ)` of a modular form are indexed by `ξ ∈ F`
and are covariant under squares of units in the cusp stabilizer:
`a(u² ξ) = c(u, ξ) a(ξ)` with unit multipliers `c(u, ξ)`. Koecher's principle says that such a
family is supported on `0` and the totally positive elements as soon as its support satisfies a
lower bound `B ≤ ∑_w τ_w(ξ) y_w` for one vector `y` with positive entries.

The argument is arithmetic. A nonzero `ξ` that is not totally positive is negative at some real
place `w₀`. A unit `v ∈ U` that is large at `w₀` and small elsewhere exists by Dirichlet's unit
theorem; along the orbit `v^{2n} ξ` the `w₀`-term of the pairing tends to `-∞` and the other terms
tend to `0`, so the pairing is unbounded below on the orbit. Unit multipliers never kill a
nonzero coefficient, so the whole orbit lies in the support, contradicting the lower bound.

The statements hold over any coefficient ring, which may have torsion or nilpotents; only the
unit multipliers are used. Koecher's principle does not give cuspidality: the family that is `1`
at `0` and `0` elsewhere, with trivial multipliers, satisfies every hypothesis.

## Main results

* `TauCeti.HilbertCusp.exists_mem_sum_lt_of_not_isTotallyPositive`: for nonzero `ξ` that is not
  totally positive, the pairing `∑_w τ_w(u² ξ) y_w` is unbounded below for `u ∈ U`.
* `TauCeti.HilbertCusp.eq_zero_or_isTotallyPositive_of_bddBelow`: a set stable under
  multiplication by squares of units in `U`, on which the pairing with `y` is bounded below,
  consists of `0` and totally positive elements.
* `TauCeti.HilbertCusp.bounded_cusp_support_is_positive`: the Koecher support theorem for
  unit-covariant coefficient families.

## References

* M. Dimitrov, *Compactifications arithmétiques des variétés de Hilbert et formes modulaires de
  Hilbert pour Γ₁(c, n)*, in *Geometric Aspects of Dwork Theory*, de Gruyter, 2004, equation (5)
  on p. 546 and the proof of Théorème 8.3 on p. 547.
-/

public section

open Filter NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.HilbertCusp

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F] {U : Subgroup (𝓞 F)ˣ}

/-- When `F` has degree greater than `1`, along the orbit of squares of a finite-index group of
units, the pairing of a nonzero, not totally positive element with a vector of positive weights is
unbounded below. -/
theorem exists_mem_sum_lt_of_not_isTotallyPositive (hU : U.index ≠ 0)
    (hF : 1 < Fintype.card (InfinitePlace F)) {ξ : F} (hξ : ξ ≠ 0)
    (hξ' : ¬IsTotallyPositive ξ) {y : InfinitePlace F → ℝ} (hy : ∀ w, 0 < y w) (B : ℝ) :
    ∃ u ∈ U, ∑ w, embedding_of_isReal (IsTotallyReal.isReal w)
      (((u : 𝓞 F) : F) ^ 2 * ξ) * y w < B := by
  classical
  obtain ⟨w₀, _, hneg⟩ := (not_isTotallyPositive_iff_exists_lt_zero hξ).mp hξ'
  obtain ⟨v, hvU, hv₀, hv⟩ :=
    NumberField.Units.exists_mem_one_lt_and_forall_ne_lt_one hU hF w₀
  -- At each place, the pairing along the powers of `v` is a geometric sequence of ratio `w v ^ 2`.
  have hpow (n : ℕ) (w : InfinitePlace F) :
      embedding_of_isReal (IsTotallyReal.isReal w) ((((v ^ n : (𝓞 F)ˣ) : 𝓞 F) : F) ^ 2 * ξ) *
        y w = (w v ^ 2) ^ n * (embedding_of_isReal (IsTotallyReal.isReal w) ξ * y w) := by
    rw [← norm_embedding_of_isReal (IsTotallyReal.isReal w), Real.norm_eq_abs, sq_abs]
    simp only [Units.val_pow_eq_pow_val, map_pow, map_mul]
    ring
  -- The `w₀`-term tends to `-∞` and the other terms tend to `0`.
  have htend : Tendsto (fun n : ℕ ↦ ∑ w, embedding_of_isReal (IsTotallyReal.isReal w)
      ((((v ^ n : (𝓞 F)ˣ) : 𝓞 F) : F) ^ 2 * ξ) * y w) atTop atBot := by
    simp_rw [hpow, Fintype.sum_eq_add_sum_compl w₀]
    refine Tendsto.atBot_add ?_ (tendsto_finsetSum (a := fun w ↦
      0 * (embedding_of_isReal (IsTotallyReal.isReal w) ξ * y w)) _ fun w hw ↦ ?_)
    · exact (tendsto_pow_atTop_atTop_of_one_lt (one_lt_pow₀ hv₀ two_ne_zero)).atTop_mul_const_of_neg
        (mul_neg_of_neg_of_pos hneg (hy w₀))
    · have hw : w ≠ w₀ := by simpa using hw
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _)
        (pow_lt_one₀ (apply_nonneg w _) (hv w hw) two_ne_zero)).mul_const _
  obtain ⟨n, hn⟩ := (htend.eventually_lt_atBot B).exists
  exact ⟨v ^ n, U.pow_mem hvU n, hn⟩

/-- **Koecher support, for sets.** Let `S ⊆ F` be stable under multiplication by squares of units
in a finite-index subgroup `U`, and let the pairing `ξ ↦ ∑_w τ_w(ξ) y_w` with a vector `y` of
positive weights be bounded below on `S`. If `F` has degree greater than `1`, every element of `S`
is `0` or totally positive. -/
theorem eq_zero_or_isTotallyPositive_of_bddBelow (hU : U.index ≠ 0)
    (hF : 1 < Fintype.card (InfinitePlace F)) {S : Set F}
    (hS : ∀ u ∈ U, ∀ ξ ∈ S, ((u : 𝓞 F) : F) ^ 2 * ξ ∈ S) {y : InfinitePlace F → ℝ}
    (hy : ∀ w, 0 < y w)
    (hbdd : BddBelow ((fun ξ ↦ ∑ w, embedding_of_isReal (IsTotallyReal.isReal w) ξ * y w) '' S))
    {ξ : F} (hξ : ξ ∈ S) : ξ = 0 ∨ IsTotallyPositive ξ := by
  by_contra! h
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨u, hu, hlt⟩ := exists_mem_sum_lt_of_not_isTotallyPositive hU hF h.1 h.2 hy B
  exact (hB ⟨_, hS u hu ξ hξ, rfl⟩).not_gt hlt

/-- **Koecher support for unit-covariant coefficient families.** Let `a : F → R` satisfy
`a(u² ξ) = c(u, ξ) a(ξ)` for `u` in a finite-index subgroup `U` of units and unit multipliers
`c(u, ξ)`, and suppose that `B ≤ ∑_w τ_w(ξ) y_w` whenever `a(ξ) ≠ 0`, for a vector `y` of positive
weights. If `F` has degree greater than `1`, every `ξ` with `a(ξ) ≠ 0` is `0` or totally
positive. No hypothesis is placed on the coefficients beyond the multipliers being units. -/
theorem bounded_cusp_support_is_positive {R : Type*} [MonoidWithZero R] (hU : U.index ≠ 0)
    (hF : 1 < Fintype.card (InfinitePlace F)) (a : F → R) (c : U → F → Rˣ)
    (ha : ∀ (u : U) (ξ : F), a ((((u : (𝓞 F)ˣ) : 𝓞 F) : F) ^ 2 * ξ) = (c u ξ : R) * a ξ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w)
    (hbound : ∃ B : ℝ, ∀ ξ : F, a ξ ≠ 0 →
      B ≤ ∑ w : InfinitePlace F, embedding_of_isReal (IsTotallyReal.isReal w) ξ * y w) :
    ∀ ξ : F, a ξ ≠ 0 → ξ = 0 ∨ IsTotallyPositive ξ := by
  obtain ⟨B, hB⟩ := hbound
  refine fun ξ hξ ↦ eq_zero_or_isTotallyPositive_of_bddBelow hU hF (S := Function.support a)
    (fun u hu ξ hξ ↦ ?_) hy ⟨B, ?_⟩ hξ
  · rw [Function.mem_support, ha ⟨u, hu⟩ ξ, Ne, Units.mul_right_eq_zero]
    exact hξ
  · rintro _ ⟨ξ, hξ, rfl⟩
    exact hB ξ hξ

end TauCeti.HilbertCusp
