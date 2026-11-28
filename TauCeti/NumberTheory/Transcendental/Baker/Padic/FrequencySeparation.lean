/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.UltrametricLiouville
public import TauCeti.NumberTheory.Padics.Exp.Disc
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Separation of frequencies in a p-adic exponential polynomial

For points `x i` of the exponential disc, consider the frequencies `∑ i, t i • x i` with
integer coordinates between zero and `D`. If the exponentials come from elements of a number
field with a common denominator and a house bound, Liouville's inequality gives an explicit
lower bound on the distance between distinct frequencies. This bound controls the denominators
in Hermite interpolation at the frequencies of Baker's auxiliary function.

## References

* A. Baker, *Transcendental Number Theory*, Chapter 2.
* B. Rousseau, *Théorème de Baker–Brumer sur les unités d'un corps de nombres algébriques*,
  Séminaire de théorie des nombres de Bordeaux (1968–1969), exposé 11.
-/

public section

open Finset NormedSpace TauCeti

/-- **Frequency separation.** Let `x i` lie in the exponential disc and let `exp (x i) = σ (α i)`,
where the `δ * α i` are algebraic integers of house at most `G ≥ δ > 0` in a number field `K`.
The sums with distinct exponent vectors in `{0,…,D}^ι` are separated by at least
`((2 * G ^ (card ι * D)) ^ [K : ℚ])⁻¹`. Independence over `ℕ` expresses injectivity of the sums
with natural coefficients. For rationally independent points use `hli.restrict_scalars' ℕ`. -/
theorem LinearIndependent.inv_pow_le_norm_sub_sum_nsmul
    {p : ℕ} [Fact p.Prime] {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {ι : Type*} [Fintype ι] {x : ι → L} (hli : LinearIndependent ℕ x)
    (hx : ∀ i, ‖x i‖ < amiceRadius p 0) {K : Type*} [Field K] [NumberField K]
    (σ : K →+* L) {α : ι → K} (hα : ∀ i, σ (α i) = exp (x i)) {δ D : ℕ} {G : ℝ}
    (hδ : δ ≠ 0) (hG : (δ : ℝ) ≤ G) (hint : ∀ i, IsIntegral ℤ ((δ : K) * α i))
    (hh : ∀ i, NumberField.house ((δ : K) * α i) ≤ G)
    {t u : ι → Fin (D + 1)} (htu : t ≠ u) :
    ((2 * G ^ (Fintype.card ι * D)) ^ Module.finrank ℚ K)⁻¹ ≤
      ‖(∑ i, (t i : ℕ) • x i) - ∑ i, (u i : ℕ) • x i‖ := by
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  let ψ (v : ι → Fin (D + 1)) := ∑ i, (v i : ℕ) • x i
  have hterm (v : ι → Fin (D + 1)) (i : ι) : ‖(v i : ℕ) • x i‖ < amiceRadius p 0 :=
    (IsUltrametricDist.norm_nsmul_le _ _).trans_lt (hx i)
  have hψ (v) : ‖ψ v‖ < amiceRadius p 0 :=
    mem_ball_zero_iff.mp <| (IsUltrametricDist.ball_openAddSubgroup L (amiceRadius_pos 0)).sum_mem
      fun i _ ↦ mem_ball_zero_iff.mpr (hterm v i)
  have hprod (v) : σ (∏ i, α i ^ (v i : ℕ)) = exp (ψ v) := by
    rw [map_prod, exp_sum_of_norm_lt univ fun i _ ↦ hterm v i]
    simp only [map_pow, hα, exp_nsmul_of_norm_lt _ (hx _)]
  have hne : ψ t ≠ ψ u := fun he ↦ htu <| funext fun i ↦ Fin.ext <|
    Fintype.linearIndependent_iffₛ.mp hli _ _ he i
  have hmon : ∏ i, α i ^ (t i : ℕ) ≠ ∏ i, α i ^ (u i : ℕ) := by
    intro he
    apply hne
    exact injOn_exp_ball (mem_ball_zero_iff.mpr (hψ t)) (mem_ball_zero_iff.mpr (hψ u))
      ((hprod t).symm.trans ((congrArg σ he).trans (hprod u)))
  have hdeg (v : ι → Fin (D + 1)) : ∑ i, (v i : ℕ) ≤ Fintype.card ι * D := by
    simpa using univ.sum_le_card_nsmul (fun i ↦ (v i : ℕ)) D
      fun i _ ↦ Nat.le_of_lt_succ (v i).isLt
  have hd := (IsUltrametricDist.norm_sub_le_max (ψ t) (ψ u)).trans_lt (max_lt (hψ t) (hψ u))
  -- Multiplication by exp (ψ u) has norm one, so the monomial distance is the frequency distance.
  have he := exp_add_of_norm_lt hd (hψ u)
  rw [sub_add_cancel] at he
  calc
    _ ≤ _ := σ.inv_pow_le_norm_sub_prod_pow (inv_abs_le_norm_intCast p) univ hδ hG
      (fun i _ ↦ hint i) (fun i _ ↦ hh i) (hdeg t) (hdeg u) hmon
    _ = ‖(exp (ψ t - ψ u) - 1) * exp (ψ u)‖ := by rw [hprod, hprod, he, sub_mul, one_mul]
    _ = _ := by rw [norm_mul, norm_exp_sub_one_of_norm_lt hd, norm_exp_of_norm_lt (hψ u), mul_one]
