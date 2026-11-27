/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Countable
import TauCeti.Analysis.Complex.AlgebraicOrbit
import TauCeti.FieldTheory.IsAlgClosed.AlgebraicEmbedding
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.NumberTheory.Padics.Cardinality
import TauCeti.NumberTheory.Padics.PadicNormProductFormula
import TauCeti.RingTheory.Norm.Logarithm

/-!
# The product formula for constant families

The constant family `1` has no negative height bound. A multiplier is algebraic because its
complex images are bounded. Taking its norm to `ℚ` turns each place bound into a bound for a
rational number, to which the finite rational product formula applies.

The application of the product formula is that of `New.HeightLe.nonneg_of_one` in
`grh/src/New/Reduction/Lattices/Heights.lean` of grh-lean (https://github.com/lsernau/grh-lean,
commit `72fead102f663d5c7a407964a13dc0cf9d977207`). Here algebraicity follows from the
archimedean bound alone.
-/

public section

open Finset Module
open scoped IntermediateField

namespace TauCeti.PrimePadicIso

private theorem log_padicNorm_norm_le {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (f : K →+* ℂ) {x : K} (hx : x ≠ 0) (b : ℕ → ℝ)
    (h : ∀ ι : PrimePadicIso, ‖ι.iso (f x)‖ ≤ (ι.prime : ℝ) ^ b ι.prime)
    (p : ℕ) [Fact p.Prime] :
    Real.log (padicNorm p (Algebra.norm ℚ x)) ≤ (finrank ℚ K : ℝ) * (b p * Real.log p) := by
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he (g : K →ₐ[ℚ] PadicAlgCl p) : Real.log ‖g x‖ ≤ b p * Real.log p := by
    let := g.toRingHom.toAlgebra
    obtain ⟨σ, hσ⟩ := TauCeti.Padic.exists_ringEquiv_complex_apply_algebraMap p (PadicAlgCl p) f
    have heq : σ.symm (f x) = g x := σ.symm_apply_eq.mpr (hσ x).symm
    have hbound : ‖g x‖ ≤ (p : ℝ) ^ b p := heq ▸ h ⟨p, σ.symm⟩
    rw [Real.rpow_def_of_pos hp, mul_comm] at hbound
    rw [← Real.log_exp (b p * Real.log p)]
    exact Real.log_le_log (norm_pos_iff.mpr ((map_ne_zero g).mpr hx)) hbound
  have hnorm (q : ℚ) : ‖algebraMap ℚ (PadicAlgCl p) q‖ = padicNorm p q := by
    rw [IsScalarTower.algebraMap_apply ℚ ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends,
      eq_ratCast, Padic.eq_padicNorm]
  calc
    Real.log (padicNorm p (Algebra.norm ℚ x)) = ∑ g : K →ₐ[ℚ] PadicAlgCl p, Real.log ‖g x‖ := by
      rw [← hnorm, Algebra.log_norm_norm_eq_sum_embeddings]
    _ ≤ _ := by
      simpa [AlgHom.card ℚ K (PadicAlgCl p)] using sum_le_sum (fun g (_ : g ∈ univ) ↦ he g)

/-- The constant family `1` cannot have height bounded by a negative number. -/
theorem HeightLe.nonneg_of_one {c : ℝ} (h : HeightLe 1 c) : 0 ≤ c := by
  obtain ⟨H, hH, a, b, _, hArch, hf, hbudget⟩ := heightLe_iff.mp h
  have hfinite : ∀ ι : PrimePadicIso, ‖ι.iso H‖ ≤ (ι.prime : ℝ) ^ b ι.prime := by
    simpa only [Pi.one_apply, mul_one] using hf
  let K := ℚ⟮H⟯
  let x : K := ⟨H, IntermediateField.mem_adjoin_simple_self ℚ H⟩
  have hx : x ≠ 0 := Subtype.coe_ne_coe.mp hH
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional
    (TauCeti.Complex.isAlgebraic_of_forall_norm_ringEquiv_le hArch).isIntegral
  let q := Algebra.norm ℚ x
  let S := (range (max q.num.natAbs q.den + 1)).filter Nat.Prime
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := (mem_filter.mp hp).2
  have hq := Rat.log_abs_add_sum_log_padicNorm_eq_zero q
    (Nat.lt_succ_of_le (le_max_left q.num.natAbs q.den))
    (Nat.lt_succ_of_le (le_max_right q.num.natAbs q.den))
  have harch : Real.log |(q : ℝ)| ≤ (finrank ℚ K : ℝ) * a := by
    let : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
    have hbound := NumberField.abs_norm_le_pow x (C := Real.exp a) fun g ↦ by
      obtain ⟨τ, hτ⟩ := K.exists_ringEquiv_apply_eq_of_isAlgebraic g
      exact (hτ x) ▸ hArch τ
    have hqpos : 0 < |(q : ℝ)| := abs_pos.mpr (by exact_mod_cast Algebra.norm_ne_zero_iff.mpr hx)
    simpa only [Real.log_pow, Real.log_exp, mul_comm] using Real.log_le_log hqpos hbound
  have hsum : ∑ p ∈ S, Real.log (padicNorm p q) ≤
      ∑ p ∈ S, (finrank ℚ K : ℝ) * (b p * Real.log p) := by
    refine sum_le_sum fun p hp ↦ ?_
    let := Fact.mk (hS p hp)
    exact log_padicNorm_norm_le (algebraMap K ℂ) hx b hfinite p
  have hupper := add_le_add harch hsum
  rw [← mul_sum, ← mul_add] at hupper
  have hdeg : (0 : ℝ) < (finrank ℚ K : ℝ) := Nat.cast_pos.mpr finrank_pos
  have hnonneg : 0 ≤ a + ∑ p ∈ S, b p * Real.log p :=
    nonneg_of_mul_nonneg_right (hq ▸ hupper) hdeg
  exact hnonneg.trans (hbudget S hS)

/-- The constant family `1` has exactly the nonnegative numbers as height bounds. -/
@[simp] theorem heightLe_one_iff {c : ℝ} : HeightLe 1 c ↔ 0 ≤ c :=
  ⟨HeightLe.nonneg_of_one, fun hc ↦ heightLe_one.mono hc fun _ ↦ le_rfl⟩

/-- The height bound of a nonzero constant family cannot be smaller than the negative of a
common logarithmic upper bound on the absolute values of its conjugates. -/
theorem HeightLe.neg_le_of_norm_map_le {z : ℂ} {c a : ℝ}
    (h : HeightLe (fun _ ↦ z) c) (hz : z ≠ 0)
    (hσ : ∀ σ : ℂ ≃+* ℂ, ‖σ z‖ ≤ Real.exp a) : -c ≤ a := by
  have hone : HeightLe 1 (c + a) := by
    have hprod : (fun _ : PrimePadicIso ↦ z) * (fun _ ↦ z⁻¹) = 1 := by
      ext ι
      simp [mul_inv_cancel₀ hz]
    rw [← hprod]
    exact h.mul (HeightLe.inv_const hσ)
  linarith [hone.nonneg_of_one]

end TauCeti.PrimePadicIso
