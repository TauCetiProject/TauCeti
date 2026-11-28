/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.Analysis.Complex.VerticalStrip.Growth
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.StripGrowth
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.PrimeFactors.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.Growth

/-!
# Growth of the pole-cleared Dirichlet L-function on strips

On any fixed vertical strip, `DirichletCharacter.entireLFunction` has polynomial growth
in the ambient level and height. For imprimitive characters this follows from the strip
bounds for primitive L-functions and the polynomial growth of the deleted Euler factors.
In the principal case use the pole-cleared zeta function in place of the primitive L-function.
The relative version compares the values on a disc with the value at its centre, for use
with Jensen's formula and Landau's local logarithmic derivative lemma.

The primitive strip bounds are `TauCeti.exists_norm_LFunction_le_rpow` and
`TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow`.
-/

public section

open Complex Real

namespace TauCeti

open DirichletCharacter

private theorem norm_entireLFunction_one_le {q d : ℕ} [NeZero q] {s : ℂ} (hs : -(d : ℝ) ≤ s.re) :
    ‖(1 : DirichletCharacter ℂ q).entireLFunction s‖ ≤
      ‖LFunctionTrivChar₁ 1 s‖ * (q : ℝ) ^ (d + 1) := by
  rw [entireLFunction_one_eq_LFunctionTrivChar₁_one_mul_prod, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [one_mul] using
    norm_prod_primeFactors_one_sub_mul_cpow_neg_le_pow (N := q) (fun _ ↦ 1)
      (fun _ ↦ norm_one.le) d hs

private theorem norm_entireLFunction_ne_one_le {q d : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : -(d : ℝ) ≤ s.re) :
    ‖χ.entireLFunction s‖ ≤ ‖χ.primitiveCharacter.LFunction s‖ * (q : ℝ) ^ (d + 1) := by
  have he := (congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ.LFunction s)
    χ.changeLevel_primitiveCharacter).symm.trans
    (LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (.inl (mt χ.primitiveCharacter_eq_one_iff.mp hχ)))
  rw [entireLFunction_of_ne_one hχ, he, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_prod_primeFactors_one_sub_mul_cpow_neg_le_pow (N := q) (fun p ↦ χ.primitiveCharacter p)
      (fun p ↦ χ.primitiveCharacter.norm_le_one p) d hs)
    (norm_nonneg (χ.primitiveCharacter.LFunction s))

/-- Uniform polynomial growth of the pole-cleared L-functions for all characters on a fixed
vertical strip, with the ambient level (not necessarily the conductor) in the bound. -/
theorem exists_norm_entireLFunction_le_rpow (a b : ℝ) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      a ≤ s.re → s.re ≤ b → ‖χ.entireLFunction s‖ ≤ C * (q * (|s.im| + 2)) ^ B := by
  obtain ⟨K, B, hK, hB, hL⟩ := exists_norm_LFunction_le_rpow a b
  obtain ⟨K', B', hζ⟩ := exists_norm_LFunctionTrivChar₁_one_le_rpow a b
  let d : ℕ := ⌈-a⌉₊
  refine ⟨max K K', max B B' + ↑(d + 1 : ℕ), hK.trans_le (le_max_left _ _), by positivity,
    fun {q} _ χ s hsa hsb ↦ ?_⟩
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have ht : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hd : -(d : ℝ) ≤ s.re := (neg_le.mp (Nat.le_ceil (-a))).trans hsa
  let X := (q : ℝ) * (|s.im| + 2)
  have hqX : (q : ℝ) ≤ X := le_mul_of_one_le_right (by positivity) ht
  have hX : 1 ≤ X := hq.trans hqX
  have hE : ‖χ.entireLFunction s‖ ≤ (max K K' * X ^ max B B') * (q : ℝ) ^ (d + 1) := by
    obtain rfl | hχ := eq_or_ne χ 1
    · refine (norm_entireLFunction_one_le hd).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      refine (hζ s hsa hsb).trans ?_
      calc
        _ ≤ max K K' * (|s.im| + 2) ^ max B B' := by
          gcongr <;> exact le_max_right _ _
        _ ≤ max K K' * X ^ max B B' := by
          gcongr
          exact le_mul_of_one_le_left (by positivity) hq
    · refine (norm_entireLFunction_ne_one_le χ hχ hd).trans
        (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have hc : (χ.conductor : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
      refine (hL _ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
        (mt χ.primitiveCharacter_eq_one_iff.mp hχ) s hsa hsb).trans ?_
      refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (by positivity)
      have hbase : (χ.conductor : ℝ) * (|s.im| + 2) ≤ X :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      exact (Real.rpow_le_rpow (by positivity) hbase hB).trans
        (Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _))
  refine hE.trans ?_
  rw [Real.rpow_add (by positivity : 0 < X), Real.rpow_natCast, ← mul_assoc]
  gcongr

/-- Growth relative to the centre on closed discs of fixed radius about a fixed vertical line
right of `Re s = 1`. The exponent is uniform in the level, character, and centre height. -/
theorem exists_norm_entireLFunction_le_rpow_mul {σ : ℝ} (hσ : 1 < σ) (R : ℝ) :
    ∃ D : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z w : ℂ},
      z.re = σ → ‖w - z‖ ≤ R →
      ‖χ.entireLFunction w‖ ≤ (q * (|z.im| + 2)) ^ D * ‖χ.entireLFunction z‖ := by
  obtain ⟨K, B, hK, hB, hL⟩ := exists_norm_entireLFunction_le_rpow (σ - R) (σ + R)
  obtain ⟨D, hD⟩ := Real.exists_mul_rpow_le_rpow_mul (K * (|R| + 1) ^ B) B
    (mul_pos (lt_min one_pos (sub_pos.mpr hσ)) (Real.exp_pos (-(riemannZeta σ).re))) one_lt_two
  refine ⟨D, fun {q} _ χ {z w} hz hw ↦ ?_⟩
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hz' : 1 < z.re := hz ▸ hσ
  have hl := χ.exp_neg_re_riemannZeta_le_norm_LFunction hz'
  rw [hz] at hl
  have hcentre : min 1 (σ - 1) * Real.exp (-(riemannZeta σ).re) ≤ ‖χ.entireLFunction z‖ := by
    obtain rfl | hχ := eq_or_ne χ 1
    · rw [entireLFunction_one_apply (ne_of_apply_ne re (by simpa using hz'.ne')), norm_mul]
      exact mul_le_mul ((min_le_right 1 (σ - 1)).trans (by simpa [hz] using re_le_norm (z - 1)))
        hl (by positivity) (norm_nonneg _)
    · rw [entireLFunction_of_ne_one hχ]
      exact (mul_le_of_le_one_left (by positivity) (min_le_left _ _)).trans hl
  exact (le_mul_rpow_mul_rpow_of_norm_sub_le (g := fun u ↦ ‖χ.entireLFunction u‖)
    hK.le (Nat.cast_nonneg q) hB (hL χ) hz hw).trans
    (hD _ _ (by nlinarith [abs_nonneg z.im]) hcentre)

end TauCeti
