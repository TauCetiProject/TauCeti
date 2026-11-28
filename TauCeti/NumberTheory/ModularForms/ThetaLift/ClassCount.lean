/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.ChangeLevel
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Class counts at congruence levels

An upper bound for the class count at the stabilizer of a lattice transfers to a congruence
level by bounding the number of matrices in the finite reduction ring. The resulting
estimate controls the class sums in the size bound for a chain of theta lifts.

The class-count budget follows `New.Data.card_stdClasses_le_exp_mul_log` in
`New/UpperBound/Size/Estimates.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Matrix NumberField Real

namespace DoubleCoset

/-- Reduction modulo a nonzero ideal of a ring of integers costs at most `absNorm(I)^(n²)`
in the number of classes under change of level. The reduction need not be onto, and `J` need
not be normal in `K`. -/
theorem natCard_quotient_le_mul_absNorm_pow_of_ker_le {G E : Type*} [Group G] [Field E]
    [NumberField E] (Γ : Subgroup G) {J K : Subgroup G} (hJK : J ≤ K)
    {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) {n : ℕ}
    (reduction : K →* GL (Fin n) (𝓞 E ⧸ I)) (hker : reduction.ker ≤ J.subgroupOf K) :
    Nat.card (Quotient (Γ : Set G) J) ≤
      Nat.card (Quotient (Γ : Set G) K) * I.absNorm ^ (n ^ 2) := by
  let R := 𝓞 E ⧸ I
  have : Finite R := Ring.HasFiniteQuotients.finiteQuotient hI
  have hinj : Function.Injective (fun g : reduction.range ↦ (g.val : Matrix (Fin n) (Fin n) R)) :=
    Units.val_injective.comp Subtype.val_injective
  have : Finite reduction.range := Finite.of_injective _ hinj
  refine (natCard_quotient_le_mul_natCard_range_of_ker_le Γ hJK reduction hker).trans
    (Nat.mul_le_mul_left _ ?_)
  calc
    Nat.card reduction.range ≤ Nat.card (Matrix (Fin n) (Fin n) R) :=
      Nat.card_le_card_of_injective _ hinj
    _ = I.absNorm ^ (n ^ 2) := by
      rw [Matrix.card_matrix, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      simp [R, pow_two]

end DoubleCoset

namespace TauCeti.ThetaLift

private theorem genusFactor_le_exp {f n : ℕ} {x c : ℝ} (hx : 32 ≤ x) (hc₀ : 0 ≤ c)
    (hc : c ≤ x ^ 52) (hf : (f : ℝ) * n ^ 2 ≤ x ^ 26) :
    (1 + 2 * c ^ 3) ^ (4 * f * n ^ 2) ≤ exp (x ^ 29) := by
  have hx₁ : 1 ≤ x := by linarith
  have hc' : 1 + 2 * c ^ 3 ≤ x ^ 157 := by
    calc
      _ ≤ 1 + 2 * (x ^ 52) ^ 3 := by gcongr
      _ ≤ x * (x ^ 52) ^ 3 := by
        have h := one_le_pow₀ (one_le_pow₀ hx₁ (n := 52)) (n := 3)
        have hx₃ : 0 ≤ x - 3 := by linarith
        nlinarith [mul_nonneg hx₃ (sub_nonneg.mpr h)]
      _ = _ := by ring
  have hlog := log_le_log (by positivity : 0 < 1 + 2 * c ^ 3) hc'
  rw [log_pow] at hlog
  norm_num at hlog
  apply (log_le_iff_le_exp (by positivity)).mp
  rw [log_pow]
  push_cast
  have hlog' : log (1 + 2 * c ^ 3) ≤ 157 * x := by linarith [log_le_self (by positivity : 0 ≤ x)]
  calc
    _ = (4 * ((f : ℝ) * n ^ 2)) * log (1 + 2 * c ^ 3) := by ring
    _ ≤ (4 * x ^ 26) * (157 * x) := by
      have hbase : 0 ≤ log (1 + 2 * c ^ 3) := log_nonneg (by linarith [pow_nonneg hc₀ 3])
      exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by norm_num)) hlog' hbase (by positivity)
    _ = 628 * x ^ 27 := by ring
    _ ≤ x ^ 29 := by
      have hpow :=
        mul_le_mul_of_nonneg_right (by nlinarith : 628 ≤ x ^ 2) (pow_nonneg (by positivity) 27)
      rwa [← pow_add x 2 27] at hpow

/-- At scales `x ≥ 32`, a genus bound with short-basis parameter `c ≤ x^52` and a rank budget
`f * n² ≤ x^26` give the class-count exponent `x^29 * (1 + log Q)` after reduction modulo an
ideal of norm at most `Q^(2f)`. For an integer modulus `Q` in a CM field of degree `2f`, this
ideal norm is exactly `Q^(2f)`. -/
theorem natCard_quotient_le_exp_of_congruence_reduction {G E : Type*} [Group G] [Field E]
    [NumberField E] (Γ : Subgroup G) {J K : Subgroup G} (hJK : J ≤ K) {n f : ℕ}
    {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (reduction : K →* GL (Fin n) (𝓞 E ⧸ I))
    (hker : reduction.ker ≤ J.subgroupOf K) {x c Q : ℝ} (hx : 32 ≤ x) (hc₀ : 0 ≤ c)
    (hc : c ≤ x ^ 52) (hQ : 1 ≤ Q) (hf : (f : ℝ) * n ^ 2 ≤ x ^ 26)
    (hNorm : (I.absNorm : ℝ) ≤ Q ^ (2 * f))
    (hgenus : (Nat.card (DoubleCoset.Quotient (Γ : Set G) K) : ℝ) ≤
      (1 + 2 * c ^ 3) ^ (4 * f * n ^ 2)) :
    (Nat.card (DoubleCoset.Quotient (Γ : Set G) J) : ℝ) ≤ exp (x ^ 29 * (1 + log Q)) := by
  have hring : (I.absNorm : ℝ) ^ (n ^ 2) ≤ exp (x ^ 29 * log Q) := by
    calc
      _ ≤ (Q ^ (2 * f)) ^ (n ^ 2) := by gcongr
      _ ≤ _ := by
        apply (log_le_iff_le_exp (by positivity)).mp
        rw [log_pow, log_pow]
        push_cast
        have hlogQ := log_nonneg hQ
        have hx₃ : 2 ≤ x ^ 3 := by
          calc
            2 ≤ (32 : ℝ) ^ 3 := by norm_num
            _ ≤ x ^ 3 := by gcongr
        calc
          _ = (2 * ((f : ℝ) * n ^ 2)) * log Q := by ring
          _ ≤ (2 * x ^ 26) * log Q := by gcongr
          _ ≤ _ := by
            have hpow := mul_le_mul_of_nonneg_right hx₃ (pow_nonneg (by positivity) 26)
            rw [← pow_add x 3 26] at hpow
            exact mul_le_mul_of_nonneg_right hpow hlogQ
  have hcount := DoubleCoset.natCard_quotient_le_mul_absNorm_pow_of_ker_le Γ hJK hI reduction hker
  calc
    _ ≤ (Nat.card (DoubleCoset.Quotient (Γ : Set G) K) : ℝ) * (I.absNorm : ℝ) ^ (n ^ 2) := by
      exact_mod_cast hcount
    _ ≤ exp (x ^ 29) * exp (x ^ 29 * log Q) :=
      mul_le_mul (hgenus.trans (genusFactor_le_exp hx hc₀ hc hf)) hring
        (by positivity) (by positivity)
    _ = _ := by rw [← exp_add]; congr 1; ring

end TauCeti.ThetaLift
