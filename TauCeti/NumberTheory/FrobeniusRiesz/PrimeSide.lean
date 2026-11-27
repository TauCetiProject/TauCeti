/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.DirichletCharacter.FrobeniusCoset
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
import Mathlib.Algebra.Order.BigOperators.Expect
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Frobenius

/-!
# The prime side of the Frobenius Riesz expansion

A Frobenius-restricted sum weights a ramp at each prime power by its average over the
Frobenius coset, with a separate cap for each element of a selected subset of the group.
The Fourier expansion uses the primitive characters of the pullbacks to the cyclotomic
level. It therefore includes the contribution from powers of primes dividing the level.

This is the prime-sum step of Levent Alpöge's `Deduction.ch_balance`, in
`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean`.
For an index-two subgroup of places, one takes its complement as the selected subset
and doubles the sum.
-/

public section

open ArithmeticFunction Finset TauCeti
open scoped BigOperators

namespace MonoidHom

variable {N : ℕ} [NeZero N] {G : Type*} [Group G]

/-- The Riesz sum of von Mangoldt weights with caps `w g` for `g ∈ S`.
At each prime power the ramp is averaged over the entire Frobenius coset, with value zero
outside `S`. For positive caps on `S`, the largest integer part of `a / w g` is a common cutoff. -/
noncomputable def frobeniusRieszSum (f : (ZMod N)ˣ →* G) (S : Finset G) (w : G → ℝ)
    (a : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ Icc 1 (S.sup fun g ↦ ⌊a / w g⌋₊), Λ n * 𝔼 g ∈ f.primePowerFrobeniusCoset n,
    if g ∈ S then max (a / (n : ℝ) - w g) 0 else 0

open scoped Classical in
/-- The finite sum formula for the Frobenius Riesz sum, without any positivity assumption
on the caps. -/
theorem frobeniusRieszSum_def (f : (ZMod N)ˣ →* G) (S : Finset G) (w : G → ℝ) (a : ℝ) :
    f.frobeniusRieszSum S w a = ∑ n ∈ Icc 1 (S.sup fun g ↦ ⌊a / w g⌋₊),
      Λ n * 𝔼 g ∈ f.primePowerFrobeniusCoset n, if g ∈ S then max (a / (n : ℝ) - w g) 0 else 0 :=
  (rfl)

open scoped Classical in
/-- A Frobenius Riesz sum is unchanged when evaluated at any common integer cutoff for all
of its rescaled arguments. -/
theorem frobeniusRieszSum_eq_sum (f : (ZMod N)ˣ →* G) (S : Finset G) (w : G → ℝ)
    (a : ℝ) (M : ℕ) (hw : ∀ g ∈ S, 0 < w g) (hM : ∀ g ∈ S, ⌊a / w g⌋₊ ≤ M) :
    f.frobeniusRieszSum S w a = ∑ n ∈ Icc 1 M, Λ n * 𝔼 g ∈ f.primePowerFrobeniusCoset n,
      if g ∈ S then max (a / (n : ℝ) - w g) 0 else 0 := by
  rw [frobeniusRieszSum_def]
  refine sum_subset (Icc_subset_Icc_right (Finset.sup_le hM)) fun n hn hout ↦ ?_
  have hn₁ : 1 ≤ n := (mem_Icc.mp hn).1
  have hn₂ : (S.sup fun g ↦ ⌊a / w g⌋₊) < n := by
    simpa only [mem_Icc, hn₁, true_and, not_le] using hout
  suffices (𝔼 g ∈ f.primePowerFrobeniusCoset n,
      if g ∈ S then max (a / (n : ℝ) - w g) 0 else 0) = 0 by rw [this, mul_zero]
  refine expect_eq_zero fun g _ ↦ ?_
  split_ifs with hg
  · have h := Nat.lt_of_floor_lt
      ((Finset.le_sup (f := fun t ↦ ⌊a / w t⌋₊) hg).trans_lt hn₂)
    rw [div_lt_iff₀ (hw g hg)] at h
    rw [max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (by positivity)).2
      (by simpa only [mul_comm] using h.le)))]
  · rfl

/-- Every Frobenius Riesz sum is nonnegative. -/
theorem frobeniusRieszSum_nonneg (f : (ZMod N)ˣ →* G) (S : Finset G) (w : G → ℝ)
    (a : ℝ) : 0 ≤ f.frobeniusRieszSum S w a := by
  rw [frobeniusRieszSum_def]
  refine sum_nonneg fun n _ ↦ mul_nonneg vonMangoldt_nonneg (Finset.expect_nonneg fun g _ ↦ ?_)
  split_ifs <;> positivity

/-- Increasing the scale and decreasing the positive caps can only increase the sum. -/
theorem frobeniusRieszSum_le (f : (ZMod N)ˣ →* G) (S : Finset G) {w v : G → ℝ} {a b : ℝ}
    (hv : ∀ g ∈ S, 0 < v g) (hvw : ∀ g ∈ S, v g ≤ w g) (hab : a ≤ b) :
    f.frobeniusRieszSum S w a ≤ f.frobeniusRieszSum S v b := by
  let M := max (S.sup fun g ↦ ⌊a / w g⌋₊) (S.sup fun g ↦ ⌊b / v g⌋₊)
  rw [f.frobeniusRieszSum_eq_sum S w a M (fun g hg ↦ (hv g hg).trans_le (hvw g hg))
    (fun g hg ↦ (Finset.le_sup (f := fun t ↦ ⌊a / w t⌋₊) hg).trans (le_max_left ..)),
    f.frobeniusRieszSum_eq_sum S v b M hv
      (fun g hg ↦ (Finset.le_sup (f := fun t ↦ ⌊b / v t⌋₊) hg).trans (le_max_right ..))]
  refine sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (Finset.expect_le_expect fun g _ ↦ ?_)
    vonMangoldt_nonneg
  split_ifs with hg
  · exact max_le_max_right 0
      (sub_le_sub (div_le_div_of_nonneg_right hab (by positivity)) (hvw g hg))
  · exact le_rfl

/-- After multiplication by the von Mangoldt weight, averaging a character on the indexed
Frobenius coset agrees with evaluating its primitive Dirichlet pullback. -/
private theorem mul_expect_primePowerFrobeniusCoset (f : (ZMod N)ˣ →* G) (χ : G →* ℂˣ)
    (n : ℕ) : (Λ n : ℂ) * (𝔼 g ∈ f.primePowerFrobeniusCoset n, (χ g : ℂ)) =
      (Λ n : ℂ) * (PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))).character n := by
  rw [PrimitiveDirichletCharacter.character_of_apply_natCast]
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [f.primePowerFrobeniusCoset_pow hp hk.ne', Finset.expect_eq_sum_div_card,
      f.primitiveCharacter_apply_pow_eq_frobeniusCoset_mean χ hp hk.ne']
  · simp [vonMangoldt_eq_zero_iff.mpr hn]

open scoped IsMulCommutative in
/-- The prime side of the Frobenius Riesz formula: expand the capped ramps in characters,
using the primitive Dirichlet pullbacks even at primes dividing the cyclotomic level. -/
theorem ofReal_frobeniusRieszSum_eq_sum_rieszSum [Finite G] [IsMulCommutative G]
    (f : (ZMod N)ˣ →* G) (S : Finset G) (w : G → ℝ) (a : ℝ) (hw : ∀ g ∈ S, 0 < w g) :
    (f.frobeniusRieszSum S w a : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g ∈ S, (w g : ℂ) * ∑ χ : G →* ℂˣ, (↑(χ g)⁻¹ : ℂ) *
        rieszSum (fun n : ℕ ↦ (Λ n : ℂ) *
          (PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))).character n)
          (a / w g) := by
  classical
  rw [frobeniusRieszSum_def]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_expect,
    apply_ite Complex.ofReal, Complex.ofReal_zero]
  have hcut (g : G) (hg : g ∈ S) : ⌊a / w g⌋₊ ≤ S.sup (fun t ↦ ⌊a / w t⌋₊) :=
    Finset.le_sup (f := fun t ↦ ⌊a / w t⌋₊) hg
  rw [TauCeti.sum_mul_expect_max_eq_sum_mul_rieszSum_expect _ _ _ _ _ _ hw hcut]
  simp_rw [f.mul_expect_primePowerFrobeniusCoset]

end MonoidHom
