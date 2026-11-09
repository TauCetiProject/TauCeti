/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Basis
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix
import TauCeti.NumberTheory.Padics.Factorial

/-!
# Diagonal transitions in Amice coordinates

Raising the analytic level from `h` to `h + 1` multiplies the `n`-th Amice coordinate by
`⌊n / pʰ⌋! / ⌊n / p^(h+1)⌋!`. This quotient is an integer, so the transition identity works
for complete ultrametric modules with contractive `ℤ_p` action, including torsion modules.
It is an identity intertwining the existing Amice maps, without assuming their surjectivity.

The multiplier has norm exactly `‖p‖ ^ ⌊n / p^(h+1)⌋` and hence tends to zero. These are the
diagonal decay estimates used to compare analytic stages and their bounded duals.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- The integral multiplier `⌊n / pʰ⌋! / ⌊n / p^(h+1)⌋!` for raising the Amice level. -/
noncomputable def amiceTransitionCoeff (h n : ℕ) : ℤ_[p] :=
  ((n / p ^ h).factorial / (n / p ^ (h + 1)).factorial : ℕ)

variable {p}

/-- Multiplication by the next-level factorial recovers the current-level factorial. -/
theorem factorial_mul_amiceTransitionCoeff (h n : ℕ) :
    ((n / p ^ (h + 1)).factorial : ℤ_[p]) * amiceTransitionCoeff p h n =
      ((n / p ^ h).factorial : ℤ_[p]) := by
  have hd : (n / p ^ (h + 1)).factorial ∣ (n / p ^ h).factorial :=
    Nat.factorial_dvd_factorial <| Nat.div_le_div_left
      (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ h)) (pow_pos hp.out.pos h)
  rw [amiceTransitionCoeff, ← Nat.cast_mul, Nat.mul_div_cancel' hd]

/-- None of the diagonal multipliers vanishes. -/
theorem amiceTransitionCoeff_ne_zero (h n : ℕ) : amiceTransitionCoeff p h n ≠ 0 := by
  intro hz
  have heq := factorial_mul_amiceTransitionCoeff (p := p) h n
  rw [hz, mul_zero] at heq
  have hne : ((n / p ^ h).factorial : ℤ_[p]) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n / p ^ h)
  exact hne heq.symm

/-- In the first block of the next level, the denominator factorial is one. -/
@[simp]
theorem amiceTransitionCoeff_of_lt {h n : ℕ} (hn : n < p ^ (h + 1)) :
    amiceTransitionCoeff p h n = ((n / p ^ h).factorial : ℤ_[p]) := by
  simp [amiceTransitionCoeff, Nat.div_eq_of_lt hn]

/-- In the first block of the current level, the diagonal multiplier is one. -/
@[simp]
theorem amiceTransitionCoeff_of_lt_pow {h n : ℕ} (hn : n < p ^ h) :
    amiceTransitionCoeff p h n = 1 := by
  have hn' : n < p ^ (h + 1) :=
    hn.trans_le (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ h))
  simp [amiceTransitionCoeff_of_lt hn', Nat.div_eq_of_lt hn]

/-- The constant Amice coordinate is unchanged. -/
@[simp]
theorem amiceTransitionCoeff_zero (h : ℕ) : amiceTransitionCoeff p h 0 = 1 := by
  simp [amiceTransitionCoeff]

/-- In the fraction field, the integral multiplier is the ratio of factorials. -/
@[simp]
theorem coe_amiceTransitionCoeff (h n : ℕ) :
    (amiceTransitionCoeff p h n : ℚ_[p]) =
      ((n / p ^ h).factorial : ℚ_[p]) / ((n / p ^ (h + 1)).factorial : ℚ_[p]) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (n / p ^ (h + 1)))).2
  rw [mul_comm]
  simpa only [PadicInt.coe_mul, PadicInt.coe_natCast] using
    congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p]))
      (factorial_mul_amiceTransitionCoeff (p := p) h n)

/-- Legendre's formula gives the exact norm of the diagonal multiplier. -/
theorem norm_amiceTransitionCoeff (h n : ℕ) :
    ‖amiceTransitionCoeff p h n‖ = ‖(p : ℤ_[p])‖ ^ (n / p ^ (h + 1)) := by
  have heq := congrArg norm (factorial_mul_amiceTransitionCoeff (p := p) h n)
  have hnorm := norm_factorial_eq_norm_factorial_div_mul_pow (p := p) 1 (n / p ^ h)
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.div_div_eq_div_mul,
    ← pow_succ] at hnorm
  rw [norm_mul, hnorm] at heq
  exact (mul_left_cancel₀ (by simp [Nat.factorial_ne_zero] :
    ‖((n / p ^ (h + 1)).factorial : ℤ_[p])‖ ≠ 0)) heq

/-- The multipliers tend to zero, with an explicit blockwise geometric rate. -/
theorem tendsto_amiceTransitionCoeff (h : ℕ) :
    Tendsto (amiceTransitionCoeff p h) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_amiceTransitionCoeff]
  refine (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (PadicInt.norm_p_lt_one (p := p))).comp ?_
  exact tendsto_atTop.2 fun b ↦ eventually_atTop.2
    ⟨b * p ^ (h + 1), fun n hn ↦ (Nat.le_div_iff_mul_le (pow_pos hp.out.pos _)).2 hn⟩

namespace AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
  [SMulCommClass ℤ_[p] S E]

private theorem diagonal_amiceTransitionCoeff_tendsto (h j : ℕ) :
    Tendsto (fun i ↦ Matrix.diagonal (amiceTransitionCoeff p h) i j) cofinite (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  have hne : ∀ᶠ i : ℕ in cofinite, i ≠ j := (Set.finite_singleton j).compl_mem_cofinite
  filter_upwards [hne] with i hi
  simp [Matrix.diagonal, hi]

private theorem diagonal_amiceTransitionCoeff_bound (h : ℕ) :
    ∀ i j, ‖Matrix.diagonal (amiceTransitionCoeff p h) i j‖ ≤ (1 : ℝ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact (PadicInt.norm_le_one _)
  · simp [Matrix.diagonal, hij]

variable (p) in
/-- The diagonal map on coefficient sequences that raises the Amice level from `h` to `h + 1`.
Its entries are integral and tend to zero. -/
noncomputable def amiceTransition (h : ℕ) : C₀(ℕ, E) →L[S] C₀(ℕ, E) :=
  (Matrix.diagonal (amiceTransitionCoeff p h)).toZeroAtInftySMulCLM S
    (diagonal_amiceTransitionCoeff_tendsto h) ⟨1, diagonal_amiceTransitionCoeff_bound h⟩

/-- The coordinate formula for the diagonal transition. -/
@[simp]
theorem amiceTransition_apply (h : ℕ) (c : C₀(ℕ, E)) (n : ℕ) :
    amiceTransition p S h c n = amiceTransitionCoeff p h n • c n := by
  rw [amiceTransition, Matrix.toZeroAtInftySMulCLM_apply, tsum_eq_single n]
  · simp
  · intro j hj
    simp [Matrix.diagonal, Ne.symm hj]

/-- The diagonal transition is contractive. -/
theorem norm_amiceTransition_le (h : ℕ) (c : C₀(ℕ, E)) :
    ‖amiceTransition p S h c‖ ≤ ‖c‖ := by
  simpa only [amiceTransition, one_mul] using
    (Matrix.diagonal (amiceTransitionCoeff p h)).norm_toZeroAtInftySMulCLM_apply_le S
    (diagonal_amiceTransitionCoeff_tendsto h) ⟨1, diagonal_amiceTransitionCoeff_bound h⟩
    zero_le_one (diagonal_amiceTransitionCoeff_bound h) c

/-- A quantitative coordinate bound for the diagonal transition. -/
theorem norm_amiceTransition_apply_le (h : ℕ) (c : C₀(ℕ, E)) (n : ℕ) :
    ‖amiceTransition p S h c n‖ ≤ ‖(p : ℤ_[p])‖ ^ (n / p ^ (h + 1)) * ‖c n‖ := by
  rw [amiceTransition_apply, ← norm_amiceTransitionCoeff]
  exact norm_smul_le _ _

/-- On a coordinate vector the transition multiplies its value by the corresponding diagonal. -/
@[simp]
theorem amiceTransition_single (h n : ℕ) (e : E) :
    amiceTransition p S h (ZeroAtInftyContinuousMap.single n e) =
      ZeroAtInftyContinuousMap.single n (amiceTransitionCoeff p h n • e) := by
  ext j
  by_cases hj : j = n
  · subst j; simp
  · simp [ZeroAtInftyContinuousMap.single_apply, hj]

private theorem transition_amiceTerm_scalar (h n : ℕ) :
    transition ℤ_[p] (amiceTerm p h n (1 : ℤ_[p])) =
      amiceTerm p (h + 1) n (amiceTransitionCoeff p h n) := by
  apply eval_injective ℤ_[p] (fun x y hxy ↦
    mul_left_cancel₀ (by exact_mod_cast hp.out.ne_zero : (p : ℤ_[p]) ≠ 0) hxy)
  rw [eval_transition, eval_amiceTerm, eval_amiceTerm]
  ext x
  simp only [PadicInt.mahlerTerm_apply, smul_eq_mul, nsmul_eq_mul, mul_one]
  rw [factorial_mul_amiceTransitionCoeff]

/-- Raising the level of an Amice polynomial multiplies its coefficient by the factorial ratio.
This also holds for torsion coefficient modules. -/
theorem transition_amiceTerm (h n : ℕ) (e : E) :
    transition S (amiceTerm p h n e) =
      amiceTerm p (h + 1) n (amiceTransitionCoeff p h n • e) := by
  -- Prove the identity integrally first, then apply its coefficients to `e`.
  -- This avoids any torsion-freeness assumption on the coefficient module.
  ext ⟨a, j⟩
  have hscalar := DFunLike.congr_fun (transition_amiceTerm_scalar (p := p) h n) (a, j)
  rw [transition_apply] at hscalar ⊢
  simp only [amiceTerm_apply, smul_eq_mul, mul_one] at hscalar
  simp only [amiceTerm_apply, smul_smul]
  rw [← hscalar]
  have hs : Summable (fun k ↦ (k.choose j : ℤ_[p]) *
      ((a.val / p ^ h : ℕ) : ℤ_[p]) ^ (k - j) * (p : ℤ_[p]) ^ j *
        (amicePolynomial p h n (((a.val : ZMod (p ^ h))).val : ℤ_[p])).coeff k) := by
    apply (hasSum_sum_of_ne_finset_zero (s := Finset.range (n + 1)) ?_).summable
    intro k hk
    have hnk : n < k := by simp only [Finset.mem_range] at hk; omega
    rw [coeff_amicePolynomial_eq_zero _ hnk, mul_zero]
  exact hs.tsum_smul_const e

/-- The analytic-stage transition is diagonal in Amice coordinates. -/
theorem transition_amiceMap (h : ℕ) (c : C₀(ℕ, E)) :
    transition S (amiceMap p h S c) =
      amiceMap p (h + 1) S (amiceTransition p S h c) := by
  apply HasSum.unique ((hasSum_amiceMap S c).mapL (transition S))
  simpa only [transition_amiceTerm, amiceTransition_apply] using
    hasSum_amiceMap S (amiceTransition p S h c)

end AnalyticStage

end TauCeti
