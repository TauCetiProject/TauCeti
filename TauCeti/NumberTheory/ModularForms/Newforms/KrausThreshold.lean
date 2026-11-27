/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.NumberTheory.ModularForms.Newforms.Dimension

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Kraus's thresholds `F♯`, `G♯` and `H♯`

Kraus's comparison theorems for the residual representation `E[ℓ]` of an elliptic curve hold for
primes `ℓ` above explicit thresholds depending only on a level `N`. They are built from two
numbers attached to `N > 0`: the index `μ(N) = [SL(2, ℤ) : Γ₀(N)]` and the dimension `g⁺(N)` of
the weight-two newspace on `Γ₀(N)` (`TauCeti.newDimension`). With square roots and the division
by `6` taken in `ℝ`, they are

```text
F♯(N) = (√(μ(N) / 6) + 1) ^ (2 g⁺(N)),
G♯(N) = (√(μ(lcm(N, 4)) / 6) + 1) ^ 2,
H♯(N) = max(F♯(N), G♯(N)).
```

The threshold `F♯` controls the rationality of the Fourier coefficients of a newform congruent to
`E` (its exponent is twice the dimension, bounding the degree of the coefficient field), `G♯`
controls a congruence modulo `4` read at the level `lcm(N, 4)`, and `H♯` combines both. At level
`0` all three are `0`, as a total-function convention.

Bennett and Siksek state the same comparisons with the cruder majorants
`(μ(N) / 6 + 1) ^ (2 g⁺(N))` and `(μ(lcm(N, 4)) / 6 + 1) ^ 2`, and this file proves that the
sharp thresholds lie below them. For `μ(N) ≥ 6` this is `√x ≤ x` at `x ≥ 1`; when `μ(N) < 6`,
that is at `N = 1, 2, 3`, the Sturm bound gives `g⁺(N) = 0` and both sides equal `1`.

## Main definitions

* `TauCeti.sharpF`, `TauCeti.sharpG`, `TauCeti.sharpH`: the thresholds `F♯`, `G♯` and `H♯`.

## Main results

* `TauCeti.sharpF_of_neZero`, `TauCeti.sharpG_of_ne_zero`, `TauCeti.sharpH_def`: the defining
  formulas at a positive level.
* `TauCeti.one_le_sharpF`, `TauCeti.four_le_sharpG`, `TauCeti.four_le_sharpH`: the thresholds at
  a positive level are at least `1`, `4` and `4`; hence `TauCeti.five_le_of_sharpH_lt`: a natural
  number above `H♯(N)` is at least `5`.
* `TauCeti.sharpH_lt_iff`: `H♯(N) < x` if and only if `F♯(N) < x` and `G♯(N) < x`.
* `TauCeti.sharpF_le_index_div_six_add_one_pow`,
  `TauCeti.sharpG_le_index_lcm_four_div_six_add_one_sq`, `TauCeti.sharpH_le_max`: the comparison
  with Bennett and Siksek's majorants.
* `TauCeti.sharpF_one`, `TauCeti.sharpG_one`, `TauCeti.sharpG_four`, `TauCeti.sharpG_eleven`,
  `TauCeti.sharpH_one`: the values `1`, `4`, `4`, `13 + 4√3` and `4`.

## References

* A. Kraus, *Majorations effectives pour l'équation de Fermat généralisée*, Canad. J. Math. 49
  (1997), 1139–1161, §3.1, equations (7)–(9).
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §2, the definitions of `F`, `G` and `H`.
-/

public section

open CongruenceSubgroup

namespace TauCeti

/-! ### The index of `Γ₀(lcm(N, 4))` -/

/-- For `N ≠ 0` the level `lcm(N, 4)` is a nonzero multiple of `4`, so its `Γ₀` index is a
nonzero multiple of `[SL(2, ℤ) : Γ₀(4)] = 6`; hence `μ(lcm(N, 4)) / 6 ≥ 1`. -/
private theorem one_le_index_Gamma0_lcm_four_div_six {N : ℕ} (hN : N ≠ 0) :
    1 ≤ ((Gamma0 (N.lcm 4)).index : ℝ) / 6 := by
  have : NeZero (N.lcm 4) := ⟨Nat.lcm_ne_zero hN (by norm_num)⟩
  have hdvd := Gamma0_index_dvd_of_dvd (Nat.dvd_lcm_right N 4)
  rw [Gamma0_four_index] at hdvd
  have h6 : 6 ≤ (Gamma0 (N.lcm 4)).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hdvd
  exact (one_le_div₀ (by norm_num)).mpr (by exact_mod_cast h6)

/-! ### The rationality threshold `F♯` -/

/-- **Kraus's coefficient-rationality threshold** `F♯(N) = (√(μ(N) / 6) + 1) ^ (2 g⁺(N))`, where
`μ(N) = [SL(2, ℤ) : Γ₀(N)]` and `g⁺(N)` is the dimension of the weight-two newspace on `Γ₀(N)`.
The square root is taken before the power, and the exponent is twice the dimension, including
dimension zero. The value `0` at `N = 0` is a total-function convention. -/
noncomputable def sharpF (N : ℕ) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩
    (√(((Gamma0 N).index : ℝ) / 6) + 1) ^ (2 * newDimension N)

@[simp]
theorem sharpF_zero : sharpF 0 = 0 := by
  simp [sharpF]

theorem sharpF_of_neZero (N : ℕ) [NeZero N] :
    sharpF N = (√(((Gamma0 N).index : ℝ) / 6) + 1) ^ (2 * newDimension N) := by
  simp [sharpF, NeZero.ne N]

theorem one_le_sharpF (N : ℕ) [NeZero N] : 1 ≤ sharpF N := by
  rw [sharpF_of_neZero]
  exact one_le_pow₀ (le_add_of_nonneg_left (Real.sqrt_nonneg _))

theorem sharpF_eq_one_of_newDimension_eq_zero {N : ℕ} [NeZero N] (h : newDimension N = 0) :
    sharpF N = 1 := by
  rw [sharpF_of_neZero, h, mul_zero, pow_zero]

/-- At level one there is no weight-two newform, so `F♯(1) = 1`, although `μ(1) / 6 < 1`. -/
@[simp]
theorem sharpF_one : sharpF 1 = 1 :=
  sharpF_eq_one_of_newDimension_eq_zero newDimension_one

/-! ### The two-torsion threshold `G♯` -/

/-- **Kraus's two-torsion threshold** `G♯(N) = (√(μ(lcm(N, 4)) / 6) + 1) ^ 2`, where `μ` is the
index of `Γ₀` in `SL(2, ℤ)`. The level is `lcm(N, 4)`, not `4N`. The value `0` at `N = 0` is a
total-function convention. -/
noncomputable def sharpG (N : ℕ) : ℝ :=
  if N = 0 then 0 else (√(((Gamma0 (N.lcm 4)).index : ℝ) / 6) + 1) ^ 2

@[simp]
theorem sharpG_zero : sharpG 0 = 0 := by
  simp [sharpG]

theorem sharpG_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    sharpG N = (√(((Gamma0 (N.lcm 4)).index : ℝ) / 6) + 1) ^ 2 := by
  simp [sharpG, hN]

/-- When `4 ∣ N`, the level `lcm(N, 4)` is `N` itself. -/
theorem sharpG_of_four_dvd {N : ℕ} (hN : N ≠ 0) (h4 : 4 ∣ N) :
    sharpG N = (√(((Gamma0 N).index : ℝ) / 6) + 1) ^ 2 := by
  rw [sharpG_of_ne_zero hN, Nat.lcm_eq_left h4]

/-- At a positive level `G♯(N) ≥ (1 + 1) ^ 2 = 4`, since `μ(lcm(N, 4)) ≥ μ(4) = 6`. -/
theorem four_le_sharpG {N : ℕ} (hN : N ≠ 0) : 4 ≤ sharpG N := by
  rw [sharpG_of_ne_zero hN]
  have h1 : 1 ≤ √(((Gamma0 (N.lcm 4)).index : ℝ) / 6) :=
    Real.one_le_sqrt.mpr (one_le_index_Gamma0_lcm_four_div_six hN)
  nlinarith

@[simp]
theorem sharpG_one : sharpG 1 = 4 := by
  rw [sharpG_of_ne_zero one_ne_zero, Nat.lcm_one_left, Gamma0_four_index]
  norm_num

@[simp]
theorem sharpG_four : sharpG 4 = 4 := by
  rw [sharpG_of_four_dvd (by norm_num) dvd_rfl, Gamma0_four_index]
  norm_num

/-- `G♯(11) = 13 + 4√3`: the index is `μ(44) = μ(4) μ(11) = 72`. -/
theorem sharpG_eleven : sharpG 11 = 13 + 4 * √3 := by
  have h44 : (Gamma0 (Nat.lcm 11 4)).index = 72 := by
    rw [show Nat.lcm 11 4 = 4 * 11 by norm_num, Gamma0_index_mul_of_coprime (by norm_num),
      Gamma0_four_index, Gamma0_prime_index 11 (by norm_num)]
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [sharpG_of_ne_zero (by norm_num), h44, show ((72 : ℕ) : ℝ) / 6 = 12 by norm_num, h12]
  -- `(2√3 + 1)² - (13 + 4√3) = 4 ((√3)² - 3)`
  linear_combination 4 * Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

/-! ### The full-two-torsion threshold `H♯` -/

/-- **Kraus's full-two-torsion threshold** `H♯(N) = max(F♯(N), G♯(N))`, combining the rationality
and two-torsion requirements. -/
noncomputable def sharpH (N : ℕ) : ℝ :=
  max (sharpF N) (sharpG N)

theorem sharpH_def (N : ℕ) : sharpH N = max (sharpF N) (sharpG N) :=
  (rfl)

@[simp]
theorem sharpH_zero : sharpH 0 = 0 := by
  simp [sharpH_def]

theorem sharpF_le_sharpH (N : ℕ) : sharpF N ≤ sharpH N :=
  le_max_left _ _

theorem sharpG_le_sharpH (N : ℕ) : sharpG N ≤ sharpH N :=
  le_max_right _ _

theorem sharpH_lt_iff {N : ℕ} {x : ℝ} : sharpH N < x ↔ sharpF N < x ∧ sharpG N < x :=
  max_lt_iff

theorem four_le_sharpH {N : ℕ} (hN : N ≠ 0) : 4 ≤ sharpH N :=
  (four_le_sharpG hN).trans (sharpG_le_sharpH N)

/-- A natural number strictly above `H♯(N)` at a positive level is at least `5`. -/
theorem five_le_of_sharpH_lt {N ℓ : ℕ} (hN : N ≠ 0) (h : sharpH N < ℓ) : 5 ≤ ℓ := by
  have h4 : (4 : ℝ) < ℓ := (four_le_sharpH hN).trans_lt h
  exact_mod_cast h4

/-- `H♯(1) = max(1, 4) = 4`. -/
@[simp]
theorem sharpH_one : sharpH 1 = 4 := by
  rw [sharpH_def, sharpF_one, sharpG_one]
  norm_num

/-! ### Comparison with Bennett and Siksek's majorants -/

/-- **`F♯` lies below Bennett and Siksek's majorant**:
`F♯(N) ≤ (μ(N) / 6 + 1) ^ (2 g⁺(N))`. For `μ(N) ≥ 6` this is `√x ≤ x` at `x ≥ 1`; otherwise
`g⁺(N) = 0` and both sides are `1`. -/
theorem sharpF_le_index_div_six_add_one_pow (N : ℕ) [NeZero N] :
    sharpF N ≤ (((Gamma0 N).index : ℝ) / 6 + 1) ^ (2 * newDimension N) := by
  by_cases h : (Gamma0 N).index < 6
  · rw [sharpF_eq_one_of_newDimension_eq_zero (newDimension_eq_zero_of_index_lt_six h),
      newDimension_eq_zero_of_index_lt_six h, mul_zero, pow_zero]
  · have h1 : 1 ≤ ((Gamma0 N).index : ℝ) / 6 :=
      (one_le_div₀ (by norm_num)).mpr (by exact_mod_cast not_lt.mp h)
    rw [sharpF_of_neZero]
    gcongr
    exact Real.sqrt_le_self_iff.mpr (Or.inr h1)

/-- **`G♯` lies below Bennett and Siksek's majorant**:
`G♯(N) ≤ (μ(lcm(N, 4)) / 6 + 1) ^ 2`. This holds at every level, since `μ(lcm(N, 4)) ≥ 6` for
`N > 0`. -/
theorem sharpG_le_index_lcm_four_div_six_add_one_sq (N : ℕ) :
    sharpG N ≤ (((Gamma0 (N.lcm 4)).index : ℝ) / 6 + 1) ^ 2 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [sharpG_zero]
    positivity
  rw [sharpG_of_ne_zero hN]
  gcongr
  exact Real.sqrt_le_self_iff.mpr (Or.inr (one_le_index_Gamma0_lcm_four_div_six hN))

/-- **`H♯` lies below Bennett and Siksek's majorant** `H = max(F, G)`. -/
theorem sharpH_le_max (N : ℕ) [NeZero N] :
    sharpH N ≤ max ((((Gamma0 N).index : ℝ) / 6 + 1) ^ (2 * newDimension N))
      ((((Gamma0 (N.lcm 4)).index : ℝ) / 6 + 1) ^ 2) :=
  max_le_max (sharpF_le_index_div_six_add_one_pow N)
    (sharpG_le_index_lcm_four_div_six_add_one_sq N)

end TauCeti
