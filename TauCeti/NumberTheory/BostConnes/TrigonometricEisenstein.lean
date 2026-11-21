/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.RingTheory.RootsOfUnity.Sawtooth
import TauCeti.Algebra.AddCircle
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Trigonometric Eisenstein functions in the rational torsion group algebra

The rational torsion group algebra `ℚ[ℚ/ℤ]` is the diagonal subalgebra of the rational
Bost–Connes algebra; we write `e(a)` for its basis element at `a ∈ ℚ/ℤ`, modelled by
`AddMonoidAlgebra ℚ (AddCircle (1 : ℚ))`. Following Connes–Marcolli, its *first trigonometric
Eisenstein function* at `a` is the finite rational Fourier sum

`e₁,ₐ = ∑_{1 ≤ j < N} (j / N - 1 / 2) e(j a)`,

for any `N > 0` with `N a = 0`; the sum does not depend on `N`, and we define it at the additive
order of `a`. Under a character `χ` of `ℚ/ℤ` with `χ(a) = e^{2π i t}` it evaluates to
`cot (π t) / (2 i)`, a finite form of the normalized cotangent series
`(2π i)⁻¹ ∑ₙ (t + n)⁻¹`, and to `0` when `χ(a) = 1`.

The higher functions are polynomials in the first one: with the recurrence polynomials
`P₀ = 0`, `P₁ = X` and `P_{k+1} = (X² - 1/4) P_k' / k` over `ℚ`, which come from the identity
`d/dt (cot (π t) / (2 i)) = -2π i ((cot (π t) / (2 i))² - 1/4)`, the `k`-th function is
`e_{k,a} = P_k(e₁,ₐ)`. Each `P_k`, `k ≥ 1`, is monic of degree `k` and has the parity of `k`, so
`e_{k,-a} = (-1)^k e_{k,a}`; at `a = 0` the value is the constant `P_k(0)`, e.g. `e_{2,0} = -1/4`.

These are the generators of `ℚ[ℚ/ℤ]` in Connes–Marcolli's description of the rational
arithmetic subalgebra of the Bost–Connes system.

## Main definitions

* `TauCeti.BostConnes.eisensteinPoly k`: the recurrence polynomial `P_k ∈ ℚ[X]`.
* `TauCeti.BostConnes.firstEisenstein a`: the first trigonometric Eisenstein function `e₁,ₐ`.
* `TauCeti.BostConnes.eisenstein k a`: the higher function `e_{k,a} = P_k(e₁,ₐ)`.

## Main results

* `TauCeti.BostConnes.monic_eisensteinPoly`, `TauCeti.BostConnes.natDegree_eisensteinPoly`:
  `P_k` is monic of degree `k` for `k ≥ 1`.
* `TauCeti.BostConnes.eisensteinPoly_comp_neg_X`: `P_k(-X) = (-1)^k P_k(X)`.
* `TauCeti.BostConnes.firstEisenstein_eq_sum`: the defining sum at any annihilating level.
* `TauCeti.BostConnes.firstEisenstein_neg`: `e₁,₋ₐ = -e₁,ₐ`.
* `TauCeti.BostConnes.lift_firstEisenstein_of_ne_one`,
  `TauCeti.BostConnes.lift_firstEisenstein_of_eq_one`: the value `(ζ + 1) / (2 (ζ - 1))` of
  `e₁,ₐ` under a character with `χ(a) = ζ ≠ 1` in a field of characteristic zero, and `0` if
  `ζ = 1`.
* `TauCeti.BostConnes.lift_firstEisenstein_eq_cot`,
  `TauCeti.BostConnes.lift_eisenstein_eq_cot`: the complex values `cot (π t) / (2 i)` and
  `P_k(cot (π t) / (2 i))` when `χ(a) = e^{2π i t}`.
* `TauCeti.BostConnes.eisenstein_zero_right`: `e_{k,0} = P_k(0) · 1`.

## References

* A. Connes, M. Marcolli, *Noncommutative geometry, quantum fields and motives*, Ch. 3, §4.4,
  Lemmas 3.27 and 3.28, (3.91)–(3.101).
-/

public section

noncomputable section

open Polynomial Finset
open scoped Real

namespace TauCeti.BostConnes

/-! ### The recurrence polynomials -/

/-- The recurrence polynomials `P_k ∈ ℚ[X]` of the trigonometric Eisenstein functions:
`P₀ = 0`, `P₁ = X` and `P_{k+1} = (X² - 1/4) P_k' / k` for `k ≥ 1`. -/
def eisensteinPoly : ℕ → ℚ[X]
  | 0 => 0
  | 1 => X
  | k + 2 => C ((k + 1 : ℚ)⁻¹) * ((X ^ 2 - C (1 / 4)) * derivative (eisensteinPoly (k + 1)))

@[simp]
theorem eisensteinPoly_zero : eisensteinPoly 0 = 0 := by
  simp [eisensteinPoly]

@[simp]
theorem eisensteinPoly_one : eisensteinPoly 1 = X := by
  simp [eisensteinPoly]

/-- The recurrence `P_{k+1} = (X² - 1/4) P_k' / k` for `k ≥ 1`. -/
theorem eisensteinPoly_succ {k : ℕ} (hk : k ≠ 0) :
    eisensteinPoly (k + 1) =
      C ((k : ℚ)⁻¹) * ((X ^ 2 - C (1 / 4)) * derivative (eisensteinPoly k)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp [eisensteinPoly]

/-- The recurrence in the division-free form `k P_{k+1} = (X² - 1/4) P_k'`, valid for every
`k`. -/
theorem natCast_mul_eisensteinPoly_succ (k : ℕ) :
    (k : ℚ[X]) * eisensteinPoly (k + 1) = (X ^ 2 - C (1 / 4)) * derivative (eisensteinPoly k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [eisensteinPoly_succ hk, ← C_eq_natCast, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk), C_1, one_mul]

/-- `P_k` is monic of degree `k` for `k ≥ 1`; the two facts are proved by a joint induction. -/
private theorem monic_eisensteinPoly_and_natDegree {k : ℕ} (hk : k ≠ 0) :
    (eisensteinPoly k).Monic ∧ (eisensteinPoly k).natDegree = k := by
  induction k with
  | zero => exact absurd rfl hk
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    obtain ⟨hmon, hdeg⟩ := ih hk0
    set Q : ℚ[X] := X ^ 2 - C (1 / 4)
    have hQ : Q.Monic := monic_X_pow_sub_C _ two_ne_zero
    have hQdeg : Q.natDegree = 2 := natDegree_X_pow_sub_C _
    have hD : derivative (eisensteinPoly k) ≠ 0 := by
      rw [Ne, derivative_eq_zero, hdeg]
      exact hk0
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    have hlead : (Q * derivative (eisensteinPoly k)).leadingCoeff = (k : ℚ) := by
      rw [leadingCoeff_mul, hQ.leadingCoeff, leadingCoeff_derivative, hmon.leadingCoeff, hdeg]
      ring
    have hdeg' : (Q * derivative (eisensteinPoly k)).natDegree = k + 1 := by
      rw [natDegree_mul hQ.ne_zero hD, hQdeg, natDegree_derivative, hdeg]
      omega
    rw [eisensteinPoly_succ hk0]
    refine ⟨?_, ?_⟩
    · rw [Monic, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero hk')), hlead,
        inv_mul_cancel₀ hk']
    · rw [natDegree_C_mul (inv_ne_zero hk'), hdeg']

/-- `P_k` is monic for `k ≥ 1`. -/
theorem monic_eisensteinPoly {k : ℕ} (hk : k ≠ 0) : (eisensteinPoly k).Monic :=
  (monic_eisensteinPoly_and_natDegree hk).1

/-- `P_k` has degree `k`. -/
@[simp]
theorem natDegree_eisensteinPoly (k : ℕ) : (eisensteinPoly k).natDegree = k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  exact (monic_eisensteinPoly_and_natDegree hk).2

/-- `P_k` has the parity of `k`: `P_k(-X) = (-1)^k P_k(X)`. -/
theorem eisensteinPoly_comp_neg_X (k : ℕ) :
    (eisensteinPoly k).comp (-X) = (-1) ^ k * eisensteinPoly k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    have hder : (derivative (eisensteinPoly k)).comp (-X) =
        (-1) ^ (k + 1) * derivative (eisensteinPoly k) := by
      have h := congrArg derivative ih
      rw [derivative_comp, derivative_neg, derivative_X, derivative_mul, derivative_pow,
        derivative_neg, derivative_one] at h
      simp only [mul_neg] at h
      rw [pow_succ]
      linear_combination -h
    rw [eisensteinPoly_succ hk, mul_comp, mul_comp, C_comp, hder, sub_comp, pow_comp, X_comp,
      C_comp]
    ring

theorem eisensteinPoly_two : eisensteinPoly 2 = X ^ 2 - C (1 / 4) := by
  simp [eisensteinPoly]

theorem eisensteinPoly_three : eisensteinPoly 3 = X ^ 3 - C (1 / 4) * X := by
  rw [eisensteinPoly_succ two_ne_zero, eisensteinPoly_two]
  refine Polynomial.funext fun x ↦ ?_
  simp
  ring

theorem eisensteinPoly_four :
    eisensteinPoly 4 = X ^ 4 - C (1 / 3) * X ^ 2 + C (1 / 48) := by
  rw [eisensteinPoly_succ three_ne_zero, eisensteinPoly_three]
  refine Polynomial.funext fun x ↦ ?_
  simp
  ring

/-! ### The first trigonometric Eisenstein function -/

/-- The finite rational Fourier sum `∑_{1 ≤ j < N} (j / N - 1 / 2) e(j a)` at level `N`. -/
private def sawtoothSum (a : AddCircle (1 : ℚ)) (N : ℕ) : AddMonoidAlgebra ℚ (AddCircle (1 : ℚ)) :=
  ∑ j ∈ Ico 1 N, AddMonoidAlgebra.single (j • a) ((j : ℚ) / N - 1 / 2)

/-- The **first trigonometric Eisenstein function** `e₁,ₐ = ∑_{1 ≤ j < N} (j / N - 1 / 2) e(j a)`
in the rational torsion group algebra `ℚ[ℚ/ℤ]`, at the level `N` the additive order of `a`. By
`firstEisenstein_eq_sum` any positive `N` with `N a = 0` gives the same element. -/
def firstEisenstein (a : AddCircle (1 : ℚ)) : AddMonoidAlgebra ℚ (AddCircle (1 : ℚ)) :=
  ∑ j ∈ Ico 1 (addOrderOf a), AddMonoidAlgebra.single (j • a) ((j : ℚ) / addOrderOf a - 1 / 2)

/-- Passing from an annihilating level `n` to a multiple `n m` does not change the sawtooth
sum: with `U_N = ∑_{j < N} e(j a)` and `T_N = ∑_{j < N} j e(j a)` one has `U_{nm} = m U_n` and
`T_{nm} = m T_n + n m (m - 1) / 2 · U_n`. -/
private theorem sawtoothSum_mul {a : AddCircle (1 : ℚ)} {n : ℕ} (hn : 0 < n) (ha : n • a = 0)
    {m : ℕ} (hm : 0 < m) : sawtoothSum a (n * m) = sawtoothSum a n := by
  set U : ℕ → AddMonoidAlgebra ℚ (AddCircle (1 : ℚ)) :=
    fun N ↦ ∑ j ∈ range N, AddMonoidAlgebra.single (j • a) 1
  set T : ℕ → AddMonoidAlgebra ℚ (AddCircle (1 : ℚ)) :=
    fun N ↦ ∑ j ∈ range N, AddMonoidAlgebra.single (j • a) (j : ℚ)
  -- the sawtooth sum in terms of `T` and `U`
  have hS (N : ℕ) (hN : 0 < N) :
      sawtoothSum a N = (N : ℚ)⁻¹ • T N - (1 / 2 : ℚ) • U N + (1 / 2 : ℚ) • 1 := by
    have h := sum_range_eq_add_Ico
      (fun j : ℕ ↦ AddMonoidAlgebra.single (j • a) ((j : ℚ) / N - 1 / 2)) hN
    rw [sawtoothSum, eq_sub_of_add_eq' h.symm]
    have hterm : ∑ j ∈ range N, AddMonoidAlgebra.single (j • a) ((j : ℚ) / N - 1 / 2) =
        ∑ j ∈ range N, (AddMonoidAlgebra.single (j • a) ((N : ℚ)⁻¹ * j) -
          AddMonoidAlgebra.single (j • a) (1 / 2 * 1)) :=
      sum_congr rfl fun j _ ↦ by rw [← AddMonoidAlgebra.single_sub]; congr 1; ring
    simp only [hterm, sum_sub_distrib, T, U, smul_sum, AddMonoidAlgebra.smul_single',
      zero_nsmul, Nat.cast_zero, zero_div, zero_sub, AddMonoidAlgebra.single_neg,
      AddMonoidAlgebra.one_def, mul_one]
    abel
  -- translating by a multiple of `n` does not move `j • a`
  have hshift (q x : ℕ) : (n * q + x) • a = x • a := by
    rw [add_nsmul, mul_nsmul, ha, nsmul_zero, zero_add]
  have hU (q : ℕ) : U (n * q) = (q : ℚ) • U n := by
    induction q with
    | zero => simp [U]
    | succ q ih =>
      simp only [U, Nat.mul_succ, sum_range_add, hshift] at ih ⊢
      rw [ih]
      push_cast
      module
  have hT (q : ℕ) : T (n * q) = (q : ℚ) • T n + ((n * q * (q - 1) / 2 : ℚ)) • U n := by
    induction q with
    | zero => simp [T]
    | succ q ih =>
      have hsplit : ∑ x ∈ range n, AddMonoidAlgebra.single ((n * q + x) • a)
          ((n * q + x : ℕ) : ℚ) = ((n * q : ℕ) : ℚ) • U n + T n := by
        simp only [U, T, hshift, smul_sum, AddMonoidAlgebra.smul_single', mul_one,
          ← sum_add_distrib, ← AddMonoidAlgebra.single_add, Nat.cast_add]
      -- split `T (n * q + n)` into its first `n * q` terms and the last block of `n` terms
      have hblock : T (n * q + n) = T (n * q) + ∑ x ∈ range n,
          AddMonoidAlgebra.single ((n * q + x) • a) ((n * q + x : ℕ) : ℚ) :=
        sum_range_add _ _ _
      rw [Nat.mul_succ, hblock, hsplit, ih]
      push_cast
      module
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [hS _ (Nat.mul_pos hn hm), hS _ hn, hU, hT]
  match_scalars <;> field_simp
  ring

/-- **Level independence.** For every `N > 0` with `N a = 0`,
`e₁,ₐ = ∑_{1 ≤ j < N} (j / N - 1 / 2) e(j a)`. -/
theorem firstEisenstein_eq_sum {a : AddCircle (1 : ℚ)} {N : ℕ} (hN : 0 < N) (ha : N • a = 0) :
    firstEisenstein a =
      ∑ j ∈ Ico 1 N, AddMonoidAlgebra.single (j • a) ((j : ℚ) / N - 1 / 2) := by
  have hfin : IsOfFinAddOrder a := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hN, ha⟩
  obtain ⟨m, rfl⟩ := addOrderOf_dvd_of_nsmul_eq_zero ha
  have hm : 0 < m := Nat.pos_of_mul_pos_left hN
  exact (sawtoothSum_mul hfin.addOrderOf_pos (addOrderOf_nsmul_eq_zero a) hm).symm

@[simp]
theorem firstEisenstein_zero : firstEisenstein 0 = 0 := by
  simp [firstEisenstein]

/-- `e₁,₋ₐ = -e₁,ₐ`. -/
@[simp]
theorem firstEisenstein_neg (a : AddCircle (1 : ℚ)) :
    firstEisenstein (-a) = -firstEisenstein a := by
  set n := addOrderOf a with hn_def
  have hna : n • a = 0 := addOrderOf_nsmul_eq_zero a
  rw [firstEisenstein, addOrderOf_neg, ← hn_def, firstEisenstein, ← hn_def, ← sum_neg_distrib]
  -- reflect `j ↦ n - j` on `[1, n)`
  refine sum_nbij' (fun j ↦ n - j) (fun j ↦ n - j) ?_ ?_ ?_ ?_ ?_
  iterate 4
    · intro j hj
      rw [mem_Ico] at hj
      try rw [mem_Ico]
      omega
  · intro j hj
    simp only [mem_Ico] at hj
    have hjn : j ≤ n := hj.2.le
    have hsmul : j • -a = (n - j) • a := by
      rw [smul_neg, neg_eq_iff_add_eq_zero, ← add_nsmul, Nat.add_sub_cancel' hjn, hna]
    have hn0 : (n : ℚ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast this.ne'
    rw [hsmul, ← AddMonoidAlgebra.single_neg, Nat.cast_sub hjn]
    congr 1
    field_simp
    ring

/-- The value of `e₁,ₐ` under a character `χ` of `ℚ/ℤ` with values in a field of characteristic
zero, as the sawtooth sum of `ζ = χ(a)` at the additive order of `a`. -/
private theorem lift_firstEisenstein_eq_sum {K : Type*} [Field K] [CharZero K]
    (χ : Multiplicative (AddCircle (1 : ℚ)) →* K) (a : AddCircle (1 : ℚ)) :
    AddMonoidAlgebra.lift ℚ K (AddCircle (1 : ℚ)) χ (firstEisenstein a) =
      ∑ j ∈ Ico 1 (addOrderOf a), ((j : K) / addOrderOf a - 1 / 2) *
        χ (Multiplicative.ofAdd a) ^ j := by
  rw [firstEisenstein, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [AddMonoidAlgebra.lift_single, ofAdd_nsmul, map_pow, Rat.smul_def]
  push_cast
  ring

/-- **The value of `e₁,ₐ` at a nondegenerate character.** If `χ(a) = ζ ≠ 1` for a character `χ`
of `ℚ/ℤ` with values in a field of characteristic zero, then `χ(e₁,ₐ) = (ζ + 1) / (2 (ζ - 1))`. -/
theorem lift_firstEisenstein_of_ne_one {K : Type*} [Field K] [CharZero K]
    (χ : Multiplicative (AddCircle (1 : ℚ)) →* K) {a : AddCircle (1 : ℚ)}
    (ha : χ (Multiplicative.ofAdd a) ≠ 1) :
    AddMonoidAlgebra.lift ℚ K (AddCircle (1 : ℚ)) χ (firstEisenstein a) =
      (χ (Multiplicative.ofAdd a) + 1) / (2 * (χ (Multiplicative.ofAdd a) - 1)) := by
  rw [lift_firstEisenstein_eq_sum]
  refine sum_Ico_div_sub_half_mul_pow_of_pow_eq_one two_ne_zero
    (Nat.cast_ne_zero.mpr (AddCircle.isOfFinAddOrder_rat a).addOrderOf_pos.ne') ?_ ha
  rw [← map_pow, ← ofAdd_nsmul, addOrderOf_nsmul_eq_zero, ofAdd_zero, map_one]

/-- **The value of `e₁,ₐ` at a degenerate character.** If `χ(a) = 1` for a character `χ` of `ℚ/ℤ`
with values in a `ℚ`-algebra, then `χ(e₁,ₐ) = 0`. -/
theorem lift_firstEisenstein_of_eq_one {A : Type*} [Semiring A] [Algebra ℚ A]
    (χ : Multiplicative (AddCircle (1 : ℚ)) →* A) {a : AddCircle (1 : ℚ)}
    (ha : χ (Multiplicative.ofAdd a) = 1) :
    AddMonoidAlgebra.lift ℚ A (AddCircle (1 : ℚ)) χ (firstEisenstein a) = 0 := by
  simp only [firstEisenstein, map_sum, AddMonoidAlgebra.lift_single, ofAdd_nsmul, map_pow, ha,
    one_pow, ← sum_smul, sum_Ico_div_sub_half two_ne_zero Nat.cast_eq_zero.mp, zero_smul]

open Complex in
/-- **The cotangent value of `e₁,ₐ`.** If a complex character `χ` of `ℚ/ℤ` has `χ(a) = e^{2π i t}`,
then `χ(e₁,ₐ) = cot (π t) / (2 i)`. When `t ∈ ℤ`, i.e. on the degenerate locus `χ(a) = 1`, both
sides are `0`: the left by `lift_firstEisenstein_of_eq_one`, the right because `Complex.cot` takes
the value `0` at its poles. -/
theorem lift_firstEisenstein_eq_cot (χ : Multiplicative (AddCircle (1 : ℚ)) →* ℂ)
    {a : AddCircle (1 : ℚ)} {t : ℂ} (ht : χ (Multiplicative.ofAdd a) = cexp (2 * π * I * t)) :
    AddMonoidAlgebra.lift ℚ ℂ (AddCircle (1 : ℚ)) χ (firstEisenstein a) =
      cot (π * t) / (2 * I) := by
  rw [cot_pi_eq_exp_ratio, ← ht]
  rcases eq_or_ne (χ (Multiplicative.ofAdd a)) 1 with h1 | h1
  · rw [lift_firstEisenstein_of_eq_one χ h1, h1]
    simp
  · rw [lift_firstEisenstein_of_ne_one χ h1, div_div]
    congr 1
    linear_combination (-2 * (1 - χ (Multiplicative.ofAdd a))) * I_sq

/-! ### The higher trigonometric Eisenstein functions -/

/-- The **higher trigonometric Eisenstein functions** `e_{k,a} = P_k(e₁,ₐ)` in the rational
torsion group algebra `ℚ[ℚ/ℤ]`, with `P_k = eisensteinPoly k`. -/
def eisenstein (k : ℕ) (a : AddCircle (1 : ℚ)) : AddMonoidAlgebra ℚ (AddCircle (1 : ℚ)) :=
  aeval (firstEisenstein a) (eisensteinPoly k)

theorem eisenstein_def (k : ℕ) (a : AddCircle (1 : ℚ)) :
    eisenstein k a = aeval (firstEisenstein a) (eisensteinPoly k) := by
  rw [eisenstein]

@[simp]
theorem eisenstein_zero_left (a : AddCircle (1 : ℚ)) : eisenstein 0 a = 0 := by
  simp [eisenstein]

@[simp]
theorem eisenstein_one_left (a : AddCircle (1 : ℚ)) : eisenstein 1 a = firstEisenstein a := by
  simp [eisenstein]

/-- At `a = 0` the `k`-th function is the constant `P_k(0)`. -/
@[simp]
theorem eisenstein_zero_right (k : ℕ) :
    eisenstein k 0 = algebraMap ℚ _ ((eisensteinPoly k).eval 0) := by
  rw [eisenstein, firstEisenstein_zero, ← map_zero (algebraMap ℚ _),
    aeval_algebraMap_apply_eq_algebraMap_eval]

/-- `e_{k,-a} = (-1)^k e_{k,a}`. -/
@[simp]
theorem eisenstein_neg (k : ℕ) (a : AddCircle (1 : ℚ)) :
    eisenstein k (-a) = (-1) ^ k * eisenstein k a := by
  have h := congrArg (aeval (firstEisenstein a)) (eisensteinPoly_comp_neg_X k)
  rwa [aeval_comp, map_neg, aeval_X, map_mul, map_pow, map_neg, map_one,
    ← firstEisenstein_neg] at h

open Complex in
/-- **The cotangent value of `e_{k,a}`.** If a complex character `χ` of `ℚ/ℤ` has
`χ(a) = e^{2π i t}`, then `χ(e_{k,a}) = P_k(cot (π t) / (2 i))`. -/
theorem lift_eisenstein_eq_cot (χ : Multiplicative (AddCircle (1 : ℚ)) →* ℂ) (k : ℕ)
    {a : AddCircle (1 : ℚ)} {t : ℂ} (ht : χ (Multiplicative.ofAdd a) = cexp (2 * π * I * t)) :
    AddMonoidAlgebra.lift ℚ ℂ (AddCircle (1 : ℚ)) χ (eisenstein k a) =
      aeval (cot (π * t) / (2 * I)) (eisensteinPoly k) := by
  rw [eisenstein, ← aeval_algHom_apply, lift_firstEisenstein_eq_cot χ ht]

/-! ### Values at `1 / 2` and `1 / 3` -/

private theorem two_nsmul_coe_half : 2 • ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [← AddCircle.coe_nsmul]
  norm_num

private theorem two_nsmul_coe_third :
    2 • ((1 / 3 : ℚ) : AddCircle (1 : ℚ)) = ((2 / 3 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← AddCircle.coe_nsmul]
  norm_num

private theorem three_nsmul_coe_third : 3 • ((1 / 3 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [← AddCircle.coe_nsmul]
  norm_num

/-- `e₁,₁/₂ = 0`. -/
theorem firstEisenstein_half : firstEisenstein ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  have hI : Ico 1 2 = {1} := by decide
  rw [firstEisenstein_eq_sum two_pos two_nsmul_coe_half, hI, sum_singleton]
  norm_num

/-- `e₁,₁/₃ = -e(1/3)/6 + e(2/3)/6`. -/
theorem firstEisenstein_third :
    firstEisenstein ((1 / 3 : ℚ) : AddCircle (1 : ℚ)) =
      AddMonoidAlgebra.single ((1 / 3 : ℚ) : AddCircle (1 : ℚ)) (-1 / 6) +
        AddMonoidAlgebra.single ((2 / 3 : ℚ) : AddCircle (1 : ℚ)) (1 / 6) := by
  have hI : Ico 1 3 = {1, 2} := by decide
  rw [firstEisenstein_eq_sum three_pos three_nsmul_coe_third, ← two_nsmul_coe_third, hI,
    sum_pair (by norm_num)]
  norm_num

/-- `e₂,₀ = -1/4`. -/
theorem eisenstein_two_zero : eisenstein 2 0 = algebraMap ℚ _ (-1 / 4) := by
  rw [eisenstein_zero_right, eisensteinPoly_two]
  norm_num

/-- `e₂,₁/₂ = -1/4`: the degenerate value `P₂(0)`, since `e₁,₁/₂ = 0`. -/
theorem eisenstein_two_half :
    eisenstein 2 ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = algebraMap ℚ _ (-1 / 4) := by
  rw [eisenstein, firstEisenstein_half, eisensteinPoly_two]
  simp
  norm_num

/-- `e₃,₁/₂ = 0`. -/
theorem eisenstein_three_half : eisenstein 3 ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [eisenstein, firstEisenstein_half, eisensteinPoly_three]
  simp

/-- `e₂,₁/₃ = (e(1/3) + e(2/3) - 11) / 36`. -/
theorem eisenstein_two_third :
    eisenstein 2 ((1 / 3 : ℚ) : AddCircle (1 : ℚ)) =
      AddMonoidAlgebra.single ((1 / 3 : ℚ) : AddCircle (1 : ℚ)) (1 / 36) +
        AddMonoidAlgebra.single ((2 / 3 : ℚ) : AddCircle (1 : ℚ)) (1 / 36) -
          algebraMap ℚ _ (11 / 36) := by
  rw [eisenstein, eisensteinPoly_two, map_sub, map_pow, aeval_X, aeval_C, firstEisenstein_third,
    ← two_nsmul_coe_third]
  set x : AddCircle (1 : ℚ) := ((1 / 3 : ℚ) : AddCircle (1 : ℚ))
  have h3 : x + 2 • x = 0 := by rw [← succ_nsmul', three_nsmul_coe_third]
  have h2 : 2 • x = -x := eq_neg_of_add_eq_zero_right h3
  have h4 : 2 • 2 • x = x := by rw [h2, smul_neg, h2, neg_neg]
  simp only [sq, add_mul, mul_add, AddMonoidAlgebra.single_mul_single, ← two_nsmul, h3, h4,
    add_comm (2 • x) x, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  -- write every term as a rational multiple of a basis element and compare coefficients
  -- split the constant term `11 / 36 = 1 / 36 + 1 / 36 + 1 / 4`, then normalize coefficients
  have h0 : AddMonoidAlgebra.single (0 : AddCircle (1 : ℚ)) (11 / 36 : ℚ) =
      AddMonoidAlgebra.single 0 (1 / 36) + AddMonoidAlgebra.single 0 (1 / 36) +
        AddMonoidAlgebra.single 0 (1 / 4) := by
    rw [← AddMonoidAlgebra.single_add, ← AddMonoidAlgebra.single_add]
    norm_num
  rw [h0]
  norm_num [AddMonoidAlgebra.single_neg]
  abel

end TauCeti.BostConnes
