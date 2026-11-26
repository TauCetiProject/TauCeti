/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic pseudo-Boolean functions and Ising energies

Optimization problems over binary configurations `x : ι → Bool` are commonly formulated in two
equivalent quadratic representations:

* `TauCeti.qubo`: the quadratic pseudo-Boolean function `∑ i, ∑ j, Q i j * bit x i * bit x j`
  in `{0, 1}` variables `bit x i`;
* `TauCeti.ising`: the Ising energy `∑ i, ∑ j, J i j * spin x i * spin x j + ∑ i, h i * spin x i`
  in `{±1}` spin variables `spin x i = 1 - 2 * bit x i`.

Because `bit x i ^ 2 = bit x i`, the diagonal of `Q` carries linear terms in `qubo Q`, whereas
because `spin x i ^ 2 = 1`, the diagonal of `J` contributes only a constant `∑ i, J i i` to
`ising J h`. We establish exact algebraic conversions between `qubo` and `ising`, minimizer and
infimum equivalences, and exact parameter-invariance criteria (`TauCeti.qubo_eq_qubo_iff` and
`TauCeti.ising_sub_diag_eq_iff`).

We also establish the existence and uniqueness of the multilinear expansion of any pseudo-Boolean
function `f : (ι → Bool) → ℝ` over subsets `S : Finset ι` (`TauCeti.existsUnique_sum_prod_bit`) and
characterize functions of the form `qubo Q + const` as those whose multilinear coefficients
vanish on subsets of cardinality greater than `2` (`TauCeti.exists_qubo_add_const_iff`).

## Main definitions

* `TauCeti.bit`, `TauCeti.spin`: `{0, 1}` and `{±1}` encodings of `x : ι → Bool`.
* `TauCeti.qubo`, `TauCeti.ising`: the QUBO and Ising objectives.
* `TauCeti.pseudoBoolCoeff`: the Möbius coefficient of `f` on a subset `S : Finset ι`.

## Main results

* `TauCeti.qubo_eq_ising`, `TauCeti.ising_eq_qubo`: exact conversions between QUBO and Ising forms,
  with minimizer (`TauCeti.isMinOn_qubo_iff_isMinOn_ising`) and infimum
  (`TauCeti.iInf_qubo_eq_iInf_ising_add`) equivalences.
* `TauCeti.qubo_eq_qubo_iff`, `TauCeti.ising_sub_diag_eq_iff`: exact parameter invariance.
* `TauCeti.existsUnique_sum_prod_bit`, `TauCeti.exists_qubo_add_const_iff`: unique multilinear
  expansion and degree-`≤ 2` characterization of quadratic pseudo-Boolean functions.

## References

* A. Lucas, *Ising formulations of many NP problems*, Front. Phys. **2** (2014), 5,
  arXiv:1302.5843, §1.1–1.2.
-/

noncomputable section

public section

open Finset Matrix

namespace TauCeti

/-! ### Bit and spin encodings -/

section BitSpin

variable {ι : Type*}

/-- The `{0, 1}` real value of variable `i` in configuration `x`: `1` when `x i` is `true` and `0`
when `x i` is `false`. -/
def bit (x : ι → Bool) (i : ι) : ℝ :=
  if x i then 1 else 0

/-- The `{±1}` spin value of variable `i` in configuration `x`: `-1` when `x i` is `true` and `1`
when `x i` is `false`. -/
def spin (x : ι → Bool) (i : ι) : ℝ :=
  if x i then -1 else 1

theorem bit_def (x : ι → Bool) (i : ι) : bit x i = if x i then 1 else 0 :=
  (rfl)

theorem spin_def (x : ι → Bool) (i : ι) : spin x i = if x i then -1 else 1 :=
  (rfl)

@[simp]
theorem bit_eq_one_iff {x : ι → Bool} {i : ι} : bit x i = 1 ↔ x i = true := by
  cases h : x i <;> simp [bit_def, h]

@[simp]
theorem bit_eq_zero_iff {x : ι → Bool} {i : ι} : bit x i = 0 ↔ x i = false := by
  cases h : x i <;> simp [bit_def, h]

@[simp]
theorem spin_eq_neg_one_iff {x : ι → Bool} {i : ι} : spin x i = -1 ↔ x i = true := by
  cases h : x i <;> norm_num [spin_def, h]

@[simp]
theorem spin_eq_one_iff {x : ι → Bool} {i : ι} : spin x i = 1 ↔ x i = false := by
  cases h : x i <;> norm_num [spin_def, h]

theorem bit_nonneg (x : ι → Bool) (i : ι) : 0 ≤ bit x i := by
  cases h : x i <;> simp [bit_def, h]

theorem bit_le_one (x : ι → Bool) (i : ι) : bit x i ≤ 1 := by
  cases h : x i <;> simp [bit_def, h]

@[simp]
theorem bit_mul_bit (x : ι → Bool) (i : ι) : bit x i * bit x i = bit x i := by
  cases h : x i <;> simp [bit_def, h]

@[simp]
theorem bit_sq (x : ι → Bool) (i : ι) : bit x i ^ 2 = bit x i := by
  rw [sq, bit_mul_bit]

@[simp]
theorem spin_mul_spin (x : ι → Bool) (i : ι) : spin x i * spin x i = 1 := by
  cases h : x i <;> simp [spin_def, h]

@[simp]
theorem spin_sq (x : ι → Bool) (i : ι) : spin x i ^ 2 = 1 := by
  rw [sq, spin_mul_spin]

theorem abs_spin (x : ι → Bool) (i : ι) : |spin x i| = 1 := by
  cases h : x i <;> simp [spin_def, h]

theorem spin_eq_one_sub_two_mul_bit (x : ι → Bool) (i : ι) : spin x i = 1 - 2 * bit x i := by
  cases h : x i <;> norm_num [spin_def, bit_def, h]

theorem bit_eq_one_sub_spin_div_two (x : ι → Bool) (i : ι) : bit x i = (1 - spin x i) / 2 := by
  cases h : x i <;> norm_num [spin_def, bit_def, h]

theorem bit_not (x : ι → Bool) (i : ι) : bit (fun j ↦ !x j) i = 1 - bit x i := by
  cases h : x i <;> norm_num [bit_def, h]

theorem spin_not (x : ι → Bool) (i : ι) : spin (fun j ↦ !x j) i = -spin x i := by
  cases h : x i <;> norm_num [spin_def, h]

theorem spin_xor (x y : ι → Bool) (i : ι) :
    spin (fun j ↦ xor (x j) (y j)) i = spin x i * spin y i := by
  cases hx : x i <;> cases hy : y i <;> norm_num [spin_def, hx, hy]

end BitSpin

/-! ### QUBO and Ising objectives -/

section QuboIsing

variable {ι : Type*} [Fintype ι]

/-- The quadratic pseudo-Boolean function with coefficient matrix `Q`, summed over all ordered
pairs of variables. -/
def qubo (Q : Matrix ι ι ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, ∑ j, Q i j * bit x i * bit x j

/-- The Ising energy with coupling matrix `J` (summed over all ordered pairs) and external field
`h`. -/
def ising (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, ∑ j, J i j * spin x i * spin x j + ∑ i, h i * spin x i

theorem qubo_def (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo Q x = ∑ i, ∑ j, Q i j * bit x i * bit x j :=
  (rfl)

theorem ising_def (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising J h x = ∑ i, ∑ j, J i j * spin x i * spin x j + ∑ i, h i * spin x i :=
  (rfl)

@[simp]
theorem qubo_zero (x : ι → Bool) : qubo (0 : Matrix ι ι ℝ) x = 0 := by
  simp [qubo_def]

@[simp]
theorem qubo_add (Q₁ Q₂ : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo (Q₁ + Q₂) x = qubo Q₁ x + qubo Q₂ x := by
  simp [qubo_def, add_mul, sum_add_distrib]

@[simp]
theorem qubo_sub (Q₁ Q₂ : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo (Q₁ - Q₂) x = qubo Q₁ x - qubo Q₂ x := by
  simp [qubo_def, sub_mul, sum_sub_distrib]

@[simp]
theorem qubo_neg (Q : Matrix ι ι ℝ) (x : ι → Bool) : qubo (-Q) x = -qubo Q x := by
  simp [qubo_def, sum_neg_distrib]

@[simp]
theorem qubo_smul (c : ℝ) (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo (c • Q) x = c * qubo Q x := by
  simp [qubo_def, mul_assoc, mul_sum]

@[simp]
theorem qubo_transpose (Q : Matrix ι ι ℝ) (x : ι → Bool) : qubo Qᵀ x = qubo Q x := by
  simp only [qubo_def, transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

@[simp]
theorem qubo_diagonal [DecidableEq ι] (d : ι → ℝ) (x : ι → Bool) :
    qubo (Matrix.diagonal d) x = ∑ i, d i * bit x i := by
  simp [qubo_def, Matrix.diagonal_apply, mul_assoc]

@[simp]
theorem ising_zero (x : ι → Bool) : ising (0 : Matrix ι ι ℝ) 0 x = 0 := by
  simp [ising_def]

@[simp]
theorem ising_add (J₁ J₂ : Matrix ι ι ℝ) (h₁ h₂ : ι → ℝ) (x : ι → Bool) :
    ising (J₁ + J₂) (h₁ + h₂) x = ising J₁ h₁ x + ising J₂ h₂ x := by
  simp only [ising_def, Matrix.add_apply, Pi.add_apply, add_mul, sum_add_distrib]
  ring

@[simp]
theorem ising_sub (J₁ J₂ : Matrix ι ι ℝ) (h₁ h₂ : ι → ℝ) (x : ι → Bool) :
    ising (J₁ - J₂) (h₁ - h₂) x = ising J₁ h₁ x - ising J₂ h₂ x := by
  simp only [ising_def, Matrix.sub_apply, Pi.sub_apply, sub_mul, sum_sub_distrib]
  ring

@[simp]
theorem ising_neg (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising (-J) (-h) x = -ising J h x := by
  simp only [ising_def, Matrix.neg_apply, Pi.neg_apply, neg_mul, sum_neg_distrib]
  ring

@[simp]
theorem ising_smul (c : ℝ) (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising (c • J) (c • h) x = c * ising J h x := by
  simp only [ising_def, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, mul_add, mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_
  · refine Finset.sum_congr rfl fun j _ ↦ by ring
  · ring

@[simp]
theorem ising_transpose (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising Jᵀ h x = ising J h x := by
  simp only [ising_def, transpose_apply]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

@[simp]
theorem ising_diagonal [DecidableEq ι] (d h : ι → ℝ) (x : ι → Bool) :
    ising (Matrix.diagonal d) h x = ∑ i, d i + ∑ i, h i * spin x i := by
  simp [ising_def, Matrix.diagonal_apply, mul_assoc]

@[simp]
theorem ising_not (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising J h (fun i ↦ !x i) = ising J (-h) x := by
  simp only [ising_def, spin_not, Pi.neg_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring

theorem qubo_add_transpose (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo (Q + Qᵀ) x = 2 * qubo Q x := by
  rw [qubo_add, qubo_transpose, two_mul]

theorem qubo_symmetrize (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo ((1 / 2 : ℝ) • (Q + Qᵀ)) x = qubo Q x := by
  rw [qubo_smul, qubo_add_transpose]
  ring

theorem ising_symmetrize (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising ((1 / 2 : ℝ) • (J + Jᵀ)) h x = ising J h x := by
  have h1 : ising (J + Jᵀ) (h + h) x = 2 * ising J h x := by
    rw [ising_add, ising_transpose, two_mul]
  have h2 : (1 / 2 : ℝ) • (h + h) = h := by
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  calc
    ising ((1 / 2 : ℝ) • (J + Jᵀ)) h x
      = ising ((1 / 2 : ℝ) • (J + Jᵀ)) ((1 / 2 : ℝ) • (h + h)) x := by rw [h2]
    _ = (1 / 2 : ℝ) * ising (J + Jᵀ) (h + h) x := ising_smul _ _ _ _
    _ = ising J h x := by rw [h1]; ring

theorem ising_eq_offDiag_add_diag [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising J h x = ising (J - Matrix.diagonal J.diag) h x + ∑ i, J i i := by
  have hsplit : ising J h x =
      ising (J - Matrix.diagonal J.diag) (h - 0) x + ising (Matrix.diagonal J.diag) 0 x := by
    rw [← ising_add]
    simp
  rw [hsplit, sub_zero, ising_diagonal]
  simp

/-! ### Parameter invariance -/

private theorem qubo_indicator_single [DecidableEq ι] (Q : Matrix ι ι ℝ) (a : ι) :
    qubo Q (fun k ↦ decide (k = a)) = Q a a := by
  simp [qubo_def, bit_def]

private theorem qubo_indicator_pair [DecidableEq ι] (Q : Matrix ι ι ℝ) {i j : ι} (hij : i ≠ j) :
    qubo Q (fun k ↦ decide (k = i ∨ k = j)) = Q i i + Q j j + (Q i j + Q j i) := by
  simp only [qubo_def, bit_def, decide_eq_true_eq]
  have hsum (f : ι → ℝ) : (∑ k, if k = i ∨ k = j then f k else 0) = f i + f j := by
    rw [← Finset.sum_filter,
      show Finset.univ.filter (fun k ↦ k = i ∨ k = j) = {i, j} by ext k; simp]
    exact Finset.sum_pair hij
  have hinner (a : ι) :
      (∑ b, Q a b * (if a = i ∨ a = j then (1 : ℝ) else 0) * if b = i ∨ b = j then 1 else 0) =
        if a = i ∨ a = j then Q a i + Q a j else 0 := by
    by_cases ha : a = i ∨ a = j
    · simp only [ha, ↓reduceIte, mul_one]
      simpa only [mul_ite, mul_one, mul_zero] using hsum (fun b ↦ Q a b)
    · simp [ha]
  simp_rw [hinner]
  rw [hsum fun a ↦ Q a i + Q a j]
  ring

/-- `qubo Q₁ = qubo Q₂` holds if and only if `Q₁ + Q₁ᵀ = Q₂ + Q₂ᵀ`. -/
theorem qubo_eq_qubo_iff (Q₁ Q₂ : Matrix ι ι ℝ) :
    qubo Q₁ = qubo Q₂ ↔ Q₁ + Q₁ᵀ = Q₂ + Q₂ᵀ := by
  classical
  constructor
  · intro hfun
    have hdiag (a : ι) : Q₁ a a = Q₂ a a := by
      simpa [qubo_indicator_single] using congrFun hfun (fun k ↦ decide (k = a))
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.add_apply, Matrix.transpose_apply, hdiag i]
    · have hpair :
          qubo Q₁ (fun k ↦ decide (k = i ∨ k = j)) = qubo Q₂ (fun k ↦ decide (k = i ∨ k = j)) :=
        congrFun hfun _
      rw [qubo_indicator_pair Q₁ hij, qubo_indicator_pair Q₂ hij, hdiag i, hdiag j] at hpair
      simp only [Matrix.add_apply, Matrix.transpose_apply]
      linarith
  · intro hsum
    ext x
    have hmul := congrArg (fun M ↦ qubo M x) hsum
    rw [qubo_add_transpose, qubo_add_transpose] at hmul
    linarith

theorem ising_eq_of_offDiag_add_transpose_eq {J₁ J₂ : Matrix ι ι ℝ} {h₁ h₂ : ι → ℝ}
    (hh : h₁ = h₂) (hJ : ∀ i j, i ≠ j → J₁ i j + J₁ j i = J₂ i j + J₂ j i) (x : ι → Bool) :
    ising J₁ h₁ x - ∑ i, J₁ i i = ising J₂ h₂ x - ∑ i, J₂ i i := by
  classical
  have hdiff (J : Matrix ι ι ℝ) (h : ι → ℝ) :
      ising J h x - ∑ i, J i i = ising ((1 / 2 : ℝ) • (J - Matrix.diagonal J.diag +
        (J - Matrix.diagonal J.diag)ᵀ)) h x := by
    rw [ising_symmetrize, sub_eq_iff_eq_add.mpr (ising_eq_offDiag_add_diag J h x)]
  rw [hdiff J₁ h₁, hdiff J₂ h₂, hh]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, hJ i j hij]

private theorem ising_alternating_pair [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    {i j : ι} (hij : i ≠ j) :
    ising J h (fun _ ↦ false) - ising J h (fun k ↦ decide (k = i)) -
        ising J h (fun k ↦ decide (k = j)) + ising J h (fun k ↦ decide (k = i ∨ k = j)) =
      4 * (J i j + J j i) := by
  let y₀ : ι → Bool := fun _ ↦ false
  let yi : ι → Bool := fun k ↦ decide (k = i)
  let yj : ι → Bool := fun k ↦ decide (k = j)
  let yij : ι → Bool := fun k ↦ decide (k = i ∨ k = j)
  have hlin :
      (∑ k, h k * spin y₀ k) - (∑ k, h k * spin yi k) - (∑ k, h k * spin yj k) +
          (∑ k, h k * spin yij k) = 0 := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [y₀, yi, yj, yij, spin_def, hki, hkj, hij, hij.symm]
  have hterm (a b : ι) :
      J a b * spin y₀ a * spin y₀ b - J a b * spin yi a * spin yi b -
          J a b * spin yj a * spin yj b + J a b * spin yij a * spin yij b =
        if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 4 * J a b else 0 := by
    by_cases hai : a = i <;> by_cases haj : a = j <;>
      by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp [y₀, yi, yj, yij, hai, haj, hbi, hbj, hij, hij.symm, spin_def] <;> ring
  have hq :
      (∑ a, ∑ b, J a b * spin y₀ a * spin y₀ b) - (∑ a, ∑ b, J a b * spin yi a * spin yi b) -
          (∑ a, ∑ b, J a b * spin yj a * spin yj b) +
          (∑ a, ∑ b, J a b * spin yij a * spin yij b) =
        4 * (J i j + J j i) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, hterm]
    rw [Finset.sum_eq_add i j hij]
    · rw [Finset.sum_eq_single j (fun b _ hbj ↦ by simp [hij, hbj]) (by simp),
        Finset.sum_eq_single i (fun b _ hbi ↦ by simp [hij.symm, hbi]) (by simp)]
      simp [hij, hij.symm]
      ring
    · intro a _ hai
      exact Finset.sum_eq_zero fun b _ ↦ by simp [hai.1, hai.2]
    · simp
    · simp
  simp only [ising_def]
  linarith

/-- Two Ising models agree up to their diagonal constants if and only if they have the same
external fields and the same symmetrized off-diagonal couplings. -/
theorem ising_sub_diag_eq_iff (J₁ J₂ : Matrix ι ι ℝ) (h₁ h₂ : ι → ℝ) :
    (∀ x, ising J₁ h₁ x - ∑ i, J₁ i i = ising J₂ h₂ x - ∑ i, J₂ i i) ↔
      h₁ = h₂ ∧ ∀ i j, i ≠ j → J₁ i j + J₁ j i = J₂ i j + J₂ j i := by
  classical
  constructor
  · intro heq
    have hfield_eq (x : ι → Bool) : ∑ i, h₁ i * spin x i = ∑ i, h₂ i * spin x i := by
      have hflip (J : Matrix ι ι ℝ) (h : ι → ℝ) :
          ising J h x - ising J h (fun k ↦ !x k) = 2 * ∑ i, h i * spin x i := by
        rw [ising_not]
        simp only [ising_def, Pi.neg_apply]
        have hsum : (∑ i, (-h i) * spin x i) = -∑ i, h i * spin x i := by
          simp [neg_mul, sum_neg_distrib]
        linarith
      have h1 := heq x
      have h2 := heq (fun k ↦ !x k)
      have hl := hflip J₁ h₁
      have hr := hflip J₂ h₂
      linarith
    have hh : h₁ = h₂ := by
      ext i
      let x₀ : ι → Bool := fun _ ↦ false
      let x₁ : ι → Bool := fun k ↦ decide (k = i)
      have hd₁ := hfield_eq x₀
      have hd₂ := hfield_eq x₁
      have hdiff (h : ι → ℝ) : (∑ k, h k * spin x₀ k) - (∑ k, h k * spin x₁ k) = 2 * h i := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · simp [x₀, x₁, spin_def]; ring
        · intro k _ hki
          simp [x₀, x₁, spin_def, hki]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      have ha := hdiff h₁
      have hb := hdiff h₂
      linarith
    refine ⟨hh, fun i j hij ↦ ?_⟩
    have hc₁ := ising_alternating_pair J₁ h₁ hij
    have hc₂ := ising_alternating_pair J₂ h₂ hij
    have e0 := heq (fun _ ↦ false)
    have ei := heq (fun k ↦ decide (k = i))
    have ej := heq (fun k ↦ decide (k = j))
    have eij := heq (fun k ↦ decide (k = i ∨ k = j))
    linarith
  · rintro ⟨hh, hJ⟩ x
    exact ising_eq_of_offDiag_add_transpose_eq hh hJ x

/-! ### Equivalence between QUBO and Ising models -/

/-- Every quadratic pseudo-Boolean function is an Ising energy plus an explicit constant. -/
theorem qubo_eq_ising (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    qubo Q x = ising ((1 / 4 : ℝ) • Q) (fun i ↦ -(∑ j, (Q i j + Q j i)) / 4) x +
      (∑ i, ∑ j, Q i j) / 4 := by
  simp only [qubo_def, ising_def, Matrix.smul_apply, smul_eq_mul, bit_eq_one_sub_spin_div_two]
  have h1 :
      (∑ i, ∑ j, Q i j * ((1 - spin x i) / 2) * ((1 - spin x j) / 2)) =
        (∑ i, ∑ j, (1 / 4 * Q i j) * spin x i * spin x j) -
          (∑ i, ∑ j, Q i j * spin x i / 4) - (∑ i, ∑ j, Q i j * spin x j / 4) +
          (∑ i, ∑ j, Q i j) / 4 := by
    simp only [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h2 :
      (∑ i, -(∑ j, (Q i j + Q j i)) / 4 * spin x i) =
        -(∑ i, ∑ j, Q i j * spin x i / 4) - (∑ i, ∑ j, Q i j * spin x j / 4) := by
    have hswap : (∑ i, ∑ j, Q i j * spin x j / 4) = ∑ i, ∑ j, Q j i * spin x i / 4 :=
      Finset.sum_comm
    rw [hswap]
    have hrow (i : ι) :
        -(∑ j, (Q i j + Q j i)) / 4 * spin x i =
          -(∑ j, Q i j * spin x i / 4) - ∑ j, Q j i * spin x i / 4 := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
      ring
    simp_rw [hrow, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [h1, h2]
  ring

/-- Every Ising energy is a quadratic pseudo-Boolean function plus an explicit constant. -/
theorem ising_eq_qubo [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising J h x =
      qubo ((4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)) x +
        (∑ i, ∑ j, J i j + ∑ i, h i) := by
  rw [qubo_sub, qubo_smul, qubo_diagonal]
  simp only [ising_def, qubo_def, spin_eq_one_sub_two_mul_bit]
  have hquad :
      (∑ i, ∑ j, J i j * (1 - 2 * bit x i) * (1 - 2 * bit x j)) =
        4 * (∑ i, ∑ j, J i j * bit x i * bit x j) -
          2 * (∑ i, ∑ j, J i j * bit x i) - 2 * (∑ i, ∑ j, J i j * bit x j) +
          ∑ i, ∑ j, J i j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hlin : (∑ i, h i * (1 - 2 * bit x i)) = ∑ i, h i - 2 * ∑ i, h i * bit x i := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hdiag :
      (∑ i, 2 * (∑ j, (J i j + J j i) + h i) * bit x i) =
        2 * (∑ i, ∑ j, J i j * bit x i) + 2 * (∑ i, ∑ j, J i j * bit x j) +
          2 * ∑ i, h i * bit x i := by
    have hswap : (∑ i, ∑ j, J i j * bit x j) = ∑ i, ∑ j, J j i * bit x i := Finset.sum_comm
    rw [hswap]
    have hrow (i : ι) :
        2 * (∑ j, (J i j + J j i) + h i) * bit x i =
          2 * (∑ j, J i j * bit x i) + 2 * (∑ j, J j i * bit x i) + 2 * (h i * bit x i) := by
      have hsum : (∑ j, (J i j + J j i)) = (∑ j, J i j) + ∑ j, J j i := Finset.sum_add_distrib
      rw [hsum, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    simp_rw [hrow, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hquad, hlin, hdiag]
  ring

theorem isMinOn_qubo_iff_isMinOn_ising (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    IsMinOn (qubo Q) Set.univ x ↔
      IsMinOn (ising ((1 / 4 : ℝ) • Q) fun i ↦ -(∑ j, (Q i j + Q j i)) / 4) Set.univ x := by
  simp only [isMinOn_univ_iff]
  refine forall_congr' fun y ↦ ?_
  rw [qubo_eq_ising Q x, qubo_eq_ising Q y, add_le_add_iff_right]

theorem isMinOn_ising_iff_isMinOn_qubo [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    (x : ι → Bool) :
    IsMinOn (ising J h) Set.univ x ↔
      IsMinOn (qubo ((4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)))
        Set.univ x := by
  simp only [isMinOn_univ_iff]
  refine forall_congr' fun y ↦ ?_
  rw [ising_eq_qubo J h x, ising_eq_qubo J h y, add_le_add_iff_right]

theorem iInf_qubo_eq_iInf_ising_add (Q : Matrix ι ι ℝ) :
    ⨅ x, qubo Q x =
      (⨅ x, ising ((1 / 4 : ℝ) • Q) (fun i ↦ -(∑ j, (Q i j + Q j i)) / 4) x) +
        (∑ i, ∑ j, Q i j) / 4 := by
  have hb : BddBelow (Set.range fun x : ι → Bool ↦
      ising ((1 / 4 : ℝ) • Q) (fun i ↦ -(∑ j, (Q i j + Q j i)) / 4) x) :=
    Set.Finite.bddBelow (Set.finite_range _)
  rw [ciInf_add hb]
  exact iInf_congr fun x ↦ qubo_eq_ising Q x

theorem iInf_ising_eq_iInf_qubo_add [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) :
    ⨅ x, ising J h x =
      (⨅ x, qubo ((4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)) x) +
        (∑ i, ∑ j, J i j + ∑ i, h i) := by
  have hb : BddBelow (Set.range fun x : ι → Bool ↦
      qubo ((4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)) x) :=
    Set.Finite.bddBelow (Set.finite_range _)
  rw [ciInf_add hb]
  exact iInf_congr fun x ↦ ising_eq_qubo J h x

end QuboIsing

/-! ### Multilinear expansion of pseudo-Boolean functions -/

section Multilinear

variable {ι : Type*}

/-- The unique coefficient of `∏ i ∈ S, bit x i` in the multilinear expansion of
`f : (ι → Bool) → ℝ`, given by Möbius inversion on the Boolean cube. -/
def pseudoBoolCoeff [DecidableEq ι] (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * f fun i ↦ decide (i ∈ T)

theorem pseudoBoolCoeff_def [DecidableEq ι] (f : (ι → Bool) → ℝ) (S : Finset ι) :
    pseudoBoolCoeff f S =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * f fun i ↦ decide (i ∈ T) :=
  (rfl)

private theorem prod_bit_eq_ite [Fintype ι] [DecidableEq ι] (x : ι → Bool) (S : Finset ι) :
    (∏ i ∈ S, bit x i) = if S ⊆ Finset.univ.filter (fun i ↦ x i = true) then 1 else 0 := by
  split_ifs with hS
  · exact Finset.prod_eq_one fun i hi ↦ bit_eq_one_iff.mpr (Finset.mem_filter.mp (hS hi)).2
  · rw [Finset.not_subset] at hS
    obtain ⟨i, hiS, hiU⟩ := hS
    have hxi : x i = false := by
      cases h : x i
      · rfl
      · exact False.elim (hiU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    exact Finset.prod_eq_zero hiS (bit_eq_zero_iff.mpr hxi)

private theorem sum_powerset_filter_neg_one_pow_card [DecidableEq ι] {T U : Finset ι}
    (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset with T ⊆ S, (-1 : ℝ) ^ (S.card - T.card)) = if T = U then 1 else 0 := by
  have hbij :
      (∑ S ∈ U.powerset with T ⊆ S, (-1 : ℝ) ^ (S.card - T.card)) =
        ∑ R ∈ (U \ T).powerset, (-1 : ℝ) ^ R.card := by
    refine Finset.sum_bij (fun S _ ↦ S \ T) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      exact Finset.sdiff_subset_sdiff hS.1 le_rfl
    · intro S₁ hS₁ S₂ hS₂ hEq
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
      rw [← Finset.sdiff_union_of_subset hS₁.2, ← Finset.sdiff_union_of_subset hS₂.2, hEq]
    · intro R hR
      rw [Finset.mem_powerset] at hR
      refine ⟨T ∪ R, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset hTU (hR.trans Finset.sdiff_subset), Finset.subset_union_left⟩
      · ext a
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨haT | haR, hnaT⟩
          · exact absurd haT hnaT
          · exact haR
        · intro haR
          exact ⟨Or.inr haR, (Finset.mem_sdiff.mp (hR haR)).2⟩
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      rw [Finset.card_sdiff_of_subset hS.2]
  rw [hbij]
  have hcast :
      (∑ R ∈ (U \ T).powerset, (-1 : ℝ) ^ R.card) =
        ((∑ R ∈ (U \ T).powerset, (-1 : ℤ) ^ R.card : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hcast, Finset.sum_powerset_neg_one_pow_card]
  simp_rw [Finset.sdiff_eq_empty_iff_subset]
  by_cases hUT : U ⊆ T
  · have hEq : T = U := Finset.Subset.antisymm hTU hUT
    simp [hEq]
  · have hNe : T ≠ U := fun h ↦ hUT (h ▸ le_rfl)
    simp [hUT, hNe]

/-- Every pseudo-Boolean function `f : (ι → Bool) → ℝ` is represented by its multilinear expansion
`∑ S, pseudoBoolCoeff f S * ∏ i ∈ S, bit x i`. -/
theorem sum_pseudoBoolCoeff_mul_prod_bit [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (x : ι → Bool) :
    ∑ S : Finset ι, pseudoBoolCoeff f S * ∏ i ∈ S, bit x i = f x := by
  let U : Finset ι := Finset.univ.filter fun i ↦ x i = true
  have hxU : (fun i ↦ decide (i ∈ U)) = x := by
    ext i
    simp [U]
  simp_rw [prod_bit_eq_ite, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  have hfilt : (Finset.univ.filter fun S : Finset ι ↦ S ⊆ U) = U.powerset := by
    ext S
    simp
  rw [hfilt]
  simp_rw [pseudoBoolCoeff_def]
  have hswap :
      (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - T.card) * f fun i ↦ decide (i ∈ T)) =
        ∑ T ∈ U.powerset, (∑ S ∈ U.powerset with T ⊆ S, (-1 : ℝ) ^ (S.card - T.card)) *
          f fun i ↦ decide (i ∈ T) := by
    simp_rw [Finset.sum_mul]
    refine Finset.sum_comm' (t' := U.powerset) (s' := fun T ↦ U.powerset.filter (T ⊆ ·)) ?_
    intro S T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun ⟨hSU, hTS⟩ ↦ ⟨⟨hSU, hTS⟩, hTS.trans hSU⟩,
      fun ⟨⟨hSU, hTS⟩, _⟩ ↦ ⟨hSU, hTS⟩⟩
  rw [hswap]
  have hcongr :
      ∑ T ∈ U.powerset,
          (∑ S ∈ U.powerset with T ⊆ S, (-1 : ℝ) ^ (S.card - T.card)) *
            f (fun i ↦ decide (i ∈ T)) =
        ∑ T ∈ U.powerset, (if T = U then 1 else 0) * f (fun i ↦ decide (i ∈ T)) :=
    Finset.sum_congr rfl fun T hT ↦ by
      rw [sum_powerset_filter_neg_one_pow_card (Finset.mem_powerset.mp hT)]
  rw [hcongr]
  simp [hxU]

private theorem sum_prod_bit_eq_zero_imp [Fintype ι] {d : Finset ι → ℝ}
    (hd : ∀ x, ∑ S : Finset ι, d S * ∏ i ∈ S, bit x i = 0) :
    ∀ S : Finset ι, d S = 0 := by
  classical
  intro S
  have hstrong : ∀ n : ℕ, ∀ T : Finset ι, T.card = n → d T = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro T hTn
      let xT : ι → Bool := fun i ↦ decide (i ∈ T)
      have hxT_supp : Finset.univ.filter (fun i ↦ xT i = true) = T := by
        ext i
        simp [xT]
      have hsum := hd xT
      simp_rw [prod_bit_eq_ite, hxT_supp, mul_ite, mul_one, mul_zero, ← Finset.sum_filter] at hsum
      have hfilt : (Finset.univ.filter fun S : Finset ι ↦ S ⊆ T) = T.powerset := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
      rw [hfilt, ← Finset.insert_erase (Finset.mem_powerset_self T),
        Finset.sum_insert (Finset.notMem_erase T _)] at hsum
      have hrest : ∑ S ∈ T.powerset.erase T, d S = 0 := by
        refine Finset.sum_eq_zero fun S hS ↦ ?_
        obtain ⟨hSne, hST⟩ := Finset.mem_erase.mp hS
        have hSsub : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hST, hSne⟩
        exact ih S.card (hTn ▸ Finset.card_lt_card hSsub) S rfl
      linarith
  exact hstrong S.card S rfl

/-- Every pseudo-Boolean function `f : (ι → Bool) → ℝ` has a unique multilinear expansion
`f x = ∑ S, c S * ∏ i ∈ S, bit x i` over subsets `S : Finset ι`. -/
theorem existsUnique_sum_prod_bit [Fintype ι] (f : (ι → Bool) → ℝ) :
    ∃! c : Finset ι → ℝ, ∀ x, f x = ∑ S : Finset ι, c S * ∏ i ∈ S, bit x i := by
  classical
  refine ⟨pseudoBoolCoeff f, fun x ↦ (sum_pseudoBoolCoeff_mul_prod_bit f x).symm, fun c hc ↦ ?_⟩
  ext S
  have hdiff : ∀ x, ∑ T : Finset ι, (c T - pseudoBoolCoeff f T) * ∏ i ∈ T, bit x i = 0 := by
    intro x
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← hc x, sum_pseudoBoolCoeff_mul_prod_bit, sub_self]
  exact sub_eq_zero.mp (sum_prod_bit_eq_zero_imp hdiff S)

private theorem sum_powersetCard_two_mul_prod_bit [Fintype ι] [DecidableEq ι] {d : Finset ι → ℝ}
    {Q : Matrix ι ι ℝ} (hd2 : ∀ i j, i ≠ j → d {i, j} = Q i j + Q j i) (x : ι → Bool) :
    (∑ S ∈ (Finset.univ : Finset ι).powersetCard 2, d S * ∏ k ∈ S, bit x k) =
      ∑ i, ∑ j with i ≠ j, Q i j * bit x i * bit x j := by
  have hrhs :
      (∑ i, ∑ j with i ≠ j, Q i j * bit x i * bit x j) =
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : ι × ι ↦ p.1 ≠ p.2),
          Q p.1 p.2 * bit x p.1 * bit x p.2 := by
    simp only [Finset.sum_filter, Finset.univ_product_univ, Fintype.sum_prod_type]
  rw [hrhs, ← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ ×ˢ Finset.univ).filter (fun p : ι × ι ↦ p.1 ≠ p.2))
    (t := (Finset.univ : Finset ι).powersetCard 2)
    (g := fun p : ι × ι ↦ ({p.1, p.2} : Finset ι))
    (f := fun p : ι × ι ↦ Q p.1 p.2 * bit x p.1 * bit x p.2)
    (fun p hp ↦ Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, Finset.card_pair (Finset.mem_filter.mp hp).2⟩)]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  obtain ⟨_, hScard⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hScard
  have hfib :
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : ι × ι ↦ p.1 ≠ p.2)).filter
          (fun p : ι × ι ↦ ({p.1, p.2} : Finset ι) = {a, b}) =
        {(a, b), (b, a)} := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Finset.Subset.antisymm_iff,
      Finset.subset_iff]
    constructor
    · rintro ⟨_, h1, _⟩
      have hu : u = a ∨ u = b := h1 (Or.inl rfl)
      have hv : v = a ∨ v = b := h1 (Or.inr rfl)
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hab, fun z hz ↦ by simp_all, fun z hz ↦ by simp_all⟩
      · exact ⟨hab.symm, fun z hz ↦ by simp_all [or_comm], fun z hz ↦ by simp_all [or_comm]⟩
  rw [hfib, Finset.sum_pair (by simp [hab]), hd2 a b hab, Finset.prod_pair hab]
  ring

private theorem qubo_eq_diag_add_offDiag [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ)
    (x : ι → Bool) :
    qubo Q x = (∑ i, Q i i * bit x i) + ∑ i, ∑ j with i ≠ j, Q i j * bit x i * bit x j := by
  simp only [qubo_def]
  have hrow (i : ι) :
      (∑ j, Q i j * bit x i * bit x j) =
        Q i i * bit x i + ∑ j with i ≠ j, Q i j * bit x i * bit x j := by
    rw [← Finset.add_sum_erase Finset.univ (fun j ↦ Q i j * bit x i * bit x j)
      (Finset.mem_univ i), mul_assoc, bit_mul_bit]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext j
    simp [ne_comm]
  simp_rw [hrow, Finset.sum_add_distrib]

private theorem sum_prod_bit_eq_qubo_add_const [Fintype ι] [DecidableEq ι] {d : Finset ι → ℝ}
    {Q : Matrix ι ι ℝ} {c₀ : ℝ}
    (hd0 : d ∅ = c₀)
    (hd1 : ∀ i, d {i} = Q i i)
    (hd2 : ∀ i j, i ≠ j → d {i, j} = Q i j + Q j i)
    (hd3 : ∀ S, 2 < S.card → d S = 0)
    (x : ι → Bool) :
    ∑ S : Finset ι, d S * ∏ i ∈ S, bit x i = qubo Q x + c₀ := by
  have hle :
      (∑ S : Finset ι, d S * ∏ k ∈ S, bit x k) =
        ∑ S ∈ Finset.univ with S.card ≤ 2, d S * ∏ k ∈ S, bit x k := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun S : Finset ι ↦ S.card ≤ 2)]
    have hzero : (∑ S ∈ Finset.univ with ¬S.card ≤ 2, d S * ∏ k ∈ S, bit x k) = 0 :=
      Finset.sum_eq_zero fun S hS ↦ by
        simp [hd3 S (Nat.lt_of_not_le (Finset.mem_filter.mp hS).2)]
    rw [hzero, add_zero]
  have hpart :
      Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ 2) =
        insert ∅ ((Finset.univ : Finset ι).powersetCard 1 ∪
          (Finset.univ : Finset ι).powersetCard 2) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_union, Finset.mem_powersetCard, Finset.subset_univ, ← Finset.card_eq_zero]
    omega
  have hdisj : Disjoint ((Finset.univ : Finset ι).powersetCard 1)
      ((Finset.univ : Finset ι).powersetCard 2) := by
    rw [Finset.disjoint_left]
    intro S h1 h2
    have c1 := (Finset.mem_powersetCard.mp h1).2
    have c2 := (Finset.mem_powersetCard.mp h2).2
    omega
  have h1 :
      (∑ S ∈ (Finset.univ : Finset ι).powersetCard 1, d S * ∏ k ∈ S, bit x k) =
        ∑ i, Q i i * bit x i := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [hd1 i]
  rw [hle, hpart, Finset.sum_insert (by simp [Finset.mem_powersetCard]), Finset.sum_union hdisj]
  simp only [Finset.prod_empty, mul_one]
  rw [hd0, h1, sum_powersetCard_two_mul_prod_bit hd2 x, qubo_eq_diag_add_offDiag]
  ring

/-- A pseudo-Boolean function with multilinear expansion `f x = ∑ S, c S * ∏ i ∈ S, bit x i` is of
the form `qubo Q + const` if and only if `c S = 0` for all subsets `S` with `2 < S.card`. -/
theorem exists_qubo_add_const_iff [Fintype ι] {f : (ι → Bool) → ℝ} {c : Finset ι → ℝ}
    (hf : ∀ x, f x = ∑ S : Finset ι, c S * ∏ i ∈ S, bit x i) :
    (∃ (Q : Matrix ι ι ℝ) (c₀ : ℝ), ∀ x, f x = qubo Q x + c₀) ↔
      ∀ S : Finset ι, 2 < S.card → c S = 0 := by
  classical
  constructor
  · rintro ⟨Q, c₀, hQ⟩ S hS
    let d : Finset ι → ℝ := fun T ↦
      match T.card with
      | 0 => c₀
      | 1 => ∑ i ∈ T, Q i i
      | 2 => ∑ i ∈ T, ∑ j ∈ T with i ≠ j, Q i j
      | _ => 0
    have hd0 : d ∅ = c₀ := by simp [d]
    have hd1 (i : ι) : d {i} = Q i i := by simp [d]
    have hd2 (i j : ι) (hij : i ≠ j) : d {i, j} = Q i j + Q j i := by
      simp only [d, Finset.card_pair hij, Finset.sum_pair hij]
      have hfi : ({i, j} : Finset ι).filter (fun k ↦ i ≠ k) = {j} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨hk, hne⟩ ↦ hk.resolve_left hne.symm, fun hk ↦ ⟨Or.inr hk, hk ▸ hij⟩⟩
      have hfj : ({i, j} : Finset ι).filter (fun k ↦ j ≠ k) = {i} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨hk, hne⟩ ↦ hk.resolve_right hne.symm,
          fun hk ↦ ⟨Or.inl hk, hk ▸ hij.symm⟩⟩
      rw [hfi, hfj, Finset.sum_singleton, Finset.sum_singleton]
    have hd3 (T : Finset ι) (hT : 2 < T.card) : d T = 0 := by
      rcases hcard : T.card with _ | _ | _ | k
      · omega
      · omega
      · omega
      · simp [d, hcard]
    have hfd : ∀ x, f x = ∑ T : Finset ι, d T * ∏ i ∈ T, bit x i := fun x ↦ by
      rw [hQ x, sum_prod_bit_eq_qubo_add_const hd0 hd1 hd2 hd3 x]
    rw [(existsUnique_sum_prod_bit f).unique hf hfd]
    exact hd3 S hS
  · intro hdeg
    let Q : Matrix ι ι ℝ := Matrix.of fun i j ↦ if i = j then c {i} else c {i, j} / 2
    refine ⟨Q, c ∅, fun x ↦ ?_⟩
    rw [hf x]
    refine sum_prod_bit_eq_qubo_add_const rfl (fun i ↦ by simp [Q]) (fun i j hij ↦ ?_) hdeg x
    simp only [Q, Matrix.of_apply, hij, hij.symm, ↓reduceIte, Finset.pair_comm j i]
    ring

end Multilinear

end TauCeti
