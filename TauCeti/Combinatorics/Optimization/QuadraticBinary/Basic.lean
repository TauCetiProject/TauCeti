/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Data.Finset.Basic
import TauCeti.Order.Filter.Extr

/-!
# Quadratic pseudo-Boolean functions and Ising energies

Optimization problems over binary configurations `x : ι → Bool` are commonly formulated in two
equivalent quadratic representations:

* `TauCeti.qubo`: the quadratic pseudo-Boolean function `∑ i, ∑ j, Q i j * bit x i * bit x j`
  in `{0, 1}` variables `bit x i`;
* `TauCeti.ising`: the Ising energy `∑ i, ∑ j, J i j * spin x i * spin x j + ∑ i, h i * spin x i`
  in `{±1}` spin variables `spin x i = 1 - 2 * bit x i`.

Because `bit x i ^ 2 = bit x i`, the diagonal of `Q` carries linear terms in `qubo Q`, whereas
because `spin x i ^ 2 = 1`, the diagonal of `J` contributes only a constant `J.trace` to
`ising J h`. We establish exact algebraic conversions between `qubo` and `ising`, minimizer and
infimum equivalences, and exact parameter-invariance criteria (`TauCeti.qubo_eq_qubo_iff` and
`TauCeti.ising_sub_trace_eq_iff`).

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
* `TauCeti.qubo_eq_qubo_iff`, `TauCeti.ising_sub_trace_eq_iff`: exact parameter invariance.
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
theorem bit_of_true {x : ι → Bool} {i : ι} (h : x i = true) : bit x i = 1 := by
  simp [bit_def, h]

@[simp]
theorem bit_of_false {x : ι → Bool} {i : ι} (h : x i = false) : bit x i = 0 := by
  simp [bit_def, h]

@[simp]
theorem spin_of_true {x : ι → Bool} {i : ι} (h : x i = true) : spin x i = -1 := by
  simp [spin_def, h]

@[simp]
theorem spin_of_false {x : ι → Bool} {i : ι} (h : x i = false) : spin x i = 1 := by
  simp [spin_def, h]

@[simp]
theorem bit_eq_one_iff {x : ι → Bool} {i : ι} : bit x i = 1 ↔ x i = true := by
  cases h : x i <;> simp [h]

@[simp]
theorem bit_eq_zero_iff {x : ι → Bool} {i : ι} : bit x i = 0 ↔ x i = false := by
  cases h : x i <;> simp [h]

@[simp]
theorem spin_eq_neg_one_iff {x : ι → Bool} {i : ι} : spin x i = -1 ↔ x i = true := by
  cases h : x i <;> norm_num [h]

@[simp]
theorem spin_eq_one_iff {x : ι → Bool} {i : ι} : spin x i = 1 ↔ x i = false := by
  cases h : x i <;> norm_num [h]

theorem bit_nonneg (x : ι → Bool) (i : ι) : 0 ≤ bit x i := by
  cases h : x i <;> simp [h]

theorem bit_le_one (x : ι → Bool) (i : ι) : bit x i ≤ 1 := by
  cases h : x i <;> simp [h]

@[simp]
theorem bit_mul_bit (x : ι → Bool) (i : ι) : bit x i * bit x i = bit x i := by
  cases h : x i <;> simp [h]

@[simp]
theorem bit_sq (x : ι → Bool) (i : ι) : bit x i ^ 2 = bit x i := by
  rw [sq, bit_mul_bit]

@[simp]
theorem spin_mul_spin (x : ι → Bool) (i : ι) : spin x i * spin x i = 1 := by
  cases h : x i <;> simp [h]

@[simp]
theorem spin_sq (x : ι → Bool) (i : ι) : spin x i ^ 2 = 1 := by
  rw [sq, spin_mul_spin]

theorem abs_spin (x : ι → Bool) (i : ι) : |spin x i| = 1 := by
  cases h : x i <;> simp [h]

theorem spin_eq_one_sub_two_mul_bit (x : ι → Bool) (i : ι) : spin x i = 1 - 2 * bit x i := by
  cases h : x i <;> norm_num [h]

theorem bit_eq_one_sub_spin_div_two (x : ι → Bool) (i : ι) : bit x i = (1 - spin x i) / 2 := by
  cases h : x i <;> norm_num [h]

@[simp]
theorem bit_not (x : ι → Bool) (i : ι) : bit (fun j ↦ !x j) i = 1 - bit x i := by
  cases h : x i <;> norm_num [h]

@[simp]
theorem spin_not (x : ι → Bool) (i : ι) : spin (fun j ↦ !x j) i = -spin x i := by
  cases h : x i <;> norm_num [h]

@[simp]
theorem spin_xor (x y : ι → Bool) (i : ι) :
    spin (fun j ↦ xor (x j) (y j)) i = spin x i * spin y i := by
  cases hx : x i <;> cases hy : y i <;> norm_num [hx, hy]

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

/-- Flipping all spins reverses the external field, so `ising J h x - ising J h (fun i ↦ !x i)`
equals `2 * ∑ i, h i * spin x i`. -/
theorem ising_sub_ising_not (J : Matrix ι ι ℝ) (h : ι → ℝ) (x : ι → Bool) :
    ising J h x - ising J h (fun i ↦ !x i) = 2 * ∑ i, h i * spin x i := by
  rw [ising_not]
  simp only [ising_def, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
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

theorem ising_eq_ising_sub_diagonal_add_trace [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    (x : ι → Bool) :
    ising J h x = ising (J - Matrix.diagonal J.diag) h x + J.trace := by
  have hsplit : ising J h x =
      ising (J - Matrix.diagonal J.diag) (h - 0) x + ising (Matrix.diagonal J.diag) 0 x := by
    rw [← ising_add]
    simp
  rw [hsplit, sub_zero, ising_diagonal]
  simp [Matrix.trace]

/-! ### Parameter invariance -/

private theorem qubo_indicator_single [DecidableEq ι] (Q : Matrix ι ι ℝ) (a : ι) :
    qubo Q (fun k ↦ decide (k = a)) = Q a a := by
  rw [qubo_def, Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single a]
    · simp
    · intro j hj
      simp [hj]
  · intro i hi
    simp [hi]

private theorem qubo_indicator_pair [DecidableEq ι] (Q : Matrix ι ι ℝ) {i j : ι} (hij : i ≠ j) :
    qubo Q (fun k ↦ decide (k = i ∨ k = j)) = Q i i + Q j j + (Q i j + Q j i) := by
  rw [qubo_def]
  have hbit (k : ι) : bit (fun m ↦ decide (m = i ∨ m = j)) k = if k = i ∨ k = j then 1 else 0 := by
    by_cases hk : k = i ∨ k = j
    · simp [hk]
    · obtain ⟨h1, h2⟩ := not_or.mp hk
      simp [h1, h2]
  simp_rw [hbit]
  have hsum (f : ι → ℝ) : (∑ k, if k = i ∨ k = j then f k else 0) = f i + f j := by
    have hfilt : Finset.univ.filter (fun k ↦ k = i ∨ k = j) = {i, j} := by
      ext k
      simp
    rw [← Finset.sum_filter, hfilt, Finset.sum_pair hij]
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

/-- Two Ising models with the same external field and the same symmetrized off-diagonal couplings
agree up to their trace constants. -/
theorem ising_sub_trace_eq_of_offDiag_add_transpose_eq {J₁ J₂ : Matrix ι ι ℝ}
    (hJ : ∀ i j, i ≠ j → J₁ i j + J₁ j i = J₂ i j + J₂ j i) (h : ι → ℝ) (x : ι → Bool) :
    ising J₁ h x - J₁.trace = ising J₂ h x - J₂.trace := by
  classical
  have hdiff (J : Matrix ι ι ℝ) :
      ising J h x - J.trace = ising ((1 / 2 : ℝ) • (J - Matrix.diagonal J.diag +
        (J - Matrix.diagonal J.diag)ᵀ)) h x := by
    rw [ising_symmetrize, sub_eq_iff_eq_add.mpr (ising_eq_ising_sub_diagonal_add_trace J h x)]
  rw [hdiff J₁, hdiff J₂]
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
      simp [y₀, yi, yj, yij, hki, hkj, hij, hij.symm]
  have hterm (a b : ι) :
      J a b * spin y₀ a * spin y₀ b - J a b * spin yi a * spin yi b -
          J a b * spin yj a * spin yj b + J a b * spin yij a * spin yij b =
        if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 4 * J a b else 0 := by
    by_cases hai : a = i <;> by_cases haj : a = j <;>
      by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp only [y₀, yi, yj, yij, hai, haj, hbi, hbj, hij, hij.symm, decide_true, decide_false,
        spin_of_false, spin_of_true, and_true, and_false, or_self, or_true, or_false,
        ↓reduceIte] <;> ring
  have hq :
      (∑ a, ∑ b, J a b * spin y₀ a * spin y₀ b) - (∑ a, ∑ b, J a b * spin yi a * spin yi b) -
          (∑ a, ∑ b, J a b * spin yj a * spin yj b) +
          (∑ a, ∑ b, J a b * spin yij a * spin yij b) =
        4 * (J i j + J j i) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, hterm]
    rw [Finset.sum_eq_add i j hij]
    · rw [Finset.sum_eq_single j (fun b _ hbj ↦ by simp [hij, hbj]) (by simp),
        Finset.sum_eq_single i (fun b _ hbi ↦ by simp [hij.symm, hbi]) (by simp)]
      simp only [hij, hij.symm, and_self, or_false, false_or, ↓reduceIte]
      ring
    · intro a _ hai
      exact Finset.sum_eq_zero fun b _ ↦ by simp [hai.1, hai.2]
    · simp
    · simp
  simp only [ising_def]
  linarith

private theorem eq_of_sum_mul_spin_eq {h₁ h₂ : ι → ℝ}
    (hfield : ∀ x, ∑ i, h₁ i * spin x i = ∑ i, h₂ i * spin x i) : h₁ = h₂ := by
  classical
  ext i
  have hdiff (h : ι → ℝ) :
      (∑ k, h k * spin (fun _ ↦ false) k) -
        (∑ k, h k * spin (fun k ↦ decide (k = i)) k) = 2 * h i := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single i]
    · simp only [decide_true, spin_of_false, spin_of_true]
      ring
    · intro k hki
      simp [hki]
  linarith [hfield (fun _ ↦ false), hfield (fun k ↦ decide (k = i)), hdiff h₁, hdiff h₂]

/-- Two Ising models agree up to their trace constants if and only if they have the same
external fields and the same symmetrized off-diagonal couplings. -/
theorem ising_sub_trace_eq_iff (J₁ J₂ : Matrix ι ι ℝ) (h₁ h₂ : ι → ℝ) :
    (∀ x, ising J₁ h₁ x - J₁.trace = ising J₂ h₂ x - J₂.trace) ↔
      h₁ = h₂ ∧ ∀ i j, i ≠ j → J₁ i j + J₁ j i = J₂ i j + J₂ j i := by
  classical
  constructor
  · intro heq
    have hfield (x : ι → Bool) : ∑ i, h₁ i * spin x i = ∑ i, h₂ i * spin x i := by
      linarith [heq x, heq (fun k ↦ !x k),
        ising_sub_ising_not J₁ h₁ x, ising_sub_ising_not J₂ h₂ x]
    refine ⟨eq_of_sum_mul_spin_eq hfield, fun i j hij ↦ ?_⟩
    linarith [ising_alternating_pair J₁ h₁ hij, ising_alternating_pair J₂ h₂ hij,
      heq (fun _ ↦ false), heq (fun k ↦ decide (k = i)),
      heq (fun k ↦ decide (k = j)), heq (fun k ↦ decide (k = i ∨ k = j))]
  · rintro ⟨rfl, hJ⟩ x
    exact ising_sub_trace_eq_of_offDiag_add_transpose_eq hJ h₁ x

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

/-- Global minimizers of `qubo Q` are the same as global minimizers of its equivalent Ising
model with coupling `(1 / 4 : ℝ) • Q` and external field `fun i ↦ -(∑ j, (Q i j + Q j i)) / 4`.
-/
theorem isMinOn_qubo_iff_isMinOn_ising (Q : Matrix ι ι ℝ) (x : ι → Bool) :
    IsMinOn (qubo Q) Set.univ x ↔
      IsMinOn (ising ((1 / 4 : ℝ) • Q) fun i ↦ -(∑ j, (Q i j + Q j i)) / 4) Set.univ x := by
  rw [funext (qubo_eq_ising Q), isMinOn_add_const]

/-- Global minimizers of `ising J h` are the same as global minimizers of its equivalent QUBO
objective `(4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)`. -/
theorem isMinOn_ising_iff_isMinOn_qubo [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    (x : ι → Bool) :
    IsMinOn (ising J h) Set.univ x ↔
      IsMinOn (qubo ((4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)))
        Set.univ x := by
  rw [funext (ising_eq_qubo J h), isMinOn_add_const]

/-- The global infimum of `qubo Q` equals the global infimum of its equivalent Ising model plus
the additive constant `(∑ i, ∑ j, Q i j) / 4`. -/
theorem iInf_qubo_eq_iInf_ising_add (Q : Matrix ι ι ℝ) :
    ⨅ x, qubo Q x =
      (⨅ x, ising ((1 / 4 : ℝ) • Q) (fun i ↦ -(∑ j, (Q i j + Q j i)) / 4) x) +
        (∑ i, ∑ j, Q i j) / 4 := by
  rw [iInf_congr (qubo_eq_ising Q), ← ciInf_add (Set.Finite.bddBelow (Set.finite_range _))]

/-- The global infimum of `ising J h` equals the global infimum of its equivalent QUBO objective
plus the additive constant `∑ i, ∑ j, J i j + ∑ i, h i`. -/
theorem iInf_ising_eq_iInf_qubo_add [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) :
    ⨅ x, ising J h x =
      (⨅ x, qubo ((4 : ℝ) • J - Matrix.diagonal fun i ↦ 2 * (∑ j, (J i j + J j i) + h i)) x) +
        (∑ i, ∑ j, J i j + ∑ i, h i) := by
  rw [iInf_congr (ising_eq_qubo J h), ← ciInf_add (Set.Finite.bddBelow (Set.finite_range _))]

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

@[simp]
theorem pseudoBoolCoeff_empty [DecidableEq ι] (f : (ι → Bool) → ℝ) :
    pseudoBoolCoeff f ∅ = f fun _ ↦ false := by
  simp [pseudoBoolCoeff_def]

@[simp]
theorem pseudoBoolCoeff_singleton [DecidableEq ι] (f : (ι → Bool) → ℝ) (i : ι) :
    pseudoBoolCoeff f {i} = f (fun j ↦ decide (j = i)) - f fun _ ↦ false := by
  have hpow : ({i} : Finset ι).powerset = {∅, {i}} := by
    ext T
    simp [Finset.subset_singleton_iff]
  rw [pseudoBoolCoeff_def, hpow, Finset.sum_pair (Finset.singleton_nonempty i).ne_empty.symm]
  simp only [Finset.card_empty, Finset.card_singleton, tsub_zero, pow_one, neg_one_mul,
    tsub_self, pow_zero, one_mul, Finset.notMem_empty, decide_false, Finset.mem_singleton]
  ring

@[simp]
theorem pseudoBoolCoeff_zero [DecidableEq ι] (S : Finset ι) :
    pseudoBoolCoeff (0 : (ι → Bool) → ℝ) S = 0 := by
  simp [pseudoBoolCoeff_def]

@[simp]
theorem pseudoBoolCoeff_add [DecidableEq ι] (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    pseudoBoolCoeff (f + g) S = pseudoBoolCoeff f S + pseudoBoolCoeff g S := by
  simp only [pseudoBoolCoeff_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp]
theorem pseudoBoolCoeff_sub [DecidableEq ι] (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    pseudoBoolCoeff (f - g) S = pseudoBoolCoeff f S - pseudoBoolCoeff g S := by
  simp only [pseudoBoolCoeff_def, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

@[simp]
theorem pseudoBoolCoeff_neg [DecidableEq ι] (f : (ι → Bool) → ℝ) (S : Finset ι) :
    pseudoBoolCoeff (-f) S = -pseudoBoolCoeff f S := by
  simp only [pseudoBoolCoeff_def, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

@[simp]
theorem pseudoBoolCoeff_smul [DecidableEq ι] (c : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    pseudoBoolCoeff (c • f) S = c * pseudoBoolCoeff f S := by
  simp only [pseudoBoolCoeff_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  ring

/-- A product of `{0, 1}` bits over a finset `S` equals `1` if every variable in `S` is `true`,
and `0` otherwise. -/
theorem prod_bit_eq_ite (x : ι → Bool) (S : Finset ι) :
    ∏ i ∈ S, bit x i = if ∀ i ∈ S, x i = true then 1 else 0 := by
  simp only [bit_def, Finset.prod_boole]

/-- Summing `d S * ∏ i ∈ S, bit x i` over all subsets `S` restricts to subsets of the true
variables of `x`. -/
theorem sum_mul_prod_bit [Fintype ι] (d : Finset ι → ℝ) (x : ι → Bool) :
    ∑ S : Finset ι, d S * ∏ i ∈ S, bit x i =
      ∑ S ∈ (Finset.univ.filter fun i ↦ x i = true).powerset, d S := by
  simp_rw [prod_bit_eq_ite, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext S
  simp [Finset.subset_iff]

/-- Every pseudo-Boolean function `f : (ι → Bool) → ℝ` is represented by its multilinear expansion
`∑ S, pseudoBoolCoeff f S * ∏ i ∈ S, bit x i`. -/
theorem sum_pseudoBoolCoeff_mul_prod_bit [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (x : ι → Bool) :
    ∑ S : Finset ι, pseudoBoolCoeff f S * ∏ i ∈ S, bit x i = f x := by
  rw [sum_mul_prod_bit]
  set U : Finset ι := Finset.univ.filter fun i ↦ x i = true
  have hxU : (fun i ↦ decide (i ∈ U)) = x := by
    ext i
    simp [U]
  simp_rw [pseudoBoolCoeff_def]
  have hswap :
      (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - T.card) * f fun i ↦ decide (i ∈ T)) =
        ∑ T ∈ U.powerset, (∑ S ∈ Finset.Icc T U, (-1 : ℝ) ^ (S.card - T.card)) *
          f fun i ↦ decide (i ∈ T) := by
    simp_rw [Finset.sum_mul]
    refine Finset.sum_comm' (t' := U.powerset) (s' := fun T ↦ Finset.Icc T U) ?_
    intro S T
    simp only [Finset.mem_powerset, Finset.mem_Icc]
    exact ⟨fun ⟨hSU, hTS⟩ ↦ ⟨⟨hTS, hSU⟩, hTS.trans hSU⟩,
      fun ⟨⟨hTS, hSU⟩, _⟩ ↦ ⟨hSU, hTS⟩⟩
  rw [hswap]
  simp_rw [Finset.sum_Icc_neg_one_pow_card_sub_card_left]
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
      have hsum := hd xT
      rw [sum_mul_prod_bit] at hsum
      have hfilt : (Finset.univ.filter fun i ↦ xT i = true) = T := by
        ext i
        simp [xT]
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
      | 2 => (∑ i ∈ T, ∑ j ∈ T, Q i j) - ∑ i ∈ T, Q i i
      | _ => 0
    have hd0 : d ∅ = c₀ := by simp [d]
    have hd1 (i : ι) : d {i} = Q i i := by simp [d]
    have hd2 (i j : ι) (hij : i ≠ j) : d {i, j} = Q i j + Q j i := by
      simp only [d, Finset.card_pair hij, Finset.sum_pair hij]
      ring
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
