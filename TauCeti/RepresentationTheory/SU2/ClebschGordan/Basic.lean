/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Factorial.Basic
public import TauCeti.RepresentationTheory.SU2.ClebschGordan.Triad

/-!
# The Clebsch–Gordan coefficients of `SU(2)` by Racah's formula

The tensor product of the irreducible representations of `SU(2)` of spins `j₁` and `j₂`
decomposes, without multiplicity, into the irreducible representations of the spins
`j = |j₁ - j₂|, |j₁ - j₂| + 1, …, j₁ + j₂`. The Clebsch–Gordan coefficient
`(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` is the component of the coupled vector of spin `j` and weight `m`
along the product vector `e_{m₁} ⊗ e_{m₂}`. This file defines these real numbers by Racah's
closed formula and records the elementary facts about their support. Its support is described
by the admissible triples `TauCeti.SU2.IsTriad` of spins `(j₁, j₂, j)`.

## Conventions

The conventions are those of Edmonds [Edmonds], which agree with DLMF Chapter 34.
Spins and magnetic quantum numbers are encoded by natural numbers: the spin `j = d / 2` is given
by its double `d : ℕ`, and the magnetic quantum number `m = i - d / 2` by its index `i : ℕ`, which
is meaningful for `i ≤ d`. So Edmonds's order `m = j, …, -j` is `i = d, …, 0`. The condition
`m = m₁ + m₂` reads `2 i + d₁ + d₂ = 2 i₁ + 2 i₂ + d` in indices.

## Main definitions

* `TauCeti.SU2.clebschGordan d₁ d₂ d i₁ i₂ i`: the Clebsch–Gordan coefficient
  `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)`, by Racah's formula [Edmonds, (3.6.11)], built from its summand
  `TauCeti.SU2.clebschGordanTerm` and the factor `TauCeti.SU2.clebschGordanPrefactor` under its
  square root. It is `0` outside its support.
* `TauCeti.SU2.triangleCoefficient d₁ d₂ d₃`: the triangle coefficient `Δ(j₁ j₂ j₃)` of
  DLMF 34.2.5.

## Main results

* `TauCeti.SU2.clebschGordan_eq_zero_of_not_isTriad`, `TauCeti.SU2.clebschGordan_eq_zero_of_ne`:
  the selection rules: the coefficient vanishes for an inadmissible triple and unless
  `m = m₁ + m₂`.
* `TauCeti.SU2.clebschGordanPrefactor_eq_mul_sq_triangleCoefficient`: the factor under the square
  root is `(2j + 1) Δ(j₁ j₂ j)² Π_r (j_r + m_r)! (j_r - m_r)!`.
* `TauCeti.SU2.triangleCoefficient_comm`, `TauCeti.SU2.triangleCoefficient_rotate`: `Δ(j₁ j₂ j₃)`
  is invariant under permutations of the three spins.
* `TauCeti.SU2.clebschGordan_eq_sqrt_mul_clebschGordanTerm`: the coefficient when a single index
  contributes to Racah's sum.

## References

* [Edmonds] A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press,
  1957, §§3.1, 3.5–3.6. Equation numbers and pages refer to the 1957 printing.
* NIST Digital Library of Mathematical Functions, §34.2, <https://dlmf.nist.gov/34.2>.

The definitions, in this encoding by doubled spins and indices, follow the prior formalization
lean-SFVK of B. J. Braams (<https://github.com/bjbraams/lean-SFVK>, Apache-2.0), file
`SFVK/ClebschGordan/Basic/Coefficients.lean`.
-/

public section

noncomputable section

namespace TauCeti.SU2

open Finset

/-! ### Racah's formula -/

/-- The summand of Racah's formula [Edmonds, (3.6.11)] at the summation index `z`: with
`L = j₁ + j₂ - j`, it is
`(-1)^z / (z! (L - z)! (j₁ - m₁ - z)! (j₂ + m₂ - z)! (j - j₂ + m₁ + z)! (j - j₁ - m₂ + z)!)`,
and `0` unless the arguments of the last four factorials are nonnegative. The term is meaningful
only for the indices `z ≤ L` summed in `clebschGordan`: the condition `z ≤ L` is not checked, and
for `z > L` truncated subtraction turns `(L - z)!` into `0! = 1`. In indices `j₁ - m₁ = d₁ - i₁`,
`j₂ + m₂ = i₂`, `j - j₂ + m₁ = i₁ - L` and `j - j₁ - m₂ = (d₂ - i₂) - L`. -/
def clebschGordanTerm (d₁ d₂ d i₁ i₂ z : ℕ) : ℝ :=
  if (d₁ + d₂ - d) / 2 ≤ z + i₁ ∧ (d₁ + d₂ - d) / 2 ≤ z + (d₂ - i₂) ∧ z ≤ d₁ - i₁ ∧
      z ≤ i₂ then
    (-1) ^ z / ((z.factorial * ((d₁ + d₂ - d) / 2 - z).factorial *
      (d₁ - i₁ - z).factorial * (i₂ - z).factorial *
      (z + i₁ - (d₁ + d₂ - d) / 2).factorial *
      (z + (d₂ - i₂) - (d₁ + d₂ - d) / 2).factorial : ℕ) : ℝ)
  else 0

/-- The factor under the square root in Racah's formula [Edmonds, (3.6.11)]:
`(2j + 1) (j₁ + j₂ - j)! (j₁ - j₂ + j)! (-j₁ + j₂ + j)! / (j₁ + j₂ + j + 1)!` times
`Π_r (j_r + m_r)! (j_r - m_r)!`, the product over the three spins. -/
def clebschGordanPrefactor (d₁ d₂ d i₁ i₂ i : ℕ) : ℝ :=
  (((d + 1) * ((d₁ + d₂ - d) / 2).factorial * ((d₁ + d - d₂) / 2).factorial *
      ((d₂ + d - d₁) / 2).factorial * i₁.factorial * (d₁ - i₁).factorial * i₂.factorial *
      (d₂ - i₂).factorial * i.factorial * (d - i).factorial : ℕ) : ℝ) /
    (((d₁ + d₂ + d) / 2 + 1).factorial : ℕ)

/-- **The Clebsch–Gordan coefficient** `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` [Edmonds, (3.5.1)], with
`j_r = d_r / 2`, `m₁ = i₁ - d₁ / 2`, `m₂ = i₂ - d₂ / 2` and `m = i - d / 2`, by Racah's formula
[Edmonds, (3.6.11)]: the square root of `clebschGordanPrefactor` times the sum of
`clebschGordanTerm` over `0 ≤ z ≤ j₁ + j₂ - j`. It is `0` unless `(j₁, j₂, j)` is an admissible
triple, every index is in range and `m = m₁ + m₂`. -/
def clebschGordan (d₁ d₂ d i₁ i₂ i : ℕ) : ℝ :=
  if IsTriad d₁ d₂ d ∧ i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i ≤ d ∧ 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d then
    Real.sqrt (clebschGordanPrefactor d₁ d₂ d i₁ i₂ i) *
      ∑ z ∈ range ((d₁ + d₂ - d) / 2 + 1), clebschGordanTerm d₁ d₂ d i₁ i₂ z
  else 0

/-- The **triangle coefficient** of DLMF 34.2.5, for doubled spins:
`Δ(j₁ j₂ j₃) = √((j₁ + j₂ - j₃)! (j₁ - j₂ + j₃)! (-j₁ + j₂ + j₃)! / (j₁ + j₂ + j₃ + 1)!)`. -/
def triangleCoefficient (d₁ d₂ d₃ : ℕ) : ℝ :=
  Real.sqrt ((((d₁ + d₂ - d₃) / 2).factorial * ((d₁ + d₃ - d₂) / 2).factorial *
    ((d₂ + d₃ - d₁) / 2).factorial : ℕ) / (((d₁ + d₂ + d₃) / 2 + 1).factorial : ℕ))

/-- The summand of Racah's formula, unfolded. -/
theorem clebschGordanTerm_def (d₁ d₂ d i₁ i₂ z : ℕ) :
    clebschGordanTerm d₁ d₂ d i₁ i₂ z =
      if (d₁ + d₂ - d) / 2 ≤ z + i₁ ∧ (d₁ + d₂ - d) / 2 ≤ z + (d₂ - i₂) ∧ z ≤ d₁ - i₁ ∧
          z ≤ i₂ then
        (-1) ^ z / ((z.factorial * ((d₁ + d₂ - d) / 2 - z).factorial *
          (d₁ - i₁ - z).factorial * (i₂ - z).factorial *
          (z + i₁ - (d₁ + d₂ - d) / 2).factorial *
          (z + (d₂ - i₂) - (d₁ + d₂ - d) / 2).factorial : ℕ) : ℝ)
      else 0 :=
  (rfl)

/-- The factor under the square root in Racah's formula, unfolded. -/
theorem clebschGordanPrefactor_def (d₁ d₂ d i₁ i₂ i : ℕ) :
    clebschGordanPrefactor d₁ d₂ d i₁ i₂ i =
      (((d + 1) * ((d₁ + d₂ - d) / 2).factorial * ((d₁ + d - d₂) / 2).factorial *
          ((d₂ + d - d₁) / 2).factorial * i₁.factorial * (d₁ - i₁).factorial * i₂.factorial *
          (d₂ - i₂).factorial * i.factorial * (d - i).factorial : ℕ) : ℝ) /
        (((d₁ + d₂ + d) / 2 + 1).factorial : ℕ) :=
  (rfl)

/-- The summand of Racah's formula at an index `z` where it is nonzero, with the arguments
`a = L - z`, `b = d₁ - i₁ - z`, `c = i₂ - z`, `e = z + i₁ - L` and `f = z + (d₂ - i₂) - L` of its
factorials evaluated, `L = (d₁ + d₂ - d) / 2`. -/
theorem clebschGordanTerm_eq {d₁ d₂ d i₁ i₂ z a b c e f : ℕ}
    (ha : (d₁ + d₂ - d) / 2 - z = a) (hb : d₁ - i₁ - z = b) (hc : i₂ - z = c)
    (he : z + i₁ - (d₁ + d₂ - d) / 2 = e) (hf : z + (d₂ - i₂) - (d₁ + d₂ - d) / 2 = f)
    (h : (d₁ + d₂ - d) / 2 ≤ z + i₁ ∧ (d₁ + d₂ - d) / 2 ≤ z + (d₂ - i₂) ∧ z ≤ d₁ - i₁ ∧
      z ≤ i₂) :
    clebschGordanTerm d₁ d₂ d i₁ i₂ z =
      (-1) ^ z / ((z.factorial * a.factorial * b.factorial * c.factorial * e.factorial *
        f.factorial : ℕ) : ℝ) := by
  subst ha hb hc he hf
  exact ite_eq_left h

/-- The summand of Racah's formula vanishes at an index `z` where one of the arguments
`z + i₁ - L`, `z + (d₂ - i₂) - L`, `d₁ - i₁ - z` or `i₂ - z` of its factorials would be negative,
`L = (d₁ + d₂ - d) / 2`. -/
theorem clebschGordanTerm_eq_zero {d₁ d₂ d i₁ i₂ z : ℕ}
    (h : ¬((d₁ + d₂ - d) / 2 ≤ z + i₁ ∧ (d₁ + d₂ - d) / 2 ≤ z + (d₂ - i₂) ∧ z ≤ d₁ - i₁ ∧
      z ≤ i₂)) :
    clebschGordanTerm d₁ d₂ d i₁ i₂ z = 0 :=
  ite_eq_right h

/-- The factor under the square root in Racah's formula, with the arguments
`a = (d₁ + d₂ - d) / 2`, `b = (d₁ + d - d₂) / 2`, `c = (d₂ + d - d₁) / 2` and
`s = (d₁ + d₂ + d) / 2` of its factorials evaluated. -/
theorem clebschGordanPrefactor_eq {d₁ d₂ d i₁ i₂ i a b c s : ℕ} (ha : (d₁ + d₂ - d) / 2 = a)
    (hb : (d₁ + d - d₂) / 2 = b) (hc : (d₂ + d - d₁) / 2 = c) (hs : (d₁ + d₂ + d) / 2 = s) :
    clebschGordanPrefactor d₁ d₂ d i₁ i₂ i =
      (((d + 1) * a.factorial * b.factorial * c.factorial * i₁.factorial * (d₁ - i₁).factorial *
          i₂.factorial * (d₂ - i₂).factorial * i.factorial * (d - i).factorial : ℕ) : ℝ) /
        ((s + 1).factorial : ℕ) := by
  subst ha hb hc hs
  rfl

/-- The triangle coefficient, unfolded. -/
theorem triangleCoefficient_def (d₁ d₂ d₃ : ℕ) :
    triangleCoefficient d₁ d₂ d₃ =
      Real.sqrt ((((d₁ + d₂ - d₃) / 2).factorial * ((d₁ + d₃ - d₂) / 2).factorial *
        ((d₂ + d₃ - d₁) / 2).factorial : ℕ) / (((d₁ + d₂ + d₃) / 2 + 1).factorial : ℕ)) :=
  (rfl)

/-- The square of the triangle coefficient is the ratio of factorials under its square root. -/
theorem sq_triangleCoefficient (d₁ d₂ d₃ : ℕ) :
    triangleCoefficient d₁ d₂ d₃ ^ 2 =
      (((d₁ + d₂ - d₃) / 2).factorial * ((d₁ + d₃ - d₂) / 2).factorial *
        ((d₂ + d₃ - d₁) / 2).factorial : ℕ) / (((d₁ + d₂ + d₃) / 2 + 1).factorial : ℕ) :=
  Real.sq_sqrt (by positivity)

/-- The triangle coefficient is positive. -/
theorem triangleCoefficient_pos (d₁ d₂ d₃ : ℕ) : 0 < triangleCoefficient d₁ d₂ d₃ :=
  Real.sqrt_pos.2 (by positivity)

/-- The triangle coefficient is symmetric in its first two spins. -/
theorem triangleCoefficient_comm (d₁ d₂ d₃ : ℕ) :
    triangleCoefficient d₁ d₂ d₃ = triangleCoefficient d₂ d₁ d₃ := by
  rw [triangleCoefficient_def, triangleCoefficient_def, Nat.add_comm d₂ d₁, Nat.mul_right_comm]

/-- The triangle coefficient is invariant under the cyclic permutation of its spins. -/
theorem triangleCoefficient_rotate (d₁ d₂ d₃ : ℕ) :
    triangleCoefficient d₁ d₂ d₃ = triangleCoefficient d₂ d₃ d₁ := by
  rw [triangleCoefficient_def, triangleCoefficient_def, Nat.add_comm d₂ d₁, Nat.add_comm d₃ d₁,
    Nat.add_comm (d₂ + d₃) d₁, ← Nat.add_assoc]
  ac_rfl

/-- The factor under the square root in Racah's formula is positive. -/
theorem clebschGordanPrefactor_pos (d₁ d₂ d i₁ i₂ i : ℕ) :
    0 < clebschGordanPrefactor d₁ d₂ d i₁ i₂ i := by
  rw [clebschGordanPrefactor_def]
  positivity

/-- The factor under the square root in Racah's formula is
`(2j + 1) Δ(j₁ j₂ j)² Π_r (j_r + m_r)! (j_r - m_r)!`. -/
theorem clebschGordanPrefactor_eq_mul_sq_triangleCoefficient (d₁ d₂ d i₁ i₂ i : ℕ) :
    clebschGordanPrefactor d₁ d₂ d i₁ i₂ i =
      (d + 1) * triangleCoefficient d₁ d₂ d ^ 2 *
        ((i₁.factorial * (d₁ - i₁).factorial * i₂.factorial * (d₂ - i₂).factorial *
          i.factorial * (d - i).factorial : ℕ) : ℝ) := by
  rw [clebschGordanPrefactor_def, sq_triangleCoefficient]
  push_cast
  ring

/-! ### The support of the coefficients -/

/-- On its support, the Clebsch–Gordan coefficient is given by Racah's formula
[Edmonds, (3.6.11)]. -/
theorem clebschGordan_of_isTriad {d₁ d₂ d i₁ i₂ i : ℕ} (h : IsTriad d₁ d₂ d) (h₁ : i₁ ≤ d₁)
    (h₂ : i₂ ≤ d₂) (hi : i ≤ d) (hm : 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      Real.sqrt (clebschGordanPrefactor d₁ d₂ d i₁ i₂ i) *
        ∑ z ∈ range ((d₁ + d₂ - d) / 2 + 1), clebschGordanTerm d₁ d₂ d i₁ i₂ z :=
  ite_eq_left ⟨h, h₁, h₂, hi, hm⟩

/-- When a single index `z₀` contributes to Racah's sum, the Clebsch–Gordan coefficient is the
square root of `clebschGordanPrefactor` times the summand `clebschGordanTerm` at `z₀`. -/
theorem clebschGordan_eq_sqrt_mul_clebschGordanTerm {d₁ d₂ d i₁ i₂ i : ℕ} (h : IsTriad d₁ d₂ d)
    (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂) (hi : i ≤ d) (hm : 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d)
    {z₀ : ℕ} (hz₀ : z₀ ≤ (d₁ + d₂ - d) / 2)
    (hz : ∀ z ≤ (d₁ + d₂ - d) / 2, z ≠ z₀ → clebschGordanTerm d₁ d₂ d i₁ i₂ z = 0) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      Real.sqrt (clebschGordanPrefactor d₁ d₂ d i₁ i₂ i) * clebschGordanTerm d₁ d₂ d i₁ i₂ z₀ := by
  rw [clebschGordan_of_isTriad h h₁ h₂ hi hm, sum_eq_single_of_mem z₀ (mem_range.2 (by omega))
    fun z hz' ↦ hz z (Nat.lt_succ_iff.1 (mem_range.1 hz'))]

/-- **Selection rule** [Edmonds, p. 38]: the coefficient vanishes for an inadmissible
triple. -/
theorem clebschGordan_eq_zero_of_not_isTriad {d₁ d₂ d : ℕ} (h : ¬IsTriad d₁ d₂ d)
    (i₁ i₂ i : ℕ) : clebschGordan d₁ d₂ d i₁ i₂ i = 0 :=
  ite_eq_right fun h' ↦ h h'.1

/-- **Selection rule** [Edmonds, p. 38]: the coefficient vanishes unless `m = m₁ + m₂`. -/
theorem clebschGordan_eq_zero_of_ne {d₁ d₂ d i₁ i₂ i : ℕ}
    (h : 2 * i + d₁ + d₂ ≠ 2 * i₁ + 2 * i₂ + d) : clebschGordan d₁ d₂ d i₁ i₂ i = 0 :=
  ite_eq_right fun h' ↦ h h'.2.2.2.2

/-- The coefficient vanishes when the first magnetic index is out of range. -/
theorem clebschGordan_eq_zero_of_lt_left {d₁ d₂ d i₁ : ℕ} (h : d₁ < i₁) (i₂ i : ℕ) :
    clebschGordan d₁ d₂ d i₁ i₂ i = 0 :=
  ite_eq_right fun h' ↦ (h.not_ge h'.2.1).elim

/-- The coefficient vanishes when the second magnetic index is out of range. -/
theorem clebschGordan_eq_zero_of_lt_right {d₁ d₂ d i₂ : ℕ} (h : d₂ < i₂) (i₁ i : ℕ) :
    clebschGordan d₁ d₂ d i₁ i₂ i = 0 :=
  ite_eq_right fun h' ↦ (h.not_ge h'.2.2.1).elim

/-- The coefficient vanishes when the coupled magnetic index is out of range. -/
theorem clebschGordan_eq_zero_of_lt {d₁ d₂ d i : ℕ} (h : d < i) (i₁ i₂ : ℕ) :
    clebschGordan d₁ d₂ d i₁ i₂ i = 0 :=
  ite_eq_right fun h' ↦ (h.not_ge h'.2.2.2.1).elim

end TauCeti.SU2
