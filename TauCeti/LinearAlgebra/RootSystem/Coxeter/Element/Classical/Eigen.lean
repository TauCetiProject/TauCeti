/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Classical.Basic
public import TauCeti.RingTheory.Polynomial.ComplexRoots

/-!
# Eigenvalues of the classical Coxeter elements

For every Coxeter element of a base of type `Aₙ`, `Bₙ`, `Cₙ` or `Dₙ`, the multiset of complex
eigenvalues (roots of the characteristic polynomial on the simple roots) is `exp (2πi e / h)` over
the exponents `e`, with multiplicity:

| type | `h` | exponents |
|---|---|---|
| `Aₙ` | `n + 1` | `1, 2, …, n` |
| `Bₙ`, `Cₙ` | `2n` | `1, 3, …, 2n - 1` |
| `Dₙ` | `2n - 2` | `1, 3, …, 2n - 3` and `n - 1` |

For `Dₙ` with `n` even, the exponent `n - 1` is odd and also occurs in `1, 3, …, 2n - 3`, so the
eigenvalue `-1` is double. The roots of the factors `Xⁿ + 1` and `1 + X + ⋯ + Xⁿ` are
`Polynomial.roots_X_pow_add_one` and `Polynomial.roots_geom_sum_X`; for `Dₙ` the factor `X + 1` is
added with `Polynomial.roots_mul`.

## Main results

* `TauCeti.Coxeter.eigenvalues_of_hasCartanType_A` (and `B`, `C`, `D`): the multiset of complex
  eigenvalues of every Coxeter element of a base of type `Aₙ` (and `Bₙ`, `Cₙ`, `Dₙ`).
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

/-- The exponents `1, 2, …, n` of `Aₙ`. -/
def aExponents (n : ℕ) : List ℕ := (List.range n).map (· + 1)

/-- The exponents `1, 3, …, 2n - 1` of `Bₙ` and `Cₙ`. -/
def bExponents (n : ℕ) : List ℕ := (List.range n).map fun k => 2 * k + 1

/-- The exponents `1, 3, …, 2n - 3` and `n - 1` of `Dₙ`, as a list with multiplicity. -/
def dExponents (n : ℕ) : List ℕ := bExponents (n - 1) ++ [n - 1]

theorem aExponents_def (n : ℕ) : aExponents n = (List.range n).map (· + 1) := by
  rw [aExponents]

theorem bExponents_def (n : ℕ) : bExponents n = (List.range n).map fun k => 2 * k + 1 := by
  rw [bExponents]

theorem dExponents_def (n : ℕ) : dExponents n = bExponents (n - 1) ++ [n - 1] := by
  rw [dExponents]

/-- The exponents of `D_{n+1}` are those of `B_n` followed by `n`. -/
theorem dExponents_succ (n : ℕ) : dExponents (n + 1) = bExponents n ++ [n] := by
  rw [dExponents_def, Nat.add_sub_cancel]

@[simp]
theorem length_aExponents (n : ℕ) : (aExponents n).length = n := by simp [aExponents]

@[simp]
theorem length_bExponents (n : ℕ) : (bExponents n).length = n := by simp [bExponents]

@[simp]
theorem length_dExponents (n : ℕ) : (dExponents (n + 1)).length = n + 1 := by
  simp [dExponents_succ]

theorem mem_aExponents_iff {n e : ℕ} : e ∈ aExponents n ↔ 1 ≤ e ∧ e ≤ n := by
  simp only [aExponents, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · intro h
    exact ⟨e - 1, by omega, by omega⟩

theorem mem_bExponents_iff {n e : ℕ} : e ∈ bExponents n ↔ Odd e ∧ e < 2 * n := by
  simp only [bExponents, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨odd_two_mul_add_one k, by omega⟩
  · rintro ⟨⟨k, rfl⟩, h⟩
    exact ⟨k, by omega, rfl⟩

theorem mem_dExponents_iff {n e : ℕ} :
    e ∈ dExponents n ↔ (Odd e ∧ e < 2 * (n - 1)) ∨ e = n - 1 := by
  simp [dExponents, mem_bExponents_iff]

/-- The multiplicity of `e` among the exponents of `Dₙ`: `n - 1` occurs once more than among the
odd numbers below `2n - 2`, so twice when `n` is even. -/
theorem count_dExponents (n e : ℕ) :
    (dExponents n).count e = (bExponents (n - 1)).count e + if e = n - 1 then 1 else 0 := by
  by_cases h : e = n - 1
  · simp [dExponents_def, h]
  · simp [dExponents_def, h, Ne.symm h]

/-- **The roots of `(X^{m+2} + 1)(X + 1)`** are `exp (2πi e / 2(m + 2))` over the exponents of
`D_{m+3}`, with multiplicity. -/
theorem roots_X_pow_add_one_mul_X_add_one (m : ℕ) :
    ((X ^ (m + 2) + 1) * (X + 1) : ℂ[X]).roots = ((dExponents (m + 3)).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * (m + 2) : ℕ) : ℂ))) :
        Multiset ℂ) := by
  have hmon : (X ^ (m + 2) + 1 : ℂ[X]).Monic := by
    simpa using monic_X_pow_add_C (1 : ℂ) (n := m + 2) (by omega)
  have h1 : (X + 1 : ℂ[X]) = X + C 1 := by simp
  rw [roots_mul (mul_ne_zero hmon.ne_zero (h1 ▸ X_add_C_ne_zero 1)),
    roots_X_pow_add_one (by omega), h1, roots_X_add_C, dExponents_succ, List.map_append,
    ← Multiset.coe_add]
  congr 1
  · simp only [bExponents, List.map_map, Function.comp_def]
  have : 2 * Real.pi * Complex.I * (((m + 2 : ℕ) : ℂ) / ((2 * (m + 2) : ℕ) : ℂ)) =
      Real.pi * Complex.I := by
    have hm : ((m : ℂ) + 2) ≠ 0 := by norm_cast
    push_cast
    field_simp
  simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.singleton_inj]
  rw [this, Complex.exp_pi_mul_I]

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of every Coxeter element of type `Aₙ`** (`n = m + 1`): `exp (2πi e / (n + 1))`
for `e = 1, …, n`, each once. -/
theorem eigenvalues_of_hasCartanType_A {m : ℕ} {b : P.Base} (h : HasCartanType P b (.A (m + 1)))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((aExponents (m + 1)).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((m + 2 : ℕ) : ℂ))) : Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW, Polynomial.map_sum]
  simp only [Polynomial.map_pow, map_X]
  exact (roots_geom_sum_X m).trans (by simp only [aExponents, List.map_map, Function.comp_def])

/-- **Eigenvalues of every Coxeter element of type `Bₙ`** (`n = m + 1`): `exp (2πi e / 2n)` for
`e = 1, 3, …, 2n - 1`, each once. -/
theorem eigenvalues_of_hasCartanType_B {m : ℕ} {b : P.Base} (h : HasCartanType P b (.B (m + 1)))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((bExponents (m + 1)).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * (m + 1) : ℕ) : ℂ))) :
        Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_B_of_actsBy h hnd hall hW]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  exact (roots_X_pow_add_one (by omega)).trans
    (by simp only [bExponents, List.map_map, Function.comp_def])

/-- **Eigenvalues of every Coxeter element of type `Cₙ`** (`n = m + 1`): `exp (2πi e / 2n)` for
`e = 1, 3, …, 2n - 1`, each once. -/
theorem eigenvalues_of_hasCartanType_C {m : ℕ} {b : P.Base} (h : HasCartanType P b (.C (m + 1)))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((bExponents (m + 1)).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * (m + 1) : ℕ) : ℂ))) :
        Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_C_of_actsBy h hnd hall hW]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  exact (roots_X_pow_add_one (by omega)).trans
    (by simp only [bExponents, List.map_map, Function.comp_def])

/-- **Eigenvalues of every Coxeter element of type `Dₙ`** (`n = m + 3`): `exp (2πi e / (2n - 2))`
over the exponents `1, 3, …, 2n - 3` and `n - 1`, with multiplicity (`-1` is double when `n` is
even). -/
theorem eigenvalues_of_hasCartanType_D {m : ℕ} {b : P.Base} (h : HasCartanType P b (.D (m + 3)))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((dExponents (m + 3)).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * (m + 2) : ℕ) : ℂ))) :
        Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_D_of_actsBy h hnd hall hW]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_one]
  exact roots_X_pow_add_one_mul_X_add_one m

end TauCeti.Coxeter

end
