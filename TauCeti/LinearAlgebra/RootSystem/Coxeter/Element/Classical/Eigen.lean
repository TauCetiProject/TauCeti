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
| `Bₙ`, `Cₙ` (`n ≥ 1`) | `2n` | `1, 3, …, 2n - 1` |
| `Dₙ` (`n ≥ 3`) | `2n - 2` | `1, 3, …, 2n - 3` and `n - 1` |

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

/-- The exponents of `D_{n+1}` are those of `B_n` followed by `n`. -/
theorem dExponents_succ (n : ℕ) : dExponents (n + 1) = bExponents n ++ [n] := by
  rw [dExponents, Nat.add_sub_cancel]

@[simp]
theorem length_aExponents (n : ℕ) : (aExponents n).length = n := by simp [aExponents]

@[simp]
theorem length_bExponents (n : ℕ) : (bExponents n).length = n := by simp [bExponents]

theorem length_dExponents {n : ℕ} (hn : 1 ≤ n) : (dExponents n).length = n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [dExponents_succ]

theorem nodup_aExponents (n : ℕ) : (aExponents n).Nodup :=
  List.nodup_range.map (add_left_injective 1)

theorem nodup_bExponents (n : ℕ) : (bExponents n).Nodup :=
  List.nodup_range.map fun a b h => by omega

@[simp]
theorem mem_aExponents_iff {n e : ℕ} : e ∈ aExponents n ↔ 1 ≤ e ∧ e ≤ n := by
  simp only [aExponents, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · intro h
    exact ⟨e - 1, by omega, by omega⟩

@[simp]
theorem mem_bExponents_iff {n e : ℕ} : e ∈ bExponents n ↔ Odd e ∧ e < 2 * n := by
  simp only [bExponents, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨odd_two_mul_add_one k, by omega⟩
  · rintro ⟨⟨k, rfl⟩, h⟩
    exact ⟨k, by omega, rfl⟩

/-- The exponents of `Aₙ` are distinct: each of `1, …, n` occurs once. -/
theorem count_aExponents (n e : ℕ) :
    (aExponents n).count e = if 1 ≤ e ∧ e ≤ n then 1 else 0 := by
  split_ifs with h
  · exact List.count_eq_one_of_mem (nodup_aExponents n) (mem_aExponents_iff.2 h)
  · exact List.count_eq_zero_of_not_mem (mt mem_aExponents_iff.1 h)

/-- The exponents of `Bₙ` are distinct: each odd number below `2n` occurs once. -/
theorem count_bExponents (n e : ℕ) :
    (bExponents n).count e = if Odd e ∧ e < 2 * n then 1 else 0 := by
  split_ifs with h
  · exact List.count_eq_one_of_mem (nodup_bExponents n) (mem_bExponents_iff.2 h)
  · exact List.count_eq_zero_of_not_mem (mt mem_bExponents_iff.1 h)

@[simp]
theorem mem_dExponents_iff {n e : ℕ} :
    e ∈ dExponents n ↔ (Odd e ∧ e < 2 * (n - 1)) ∨ e = n - 1 := by
  simp [dExponents]

/-- The multiplicity of `e` among the exponents of `Dₙ`: `n - 1` occurs once more than among the
odd numbers below `2n - 2`, so twice when `n` is positive and even. -/
theorem count_dExponents (n e : ℕ) :
    (dExponents n).count e = (bExponents (n - 1)).count e + if e = n - 1 then 1 else 0 := by
  by_cases h : e = n - 1
  · simp [dExponents, h]
  · simp [dExponents, h, Ne.symm h]

/-- **The roots of `(X^{n-1} + 1)(X + 1)`** are `exp (2πi e / (2n - 2))` over the exponents of
`Dₙ`, with multiplicity. -/
theorem roots_X_pow_add_one_mul_X_add_one {n : ℕ} (hn : 2 ≤ n) :
    ((X ^ (n - 1) + 1) * (X + 1) : ℂ[X]).roots = ((dExponents n).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * (n - 1) : ℕ) : ℂ))) :
        Multiset ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmon : (X ^ k + 1 : ℂ[X]).Monic := by
    simpa using monic_X_pow_add_C (1 : ℂ) (n := k) (by omega)
  have h1 : (X + 1 : ℂ[X]) = X + C 1 := by simp
  rw [roots_mul (mul_ne_zero hmon.ne_zero (h1 ▸ X_add_C_ne_zero 1)),
    roots_X_pow_add_one, h1, roots_X_add_C, dExponents_succ, List.map_append,
    ← Multiset.coe_add]
  congr 1
  · simp only [bExponents, List.map_map, Function.comp_def]
  have : 2 * Real.pi * Complex.I * ((k : ℂ) / ((2 * k : ℕ) : ℂ)) = Real.pi * Complex.I := by
    have hk : (k : ℂ) ≠ 0 := by norm_cast; omega
    push_cast
    field_simp
  simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.singleton_inj]
  rw [this, Complex.exp_pi_mul_I]

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of every Coxeter element of type `Aₙ`**: `exp (2πi e / (n + 1))` for
`e = 1, …, n`, each once. -/
theorem eigenvalues_of_hasCartanType_A {n : ℕ} {b : P.Base} (h : HasCartanType P b (.A n))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((aExponents n).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((n + 1 : ℕ) : ℂ))) : Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW, Polynomial.map_sum]
  simp only [Polynomial.map_pow, map_X]
  exact (roots_geom_sum_X n).trans (by simp only [aExponents, List.map_map, Function.comp_def])

/-- **Eigenvalues of every Coxeter element of type `Bₙ`** (`n ≥ 1`): `exp (2πi e / 2n)` for
`e = 1, 3, …, 2n - 1`, each once. -/
theorem eigenvalues_of_hasCartanType_B {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.B n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((bExponents n).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * n : ℕ) : ℂ))) : Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  exact (roots_X_pow_add_one _).trans
    (by simp only [bExponents, List.map_map, Function.comp_def])

/-- **Eigenvalues of every Coxeter element of type `Cₙ`** (`n ≥ 1`): `exp (2πi e / 2n)` for
`e = 1, 3, …, 2n - 1`, each once. -/
theorem eigenvalues_of_hasCartanType_C {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.C n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((bExponents n).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * n : ℕ) : ℂ))) : Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  exact (roots_X_pow_add_one _).trans
    (by simp only [bExponents, List.map_map, Function.comp_def])

/-- **Eigenvalues of every Coxeter element of type `Dₙ`** (`n ≥ 3`): `exp (2πi e / (2n - 2))`
over the exponents `1, 3, …, 2n - 3` and `n - 1`, with multiplicity (`-1` is double when `n` is
even). -/
theorem eigenvalues_of_hasCartanType_D {n : ℕ} (hn : 3 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.D n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots = ((dExponents n).map fun (e : ℕ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / ((2 * (n - 1) : ℕ) : ℂ))) :
        Multiset ℂ) := by
  rw [charpoly_map, charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_one]
  exact roots_X_pow_add_one_mul_X_add_one (by omega)

end TauCeti.Coxeter

end
