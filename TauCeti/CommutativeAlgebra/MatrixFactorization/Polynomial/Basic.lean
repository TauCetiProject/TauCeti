/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Polynomial matrix factorizations

The rank-one factorization of `X ^ (i + j)` has differentials `X ^ i` and `X ^ j`.
Its two components are finite free modules over the polynomial ring. For `i ≤ n`, the variant
`powerXOfLE` is the rank-one factorization of the potential `X ^ n` with differentials `X ^ i`
and `X ^ (n - i)`.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

/-- The polynomial factorization `S[X] --X^i--> S[X] --X^j--> S[X]`
of `X^(i+j)`, obtained from `rankOne`. See `powerXOfLE` for the factorization indexed
by `X^n`. -/
@[expose] noncomputable def powerX (S : Type u) [CommRing S] (i j : ℕ) :
    MatrixFactorization (Polynomial S) (Polynomial.X ^ (i + j)) :=
  rankOne (Polynomial.X ^ i) (Polynomial.X ^ j) (by rw [← pow_add])

@[simp] theorem powerX_d₀ (S : Type u) [CommRing S] (i j : ℕ) :
    (powerX S i j).obj.d₀ =
      (Polynomial.X ^ i : Polynomial S) • 𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₀ ..

@[simp] theorem powerX_d₁ (S : Type u) [CommRing S] (i j : ℕ) :
    (powerX S i j).obj.d₁ =
      (Polynomial.X ^ j : Polynomial S) •
        𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₁ ..

@[simp] theorem powerX_X₀ (S : Type u) [CommRing S] (i j : ℕ) :
    (powerX S i j).obj.X₀ = FGModuleCat.of (Polynomial S) (Polynomial S) :=
  rankOne_X₀ ..

@[simp] theorem powerX_X₁ (S : Type u) [CommRing S] (i j : ℕ) :
    (powerX S i j).obj.X₁ = FGModuleCat.of (Polynomial S) (Polynomial S) :=
  rankOne_X₁ ..

/-- The polynomial factorization `S[X] --X^i--> S[X] --X^(n-i)--> S[X]` of `X^n`,
for `i ≤ n`, obtained from `rankOne`. -/
@[expose] noncomputable def powerXOfLE (S : Type u) [CommRing S] {i n : ℕ} (h : i ≤ n) :
    MatrixFactorization (Polynomial S) (Polynomial.X ^ n) :=
  rankOne (Polynomial.X ^ i) (Polynomial.X ^ (n - i)) (by rw [← pow_add, Nat.add_sub_cancel' h])

@[simp] theorem powerXOfLE_d₀ (S : Type u) [CommRing S] {i n : ℕ} (h : i ≤ n) :
    (powerXOfLE S h).obj.d₀ =
      (Polynomial.X ^ i : Polynomial S) • 𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₀ ..

@[simp] theorem powerXOfLE_d₁ (S : Type u) [CommRing S] {i n : ℕ} (h : i ≤ n) :
    (powerXOfLE S h).obj.d₁ =
      (Polynomial.X ^ (n - i) : Polynomial S) •
        𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₁ ..

@[simp] theorem powerXOfLE_X₀ (S : Type u) [CommRing S] {i n : ℕ} (h : i ≤ n) :
    (powerXOfLE S h).obj.X₀ = FGModuleCat.of (Polynomial S) (Polynomial S) :=
  rankOne_X₀ ..

@[simp] theorem powerXOfLE_X₁ (S : Type u) [CommRing S] {i n : ℕ} (h : i ≤ n) :
    (powerXOfLE S h).obj.X₁ = FGModuleCat.of (Polynomial S) (Polynomial S) :=
  rankOne_X₁ ..

end TauCeti.MatrixFactorization
