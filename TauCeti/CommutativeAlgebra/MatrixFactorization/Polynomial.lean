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

The rank-one factorization of `X ^ n` has differentials `X ^ i` and `X ^ (n - i)`.
Its two components are finite free modules over the polynomial ring.
These standard examples model the hypersurface `S[X]/(X^n)` in the homotopy category
of matrix factorizations.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

/-- The polynomial factorization `S[X] --X^i--> S[X] --X^(n-i)--> S[X]`
of `X^n`. The indices are allowed to lie at either endpoint; the interesting stable
factorizations have `0 < i < n`. -/
@[expose] noncomputable def power (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    MatrixFactorization (Polynomial S) (Polynomial.X ^ n) :=
  rankOne (Polynomial.X ^ i) (Polynomial.X ^ (n - i)) (by
    rw [← pow_add, Nat.add_sub_of_le hi])

@[simp] theorem power_d₀ (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    (power S n i hi).obj.d₀ =
      (Polynomial.X ^ i : Polynomial S) • 𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₀ ..

@[simp] theorem power_d₁ (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    (power S n i hi).obj.d₁ =
      (Polynomial.X ^ (n - i) : Polynomial S) •
        𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₁ ..

@[simp] theorem power_X₀ (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    (power S n i hi).obj.X₀ = FGModuleCat.of (Polynomial S) (Polynomial S) :=
  rankOne_X₀ ..

@[simp] theorem power_X₁ (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    (power S n i hi).obj.X₁ = FGModuleCat.of (Polynomial S) (Polynomial S) :=
  rankOne_X₁ ..

end TauCeti.MatrixFactorization
