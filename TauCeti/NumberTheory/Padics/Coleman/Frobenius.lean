/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution

import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Coleman's Frobenius substitution on power series

Over any commutative ring `O` and natural number `p`, Frobenius substitution
`Φ = TauCeti.Coleman.frobeniusHom p O : O⟦X⟧ →ₐ[O] O⟦X⟧` sends `f(X)` to `f((1 + X) ^ p - 1)`.
It is continuous for the coefficientwise topology `PowerSeries.WithPiTopology` when `O` is a
topological ring (`TauCeti.Coleman.continuous_frobeniusHom`), commutes with coefficientwise change
of base ring (`TauCeti.Coleman.map_frobeniusHom`), and agrees with `PowerSeries.expand p` when `p`
is prime and `(p : O) = 0` (`TauCeti.Coleman.frobeniusHom_eq_expand`).

## Main definitions and results

* `TauCeti.Coleman.hasSubst_one_add_X_pow_sub_one`: `(1 + X) ^ p - 1` satisfies `HasSubst`.
* `TauCeti.Coleman.frobeniusHom`: Frobenius substitution `f(X) ↦ f((1 + X) ^ p - 1)`.
* `TauCeti.Coleman.frobeniusHom_eq_expand`: for prime `p` with `(p : O) = 0`, `frobeniusHom`
  coincides with `PowerSeries.expand p`.
* `TauCeti.Coleman.map_frobeniusHom`: compatibility with `PowerSeries.map`.
* `TauCeti.Coleman.continuous_frobeniusHom`: continuity for `PowerSeries.WithPiTopology`.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §II.
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.2
  (Proposition 2.2.3).
* R. Sharifi, *Iwasawa Theory*, §5.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Chapter 10.
-/

public noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.Coleman

section Frobenius

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The series `(1 + X) ^ p - 1` satisfies `HasSubst` over any commutative ring `O`. -/
theorem hasSubst_one_add_X_pow_sub_one : HasSubst ((1 + X : O⟦X⟧) ^ p - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- The Frobenius substitution `Φ : O⟦X⟧ →ₐ[O] O⟦X⟧` sending `f(X)` to `f((1 + X) ^ p - 1)`. -/
def frobeniusHom : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom (hasSubst_one_add_X_pow_sub_one p O)

variable {p O}

/-- Applying `frobeniusHom` substitutes `(1 + X) ^ p - 1`. -/
theorem frobeniusHom_apply (f : O⟦X⟧) : frobeniusHom p O f = f.subst ((1 + X : O⟦X⟧) ^ p - 1) :=
  congrFun (coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p O)) f

/-- `frobeniusHom` sends `X` to `(1 + X) ^ p - 1`. -/
@[simp]
theorem frobeniusHom_X : frobeniusHom p O X = (1 + X : O⟦X⟧) ^ p - 1 := by
  rw [frobeniusHom_apply, subst_X (hasSubst_one_add_X_pow_sub_one p O)]

/-- `frobeniusHom` fixes constant power series. -/
@[simp]
theorem frobeniusHom_C (c : O) : frobeniusHom p O (C c) = C c := (frobeniusHom p O).commutes c

/-- `frobeniusHom` preserves the constant coefficient. -/
@[simp]
theorem constantCoeff_frobeniusHom (f : O⟦X⟧) :
    constantCoeff (frobeniusHom p O f) = constantCoeff f := by
  rw [frobeniusHom_apply, PowerSeries.constantCoeff_subst_of_constantCoeff_zero' (by simp)]
  simp

/-- `frobeniusHom` raises `1 + X` to the `p`-th power. -/
@[simp]
theorem frobeniusHom_one_add_X : frobeniusHom p O (1 + X) = (1 + X : O⟦X⟧) ^ p := by simp [map_add]

/-- `frobeniusHom` sends `(1 + X) ^ n` to `(1 + X) ^ (p * n)`. -/
@[simp]
theorem frobeniusHom_one_add_X_pow (n : ℕ) :
    frobeniusHom p O ((1 + X) ^ n) = (1 + X : O⟦X⟧) ^ (p * n) := by
  rw [map_pow, frobeniusHom_one_add_X, ← pow_mul]

/-- Coefficientwise change of base ring commutes with `frobeniusHom`. -/
theorem map_frobeniusHom {O' : Type*} [CommRing O'] (φ : O →+* O') (f : O⟦X⟧) :
    PowerSeries.map φ (frobeniusHom p O f) = frobeniusHom p O' (PowerSeries.map φ f) := by
  rw [frobeniusHom_apply, frobeniusHom_apply]
  have hsub : PowerSeries.map φ ((1 + X : O⟦X⟧) ^ p - 1) = (1 + X : O'⟦X⟧) ^ p - 1 := by
    simp [PowerSeries.map_X]
  exact (PowerSeries.map_subst (hasSubst_one_add_X_pow_sub_one p O) (h := φ) f).trans
    (congrArg (subst · _) hsub)

/-- For prime `p` with `(p : O) = 0`, `frobeniusHom` coincides with `PowerSeries.expand p`. -/
theorem frobeniusHom_eq_expand [Fact p.Prime] (hp : (p : O) = 0) (f : O⟦X⟧) :
    frobeniusHom p O f = expand p (Fact.out : p.Prime).ne_zero f := by
  obtain ⟨q, hq⟩ := C_dvd_one_add_X_pow_sub_one_sub_X_pow (O := O) (Fact.out : p.Prime)
  rw [hp, map_zero, zero_mul, sub_eq_zero] at hq
  rw [frobeniusHom_apply, expand_apply, hq]

/-- Frobenius substitution `Φ` is continuous for the coefficientwise topology on `O⟦X⟧`. -/
theorem continuous_frobeniusHom [TopologicalSpace O] [IsTopologicalRing O] :
    Continuous (frobeniusHom p O) :=
  (funext frobeniusHom_apply : (frobeniusHom p O : O⟦X⟧ → O⟦X⟧) = _).symm ▸
    Continuous.powerSeries_subst continuous_id continuous_const (fun _ ↦ by simp)

end Frobenius

end TauCeti.Coleman
