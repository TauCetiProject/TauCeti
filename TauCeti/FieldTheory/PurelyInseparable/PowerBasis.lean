/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Power bases for prime-degree purely inseparable adjunctions

In prime characteristic `p`, an element `x ∉ Set.range (algebraMap E k)` of a field extension
`k / E` whose `p`-th power lies in `Set.range (algebraMap E k)` has `X ^ p - C (x ^ p)` irreducible
over `E` (via Mathlib's `irreducible_X_pow_sub_C_of_prime` in
`Mathlib.FieldTheory.KummerPolynomial`), so `1, x, …, x ^ (p - 1)` are linearly independent
over `E`.

## Main results

* `TauCeti.minpoly_eq_X_pow_sub_C_of_notMem_range`: in a field extension `k / E` where `k` has
  characteristic `p` for a prime `p`, an element `x ∉ Set.range (algebraMap E k)` with
  `x ^ p = algebraMap E k a` has minimal polynomial `X ^ p - C a` over `E`.
* `TauCeti.linearIndependent_pow_of_notMem_range`: in a field extension `k / E` where `k` has
  characteristic `p` for a prime `p`, an element `x ∉ Set.range (algebraMap E k)` with
  `x ^ p ∈ Set.range (algebraMap E k)` has `1, x, …, x ^ (p - 1)` linearly independent over `E`.
-/

public section

namespace TauCeti

/-- In a field extension `k / E` where `k` has characteristic `p` for a prime `p`, an element
`x ∉ Set.range (algebraMap E k)` with `x ^ p = algebraMap E k a` has minimal polynomial
`X ^ p - C a` over `E`. -/
theorem minpoly_eq_X_pow_sub_C_of_notMem_range {p : ℕ} [Fact p.Prime] {E k : Type*}
    [Field E] [Field k] [Algebra E k] [ExpChar k p] {x : k}
    (hx : x ∉ Set.range (algebraMap E k)) {a : E} (hxp : x ^ p = algebraMap E k a) :
    minpoly E x = Polynomial.X ^ p - Polynomial.C a := by
  have hp : p.Prime := Fact.out
  have ha : ∀ y : E, y ^ p ≠ a := fun y hy ↦
    hx ⟨y, frobenius_inj k p (by simp only [frobenius_def, ← map_pow, hy, hxp])⟩
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C a) :=
    irreducible_X_pow_sub_C_of_prime hp ha
  have hmonic : (Polynomial.X ^ p - Polynomial.C a).Monic :=
    Polynomial.monic_X_pow_sub_C a hp.ne_zero
  have haeval : Polynomial.aeval x (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    simp [hxp]
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm

/-- In a field extension `k / E` where `k` has characteristic `p` for a prime `p`, an element
`x ∉ Set.range (algebraMap E k)` with `x ^ p ∈ Set.range (algebraMap E k)` has
`1, x, …, x ^ (p - 1)` linearly independent over `E`. -/
theorem linearIndependent_pow_of_notMem_range {p : ℕ} [Fact p.Prime] {E k : Type*}
    [Field E] [Field k] [Algebra E k] [ExpChar k p] {x : k}
    (hx : x ∉ Set.range (algebraMap E k)) (hxp : x ^ p ∈ Set.range (algebraMap E k)) :
    LinearIndependent E (fun n : Fin p ↦ x ^ (n : ℕ)) := by
  obtain ⟨a, ha_eq⟩ := hxp
  have hmin : minpoly E x = Polynomial.X ^ p - Polynomial.C a :=
    minpoly_eq_X_pow_sub_C_of_notMem_range hx ha_eq.symm
  have hdeg : (minpoly E x).natDegree = p := by
    rw [hmin]
    exact Polynomial.natDegree_X_pow_sub_C a
  have hcomp : (fun n : Fin p ↦ x ^ (n : ℕ)) =
      (fun i : Fin (minpoly E x).natDegree ↦ x ^ (i : ℕ)) ∘ finCongr hdeg.symm :=
    funext fun n ↦ by simp only [Function.comp_apply, finCongr_apply_coe]
  rw [hcomp, linearIndependent_equiv]
  exact linearIndependent_pow (K := E) x

end TauCeti
