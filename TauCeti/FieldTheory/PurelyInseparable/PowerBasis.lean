/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
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

* `TauCeti.linearIndependent_pow_of_notMem_range`: in a field extension `k / E` where `k` has
  characteristic `p` for a prime `p`, an element `x ∉ Set.range (algebraMap E k)` with
  `x ^ p ∈ Set.range (algebraMap E k)` has `1, x, …, x ^ (p - 1)` linearly independent over `E`.
-/

public section

namespace TauCeti

/-- In a field extension `k / E` where `k` has characteristic `p` for a prime `p`, an element
`x ∉ Set.range (algebraMap E k)` with `x ^ p ∈ Set.range (algebraMap E k)` has
`1, x, …, x ^ (p - 1)` linearly independent over `E`. -/
theorem linearIndependent_pow_of_notMem_range {p : ℕ} [Fact p.Prime] {E k : Type*}
    [Field E] [Field k] [Algebra E k] [ExpChar k p] {x : k}
    (hx : x ∉ Set.range (algebraMap E k)) (hxp : x ^ p ∈ Set.range (algebraMap E k)) :
    LinearIndependent E (fun n : Fin p ↦ x ^ (n : ℕ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha_eq⟩ := hxp
  have ha : ∀ y : E, y ^ p ≠ a := by
    intro y hy
    have hy' : algebraMap E k y ^ p = x ^ p := by rw [← map_pow, hy, ha_eq]
    exact hx ⟨y, frobenius_inj k p hy'⟩
  let f : Polynomial E := Polynomial.X ^ p - Polynomial.C a
  have hirr : Irreducible f := irreducible_X_pow_sub_C_of_prime hp ha
  have hmonic : f.Monic := Polynomial.monic_X_pow_sub_C a hp.ne_zero
  have haeval : Polynomial.aeval x f = 0 := by
    simp only [f, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ha_eq, sub_self]
  have hmin : minpoly E x = f := (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm
  have hdeg : (minpoly E x).natDegree = p := by
    rw [hmin]
    exact Polynomial.natDegree_X_pow_sub_C a
  have hcomp : (fun n : Fin p ↦ x ^ (n : ℕ)) =
      (fun i : Fin (minpoly E x).natDegree ↦ x ^ (i : ℕ)) ∘ finCongr hdeg.symm :=
    funext fun n ↦ by simp only [Function.comp_apply, finCongr_apply_coe]
  rw [hcomp, linearIndependent_equiv]
  exact linearIndependent_pow (K := E) x

end TauCeti
