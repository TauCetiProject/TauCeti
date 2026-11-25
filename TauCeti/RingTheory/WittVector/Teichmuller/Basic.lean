/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Multiplication by a Teichmüller representative

Multiplication by `[a]` scales the `i`-th Witt coordinate by `a ^ (p ^ i)`. This formula
allows denominators in finitely many Witt coordinates to be cleared by one Teichmüller power.

The proof uses the same passage to rational ghost components and specialization as Mathlib's
construction of `WittVector.teichmuller`.
-/

public section

namespace WittVector

open MvPolynomial

variable {p : ℕ} [Fact p.Prime]

private theorem teichmuller_mul_of_invertible {R : Type*} [CommRing R] [Invertible (p : R)]
    (a : R) (x : WittVector p R) :
    teichmuller p a * x = mk p (fun j ↦ a ^ p ^ j * x.coeff j) := by
  apply (ghostMap.bijective_of_invertible p R).1
  funext n
  rw [ghostMap_apply, ghostMap_apply, map_mul, ghostComponent_teichmuller]
  simp only [ghostComponent_apply, aeval_wittPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le hjn]
  exact mul_left_comm _ _ _

/-- Multiplying by `[a]` scales the `i`-th Witt coordinate by `a ^ (p ^ i)`. -/
@[simp]
theorem teichmuller_mul_coeff {R : Type*} [CommRing R] (a : R) (x : WittVector p R) (i : ℕ) :
    (teichmuller p a * x).coeff i = a ^ p ^ i * x.coeff i := by
  let c : MvPolynomial (Option ℕ) ℤ := X none
  let y : WittVector p (MvPolynomial (Option ℕ) ℤ) := mk p (fun j ↦ X (some j))
  let f : MvPolynomial (Option ℕ) ℤ →+* MvPolynomial (Option ℕ) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hf : Function.Injective f := MvPolynomial.map_injective _ Int.cast_injective
  have hy : f ((teichmuller p c * y).coeff i) = f (c ^ p ^ i * y.coeff i) := by
    rw [← map_coeff, map_mul, map_teichmuller]
    simpa only [map_mul, map_pow, map_coeff, coeff_mk] using
      congrArg (fun z : WittVector p (MvPolynomial (Option ℕ) ℚ) ↦ z.coeff i)
        (teichmuller_mul_of_invertible (f c) (map f y))
  let g : MvPolynomial (Option ℕ) ℤ →+* R := (aeval (fun j : Option ℕ ↦ j.elim a x.coeff)).toRingHom
  have hg : map g y = x := by
    ext j
    simp [g, y]
  have hgc : g c = a := by simp [g, c]
  simpa only [← map_coeff, map_mul, map_teichmuller, map_pow, hg, hgc] using
    congrArg g (hf hy)

end WittVector
