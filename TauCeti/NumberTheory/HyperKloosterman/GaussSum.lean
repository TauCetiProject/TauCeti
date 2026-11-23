/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.GaussSum
public import TauCeti.NumberTheory.HyperKloosterman.Basic
import TauCeti.NumberTheory.DirichletCharacter.Even
import TauCeti.NumberTheory.GaussSum.Basic

/-!
# Character sums of powers of Gauss sums

Let `ψ` be an additive character of `ZMod n` and `τ(χ) = gaussSum χ ψ` the Gauss sum of a
Dirichlet character `χ` of level `n`. Expanding `τ(χ) ^ k` over `k`-tuples and applying the
orthogonality of characters, the sum of `χ⁻¹ (r) τ(χ) ^ k` over all characters selects the
tuples of product `r`, which gives the hyper-Kloosterman sum:

  `∑_χ χ⁻¹ (r) τ(χ) ^ k = φ(n) Kl_k(ψ, r)`.

Restricting to the even characters selects the tuples of product `±r`. At an odd prime level `q`
and for a nontrivial `ψ`, the trivial character contributes `τ(1) ^ k = (-1) ^ k`, so that

  `∑_{χ even, χ ≠ 1} χ⁻¹ (r) τ(χ) ^ k = (q - 1) / 2 * (Kl_k(ψ, r) + Kl_k(ψ, -r)) - (-1) ^ k`.

This exact identity is the finite-field step of the first moment of the even prime twists of
Luo, Rudnick and Sarnak: combined with Deligne's estimate for hyper-Kloosterman sums it bounds the
absolute value of this sum by `(q - 1) k q ^ ((k - 1) / 2) + 1` for `k ≥ 1`. Over `ℂ` the
factor `χ⁻¹ (r)` is the complex conjugate of `χ (r)` (`MulChar.star_apply'`).

## Main statements

* `TauCeti.sum_inv_apply_mul_gaussSum_pow`: the sum over all Dirichlet characters.
* `TauCeti.two_mul_sum_even_inv_apply_mul_gaussSum_pow`,
  `TauCeti.sum_even_inv_apply_mul_gaussSum_pow`: the sum over the even characters.
* `TauCeti.sum_even_ne_one_inv_apply_mul_gaussSum_pow`: the sum over the even nontrivial
  characters at an odd prime level.

## References

* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equations (3.18)–(3.20).
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDomain R]

section Level

variable {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/-- **Gauss-power sum over all characters.** The sum of `χ⁻¹ (r) τ(χ) ^ k` over the
Dirichlet characters of level `n` is `φ(n)` times the hyper-Kloosterman sum of rank `k` at
`r`. -/
theorem sum_inv_apply_mul_gaussSum_pow (ψ : AddChar (ZMod n) R) (k : ℕ) (r : (ZMod n)ˣ) :
    ∑ χ : DirichletCharacter R n, χ⁻¹ r * gaussSum χ ψ ^ k =
      n.totient * hyperKloosterman (ZMod n) k ψ r := by
  classical
  -- Expand the powers and exchange the two sums; orthogonality then selects the tuples of
  -- product `r`.
  have h (b : ZMod n) :
      ∑ χ : DirichletCharacter R n, χ⁻¹ r * χ b =
        if (r : ZMod n) = b then (n.totient : R) else 0 := by
    simp_rw [MulChar.inv_apply, Ring.inverse_unit, ← ZMod.inv_coe_unit]
    exact DirichletCharacter.sum_char_inv_mul_char_eq R r.isUnit b
  simp_rw [MulChar.gaussSum_pow_eq_sum, mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul, h, ite_mul, zero_mul]
  rw [← sum_filter, hyperKloosterman_eq_sum_prod_eq, mul_sum]
  simp_rw [eq_comm (a := (r : ZMod n))]

open scoped Classical in
/-- **Gauss-power sum over the even characters.** Twice the sum of `χ⁻¹ (r) τ(χ) ^ k`
over the even Dirichlet characters of level `n` is `φ(n)` times the sum of the
hyper-Kloosterman sums of rank `k` at `r` and at `-r`. -/
theorem two_mul_sum_even_inv_apply_mul_gaussSum_pow (ψ : AddChar (ZMod n) R) (k : ℕ)
    (r : (ZMod n)ˣ) :
    2 * ∑ χ : DirichletCharacter R n with χ.Even, χ⁻¹ r * gaussSum χ ψ ^ k =
      n.totient * (hyperKloosterman (ZMod n) k ψ r + hyperKloosterman (ZMod n) k ψ (-r)) := by
  have h (χ : DirichletCharacter R n) : χ (-1) * χ⁻¹ r = χ⁻¹ ↑(-r) := by
    simp_rw [MulChar.inv_apply, Ring.inverse_unit, ← map_mul]
    simp
  rw [DirichletCharacter.two_mul_sum_even, mul_add, ← sum_inv_apply_mul_gaussSum_pow,
    ← sum_inv_apply_mul_gaussSum_pow]
  simp_rw [← mul_assoc, h]

open scoped Classical in
/-- **Gauss-power sum over the even characters**, above level two: the sum of
`χ⁻¹ (r) τ(χ) ^ k` over the even Dirichlet characters of level `n` is `φ(n) / 2` times the sum of
the hyper-Kloosterman sums of rank `k` at `r` and at `-r`. -/
theorem sum_even_inv_apply_mul_gaussSum_pow (hn : 2 < n) (ψ : AddChar (ZMod n) R) (k : ℕ)
    (r : (ZMod n)ˣ) :
    ∑ χ : DirichletCharacter R n with χ.Even, χ⁻¹ r * gaussSum χ ψ ^ k =
      ((n.totient / 2 : ℕ) : R) *
        (hyperKloosterman (ZMod n) k ψ r + hyperKloosterman (ZMod n) k ψ (-r)) :=
  DirichletCharacter.sum_even_eq_totient_div_two_mul hn
    (two_mul_sum_even_inv_apply_mul_gaussSum_pow ψ k r)

end Level

open scoped Classical in
/-- **Gauss-power sum over the even nontrivial characters.** At an odd prime level `q`
and for a nontrivial additive character `ψ`, the sum of `χ⁻¹ (r) τ(χ) ^ k` over the even
Dirichlet characters `χ ≠ 1` is `(q - 1) / 2` times the sum of the hyper-Kloosterman sums of
rank `k` at `r` and at `-r`, minus the contribution `τ(1) ^ k = (-1) ^ k` of the trivial
character. -/
theorem sum_even_ne_one_inv_apply_mul_gaussSum_pow {q : ℕ} [Fact q.Prime]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod q)ˣ)] (hq : 2 < q) {ψ : AddChar (ZMod q) R}
    (hψ : ψ ≠ 1) (k : ℕ) (r : (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter R q with χ.Even ∧ χ ≠ 1, χ⁻¹ r * gaussSum χ ψ ^ k =
      (((q - 1) / 2 : ℕ) : R) *
        (hyperKloosterman (ZMod q) k ψ r + hyperKloosterman (ZMod q) k ψ (-r)) - (-1) ^ k := by
  rw [DirichletCharacter.sum_even_ne_one, sum_even_inv_apply_mul_gaussSum_pow hq, inv_one,
    MulChar.one_apply r.isUnit, gaussSum_one_left hψ, one_mul, Nat.totient_prime Fact.out]

end TauCeti
