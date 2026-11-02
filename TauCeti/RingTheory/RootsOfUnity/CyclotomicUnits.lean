/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# `p` and `(ζ - 1) ^ (p - 1)` are associated

Let `p` be a prime and `ζ` a primitive `p`-th root of unity in a domain `A`. Evaluating the
cyclotomic polynomial `Φ_p = ∏ (X - η)`, the product over the primitive `p`-th roots `η`, at `1`
gives `p = ∏ (1 - η)`, and each `1 - η` is associated to `ζ - 1`. Hence `p` is associated to
`(ζ - 1) ^ (p - 1)`. In particular every valuation of `A` takes the value `v(ζ - 1) ^ (p - 1)`
at `p`, which is how the valuation normalised by `v(p) = 1` is read off from one normalised by
`v(ζ - 1) = 1`.

Mathlib proves this statement for the ring of integers of a `p`-th cyclotomic field
(`IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime`); the proof here is the same, in an
arbitrary domain.

## Main results

* `IsPrimitiveRoot.associated_sub_one_pow_prime`: `(ζ - 1) ^ (p - 1)` is associated to `p`.
-/

public section

open Polynomial in
/-- If `ζ` is a primitive `p`-th root of unity in a domain `A` and `p` is prime, then
`(ζ - 1) ^ (p - 1)` is associated to `p`. -/
theorem IsPrimitiveRoot.associated_sub_one_pow_prime {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} [hp : Fact p.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : A) := by
  rw [← eval_one_cyclotomic_prime (R := A) (p := p), cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨i, -, hi, rfl⟩ := hζ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right
