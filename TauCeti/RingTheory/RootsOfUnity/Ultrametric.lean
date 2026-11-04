/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Distance from `1` of primitive roots of unity in ultrametric fields

Let `K` be a normed field with an ultrametric norm and `ζ ∈ K` a primitive `k`-th root of unity,
`k ≠ 0`. Every power of `ζ` is at most as far from `1` as `ζ`, and each primitive `k`-th root of
unity is a power of every other, so all primitive `k`-th roots of unity are at the same distance
from `1`. The cyclotomic polynomial `Φ_k = ∏ (X - η)`, the product over these roots `η`, then
gives `‖ζ - 1‖ ^ φ(k) = ‖Φ_k(1)‖`. For `k = p ^ (n + 1)` a prime power `Φ_k(1) = p`, so

`‖ζ - 1‖ ^ φ(p ^ (n + 1)) = ‖p‖`.

Over a normed field over `ℚ_p`, where `‖p‖ = p⁻¹`, this is the value `1 / (pⁿ (p - 1))` of the
normalised valuation of `ζ - 1`, which computes the coordinates of finite-order characters of
`ℤ_pˣ` from their conductors.

Following Mathlib's `IsPrimitiveRoot.norm'_eq_one`, the primed names distinguish the norm `‖·‖`
from `Algebra.norm`, which the unprimed names `IsPrimitiveRoot.norm_sub_one_*` refer to.

## Main results

* `IsPrimitiveRoot.norm'_sub_one_eq`: two primitive `k`-th roots of unity are at the same
  distance from `1`.
* `IsPrimitiveRoot.norm'_sub_one_pow_totient`: `‖ζ - 1‖ ^ φ(k) = ‖Φ_k(1)‖`.
* `IsPrimitiveRoot.norm'_sub_one_pow_totient_prime_pow`: `‖ζ - 1‖ ^ φ(p ^ (n + 1)) = ‖p‖`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Chapters 1–2.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {k : ℕ} {ζ η : K}

/-- In an ultrametric normed field, two primitive `k`-th roots of unity, `k ≠ 0`, are at the same
distance from `1`. -/
theorem norm'_sub_one_eq (hζ : IsPrimitiveRoot ζ k) (hη : IsPrimitiveRoot η k) (hk : k ≠ 0) :
    ‖η - 1‖ = ‖ζ - 1‖ := by
  have : NeZero k := ⟨hk⟩
  -- each of the two roots is a power of the other
  have key {ζ η : K} (hζ : IsPrimitiveRoot ζ k) (hη : IsPrimitiveRoot η k) :
      ‖η - 1‖ ≤ ‖ζ - 1‖ := by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη.pow_eq_one
    exact TauCeti.norm_pow_sub_one_le_norm_sub_one (hζ.isOfFinOrder hk).norm_eq_one.le i
  exact (key hζ hη).antisymm (key hη hζ)

/-- In an ultrametric normed field, a primitive `k`-th root of unity `ζ`, `k ≠ 0`, satisfies
`‖ζ - 1‖ ^ φ(k) = ‖Φ_k(1)‖`, where `Φ_k` is the `k`-th cyclotomic polynomial. -/
theorem norm'_sub_one_pow_totient (hζ : IsPrimitiveRoot ζ k) (hk : k ≠ 0) :
    ‖ζ - 1‖ ^ k.totient = ‖(cyclotomic k K).eval 1‖ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, norm_prod, ← hζ.card_primitiveRoots,
    ← Finset.prod_const]
  refine Finset.prod_congr rfl fun η hη ↦ ?_
  rw [eval_sub, eval_X, eval_C, norm_sub_rev 1 η,
    (isPrimitiveRoot_of_mem_primitiveRoots hη).norm'_sub_one_eq hζ hk]

/-- In an ultrametric normed field, a primitive `p ^ (n + 1)`-th root of unity `ζ`, `p` prime,
satisfies `‖ζ - 1‖ ^ φ(p ^ (n + 1)) = ‖p‖`. -/
theorem norm'_sub_one_pow_totient_prime_pow {p n : ℕ} [Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    ‖ζ - 1‖ ^ (p ^ (n + 1)).totient = ‖(p : K)‖ := by
  rw [hζ.norm'_sub_one_pow_totient (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    eval_one_cyclotomic_prime_pow]

end IsPrimitiveRoot
