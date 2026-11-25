/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.RingTheory.RootsOfUnity.Ultrametric
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Distances from roots of unity to one

In an ultrametric normed field, primitive roots of the same order have the same distance
from one. Factoring the cyclotomic polynomial at one therefore computes a power of that
distance. In prime order `p`, this gives `‖ζ - 1‖ ^ (p - 1) = ‖p‖`, the identity used to
compute the radius of cyclotomic translations in p-adic analysis.

More generally, the cyclotomic polynomial of order `p ^ (k + 1)` takes the value `p` at one, and
that of an order other than one and a prime power takes the value one. So a primitive root of
order `p ^ (k + 1)` satisfies `‖ζ - 1‖ ^ φ(p ^ (k + 1)) = ‖p‖`, and one whose order is neither
one nor a prime power lies at distance one from one. If moreover `‖p‖ < 1`, every other prime has
norm one, and these combine into the lower bound `‖p‖ ≤ ‖ζ - 1‖ ^ (p - 1)` for every root of unity
`ζ ≠ 1`. Over `ℚ_[p]` and its extensions, where `‖p‖ = p⁻¹`, this is the classical bound
`|ζ - 1| ≥ p ^ (-1 / (p - 1))`: the open ball of that radius about one contains no root of unity
other than one. This is the cyclotomic input to the congruence argument of Borel showing that
arithmetic groups have neat subgroups of finite index (see Milne, Proposition 3.5).

The factorization and the enumeration of primitive roots are Mathlib's
`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots` and
`IsPrimitiveRoot.card_primitiveRoots`; the values at one are Mathlib's
`Polynomial.eval_one_cyclotomic_prime_pow` and `Polynomial.eval_one_cyclotomic_not_prime_pow`.

A square root `i` of `-1` is a fourth root of unity, so it has norm one in any normed ring whose
norm is multiplicative (`TauCeti.norm_eq_one_of_sq_eq_neg_one`), and in a nonarchimedean normed
field it lies in the valuation ring (`TauCeti.mem_integer_of_sq_eq_neg_one`).

## Main results

* `IsPrimitiveRoot.norm_sub_one_pow_totient`: `‖ζ - 1‖ ^ φ(n)` is the norm of the value of the
  `n`th cyclotomic polynomial at one.
* `IsPrimitiveRoot.norm'_sub_one_pow_totient_prime_pow` (in
  `TauCeti.RingTheory.RootsOfUnity.Ultrametric`): in order `p ^ (k + 1)` it is `‖p‖`.
* `IsPrimitiveRoot.norm_sub_one_eq_one_of_ne_pow`: if `‖p‖ < 1`, a primitive root whose order is
  not a power of `p` lies at distance one from one.
* `IsPrimitiveRoot.norm_natCast_le_norm_sub_one_pow`: if `‖p‖ < 1`, then
  `‖p‖ ≤ ‖ζ - 1‖ ^ (p - 1)` for every primitive root of order `n ≠ 1`.
* `IsOfFinOrder.eq_one_of_norm_sub_one_pow_lt`: a root of unity with
  `‖ζ - 1‖ ^ (p - 1) < ‖p‖` is one.
* `TauCeti.norm_eq_one_of_sq_eq_neg_one`, `TauCeti.mem_integer_of_sq_eq_neg_one`: a square root
  of `-1` has norm one and lies in the valuation ring.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §3, Proposition 3.5.
-/

public section

namespace IsPrimitiveRoot

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {n : ℕ} [NeZero n] {ζ ξ : K}

/-- Primitive roots of the same nonzero order have equal distance from one in an
ultrametric normed field. -/
theorem norm_sub_one_eq (hζ : IsPrimitiveRoot ζ n) (hξ : IsPrimitiveRoot ξ n) :
    ‖ζ - 1‖ = ‖ξ - 1‖ := by
  have hle {a b : K} (ha : IsPrimitiveRoot a n) (hb : IsPrimitiveRoot b n) :
      ‖b - 1‖ ≤ ‖a - 1‖ := by
    obtain ⟨i, _, rfl⟩ := ha.eq_pow_of_pow_eq_one hb.pow_eq_one
    have hnorm := (ha.isOfFinOrder (NeZero.ne n)).norm_eq_one
    simpa using TauCeti.norm_prod_sub_prod_le (s := Finset.range i)
      (f := fun _ => a) (g := fun _ => (1 : K)) (M := 1)
      (norm_nonneg (a - 1)) (by simp [hnorm]) (by simp) (by simp)
  exact le_antisymm (hle hξ hζ) (hle hζ hξ)

/-- Evaluating the cyclotomic polynomial at one computes a power of the distance from
a primitive root to one. -/
theorem norm_sub_one_pow_totient (hζ : IsPrimitiveRoot ζ n) :
    ‖ζ - 1‖ ^ n.totient = ‖(Polynomial.cyclotomic n K).eval 1‖ := by
  classical
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    Polynomial.eval_prod, norm_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  calc
    ‖ζ - 1‖ ^ n.totient = ∏ _ ∈ primitiveRoots n K, ‖ζ - 1‖ := by
      rw [Finset.prod_const, hζ.card_primitiveRoots]
    _ = ∏ ξ ∈ primitiveRoots n K, ‖1 - ξ‖ := by
      apply Finset.prod_congr rfl
      intro ξ hξ
      exact (hζ.norm_sub_one_eq ((mem_primitiveRoots (NeZero.pos n)).mp hξ)).trans
        (norm_sub_rev ξ 1)

/-- In prime order, the `(p - 1)`st power of the distance from a primitive root to one
is the norm of `p`. This includes order two and requires no completeness hypothesis. -/
theorem norm_sub_one_pow_prime_sub_one {p : ℕ} [Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) : ‖ζ - 1‖ ^ (p - 1) = ‖(p : K)‖ := by
  simpa [Nat.totient_prime (Fact.out : p.Prime), Polynomial.eval_one_cyclotomic_prime]
    using hζ.norm_sub_one_pow_totient

/-- A primitive root whose order is neither one nor a prime power lies at distance one from
one, since the cyclotomic polynomial of such an order takes the value one at one. -/
theorem norm_sub_one_of_not_isPrimePow (hζ : IsPrimitiveRoot ζ n) (hn1 : n ≠ 1)
    (hn : ¬IsPrimePow n) : ‖ζ - 1‖ = 1 := by
  have h := hζ.norm_sub_one_pow_totient
  rw [Polynomial.eval_one_cyclotomic_not_prime_pow fun {q} hq k hk ↦ ?_, norm_one] at h
  · exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.totient_pos.2 (NeZero.pos n)).ne').1 h
  · rcases k with _ | k
    · exact hn1 (by simpa using hk.symm)
    · exact hn ⟨q, k + 1, hq.prime, k.succ_pos, hk⟩

/-- If a prime `p` has norm less than one, a primitive root whose order is not a power of `p`
lies at distance one from one. This covers both a nontrivial order prime to `p` and an order
with a nontrivial part prime to `p`. -/
theorem norm_sub_one_eq_one_of_ne_pow {p : ℕ} (hp : p.Prime) (hpK : ‖(p : K)‖ < 1)
    (hζ : IsPrimitiveRoot ζ n) (hn : ∀ k, n ≠ p ^ k) : ‖ζ - 1‖ = 1 := by
  by_cases hpow : IsPrimePow n
  · obtain ⟨q, k, hq, hk, rfl⟩ := hpow
    have hq' : q.Prime := Nat.prime_iff.mpr hq
    have : Fact q.Prime := ⟨hq'⟩
    have hqp : q ≠ p := by
      rintro rfl
      exact hn k rfl
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
    have h := hζ.norm'_sub_one_pow_totient_prime_pow
    rw [IsUltrametricDist.norm_natCast_eq_one_of_coprime hpK
      ((Nat.coprime_primes hp hq').2 hqp.symm)] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.totient_pos.2 (NeZero.pos _)).ne').1 h
  · exact hζ.norm_sub_one_of_not_isPrimePow (fun h ↦ hn 0 (by simpa using h)) hpow

/-- **Distance of roots of unity from one.** If a prime `p` has norm less than one, every
primitive root of unity `ζ` of order `n ≠ 1` satisfies `‖p‖ ≤ ‖ζ - 1‖ ^ (p - 1)`. When `‖p‖ = p⁻¹`,
as over `ℚ_[p]` and its extensions, this says `‖ζ - 1‖ ≥ p ^ (-1 / (p - 1))`. -/
theorem norm_natCast_le_norm_sub_one_pow {p : ℕ} (hp : p.Prime) (hpK : ‖(p : K)‖ < 1)
    (hζ : IsPrimitiveRoot ζ n) (hn1 : n ≠ 1) : ‖(p : K)‖ ≤ ‖ζ - 1‖ ^ (p - 1) := by
  by_cases hpow : ∃ k, n = p ^ k
  · obtain ⟨k, rfl⟩ := hpow
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (show k ≠ 0 by
      rintro rfl
      exact hn1 (pow_zero p))
    have : Fact p.Prime := ⟨hp⟩
    have hle : ‖ζ - 1‖ ≤ 1 := Subring.mem_unitClosedBall.1 <| sub_mem
      (Subring.mem_unitClosedBall.2 (hζ.isOfFinOrder (NeZero.ne _)).norm_eq_one.le) (one_mem _)
    rw [← hζ.norm'_sub_one_pow_totient_prime_pow, Nat.totient_prime_pow_succ hp]
    exact pow_le_pow_of_le_one (norm_nonneg _) hle
      (Nat.le_mul_of_pos_left _ (pow_pos hp.pos k))
  · rw [hζ.norm_sub_one_eq_one_of_ne_pow hp hpK (not_exists.mp hpow), one_pow]
    exact hpK.le

end IsPrimitiveRoot

/-- **Roots of unity near one are trivial.** If a prime `p` has norm less than one, the only
root of unity `ζ` with `‖ζ - 1‖ ^ (p - 1) < ‖p‖` is `1`. When `‖p‖ = p⁻¹` the condition says
that `ζ` lies in the open ball of radius `p ^ (-1 / (p - 1))` about one. -/
theorem IsOfFinOrder.eq_one_of_norm_sub_one_pow_lt {K : Type*} [NormedField K]
    [IsUltrametricDist K] {p : ℕ} (hp : p.Prime) (hpK : ‖(p : K)‖ < 1) {ζ : K}
    (hζ : IsOfFinOrder ζ) (h : ‖ζ - 1‖ ^ (p - 1) < ‖(p : K)‖) : ζ = 1 := by
  have : NeZero (orderOf ζ) := ⟨hζ.orderOf_pos.ne'⟩
  by_contra hne
  exact ((IsPrimitiveRoot.orderOf ζ).norm_natCast_le_norm_sub_one_pow hp hpK
    (by rwa [Ne, orderOf_eq_one_iff])).not_gt h

namespace TauCeti

/-- A square root `i` of `-1` in a normed ring with multiplicative norm has norm one. -/
theorem norm_eq_one_of_sq_eq_neg_one {R : Type*} [NormedRing R] [NormMulClass R] [NormOneClass R]
    {i : R} (hi : i ^ 2 = -1) : ‖i‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg i) two_ne_zero).mp (by rw [← norm_pow, hi, norm_neg,
    norm_one])

/-- A square root `i` of `-1` in a nonarchimedean normed field lies in its valuation ring. -/
theorem mem_integer_of_sq_eq_neg_one {K : Type*} [NormedField K] [IsUltrametricDist K] {i : K}
    (hi : i ^ 2 = -1) : i ∈ (NormedField.valuation (K := K)).integer := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnNorm,
    norm_eq_one_of_sq_eq_neg_one hi]

end TauCeti
