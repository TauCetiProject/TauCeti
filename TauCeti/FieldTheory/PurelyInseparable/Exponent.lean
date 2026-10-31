/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# The exponent of a finite purely inseparable extension: degree bound and denominators

Let `L / K` be a finite purely inseparable extension in exponential characteristic `p`. If
`[L : K] ≤ p ^ n`, then every `p ^ n`-th power of `L` lies in `K`, and so the exponent of `L / K`
is at most `n`. In particular a purely inseparable extension of degree `p ^ n` is cut out by
`p ^ n`-th powers.

Mathlib's `IsPurelyInseparable.hasExponent_of_finiteDimensional` shows that a finite purely
inseparable extension *has* an exponent, but keeps the bound inside the instance proof. This file
states the bound, in the pointwise form a caller holding a degree uses and as a bound on
`IsPurelyInseparable.exponent`.

When `K` is the fraction field of a domain `A`, the exponent also clears denominators: rescaling
any `K`-basis of `L` gives one whose `p ^ n`-th powers all come from `A`.

## Main results

* `TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow`: if `[L : K] ≤ p ^ n`, every `p ^ n`-th
  power of `L` lies in `K`.
* `TauCeti.IsPurelyInseparable.exponent_le_of_finrank_le_pow`: if `[L : K] ≤ p ^ n`, the exponent
  of `L / K` is at most `n`.
* `TauCeti.IsPurelyInseparable.exists_basis_iterateFrobenius_eq_algebraMap`: over the fraction
  field of a domain `A`, a basis whose `p ^ n`-th powers lie in the image of `A`.
-/

public section

namespace TauCeti.IsPurelyInseparable

open _root_.IsPurelyInseparable

/-- **A basis with `p ^ n`-th powers in the base ring.** Let `K` be the fraction field of a domain
`A` and `L / K` a finite purely inseparable extension of exponent at most `n`. Then `L` has a
`K`-basis whose vectors have `p ^ n`-th powers in the image of `A`; `g` lists those preimages.
Start from any basis and multiply each vector by the denominator of its `p ^ n`-th power, which
lies in `K`. -/
theorem exists_basis_iterateFrobenius_eq_algebraMap (A K L : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [HasExponent K L] (p : ℕ) [ExpChar K p] {n : ℕ} (hn : exponent K L ≤ n) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) K L) (g : Fin m → A), ∀ j,
      algebraMap A K (g j) = iterateFrobenius K L p hn (b j) := by
  let b₀ := Module.finBasis K L
  choose a s hs has using fun j ↦ IsFractionRing.div_surjective (A := A)
    (iterateFrobenius K L p hn (b₀ j))
  have hs0 (j) : algebraMap A K (s j) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hs j)
  let b := b₀.unitsSMul fun j ↦ Units.mk0 _ (hs0 j)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_pos (expChar_pos K p) n).ne'
  refine ⟨_, b, fun j ↦ s j ^ k * a j, fun j ↦ ?_⟩
  -- scaling `b₀ j` by `c ∈ K` scales its `p ^ n`-th power by `c ^ p ^ n`
  have hscale : iterateFrobenius K L p hn (b j) =
      algebraMap A K (s j) ^ p ^ n * iterateFrobenius K L p hn (b₀ j) := by
    simp [b, Module.Basis.unitsSMul_apply, Units.smul_def, Algebra.smul_def,
      iterateFrobenius_algebraMap]
  -- what remains is denominator arithmetic in `K`
  rw [hscale, ← has j, hk, map_mul, map_pow]
  field_simp [hs0 j]
  ring

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
  [FiniteDimensional K L] (p : ℕ) [ExpChar K p]

/-- **A purely inseparable extension of degree at most `p ^ n` is cut out by `p ^ n`-th powers**:
every `a ^ p ^ n` lies in the base field. -/
theorem pow_mem_of_finrank_le_pow {n : ℕ} (h : Module.finrank K L ≤ p ^ n) (a : L) :
    a ^ p ^ n ∈ (algebraMap K L).range := by
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · -- in characteristic zero a purely inseparable extension is trivial
    obtain ⟨k, hk⟩ := IsPurelyInseparable.pow_mem K 1 a
    simpa using hk
  · -- the minimal polynomial of `a` is `X ^ p ^ e - c` with `e` its exponent, of degree at most
    -- `[L : K] ≤ p ^ n`, so `e ≤ n`
    have he : elemExponent K a ≤ n := by
      have h1 := minpoly.natDegree_le (A := K) a
      rw [minpoly_natDegree_eq' K p a] at h1
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h)
    obtain ⟨b, hb⟩ := elemExponent_def' K p a
    exact ⟨b ^ p ^ (n - elemExponent K a), by
      rw [map_pow, hb, ← pow_mul, ← pow_add, Nat.add_sub_cancel' he]⟩

/-- **The exponent of a purely inseparable extension of degree at most `p ^ n` is at most `n`.** -/
theorem exponent_le_of_finrank_le_pow {n : ℕ} (h : Module.finrank K L ≤ p ^ n) :
    exponent K L ≤ n := by
  by_contra hn
  obtain ⟨a, ha⟩ := exponent_min' p (not_le.1 hn)
  exact ha (pow_mem_of_finrank_le_pow K L p h a)

end TauCeti.IsPurelyInseparable

end
