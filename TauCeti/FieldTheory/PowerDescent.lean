/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import TauCeti.FieldTheory.Kummer.Character
import TauCeti.RingTheory.RootsOfUnity.PPower

/-!
# Descending roots along a field extension

Let `L / K` be a field extension and let `x ∈ K` be an `n`-th power in `L`. This file gives two
conditions under which `x` is already an `n`-th power in `K`.

* If `n` is coprime to `[L : K]`, write `x = yⁿ` with `y ∈ L`. Taking norms gives
  `N(y)ⁿ = x ^ [L : K]`, and a Bézout identity between `n` and `[L : K]` turns this into an `n`-th
  root of `x` in `K`.
* If `L / K` is Galois and `x = y ^ m`, then `σ y / y` is an `m`-th root of unity for every
  automorphism `σ`. When every `m`-th root of unity of `L` is an `r`-th root of unity, `y ^ r` is
  fixed by the Galois group, so it lies in `K`. In particular, if `L` contains no primitive
  `p ^ (k + 1)`-th root of unity for a prime `p` and `x` is a `p ^ (k + e)`-th power in `L`, then
  `x` is a `p ^ e`-th power in `K`.

These are two of the descent steps in Chevalley's proof that a congruence condition detects the
`n`-th powers in a finitely generated subgroup of the multiplicative group of a number field `M`.
The coprime case descends roots from the field `M(μ_p)`, whose degree over `M` divides `p - 1`.
The Galois case, for `p = 2` with `L = M(i)` and `2 ^ k` the largest order of a `2`-power root of
unity in `L`, returns roots from `M(i)` to `M` when `i ∉ M`.

## Main results

* `TauCeti.exists_pow_eq_of_coprime_finrank`: if `n` is coprime to `[L : K]`, then an element of
  `K` that is an `n`-th power in `L` is an `n`-th power in `K`.
* `TauCeti.pow_mem_range_algebraMap_of_forall_pow_eq_one`: for `L / K` Galois, if `y ^ m ∈ K` and
  every `m`-th root of unity of `L` is an `r`-th root of unity, then `y ^ r ∈ K`.
* `TauCeti.exists_pow_eq_of_forall_not_isPrimitiveRoot`: for `L / K` Galois without primitive
  `p ^ (k + 1)`-th roots of unity, a `p ^ (k + e)`-th power in `L` of an element of `K` is a
  `p ^ e`-th power in `K`.

## References

* C. Chevalley, *Deux théorèmes d'arithmétique*, J. Math. Soc. Japan 3 (1951), 36–44, §§1–5.
-/

public section

open Module

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Descent of roots through a coprime degree.** If `n` is coprime to `[L : K]`, an element of
`K` that is an `n`-th power in `L` is an `n`-th power in `K`. If `L / K` is infinite then
`finrank K L = 0`, so the hypothesis forces `n = 1`. -/
theorem exists_pow_eq_of_coprime_finrank {n : ℕ} (hn : n.Coprime (finrank K L)) {x : K} {y : L}
    (hy : y ^ n = algebraMap K L x) : ∃ z : K, z ^ n = x := by
  have h : Algebra.norm K y ^ n = x ^ finrank K L := by
    rw [← map_pow, hy, Algebra.norm_algebraMap]
  obtain ⟨z, -, hz⟩ := (pow_eq_pow_iff_of_coprime hn).1 h
  exact ⟨z, hz.symm⟩

/-- **Galois descent of a root.** Let `L / K` be Galois, and suppose every `m`-th root of unity of
`L` is an `r`-th root of unity. If `y ^ m` lies in `K`, then so does `y ^ r`: each automorphism `σ`
moves `y` by the `m`-th root of unity `σ y / y`, which is then an `r`-th root of unity. -/
theorem pow_mem_range_algebraMap_of_forall_pow_eq_one [IsGalois K L] {m r : ℕ}
    (hμ : ∀ ζ : L, ζ ^ m = 1 → ζ ^ r = 1) {y : L} (hy : y ^ m ∈ Set.range (algebraMap K L)) :
    y ^ r ∈ Set.range (algebraMap K L) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rcases r with _ | r
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed] at hy ⊢
  intro σ
  have h := hμ _ (apply_div_pow_eq_one hy0 (hy σ))
  rwa [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hy0), ← map_pow] at h

/-- **Galois descent of `p`-power roots.** Let `L / K` be Galois, `p` a prime, and suppose `L`
contains no primitive `p ^ (k + 1)`-th root of unity. If `x ∈ K` is a `p ^ (k + e)`-th power in
`L`, then it is a `p ^ e`-th power in `K`. -/
theorem exists_pow_eq_of_forall_not_isPrimitiveRoot [IsGalois K L] {p k e : ℕ} (hp : p.Prime)
    (hμ : ∀ ζ : L, ¬IsPrimitiveRoot ζ (p ^ (k + 1))) {x : K} {y : L}
    (hy : y ^ p ^ (k + e) = algebraMap K L x) : ∃ z : K, z ^ p ^ e = x := by
  obtain ⟨z, hz⟩ := pow_mem_range_algebraMap_of_forall_pow_eq_one (m := p ^ (k + e))
    (fun ζ hζ ↦ pow_prime_pow_eq_one_of_forall_not_isPrimitiveRoot hp hμ hζ) ⟨x, hy.symm⟩
  refine ⟨z, (algebraMap K L).injective ?_⟩
  rw [map_pow, hz, ← pow_mul, ← pow_add, hy]

end TauCeti
