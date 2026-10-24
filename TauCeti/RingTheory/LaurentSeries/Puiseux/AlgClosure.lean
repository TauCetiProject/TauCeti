/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.RingTheory.LaurentSeries.Level.Basis
public import TauCeti.RingTheory.LaurentSeries.NewtonPuiseux

/-!
# The Puiseux field is an algebraic closure of the Laurent-series field

Let `K` be an algebraically closed field of characteristic zero. This file proves that the Puiseux
field `puiseuxField K` is algebraically closed, and hence, being algebraic over `K⸨X⸩`, an
algebraic closure of `K⸨X⸩`.

A polynomial `P` over the Puiseux field has its finitely many coefficients in a single ramified
level `n`, so it is the image of a polynomial `Q` over `K⸨u⸩` under the level-`n` embedding
`u ↦ t ^ (1 / n)`. The Newton–Puiseux theorem over `K⸨u⸩` gives a root of `Q` after a further
ramification `u ↦ u ^ m`, and the level-`n * m` embedding carries it to a root of `P`. In
particular every root found this way lies in one ramified level.

The last section computes the roots of the binomials `Y ^ n - a t ^ (n * q)` whenever `K` contains
a primitive `n`-th root of unity: they are the monomials `ζ ^ i b t ^ q` with `b ^ n = a`. This
covers the roots `ζ ^ i t ^ (1 / n)` of `Y ^ n - t`, whose leading order `1 / n` is fractional,
and the branches `t ± t ^ (3 / 2)` of `(Y - t) ^ 2 = t ^ 3`, which share the initial term `t`.

## Main results

* `TauCeti.puiseuxField.exists_isRoot_levelEmbedding`: a nonconstant polynomial over the
  Puiseux field has a root lying in a single ramified level.
* `TauCeti.puiseuxField.instIsAlgClosed`: the Puiseux field is algebraically closed.
* `TauCeti.puiseuxField.instIsAlgClosure`: the Puiseux field is an algebraic closure of `K⸨X⸩`.
* `TauCeti.puiseuxField.pow_eq_single_iff`: the solutions of `y ^ n = a t ^ (n * q)`.
* `TauCeti.puiseuxField.pow_eq_single_one_iff`: the solutions of `y ^ n = t`.
* `TauCeti.puiseuxField.sub_single_sq_eq_single_iff`: the solutions of `(y - t) ^ 2 = t ^ 3`.

## References

* H. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, arXiv:1304.6770, §1.
-/

public section

open Polynomial hiding expand
open scoped LaurentSeries

namespace TauCeti.puiseuxField

open _root_.LaurentSeries

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- **Newton–Puiseux theorem.** Over an algebraically closed field `K` of characteristic zero,
every nonconstant polynomial over the Puiseux field has a root lying in a single ramified level. -/
theorem exists_isRoot_levelEmbedding {P : (puiseuxField K)[X]} (hP : P.degree ≠ 0) :
    ∃ (n : ℕ+) (y : K⸨X⸩), P.IsRoot (levelEmbedding K n y) := by
  obtain ⟨n, Q, rfl⟩ := exists_map_levelEmbedding_eq P
  rw [degree_map] at hP
  obtain ⟨m, y, hy⟩ := exists_isRoot_map_levelEmbedding n hP
  exact ⟨n * m, y, hy⟩

/-- Over an algebraically closed field `K` of characteristic zero, the Puiseux field is
algebraically closed. -/
instance instIsAlgClosed : IsAlgClosed (puiseuxField K) :=
  IsAlgClosed.of_exists_root _ fun _ _ hirr ↦
    let ⟨_, _, hy⟩ := exists_isRoot_levelEmbedding (degree_pos_of_irreducible hirr).ne'
    ⟨_, hy⟩

/-- Over an algebraically closed field `K` of characteristic zero, the Puiseux field is an
algebraic closure of the Laurent-series field `K⸨X⸩`. -/
instance instIsAlgClosure : IsAlgClosure K⸨X⸩ (puiseuxField K) :=
  ⟨inferInstance, isAlgebraic_laurentSeries K⟩

end AlgClosed

/-! ### Binomial equations -/

section Binomial

variable {K : Type*} [Field K]

/-- If `K` contains a primitive `n`-th root of unity `ζ` and `b ^ n = a`, then the solutions of
`y ^ n = a t ^ (n * q)` in the Puiseux field are the monomials `ζ ^ i b t ^ q` for `i < n`. -/
theorem pow_eq_single_iff {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) (q : ℚ)
    (b : K) {y : puiseuxField K} :
    y ^ n = single K (n * q) (b ^ n) ↔ ∃ i < n, y = single K q (ζ ^ i * b) := by
  have hroots := (hζ.map_of_injective (algebraMap K (puiseuxField K)).injective).nthRoots_eq
    (single_pow q b n)
  rw [← mem_nthRoots hn, hroots, Multiset.mem_map]
  simp only [Multiset.mem_range, ← map_pow, algebraMap_mul_single, eq_comm (a := y)]

/-- If `K` contains a primitive `n`-th root of unity `ζ`, then the roots of `Y ^ n - t` in the
Puiseux field are the monomials `ζ ^ i t ^ (1 / n)` for `i < n`. -/
theorem pow_eq_single_one_iff {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {y : puiseuxField K} :
    y ^ n = single K 1 1 ↔ ∃ i < n, y = single K (1 / n) (ζ ^ i) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  simpa [mul_inv_cancel₀ hn'] using pow_eq_single_iff hn hζ (1 / n) 1 (y := y)

/-- The solutions of `(Y - t) ^ 2 = t ^ 3` in the Puiseux field are the branches
`t ± t ^ (3 / 2)`, which share the initial term `t`. -/
theorem sub_single_sq_eq_single_iff {y : puiseuxField K} :
    (y - single K 1 1) ^ 2 = single K 3 1 ↔
      y = single K 1 1 + single K (3 / 2) 1 ∨ y = single K 1 1 - single K (3 / 2) 1 := by
  have h : single K (3 / 2) 1 ^ 2 = single K 3 1 := by
    rw [single_pow]
    norm_num
  rw [← h, sq_eq_sq_iff_eq_or_eq_neg, sub_eq_iff_eq_add', sub_eq_iff_eq_add', ← sub_eq_add_neg]

end Binomial

end TauCeti.puiseuxField
