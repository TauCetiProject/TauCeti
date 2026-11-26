/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.K3Surface.Cyclic.OrbitArithmetic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Simproc.Divisors
import Mathlib.Tactic.Simproc.Factors

/-!
# The exceptional root lattice of a symplectic cyclic quotient of a K3 surface

Let the cyclic group `C_n` act faithfully and symplectically on a K3 surface `X`, with `n`
invertible in the algebraically closed ground field, and let `a m` be the number of orbits whose
stabilizer has order `m`. The quotient `X / C_n` has an `A_{m-1}` singularity at the image of each
such orbit, and the `m - 1` exceptional `(-2)`-curves over it span a negative definite root lattice
of type `A_{m-1}` in the Picard lattice of the minimal resolution. The exceptional root lattice of
the resolution is therefore

```text
R = ⨁_{m ∣ n} A_{m-1}(-1) ^ (a m),
```

of rank `∑_{m ∣ n} a m * (m - 1)` and signed determinant `(-1) ^ rank * ∏_{m ∣ n} m ^ (a m)`.

The orbit relations of `TauCeti.IsK3CyclicOrbitData` leave the orders
`n ∈ {1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15}` when this lattice has rank at most `21`, and force
the lattices `2 A₁₀`, `A₁₃ ⊕ A₆ ⊕ A₁` and `A₁₄ ⊕ A₄ ⊕ A₂` of rank `20` for `n = 11, 14, 15`.
This file shows that these three lattices have the square determinants `121`, `196` and `225`
(in each case `n ^ 2`). In positive characteristic, an exceptional root lattice of rank `20`
has nonsquare determinant (Dolgachev–Keum), so this excludes the three orders, and the orbit
relations then determine the number of points fixed by the generator: the pair
`(n, fixed points)` is one of `(2, 8)`, `(3, 6)`, `(4, 4)`, `(5, 4)`, `(6, 2)`, `(7, 3)`,
`(8, 2)`. In characteristic zero the rank is at most `19` and the nonsquare hypothesis is
vacuous.

## Main definitions

* `TauCeti.cyclicRootLattice n a`: the integral lattice `⨁_{m ∣ n} A_{m-1}(-1) ^ (a m)`.

## Main results

* `TauCeti.finrank_cyclicRootLattice`, `TauCeti.discriminant_cyclicRootLattice`,
  `TauCeti.determinant_cyclicRootLattice`: its rank `TauCeti.cyclicRootRank n a`, discriminant
  `∏_{m ∣ n} m ^ (a m)` and signed determinant.
* `TauCeti.IsK3CyclicOrbitData.determinant_cyclicRootLattice_eq_sq`: for the orders `11`, `14`
  and `15` the determinant is `n ^ 2`.
* `TauCeti.IsK3CyclicOrbitData.le_eight_of_not_isSquare`: if a rank-`20` exceptional lattice has
  nonsquare determinant, then `n ≤ 8`.
* `TauCeti.IsK3CyclicOrbitData.mem_fixedPointTable`: the order of the action and the number of
  points fixed by its generator form one of the seven pairs above.

## References

* V. V. Nikulin, *Finite automorphism groups of Kähler K3 surfaces*, Trans. Moscow Math. Soc.
  38 (1980), §5.
* I. Dolgachev and J. Keum, *Finite groups of symplectic automorphisms of K3 surfaces in positive
  characteristic*, Ann. of Math. 169 (2009), Lemmas 3.1–3.2 and Theorem 3.3.
-/

public section

namespace TauCeti

open IntegralLattice

/-- **The exceptional root lattice** `⨁_{m ∣ n} A_{m-1}(-1) ^ (a m)` of the minimal resolution of
the quotient of a K3 surface by a symplectic action of the cyclic group of order `n` with `a m`
orbits whose stabilizer has order `m`. It has one summand for each pair `⟨m, i⟩` with `m ∣ n` and
`i < a m`: the type `A_{m-1}` root lattice with its form negated, the lattice spanned by the
exceptional `(-2)`-curves over the image of an orbit with stabilizer of order `m`. Summands with
`m = 1` have rank `0`. -/
noncomputable def cyclicRootLattice (n : ℕ) (a : ℕ → ℕ) :
    IntegralLattice (∀ p : Σ m : n.divisors, Fin (a m), Fin ((p.1 : ℕ) - 1) → ℚ) :=
  -pi fun p ↦ typeARootLattice ((p.1 : ℕ) - 1)

theorem cyclicRootLattice_def (n : ℕ) (a : ℕ → ℕ) :
    cyclicRootLattice n a = -pi fun p ↦ typeARootLattice ((p.1 : ℕ) - 1) :=
  (rfl)

/-- The exceptional root lattice is even. -/
theorem isEven_cyclicRootLattice (n : ℕ) (a : ℕ → ℕ) : (cyclicRootLattice n a).IsEven := by
  rw [cyclicRootLattice_def, isEven_neg_iff, isEven_pi_iff]
  exact fun _ ↦ isEven_typeARootLattice _

/-- The exceptional root lattice is negative definite. -/
theorem isNegDef_cyclicRootLattice (n : ℕ) (a : ℕ → ℕ) : (cyclicRootLattice n a).IsNegDef := by
  rw [cyclicRootLattice_def, isNegDef_neg_iff, isPosDef_pi_iff]
  exact fun _ ↦ isPosDef_typeARootLattice _

/-- The rank of the exceptional root lattice is `∑_{m ∣ n} a m * (m - 1)`. -/
@[simp]
theorem finrank_cyclicRootLattice (n : ℕ) (a : ℕ → ℕ) :
    Module.finrank ℤ (cyclicRootLattice n a) = cyclicRootRank n a := by
  rw [cyclicRootLattice_def, finrank_neg, finrank_pi, cyclicRootRank_def,
    ← Finset.sum_coe_sort n.divisors, Fintype.sum_sigma]
  simp [finrank_carrier]

/-- The discriminant of the exceptional root lattice is `∏_{m ∣ n} m ^ (a m)`: the type `A_{m-1}`
root lattice has discriminant `m`. -/
@[simp]
theorem discriminant_cyclicRootLattice (n : ℕ) (a : ℕ → ℕ) :
    (cyclicRootLattice n a).discriminant = ∏ m ∈ n.divisors, m ^ a m := by
  rw [cyclicRootLattice_def, discriminant_neg, discriminant_pi,
    ← Finset.prod_coe_sort n.divisors, Fintype.prod_sigma]
  refine Fintype.prod_congr _ _ fun m ↦ ?_
  simp [Nat.sub_add_cancel (Nat.pos_of_mem_divisors m.property)]

/-- The signed determinant of the exceptional root lattice is
`(-1) ^ rank * ∏_{m ∣ n} m ^ (a m)`, the lattice being negative definite. -/
theorem determinant_cyclicRootLattice (n : ℕ) (a : ℕ → ℕ) :
    (cyclicRootLattice n a).determinant =
      (-1) ^ cyclicRootRank n a * ∏ m ∈ n.divisors, (m : ℤ) ^ a m := by
  obtain ⟨hpos, hnull⟩ := (isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero _).mp
    (isNegDef_cyclicRootLattice n a)
  have hsum := (cyclicRootLattice n a).signature_sum_eq_finrank
  rw [← finrank_carrier, finrank_cyclicRootLattice] at hsum
  rw [determinant_eq_neg_one_pow_sigNeg_mul_discriminant, discriminant_cyclicRootLattice]
  push_cast
  congr 2
  omega

/-- **The exceptional root lattices of orders `11`, `14` and `15` have square determinant.** For
these orders the orbit relations force the lattices `2 A₁₀`, `A₁₃ ⊕ A₆ ⊕ A₁` and
`A₁₄ ⊕ A₄ ⊕ A₂` of rank `20`, with determinants `121`, `196` and `225`, in each case `n ^ 2`. -/
theorem IsK3CyclicOrbitData.determinant_cyclicRootLattice_eq_sq {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n = 11 ∨ n = 14 ∨ n = 15) :
    (cyclicRootLattice n a).determinant = n ^ 2 := by
  rw [determinant_cyclicRootLattice, h.cyclicRootRank_eq_twenty hn]
  rcases hn with rfl | rfl | rfl
  · simp [Nat.divisors_ofNat, h.orbitCounts_eleven]
  · obtain ⟨h2, h7, h14⟩ := h.orbitCounts_fourteen
    simp [Nat.divisors_ofNat, h2, h7, h14]
  · obtain ⟨h3, h5, h15⟩ := h.orbitCounts_fifteen
    simp [Nat.divisors_ofNat, h3, h5, h15]

/-- **Exclusion of the orders `11`, `14` and `15`.** If the orbit relations hold for the cyclic
group of order `n`, the exceptional root lattice has rank at most `21`, and its determinant is not
a square when its rank is `20` (as holds in positive characteristic), then `n ≤ 8`. -/
theorem IsK3CyclicOrbitData.le_eight_of_not_isSquare {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hrank : cyclicRootRank n a ≤ 21)
    (hsq : cyclicRootRank n a = 20 → ¬IsSquare (cyclicRootLattice n a).determinant) : n ≤ 8 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Nat.zero_le 8
  have hmem := h.mem_candidates hn hrank
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  by_contra h8
  have h' : n = 11 ∨ n = 14 ∨ n = 15 := by omega
  refine hsq (h.cyclicRootRank_eq_twenty h') ?_
  rw [h.determinant_cyclicRootLattice_eq_sq h']
  exact ⟨n, sq (n : ℤ)⟩

/-- **The element-order and fixed-point table.** If the orbit relations hold for the cyclic group
of order `n > 1`, the exceptional root lattice has rank at most `21`, and its determinant is not a
square when its rank is `20`, then the order `n` and the number of points fixed by a generator form
one of the pairs `(2, 8)`, `(3, 6)`, `(4, 4)`, `(5, 4)`, `(6, 2)`, `(7, 3)`, `(8, 2)`. -/
theorem IsK3CyclicOrbitData.mem_fixedPointTable {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : 1 < n) (hrank : cyclicRootRank n a ≤ 21)
    (hsq : cyclicRootRank n a = 20 → ¬IsSquare (cyclicRootLattice n a).determinant) :
    (n, cyclicFixedPointCount n a n) ∈
      ({(2, 8), (3, 6), (4, 4), (5, 4), (6, 2), (7, 3), (8, 2)} : Finset (ℕ × ℕ)) := by
  have h8 := h.le_eight_of_not_isSquare hrank hsq
  have hF := h.cyclicFixedPointCount_eq_mathieuFunction (Nat.mem_divisors_self n (by omega)) hn
  interval_cases n <;>
    · norm_num [mathieuFunction_eq_primeFactorsList] at hF
      norm_cast at hF
      simp [hF]

/-! ### Examples -/

/-- Under the rank bound `19`, as in characteristic zero, the nonsquare hypothesis is vacuous and
the order is at most `8`. -/
example {n : ℕ} {a : ℕ → ℕ} (h : IsK3CyclicOrbitData n a) (hrank : cyclicRootRank n a ≤ 19) :
    n ≤ 8 :=
  h.le_eight_of_not_isSquare (by omega) fun h20 ↦ absurd h20 (by omega)

/-- A symplectic involution: eight `A₁` points, an exceptional lattice `8 A₁(-1)` of determinant
`2 ^ 8`. -/
example : (cyclicRootLattice 2 (fun m ↦ if m = 2 then 8 else 0)).determinant = 256 := by
  rw [determinant_cyclicRootLattice]
  simp [cyclicRootRank_def, Nat.divisors_ofNat]

/-- Order `14` survives the orbit relations, with exceptional lattice `A₁₃ ⊕ A₆ ⊕ A₁` of rank `20`
and square determinant `196 = 14 ^ 2`. -/
example : (cyclicRootLattice 14 (fun m ↦ if m = 2 ∨ m = 7 ∨ m = 14 then 1 else 0)).determinant =
    196 := by
  rw [determinant_cyclicRootLattice]
  simp [cyclicRootRank_def, Nat.divisors_ofNat]

end TauCeti
