/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate

/-!
# The rank and the crank of a partition

Dyson's **rank** of a partition is its largest part minus its number of parts. The **crank** of
Andrews and Garvan is defined in terms of the number `o` of parts equal to `1`: it is the largest
part when `o = 0`, and otherwise the number of parts strictly larger than `o`, minus `o`. Both
statistics are integers, and both vanish on the empty partition. They are the statistics whose
residue classes explain Ramanujan's partition congruences: the rank modulo `5` and `7`, and the
crank modulo `5`, `7` and `11`.

This file defines `Nat.Partition.rank` and `Nat.Partition.crank` on Mathlib's partitions, proves
that conjugation negates the rank (`Nat.Partition.rank_conjugate`), and computes both statistics on
the partitions of `0` and `1`; the crank of `(1)` is `-1`, so the crank counts of size one are not
symmetric. It then defines the two-variable generating series
`Nat.Partition.rankGenFun R = ∑ₙ (∑_{λ ⊢ n} z^{rank λ}) Xⁿ` and
`Nat.Partition.crankGenFun R = ∑ₙ (∑_{λ ⊢ n} z^{crank λ}) Xⁿ` as power series in `X` over the
Laurent polynomials `R[z, z⁻¹]`, given coefficientwise by finite sums so that no convergence in
`z` is involved. The coefficient of `z^m Xⁿ` counts the partitions of `n` with rank, respectively
crank, `m`. Conjugation shows that every rank coefficient is invariant under `z ↦ z⁻¹`
(`Nat.Partition.invert_coeff_rankGenFun`), that is, the number of partitions of `n` with rank `m`
equals the number with rank `-m` (`Nat.Partition.card_filter_rank_eq_neg`).

## References

* F. J. Dyson, *Some guesses in the theory of partitions*, Eureka 8 (1944), 10–15.
* G. E. Andrews and F. G. Garvan, *Dyson's crank of a partition*, Bull. Amer. Math. Soc. 18
  (1988), 167–171.
-/

public section

open Finset LaurentPolynomial

namespace Nat.Partition

variable {n : ℕ}

/-- **Dyson's rank** of a partition: its largest part minus its number of parts. The largest part
of the empty partition is taken to be `0`, so its rank is `0`. -/
def rank (p : n.Partition) : ℤ :=
  (p.parts.sup : ℤ) - Multiset.card p.parts

theorem rank_def (p : n.Partition) : p.rank = (p.parts.sup : ℤ) - Multiset.card p.parts :=
  (rfl)

/-- The **crank** of Andrews and Garvan. Write `o` for the number of parts equal to `1`. When
`o = 0` the crank is the largest part (`0` for the empty partition); otherwise it is the number of
parts strictly larger than `o`, minus `o`. -/
def crank (p : n.Partition) : ℤ :=
  if p.parts.count 1 = 0 then (p.parts.sup : ℤ)
  else (Multiset.card (p.parts.filter (p.parts.count 1 < ·)) : ℤ) - p.parts.count 1

/-- **A partition with no part equal to `1` has its largest part as crank.** -/
theorem crank_of_one_notMem {p : n.Partition} (h : 1 ∉ p.parts) : p.crank = p.parts.sup := by
  simp [crank, h]

/-- **The crank of a partition with a part equal to `1`**: with `o` parts equal to `1`, it is the
number of parts strictly larger than `o`, minus `o`. -/
theorem crank_of_one_mem {p : n.Partition} (h : 1 ∈ p.parts) :
    p.crank =
      (Multiset.card (p.parts.filter (p.parts.count 1 < ·)) : ℤ) - p.parts.count 1 := by
  simp [crank, h]

/-- **Conjugation negates the rank**: conjugation exchanges the largest part with the number of
parts. -/
@[simp]
theorem rank_conjugate (p : n.Partition) : p.conjugate.rank = -p.rank := by
  simp only [rank_def, card_conjugate_parts, sup_conjugate_parts]
  ring

/-- The empty partition has rank `0`. -/
@[simp]
theorem partition_zero_rank (p : Partition 0) : p.rank = 0 := by
  simp [rank_def]

/-- The empty partition has crank `0`. -/
@[simp]
theorem partition_zero_crank (p : Partition 0) : p.crank = 0 := by
  simp [crank_of_one_notMem]

/-- The partition `(1)` has rank `0`. -/
@[simp]
theorem partition_one_rank (p : Partition 1) : p.rank = 0 := by
  simp [rank_def]

/-- **The partition `(1)` has crank `-1`**: it has one part equal to `1` and no part larger than
`1`. In particular the crank counts of size one are not symmetric under `m ↦ -m`. -/
@[simp]
theorem partition_one_crank (p : Partition 1) : p.crank = -1 := by
  rw [crank_of_one_mem (by simp)]
  simp

/-- **The number of partitions of `n` with rank `-m` equals the number with rank `m`**, since
conjugation is an involution negating the rank. -/
theorem card_filter_rank_eq_neg (n : ℕ) (m : ℤ) :
    #{p : n.Partition | p.rank = -m} = #{p : n.Partition | p.rank = m} := by
  refine Finset.card_nbij' conjugate conjugate ?_ ?_ (fun p _ => conjugate_conjugate p)
    (fun p _ => conjugate_conjugate p) <;>
  · intro p hp
    simp at hp ⊢
    omega

section GenFun

variable (R : Type*) [Semiring R]

/-- The **rank generating series** `∑ₙ (∑_{λ ⊢ n} z^{rank λ}) Xⁿ`, a power series in `X` whose
`n`-th coefficient is the Laurent polynomial in `z` recording the ranks of the partitions of `n`.
The coefficients are finite sums, so no convergence in `z` is involved. -/
noncomputable def rankGenFun : PowerSeries R[T;T⁻¹] :=
  PowerSeries.mk fun n => ∑ p : n.Partition, T p.rank

/-- The **crank generating series** `∑ₙ (∑_{λ ⊢ n} z^{crank λ}) Xⁿ`, a power series in `X` whose
`n`-th coefficient is the Laurent polynomial in `z` recording the cranks of the partitions of `n`.
Its coefficient at `n = 1` is `z⁻¹`. -/
noncomputable def crankGenFun : PowerSeries R[T;T⁻¹] :=
  PowerSeries.mk fun n => ∑ p : n.Partition, T p.crank

variable {R}

/-- The `n`-th coefficient of the rank generating series is the sum of `z^{rank λ}` over the
partitions `λ` of `n`. -/
@[simp]
theorem coeff_rankGenFun (n : ℕ) :
    PowerSeries.coeff n (rankGenFun R) = ∑ p : n.Partition, T p.rank :=
  PowerSeries.coeff_mk _ _

/-- The `n`-th coefficient of the crank generating series is the sum of `z^{crank λ}` over the
partitions `λ` of `n`. -/
@[simp]
theorem coeff_crankGenFun (n : ℕ) :
    PowerSeries.coeff n (crankGenFun R) = ∑ p : n.Partition, T p.crank :=
  PowerSeries.coeff_mk _ _

/-- **The coefficient of `z^m Xⁿ` in the rank generating series counts the partitions of `n` with
rank `m`.** -/
theorem coeff_coeff_rankGenFun (n : ℕ) (m : ℤ) :
    (PowerSeries.coeff n (rankGenFun R)).coeff m = #{p : n.Partition | p.rank = m} := by
  simp [AddMonoidAlgebra.coeff_sum, Finset.sum_boole]

/-- **The coefficient of `z^m Xⁿ` in the crank generating series counts the partitions of `n`
with crank `m`.** -/
theorem coeff_coeff_crankGenFun (n : ℕ) (m : ℤ) :
    (PowerSeries.coeff n (crankGenFun R)).coeff m = #{p : n.Partition | p.crank = m} := by
  simp [AddMonoidAlgebra.coeff_sum, Finset.sum_boole]

/-- The rank generating series has constant coefficient `1`, from the empty partition. -/
theorem coeff_zero_rankGenFun : PowerSeries.coeff 0 (rankGenFun R) = 1 := by
  simp [T_zero]

/-- The coefficient of `X` in the rank generating series is `1`, from the partition `(1)` of
rank `0`. -/
theorem coeff_one_rankGenFun : PowerSeries.coeff 1 (rankGenFun R) = 1 := by
  simp [T_zero]

/-- The crank generating series has constant coefficient `1`, from the empty partition. -/
theorem coeff_zero_crankGenFun : PowerSeries.coeff 0 (crankGenFun R) = 1 := by
  simp [T_zero]

/-- The coefficient of `X` in the crank generating series is `z⁻¹`, from the partition `(1)` of
crank `-1`. -/
theorem coeff_one_crankGenFun : PowerSeries.coeff 1 (crankGenFun R) = T (-1) := by
  simp

end GenFun

/-- **The rank coefficients are symmetric under `z ↦ z⁻¹`**: conjugation is an involution of the
partitions of `n` negating the rank. -/
theorem invert_coeff_rankGenFun {R : Type*} [CommSemiring R] (n : ℕ) :
    invert (PowerSeries.coeff n (rankGenFun R)) = PowerSeries.coeff n (rankGenFun R) := by
  rw [coeff_rankGenFun, map_sum]
  simp_rw [invert_T, ← rank_conjugate]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ conjugate_conjugate)
    fun p : n.Partition => (T p.rank : R[T;T⁻¹])

end Nat.Partition
