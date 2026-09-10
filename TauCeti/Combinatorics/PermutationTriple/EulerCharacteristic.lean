/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.DisjointSum
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The Euler characteristic of a permutation triple

The surface carrying the cover encoded by a degree-`n` permutation triple `t` is glued from `n`
faces, and its cells are counted by the cycles of the three components. Its Euler characteristic
is therefore the integer

`χ(t) = cycleCount σ0 + cycleCount σ1 + cycleCount σinf − n`,

which this file defines as `TauCeti.PermutationTriple.eulerChar` — combinatorially, without
constructing the surface. The cycle counts are `TauCeti.orbitCount`, so a fixed point of a
component contributes a cycle of its own.

## Main results

* `TauCeti.PermutationTriple.even_eulerChar`: the Euler characteristic is even, equivalently
  `2 ∣ 2 - χ(t)`. This is the parity that makes the genus an integer, and it is a consequence of
  the defining relation `σinf * σ1 * σ0 = 1` alone: applying `Equiv.Perm.sign` to the relation and
  reading each sign off `Equiv.Perm.sign_eq_neg_one_pow_card_sub_orbitCount` says exactly that
  `3n - (cycleCount σ0 + cycleCount σ1 + cycleCount σinf)` is even.
* `TauCeti.PermutationTriple.eulerChar_disjointSum`: the Euler characteristic is additive over
  `TauCeti.PermutationTriple.disjointSum`, as an Euler characteristic of a disjoint union should
  be.
* `TauCeti.PermutationTriple.eulerChar_smul`,
  `TauCeti.PermutationTriple.eulerChar_eq_of_equivalent`: it is an invariant of the isomorphism
  class of a triple, and `TauCeti.PermutationTriple.eulerChar_transport` says it does not depend
  on the numbering of the sheets either.
* `TauCeti.PermutationTriple.eulerChar_one`: the trivial `n`-sheeted cover has Euler
  characteristic `2n`, the `n` spheres it consists of contributing `2` each.

The bound `χ(t) ≤ 2` for a connected triple, and with it the genus, are not proved here: they
need the transposition step lemma for `TauCeti.orbitCount` and an induction along a minimal
factorization of `σ1`.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, Proposition 1.5.3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {m n : ℕ}

/-- The Euler characteristic of a permutation triple: the total number of cycles of its three
components, fixed points included, less the degree. It is the Euler characteristic of the surface
obtained by gluing the associated cover, computed from the combinatorics alone. -/
noncomputable def eulerChar (t : PermutationTriple n) : ℤ :=
  (orbitCount t.σ0 : ℤ) + orbitCount t.σ1 + orbitCount t.σinf - n

theorem eulerChar_eq (t : PermutationTriple n) :
    t.eulerChar = (orbitCount t.σ0 : ℤ) + orbitCount t.σ1 + orbitCount t.σinf - n := (rfl)

/-- The Euler characteristic, read off the packaged cycle counts of a triple. -/
theorem eulerChar_eq_cycleCounts (t : PermutationTriple n) :
    t.eulerChar = (t.cycleCounts.1 : ℤ) + t.cycleCounts.2.1 + t.cycleCounts.2.2 - n := by
  simp [eulerChar_eq]

/-! ### Invariance -/

/-- Relabeling the sheets does not change the Euler characteristic. -/
@[simp]
theorem eulerChar_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    (τ • t).eulerChar = t.eulerChar := by
  rw [eulerChar_eq, eulerChar_eq]
  simp [orbitCount_conj]

/-- Isomorphic triples have the same Euler characteristic. -/
theorem eulerChar_eq_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    t.eulerChar = t'.eulerChar := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (eulerChar_smul τ t).symm

/-- Renumbering the sheets does not change the Euler characteristic. -/
@[simp]
theorem eulerChar_transport (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).eulerChar = t.eulerChar := by
  obtain rfl : n = m := by simpa using Fintype.card_congr e
  rw [eulerChar_eq, eulerChar_eq]
  simp [Equiv.permCongrHom_coe]

/-- The trivial `n`-sheeted cover is a disjoint union of `n` spheres. -/
@[simp]
theorem eulerChar_one : (1 : PermutationTriple n).eulerChar = 2 * n := by
  rw [eulerChar_eq]
  simp only [one_σ0, one_σ1, one_σinf, orbitCount_one, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  ring

/-! ### Parity -/

/-- The number of orbits of a permutation of `Fin n` is at most `n`, the orbits being the classes
of a partition of the sheets. -/
private theorem orbitCount_le (σ : Perm (Fin n)) : orbitCount σ ≤ n := by
  rw [Perm.orbitCount_eq_card_parts_partition]
  calc
    σ.partition.parts.card = σ.partition.parts.card • 1 := by simp
    _ ≤ σ.partition.parts.sum :=
      Multiset.card_nsmul_le_sum fun k hk ↦ σ.partition.parts_pos hk
    _ = n := by simpa using σ.partition.parts_sum

/-- The Euler characteristic of a permutation triple is even. Equivalently, by
`TauCeti.PermutationTriple.two_dvd_two_sub_eulerChar`, the genus `(2 - χ) / 2` is an integer.
The only input is the defining relation of a triple: the product of the three signs is the sign
of the identity, and each sign is the parity of the degree less the number of cycles. -/
theorem even_eulerChar (t : PermutationTriple n) : Even t.eulerChar := by
  have hsign : Perm.sign t.σinf * Perm.sign t.σ1 * Perm.sign t.σ0 = 1 := by
    rw [← Perm.sign_mul, ← Perm.sign_mul, t.product_eq_one, Perm.sign_one]
  rw [Perm.sign_eq_neg_one_pow_card_sub_orbitCount, Perm.sign_eq_neg_one_pow_card_sub_orbitCount,
    Perm.sign_eq_neg_one_pow_card_sub_orbitCount, Fintype.card_fin, ← pow_add, ← pow_add] at hsign
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mp hsign
  have h0 := orbitCount_le t.σ0
  have h1 := orbitCount_le t.σ1
  have hinf := orbitCount_le t.σinf
  refine ⟨(n : ℤ) - k, ?_⟩
  rw [eulerChar_eq]
  omega

/-- The genus of a permutation triple is `(2 - χ) / 2`, and this is the divisibility that makes
that an integer. -/
theorem two_dvd_two_sub_eulerChar (t : PermutationTriple n) : (2 : ℤ) ∣ 2 - t.eulerChar := by
  obtain ⟨k, hk⟩ := even_eulerChar t
  exact ⟨1 - k, by omega⟩

/-! ### Disjoint sums -/

/-- The Euler characteristic is additive over disjoint sums of triples, the two summands being
carried by disjoint sets of sheets. -/
@[simp]
theorem eulerChar_disjointSum (s : PermutationTriple m) (t : PermutationTriple n) :
    (s.disjointSum t).eulerChar = s.eulerChar + t.eulerChar := by
  rw [eulerChar_eq, eulerChar_eq, eulerChar_eq]
  simp only [disjointSum_σ0, disjointSum_σ1, disjointSum_σinf, orbitCount_finSumPerm]
  push_cast
  ring

/-! ### Worked examples

The monodromy of `z ↦ z ^ 3`, and a disjoint union of two trivial covers. -/

example : (ofTwo (finRotate 3) 1).eulerChar = 2 := by
  have h0 : (finRotate 3).partition.parts = {3} := by decide
  have h1 : (1 : Perm (Fin 3)).partition.parts = {1, 1, 1} := by decide
  have hinf : ((1 : Perm (Fin 3)) * finRotate 3)⁻¹.partition.parts = {3} := by decide
  rw [eulerChar_eq, Perm.orbitCount_eq_card_parts_partition,
    Perm.orbitCount_eq_card_parts_partition, Perm.orbitCount_eq_card_parts_partition,
    ofTwo_σ0, ofTwo_σ1, ofTwo_σinf, h0, h1, hinf]
  decide

example : ((1 : PermutationTriple 2).disjointSum (1 : PermutationTriple 3)).eulerChar = 10 := by
  rw [eulerChar_disjointSum, eulerChar_one, eulerChar_one]
  norm_num

end PermutationTriple

end TauCeti
