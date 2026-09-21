/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.DisjointSum
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.GroupTheory.Perm.SwapFactors
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
  `2 ∣ 2 - χ(t)`. For connected triples, this is the divisibility needed to define the genus.
* `TauCeti.PermutationTriple.eulerChar_disjointSum`: the Euler characteristic is additive over
  `TauCeti.PermutationTriple.disjointSum`, as an Euler characteristic of a disjoint union should
  be.
* `TauCeti.PermutationTriple.eulerChar_le_two_mul_card_monodromyOrbits`: the Euler characteristic
  is at most twice the number of monodromy orbits.
* `TauCeti.PermutationTriple.IsConnected.eulerChar_le_two`: a connected triple has Euler
  characteristic at most two, proved combinatorially from transposition factorizations.
* `TauCeti.PermutationTriple.genus`: the genus derived from the Euler characteristic, with its
  integer characterizations for connected triples.
* `TauCeti.PermutationTriple.eulerChar_smul`,
  `TauCeti.PermutationTriple.eulerChar_eq_of_equivalent`: it is an invariant of the isomorphism
  class of a triple, and `TauCeti.PermutationTriple.eulerChar_transport` says it does not depend
  on the numbering of the sheets either.
* `TauCeti.PermutationTriple.eulerChar_one`: the trivial `n`-sheeted cover has Euler
  characteristic `2n`, the `n` spheres it consists of contributing `2` each.

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

theorem eulerChar_def (t : PermutationTriple n) :
    t.eulerChar = (orbitCount t.σ0 : ℤ) + orbitCount t.σ1 + orbitCount t.σinf - n := (rfl)

/-- The Euler characteristic, read off the packaged cycle counts of a triple. -/
theorem eulerChar_eq_cycleCounts (t : PermutationTriple n) :
    t.eulerChar = (t.cycleCounts.1 : ℤ) + t.cycleCounts.2.1 + t.cycleCounts.2.2 - n := by
  simp [eulerChar_def]

/-! ### Invariance -/

/-- Relabeling the sheets does not change the Euler characteristic. -/
@[simp]
theorem eulerChar_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    (τ • t).eulerChar = t.eulerChar := by
  rw [eulerChar_def, eulerChar_def]
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
  rw [eulerChar_def, eulerChar_def]
  simp [Equiv.permCongrHom_coe]

/-- The trivial `n`-sheeted cover is a disjoint union of `n` spheres. -/
@[simp]
theorem eulerChar_one : (1 : PermutationTriple n).eulerChar = 2 * n := by
  rw [eulerChar_def]
  simp only [one_σ0, one_σ1, one_σinf, orbitCount_one, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  ring

/-! ### Parity -/

/-- The Euler characteristic of a permutation triple is even. -/
theorem even_eulerChar (t : PermutationTriple n) : Even t.eulerChar := by
  have hsign : Perm.sign t.σinf * Perm.sign t.σ1 * Perm.sign t.σ0 = 1 := by
    rw [← Perm.sign_mul, ← Perm.sign_mul, t.product_eq_one, Perm.sign_one]
  rw [Perm.sign_eq_neg_one_pow_card_sub_orbitCount, Perm.sign_eq_neg_one_pow_card_sub_orbitCount,
    Perm.sign_eq_neg_one_pow_card_sub_orbitCount, Fintype.card_fin, ← pow_add, ← pow_add] at hsign
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mp hsign
  have h0 : orbitCount t.σ0 ≤ n := by simpa using t.σ0.orbitCount_le_card
  have h1 : orbitCount t.σ1 ≤ n := by simpa using t.σ1.orbitCount_le_card
  have hinf : orbitCount t.σinf ≤ n := by simpa using t.σinf.orbitCount_le_card
  refine ⟨(n : ℤ) - k, ?_⟩
  rw [eulerChar_def]
  omega

/-- Two divides `2 - χ` for every permutation triple. For connected triples, this is the
divisibility needed to define the genus. -/
theorem two_dvd_two_sub_eulerChar (t : PermutationTriple n) : (2 : ℤ) ∣ 2 - t.eulerChar := by
  obtain ⟨k, hk⟩ := even_eulerChar t
  exact ⟨1 - k, by omega⟩

/-! ### The Euler bound and genus -/

-- The proof applies the combinatorial transposition route componentwise, through
-- `TauCeti.card_add_orbitCount_le_length_add_two_mul_card_orbits`.
/-- The Euler characteristic of a permutation triple is at most twice the number of orbits of
its monodromy group. For a connected triple the orbit quotient has one element, recovering
`TauCeti.PermutationTriple.IsConnected.eulerChar_le_two`. -/
theorem eulerChar_le_two_mul_card_monodromyOrbits (t : PermutationTriple n) :
    t.eulerChar ≤
      2 * Nat.card (MulAction.orbitRel.Quotient t.monodromyGroup (Fin n)) := by
  obtain ⟨L0, hswap0, hprod0, hlen0⟩ :=
    t.σ0.exists_isSwap_list_prod_eq_and_orbitCount_add_length_eq_card
  obtain ⟨L1, hswap1, hprod1, hlen1⟩ :=
    t.σ1.exists_isSwap_list_prod_eq_and_orbitCount_add_length_eq_card
  let L := L1 ++ L0
  let H := Subgroup.closure {g : Perm (Fin n) | g ∈ L}
  have hL : ∀ g ∈ L, g.IsSwap := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hswap1 g hg
    · exact hswap0 g hg
  have hσ0 : t.σ0 ∈ H := by
    rw [← hprod0]
    exact H.list_prod_mem fun g hg => Subgroup.subset_closure
      (List.mem_append_right L1 hg)
  have hσ1 : t.σ1 ∈ H := by
    rw [← hprod1]
    exact H.list_prod_mem fun g hg => Subgroup.subset_closure
      (List.mem_append_left L0 hg)
  have hmonodromy : t.monodromyGroup ≤ H := by
    rw [← t.closure_triple_eq_monodromyGroup, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hσ0
    · exact hσ1
    · rw [t.σinf_eq_inv]
      exact inv_mem (mul_mem hσ1 hσ0)
  have hcomponent : Nat.card (MulAction.orbitRel.Quotient H (Fin n)) ≤
      Nat.card (MulAction.orbitRel.Quotient t.monodromyGroup (Fin n)) :=
    MulAction.card_orbitRelQuotient_anti hmonodromy
  have hbound := card_add_orbitCount_le_length_add_two_mul_card_orbits hL
  have hprod : L.prod = t.σinf⁻¹ := by
    dsimp only [L]
    rw [List.prod_append, hprod1, hprod0, t.σ1_mul_σ0_eq_σinf_inv]
  have hn : Nat.card (Fin n) = n := by simp
  rw [hprod, orbitCount_inv] at hbound
  dsimp only [L, H] at hbound hcomponent
  rw [List.length_append, hn] at hbound
  rw [hn] at hlen0 hlen1
  rw [eulerChar_def]
  omega

/-- The Euler characteristic of a connected permutation triple is at most two. This is the
combinatorial Euler bound; it is what makes the genus
`TauCeti.PermutationTriple.genus` of a connected triple a genuine natural number. -/
theorem IsConnected.eulerChar_le_two {t : PermutationTriple n} (ht : t.IsConnected) :
    t.eulerChar ≤ 2 := by
  let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero ht.ne_zero)
  have := ht.isPretransitive
  have horbit : Nat.card (MulAction.orbitRel.Quotient t.monodromyGroup (Fin n)) = 1 :=
    MulAction.card_orbitRelQuotient_eq_one
  have hbound := eulerChar_le_two_mul_card_monodromyOrbits t
  rw [horbit] at hbound
  omega

/-- The genus of a permutation triple, defined by the Euler-characteristic formula. For a
connected triple, `TauCeti.PermutationTriple.IsConnected.natCast_genus` identifies this natural
number with the integer quotient `(2 - χ) / 2`, and
`TauCeti.PermutationTriple.IsConnected.two_sub_two_mul_genus` makes the `Int.toNat` junk-free.

Connectedness is what gives the number its geometric meaning: the surface of a triple with `c`
monodromy orbits has total genus `c - χ / 2`, which this formula computes only when `c = 1`, so
on a disconnected triple the truncation returns a junk value and not a genus. Accordingly every
statement below that reads the genus geometrically assumes
`TauCeti.PermutationTriple.IsConnected`. -/
noncomputable def genus (t : PermutationTriple n) : ℕ := ((2 - t.eulerChar) / 2).toNat

/-- The defining formula for the genus. -/
theorem genus_def (t : PermutationTriple n) :
    t.genus = ((2 - t.eulerChar) / 2).toNat := (rfl)

/-- Relabeling the sheets does not change the genus. -/
@[simp]
theorem genus_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    (τ • t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_smul]

/-- Isomorphic permutation triples have the same genus. -/
theorem genus_eq_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    t.genus = t'.genus := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (genus_smul τ t).symm

/-- Renumbering the sheets does not change the genus. -/
@[simp]
theorem genus_transport (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_transport]

/-- A triple of degree one has genus zero. -/
theorem genus_of_degree_one (t : PermutationTriple 1) : t.genus = 0 := by
  rw [Subsingleton.elim t 1, genus_def, eulerChar_one]
  norm_num

/-- For a connected triple, coercing its genus back to the integers recovers the exact quotient
`(2 - χ) / 2`; the connected Euler bound supplies its nonnegativity. -/
theorem IsConnected.natCast_genus {t : PermutationTriple n} (ht : t.IsConnected) :
    (t.genus : ℤ) = (2 - t.eulerChar) / 2 := by
  rw [genus_def, Int.natCast_toNat_eq_self]
  have hle := ht.eulerChar_le_two
  have hnonneg : 0 ≤ 2 - t.eulerChar := by omega
  exact Int.ediv_nonneg hnonneg (by norm_num)

/-- The Euler characteristic of a connected permutation triple is `2 - 2g`. -/
theorem IsConnected.two_sub_two_mul_genus {t : PermutationTriple n} (ht : t.IsConnected) :
    2 - 2 * (t.genus : ℤ) = t.eulerChar := by
  have hdiv := Int.ediv_mul_cancel (two_dvd_two_sub_eulerChar t)
  rw [ht.natCast_genus]
  omega

/-- The cycle-count display formula for the genus of a connected permutation triple, written in
the integers so that no truncated subtraction occurs. -/
theorem IsConnected.natCast_genus_eq_one_add {t : PermutationTriple n} (ht : t.IsConnected) :
    (t.genus : ℤ) =
      1 + ((n : ℤ) - orbitCount t.σ0 - orbitCount t.σ1 - orbitCount t.σinf) / 2 := by
  rw [ht.natCast_genus, eulerChar_def]
  calc
    (2 - ((orbitCount t.σ0 : ℤ) + orbitCount t.σ1 + orbitCount t.σinf - n)) / 2 =
        (2 + ((n : ℤ) - orbitCount t.σ0 - orbitCount t.σ1 - orbitCount t.σinf)) / 2 := by
      congr 1
      ring
    _ = 2 / 2 +
        ((n : ℤ) - orbitCount t.σ0 - orbitCount t.σ1 - orbitCount t.σinf) / 2 :=
      Int.add_ediv_of_dvd_left (by norm_num)
    _ = 1 +
        ((n : ℤ) - orbitCount t.σ0 - orbitCount t.σ1 - orbitCount t.σinf) / 2 := by
      norm_num

/-! ### Disjoint sums -/

/-- The Euler characteristic is additive over disjoint sums of triples, the two summands being
carried by disjoint sets of sheets. -/
@[simp]
theorem eulerChar_disjointSum (s : PermutationTriple m) (t : PermutationTriple n) :
    (s.disjointSum t).eulerChar = s.eulerChar + t.eulerChar := by
  rw [eulerChar_def, eulerChar_def, eulerChar_def]
  simp only [disjointSum_σ0, disjointSum_σ1, disjointSum_σinf, orbitCount_finSumPerm]
  push_cast
  ring

/-! ### Worked examples

The monodromy of `z ↦ z ^ 3`, and a disjoint union of two trivial covers. -/

example : (ofTwo (finRotate 3) 1).eulerChar = 2 := by
  have h0 : (finRotate 3).partition.parts = {3} := by decide
  have h1 : (1 : Perm (Fin 3)).partition.parts = {1, 1, 1} := by decide
  have hinf : ((1 : Perm (Fin 3)) * finRotate 3)⁻¹.partition.parts = {3} := by decide
  rw [eulerChar_def, Perm.orbitCount_eq_card_parts_partition,
    Perm.orbitCount_eq_card_parts_partition, Perm.orbitCount_eq_card_parts_partition,
    ofTwo_σ0, ofTwo_σ1, ofTwo_σinf, h0, h1, hinf]
  decide

example : ((1 : PermutationTriple 2).disjointSum (1 : PermutationTriple 3)).eulerChar = 10 := by
  rw [eulerChar_disjointSum, eulerChar_one, eulerChar_one]
  norm_num

end PermutationTriple

end TauCeti
