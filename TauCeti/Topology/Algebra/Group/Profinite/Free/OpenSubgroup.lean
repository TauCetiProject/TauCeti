/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic

/-!
# The generator rank of an open subgroup of a free pro-`p` group

An open subgroup `U` of index `m` in a free pro-`p` group `F` of finite rank `n ≥ 1` has
topological generator rank `d(U) = 1 + m * (n - 1)`.

The vanishing of `H²(F, M)` on the trivial modules of order `p`
(`TauCeti.freeProP.subsingleton_H2_of_isPPrimaryTorsion`) puts `F` under the hypotheses of the
two-term Euler formula `TauCeti.IsProP.topologicalGeneratorRankNat_add_index`, which reads
`d(U) + m = 1 + m * n` since `d(F) = n`; rearranging gives `d(U) = 1 + m * (n - 1)` once `n ≥ 1`.
The Schreier bound `TauCeti.topologicalGeneratorRankNat_le_of_openSubgroup` is therefore an
equality for free pro-`p` groups. This is the rank half of the pro-`p` Nielsen–Schreier theorem for
open subgroups; that `U` is itself free pro-`p` is not proved here.

## Main results

* `TauCeti.freeProP.topologicalGeneratorRankNat_add_index`: `d(U) + [F : U] = 1 + [F : U] * n`.
* `TauCeti.freeProP.topologicalGeneratorRankNat_openSubgroup`: `d(U) = 1 + [F : U] * (n - 1)` for
  `n ≥ 1`.

## References

* H. Koch, *Galois Theory of `p`-Extensions*, Example 6.3.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Thm. 3.6.2, for the transversal proof.
-/

public section

namespace TauCeti

universe u

namespace freeProP

variable {p : ℕ} [hp : Fact p.Prime] {X : Type u} [Finite X]

/-- **The Schreier index formula for open subgroups, additive form.** For an open subgroup
`U` of the free pro-`p` group on a finite type `X`, `d(U) + [F : U] = 1 + [F : U] * #X`. -/
theorem topologicalGeneratorRankNat_add_index (U : OpenSubgroup (freeProP p X)) :
    topologicalGeneratorRankNat U.toSubgroup
        ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U) + U.toSubgroup.index =
      1 + U.toSubgroup.index * Nat.card X := by
  have h := (isProP_freeProP p X).topologicalGeneratorRankNat_add_index
    (isTopologicallyFinitelyGenerated_freeProP p X)
    (fun A _ _ _ _ _ _ hA _ ↦ subsingleton_H2_of_isPPrimaryTorsion
      (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) U
  rwa [topologicalGeneratorRankNat_freeProP] at h

/-- **The Schreier index formula for open subgroups.** For an open subgroup `U` of index
`m` in the free pro-`p` group on a nonempty finite type `X` of cardinality `n`,
`d(U) = 1 + m * (n - 1)`. -/
theorem topologicalGeneratorRankNat_openSubgroup [Nonempty X] (U : OpenSubgroup (freeProP p X)) :
    topologicalGeneratorRankNat U.toSubgroup
        ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U) =
      1 + U.toSubgroup.index * (Nat.card X - 1) := by
  have h := topologicalGeneratorRankNat_add_index U
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := X)).ne'
  rw [hn, Nat.succ_sub_one]
  rw [hn, Nat.succ_eq_add_one, mul_add, mul_one] at h
  omega

end freeProP

end TauCeti
