/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Positive roots of the rational G₂ system

The positive roots of the rational `G₂` system have the same first-six-entry description as
those of the integral datum. This identifies positive-root indices for constructions using
the rational system, without importing the Lie-algebra or root-subgroup development.

The native integral positivity results remain in `G2.Positive`, independently of the uniform
assembly and rational base change. In the same table order, the sums of two positive roots are
recorded by `TauCeti.DynkinType.index_pair_of_root_add_mem_range_root_g2` and
`TauCeti.DynkinType.root_add_root_ne_zero_g2`; these drive the collection of positive root
subgroups in type `G₂`.
-/

public section

namespace TauCeti.DynkinType

/-- The positive roots of the rational `G₂` system are the first six entries of the native
root table, just as for the integral datum. -/
theorem mem_posRoots_rational_g2_iff (ht : G2.Valid) (k : Fin G2.numRoots) :
    k ∈ posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht) ↔ (k : ℕ) < 6 := by
  rw [posRoots_rationalRootSystem]
  -- The uniform integral base is transported to the native G₂ datum by its assembly equation.
  have hpos : posRoots (G2.simplyConnectedRootDatum ht) (G2.simplyConnectedBase ht) =
      posRoots g2SimplyConnectedRootDatum g2SimplyConnectedBase := by
    congr 1
    · exact simplyConnectedRootDatum_G2 ht
    · exact heq_of_eqRec_eq _ (simplyConnectedBase_G2 ht)
  rw [hpos]
  exact mem_posRoots_g2_iff k

/-- **Sums of positive roots of `G₂`.** Among the first six entries of the native root table, the
pairs `i < j` whose roots sum to a root are `(0, 1)`, `(0, 2)`, `(0, 3)`, `(1, 4)` and `(2, 3)`. -/
theorem index_pair_of_root_add_mem_range_root_g2 (ht : G2.Valid) : ∀ i j : Fin 6, i < j →
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∈
        Set.range (G2.simplyConnectedRootDatum ht).root →
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 3) := by
  simp only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root, Set.mem_range]
  dsimp +instances only [numRoots, rank]
  simp only [g2Root_apply]
  decide

/-- Two positive roots of `G₂`, read in the first six entries of the native root table, never sum
to zero. -/
theorem root_add_root_ne_zero_g2 (ht : G2.Valid) (i j : Fin 6) :
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ≠ 0 := by
  revert i j
  simp only [ne_eq, funext_iff, Pi.add_apply, Pi.zero_apply, simplyConnectedRootDatum_G2,
    g2SimplyConnectedRootDatum_root]
  dsimp +instances only [numRoots, rank]
  simp only [g2Root_apply]
  decide

end TauCeti.DynkinType
