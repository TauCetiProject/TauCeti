/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Heights and positive roots of the rational G₂ system

The uniform integral and rational `G₂` bases inherit the root-height and positivity formulas of
the pinned integral table. In fundamental-weight coordinates `![a, b]`, the height of a `G₂` root
is `3 * a + 5 * b`, so the six positive roots at indices `0, ..., 5` have heights `1, 1, 2, 3, 4, 5`
(`max k 1`). This identifies positive-root indices and heights for constructions using the rational
system, without importing the Lie-algebra or root-subgroup development.

The native integral root-height, coroot-height, and positivity results live in `G2.Positive`,
independently of the uniform assembly and rational base change. In the same table order, the sums
of two positive roots are recorded by `TauCeti.DynkinType.index_pair_of_root_add_mem_range_root_g2`,
`TauCeti.DynkinType.root_castAdd_eq_add_g2` and
`TauCeti.DynkinType.two_nsmul_add_notMem_range_root_g2`; these drive the collection of positive
root subgroups in type `G₂`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

namespace TauCeti.DynkinType

/-- The uniform integral `G₂` base has the pinned table's root-height formula. -/
-- Rewrite before simplification normalizes the dependent root-index type to `Fin 12`.
@[simp↓] theorem height_simplyConnectedBase_G2 (ht : G2.Valid) (i : Fin G2.numRoots) :
    (G2.simplyConnectedBase ht).height i = 3 * g2Root i 0 + 5 * g2Root i 1 := by
  have hh : (G2.simplyConnectedBase ht).height i = g2SimplyConnectedBase.height i :=
    congr_heq (by
      congr 1
      · exact simplyConnectedRootDatum_G2 ht
      · exact heq_of_eqRec_eq _ (simplyConnectedBase_G2 ht)) (HEq.refl i)
  exact hh.trans (height_g2SimplyConnectedBase i)

/-- The height of a rational pinned `G₂` root in fundamental-weight coordinates. -/
-- Simplify before the dependent root-index type is normalized to `Fin 12`.
@[simp↓] theorem height_rationalBase_G2 (ht : G2.Valid) (i : Fin G2.numRoots) :
    (G2.rationalBase ht).height i = 3 * g2Root i 0 + 5 * g2Root i 1 := by
  rw [height_rationalBase, height_simplyConnectedBase_G2]

/-- The six positive roots of the rational `G₂` system at table indices `0, ..., 5` have heights
`1, 1, 2, 3, 4, 5`, namely `max (k : ℤ) 1`. -/
theorem height_rationalBase_G2_castAdd (ht : G2.Valid) (k : Fin 6) :
    (G2.rationalBase ht).height (Fin.castAdd 6 k : Fin G2.numRoots) = max (k : ℤ) 1 := by
  -- `G2.numRoots` is definitionally `6 + 6`.
  rw [height_rationalBase_G2 ht (Fin.castAdd 6 k : Fin G2.numRoots)]
  fin_cases k <;> simp [g2Root_apply]

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

-- The three certificates below unfold the assembled datum to the native root table and decide.
local macro "g2_table" : tactic => `(tactic|
  (simp only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root, Set.mem_range]
   dsimp +instances only [numRoots, rank]
   simp only [g2Root_apply]
   decide))

/-- **Sums of positive roots of `G₂`.** Among the first six entries of the native root table, the
pairs `i < j` whose roots sum to a root are `(0, 1)`, `(0, 2)`, `(0, 3)`, `(1, 4)` and `(2, 3)`. -/
theorem index_pair_of_root_add_mem_range_root_g2 (ht : G2.Valid) : ∀ i j : Fin 6, i < j →
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∈
        Set.range (G2.simplyConnectedRootDatum ht).root →
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 3) := by
  g2_table

/-- **Additive relations among the positive roots of `G₂`.** Writing `rₖ` for the root at index
`k` of the native root table: `r₂ = r₀ + r₁`, `r₃ = r₀ + r₂`, `r₄ = r₀ + r₃`, `r₅ = r₃ + r₂` and
`r₅ = r₁ + r₄`. -/
theorem root_castAdd_eq_add_g2 (ht : G2.Valid) :
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 2) =
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 0) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 1) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 3) =
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 0) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 2) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 4) =
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 0) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 3) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 5) =
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 3) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 2) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 5) =
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 1) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 4) := by
  g2_table

/-- **Root strings of length two in `G₂`.** For the pairs `(0, 3)`, `(1, 4)` and `(2, 3)` of the
native root table, whose roots `a` and `b` sum to a root, neither `2a + b` nor `a + 2b` is a
root. -/
theorem two_nsmul_add_notMem_range_root_g2 (ht : G2.Valid) (i j : Fin 6)
    (hij : (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 3)) :
    2 • (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∉
          Set.range (G2.simplyConnectedRootDatum ht).root ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
        2 • (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∉
          Set.range (G2.simplyConnectedRootDatum ht).root := by
  revert i j
  g2_table

end TauCeti.DynkinType
