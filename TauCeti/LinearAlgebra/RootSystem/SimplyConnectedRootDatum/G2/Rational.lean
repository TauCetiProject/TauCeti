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
recorded by `TauCeti.DynkinType.index_pair_of_root_add_mem_range_root_g2`,
`TauCeti.DynkinType.root_castAdd_eq_add_g2` and
`TauCeti.DynkinType.two_nsmul_add_notMem_range_root_g2`; these drive the collection of positive
root subgroups in type `G₂`. The negative roots are the entries `6 + l`, with
`TauCeti.DynkinType.root_natAdd_g2` recording that entry `6 + l` is the negative of entry `l`. The
sums of a negative simple root with a positive root are recorded by
`TauCeti.DynkinType.index_pair_of_root_natAdd_add_mem_range_root_g2`,
`TauCeti.DynkinType.root_castAdd_eq_natAdd_add_g2` and
`TauCeti.DynkinType.two_nsmul_natAdd_add_notMem_range_root_g2`; these drive the normalization of
the positive root subgroups other than a simple one by the negative simple root subgroup.
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

/-- **Negative roots of `G₂`.** The root at index `6 + l` of the native root table is the negative
of the root at index `l`, by `TauCeti.DynkinType.g2Root_addNat`. -/
theorem root_natAdd_g2 (ht : G2.Valid) (l : Fin 6) :
    (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 l) =
      -(G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 l) := by
  rw [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root, Fin.natAdd_eq_addNat]
  exact g2Root_addNat l

/-- The root at index `6 + l` of the native `G₂` root table and the root at another index `k < 6`
do not sum to zero. -/
theorem root_natAdd_add_root_castAdd_ne_zero_g2 (ht : G2.Valid) {k l : Fin 6} (hkl : k ≠ l) :
    (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 l) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 k) ≠ 0 := fun h =>
  hkl (Fin.castAdd_injective _ _ ((G2.simplyConnectedRootDatum ht).root.injective
    (neg_add_eq_zero.mp (by rwa [root_natAdd_g2] at h)).symm))

-- The certificates below unfold the assembled datum to the native root table and decide.
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

/-- **Sums with the negative simple roots of `G₂`.** For `l < 2`, so that the entry `6 + l` of the
native root table is the negative of the simple root at index `l`, and `k < 6`, the pairs `(l, k)`
whose roots at the indices `6 + l` and `k` sum to a root are `(0, 2)`, `(0, 3)`, `(0, 4)`, `(1, 2)`
and `(1, 5)`. -/
theorem index_pair_of_root_natAdd_add_mem_range_root_g2 (ht : G2.Valid) : ∀ l k : Fin 6, l < 2 →
    (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 l) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 k) ∈
        Set.range (G2.simplyConnectedRootDatum ht).root →
    (l = 0 ∧ k = 2) ∨ (l = 0 ∧ k = 3) ∨ (l = 0 ∧ k = 4) ∨ (l = 1 ∧ k = 2) ∨ (l = 1 ∧ k = 5) := by
  g2_table

/-- **Additive relations with the negative simple roots of `G₂`.** Writing `rₖ` for the root at
index `k` of the native root table, so that `r₆ = -r₀` and `r₇ = -r₁`: `r₁ = r₆ + r₂`,
`r₂ = r₆ + r₃`, `r₃ = r₆ + r₄`, `r₀ = r₇ + r₂` and `r₄ = r₇ + r₅`. -/
theorem root_castAdd_eq_natAdd_add_g2 (ht : G2.Valid) :
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 1) =
        (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 (0 : Fin 6)) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 2) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 2) =
        (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 (0 : Fin 6)) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 3) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 3) =
        (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 (0 : Fin 6)) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 4) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 0) =
        (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 (1 : Fin 6)) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 2) ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 4) =
        (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 (1 : Fin 6)) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 5) := by
  g2_table

/-- **Root strings of length two through the negative simple roots of `G₂`.** For the pairs
`(0, 2)` and `(1, 5)`, whose roots `a` at index `6 + l` and `b` at index `k` sum to a root, neither
`2a + b` nor `a + 2b` is a root. -/
theorem two_nsmul_natAdd_add_notMem_range_root_g2 (ht : G2.Valid) (l k : Fin 6)
    (hlk : (l = 0 ∧ k = 2) ∨ (l = 1 ∧ k = 5)) :
    2 • (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 l) +
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 k) ∉
          Set.range (G2.simplyConnectedRootDatum ht).root ∧
      (G2.simplyConnectedRootDatum ht).root (Fin.natAdd 6 l) +
        2 • (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 k) ∉
          Set.range (G2.simplyConnectedRootDatum ht).root := by
  revert l k
  g2_table

end TauCeti.DynkinType
