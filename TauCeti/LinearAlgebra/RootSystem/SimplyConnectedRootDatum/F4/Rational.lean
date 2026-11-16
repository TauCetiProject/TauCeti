/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Heights and positive roots in the rational F₄ system

The uniform integral and rational F₄ bases inherit the height and positivity formulas of the
pinned integral table. In particular, their positive roots are the first twenty-four entries.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

namespace TauCeti.DynkinType

/-- The uniform integral F₄ base has the pinned table's height formula. -/
-- Rewrite before simplification normalizes the dependent root-index type to Fin 48.
@[simp↓] theorem height_simplyConnectedBase_F4 (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.simplyConnectedBase ht).height i =
      11 * f4Root i 0 + 21 * f4Root i 1 + 15 * f4Root i 2 + 8 * f4Root i 3 := by
  -- Transport the assembled base along the datum equation, without unfolding either base.
  have hb := heq_of_eqRec_eq _ (simplyConnectedBase_F4 ht)
  have hP := simplyConnectedRootDatum_F4 ht
  have hh : (F4.simplyConnectedBase ht).height i = f4SimplyConnectedBase.height i :=
    congr_heq (by congr 1) (HEq.refl i)
  exact hh.trans (height_f4SimplyConnectedBase i)

/-- The height of a rational pinned F₄ root in fundamental-weight coordinates. -/
-- Simplify before the dependent root-index type is normalized to Fin 48.
@[simp↓] theorem height_rationalBase_F4 (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.rationalBase ht).height i =
      11 * f4Root i 0 + 21 * f4Root i 1 + 15 * f4Root i 2 + 8 * f4Root i 3 := by
  rw [height_rationalBase, height_simplyConnectedBase_F4]

/-- The uniform integral F₄ base has the pinned table's positive indices. -/
@[simp↓] theorem isPos_simplyConnectedBase_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.simplyConnectedBase ht).IsPos i ↔ i.val < 24 := by
  rw [RootPairing.Base.isPos_iff, height_simplyConnectedBase_F4]
  -- The native height simp lemma cannot match until the dependent index type is normalized.
  change Fin 48 at i
  simpa only [RootPairing.Base.isPos_iff, height_f4SimplyConnectedBase] using
    isPos_f4SimplyConnectedBase_iff i

/-- Rational base change preserves the pinned F₄ positive indices. -/
@[simp↓] theorem isPos_rationalBase_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.rationalBase ht).IsPos i ↔ i.val < 24 := by
  rw [RootPairing.Base.isPos_iff, height_rationalBase, ← RootPairing.Base.isPos_iff]
  exact isPos_simplyConnectedBase_F4_iff ht i

/-- The positive rational F₄ roots are exactly the first half of the pinned root table. -/
-- The generic membership lemma does not match after dependent-index normalization.
@[simp↓] theorem mem_posRoots_rationalRootSystem_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    i ∈ TauCeti.posRoots (F4.rationalRootSystem ht) (F4.rationalBase ht) ↔ i.val < 24 := by
  rw [TauCeti.mem_posRoots, isPos_rationalBase_F4_iff]

/-- The negative rational F₄ roots are exactly the second half of the pinned root table. -/
@[simp↓] theorem mem_negRoots_rationalRootSystem_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    i ∈ TauCeti.negRoots (F4.rationalRootSystem ht) (F4.rationalBase ht) ↔ 24 ≤ i.val := by
  rw [TauCeti.mem_negRoots, isPos_rationalBase_F4_iff, not_lt]

/-- The positive rational F₄ root finset consists of the first twenty-four table indices. -/
theorem posRootsFinset_rationalRootSystem_F4 (ht : F4.Valid) :
    posRootsFinset (F4.rationalRootSystem ht) (F4.rationalBase ht) =
      Finset.univ.filter (fun i => i.val < 24) := by
  ext i
  simp only [mem_posRootsFinset, mem_posRoots_rationalRootSystem_F4_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

end TauCeti.DynkinType
