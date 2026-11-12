/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# The rational B₂ root system and its integral table

The Bourbaki simple indices of the rational B₂ root system agree with the first two
entries of the integral coordinate table, and rationalization preserves the positive-root
set. These identifications let root-system clients use the explicit B₂ table without
importing the Lie algebra or a Chevalley representation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti.DynkinType

/-- The Bourbaki simple indices of B₂ are the first two entries of the root table. -/
theorem simpleIndex_B_two_eq_b2Index (ht : (B 2).Valid) (i : Fin 2) :
    (B 2).simpleIndex ht i = b2Index (Fin.castAdd 6 i) := by
  fin_cases i <;> simp

/-- The assembled B₂ datum reads the existing coordinate table at its table indices. -/
theorem root_simplyConnectedRootDatum_B_two_b2Index (ht : (B 2).Valid) (m : Fin 8) :
    ((B 2).simplyConnectedRootDatum ht).root (b2Index m) = b2Root m := by
  simpa +instances only [simplyConnectedRootDatum_B, rank_B, numRoots_B] using root_b2Index m

/-- The roots of the assembled B₂ datum are exactly the entries of the coordinate table. -/
theorem range_root_simplyConnectedRootDatum_B_two (ht : (B 2).Valid) :
    Set.range ((B 2).simplyConnectedRootDatum ht).root = Set.range b2Root := by
  simpa +instances only [simplyConnectedRootDatum_B, rank_B, numRoots_B] using
    range_root_typeBSimplyConnectedRootDatum_two

/-- A root-sum equation in the B₂ table gives the same equation in the assembled datum. -/
lemma b2_root_eq_nsmul_add {ht : (B 2).Valid} (a b c : Fin 8) (n : ℕ)
    (h : b2Root c = n • b2Root a + b2Root b) :
    ((B 2).simplyConnectedRootDatum ht).root (b2Index c) =
      n • ((B 2).simplyConnectedRootDatum ht).root (b2Index a) +
        ((B 2).simplyConnectedRootDatum ht).root (b2Index b) := by
  simp only [root_simplyConnectedRootDatum_B_two_b2Index]
  simpa +instances only [rank_B] using h

/-- A sum excluded from the B₂ table is not a root of the assembled datum. -/
lemma b2_nsmul_add_nsmul_not_mem_range {ht : (B 2).Valid} (a b : Fin 8) (m n : ℕ)
    (h : m • b2Root a + n • b2Root b ∉ Set.range b2Root) :
    m • ((B 2).simplyConnectedRootDatum ht).root (b2Index a) +
        n • ((B 2).simplyConnectedRootDatum ht).root (b2Index b) ∉
      Set.range ((B 2).simplyConnectedRootDatum ht).root := by
  simp only [root_simplyConnectedRootDatum_B_two_b2Index,
    range_root_simplyConnectedRootDatum_B_two]
  simpa +instances only [rank_B] using h

/-- Rationalization identifies B₂ positivity with the pinned integral table. -/
theorem posRoots_rationalRootSystem_B_two (ht : (B 2).Valid) :
    posRoots ((B 2).rationalRootSystem ht) ((B 2).rationalBase ht) =
      posRoots (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2) := by
  rw [posRoots_rationalRootSystem]
  have htransport {P Q : RootPairing (Fin (B 2).numRoots) ℤ
      (Fin (B 2).rank → ℤ) (Fin (B 2).rank → ℤ)} (h : P = Q) (b : P.Base) :
      posRoots Q (Eq.mp (congrArg (fun P => P.Base) h) b) = posRoots P b := by
    subst Q
    rfl
  exact (htransport (simplyConnectedRootDatum_B 2 ht) _).symm.trans
    (congrArg (posRoots (typeBSimplyConnectedRootDatum 2)) (simplyConnectedBase_B 2 ht))

end TauCeti.DynkinType
