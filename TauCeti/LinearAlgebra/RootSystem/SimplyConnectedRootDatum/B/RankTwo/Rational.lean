/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Positive roots of the rational B₂ system

The native `b2Index` table enumerates the positive roots in its first four entries, also
for the rational root system. This transfers the integral positivity criterion to the
indices used by Chevalley root subgroups, without introducing a second enumeration.
-/

public section

namespace TauCeti.DynkinType

/-- The positive roots of the rational B₂ system are the first four entries of the native
root table: the long simple root, the short simple root, their sum and the highest root. -/
theorem b2Index_mem_posRoots_rational_iff (ht : (B 2).Valid) (k : Fin 8) :
    b2Index k ∈ posRoots ((B 2).rationalRootSystem ht) ((B 2).rationalBase ht) ↔
      (k : ℕ) < 4 := by
  rw [posRoots_rationalRootSystem]
  have hpos : posRoots ((B 2).simplyConnectedRootDatum ht) ((B 2).simplyConnectedBase ht) =
      posRoots (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2) := by
    congr 1
    · exact simplyConnectedRootDatum_B 2 ht
    · exact eqRec_heq_iff.mp (heq_of_eq (simplyConnectedBase_B 2 ht))
  rw [hpos]
  exact b2Index_mem_posRoots_iff k

end TauCeti.DynkinType
