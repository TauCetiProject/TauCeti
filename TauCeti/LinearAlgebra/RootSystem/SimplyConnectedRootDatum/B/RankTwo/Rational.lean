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

/-- Rationalization preserves the positive-root set of the pinned B₂ datum. -/
theorem posRoots_rational_B_two (ht : (B 2).Valid) :
    posRoots ((B 2).rationalRootSystem ht) ((B 2).rationalBase ht) =
      posRoots (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2) := by
  have hs : ((B 2).rationalBase ht).support = (typeBSimplyConnectedBase 2).support := by
    ext j
    rw [support_rationalBase]
    exact (mem_support_simplyConnectedBase (B 2) ht (k := j)).trans
      (mem_typeBSimplyConnectedBase_support (n := 2) (k := j)).symm
  -- Rationalization preserves the simple-root expansion coefficients, hence their sum.
  have hheight (γ : Fin (B 2).numRoots) :
      ((B 2).rationalBase ht).height γ = (typeBSimplyConnectedBase 2).height γ := by
    obtain ⟨f, _, _, hf⟩ := (typeBSimplyConnectedBase 2).exists_root_eq_sum_int γ
    have heq : ((B 2).rationalRootSystem ht).root γ =
        ∑ j ∈ ((B 2).rationalBase ht).support,
          f j • ((B 2).rationalRootSystem ht).root j := by
      rw [hs]
      ext k
      have hr (j : Fin (2 * 2 ^ 2)) : ((B 2).rationalRootSystem ht).root j k =
          ((typeBSimplyConnectedRootDatum 2).root j k : ℚ) := by
        rw [root_rationalRootSystem (B 2) ht j k, simplyConnectedRootDatum_B]
        rfl
      have hf' : (typeBSimplyConnectedRootDatum 2).root γ k =
          ∑ j ∈ (typeBSimplyConnectedBase 2).support,
            f j * (typeBSimplyConnectedRootDatum 2).root j k := by
        have h := congrFun hf k
        -- The coordinate index uses the Dynkin rank, definitionally equal to the table rank.
        erw [Finset.sum_apply k (typeBSimplyConnectedBase 2).support
          (fun j => f j • (typeBSimplyConnectedRootDatum 2).root j)] at h
        simpa only [Pi.smul_apply, zsmul_eq_mul] using! h
      erw [Finset.sum_apply k (typeBSimplyConnectedBase 2).support
        (fun j => f j • ((B 2).rationalRootSystem ht).root j)]
      simp only [Pi.smul_apply, zsmul_eq_mul]
      rw [hr γ]
      simp_rw [hr]
      exact_mod_cast hf'
    rw [RootPairing.Base.height_eq_sum heq, RootPairing.Base.height_eq_sum hf, hs]
    rfl
  ext γ
  have hpos : ((B 2).rationalBase ht).IsPos γ ↔ (typeBSimplyConnectedBase 2).IsPos γ :=
    (RootPairing.Base.isPos_iff _).trans ((hheight γ).symm ▸
      (RootPairing.Base.isPos_iff _).symm)
  exact ((mem_posRoots _ _ γ).trans hpos).trans (mem_posRoots _ _ γ).symm

end TauCeti.DynkinType
