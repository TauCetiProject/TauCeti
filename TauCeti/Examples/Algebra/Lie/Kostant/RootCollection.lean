/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootCollection
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo

/-!
# A short–long B₂ collection calculation

For a supplied integral Chevalley table of the pinned B₂ root datum, collect the
short-root divided power of degree two past the long-root vector. The last term is
multiplied by both bracket signs. The reversed product checks the minus sign and
reversed middle factors in the opposite double-chain formula.

The root and coroot numbering is that of `TauCeti.DynkinType.b2Index`, following
Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plate II.
-/

public section

open scoped TensorProduct
open RootPairing RootPairing.ChevalleyLieAlgebra TauCeti.Associative

namespace TauCeti.Examples.KostantRootCollection

open DynkinType

local notation "P" => typeBSimplyConnectedRootDatum 2

private theorem b2_sum : (P).root (b2Index 2) = (P).root (b2Index 1) + (P).root (b2Index 0) := by
  simp only [root_b2Index]
  decide

private theorem b2_double :
    (P).root (b2Index 3) = (P).root (b2Index 1) + (P).root (b2Index 2) := by
  simp only [root_b2Index]
  decide

private theorem b2_length :
    (P).chainBotCoeff (b2Index 1) (b2Index 0) +
      (P).chainTopCoeff (b2Index 1) (b2Index 0) ≤ 2 := by
  have hli := (P).linearIndependent_of_root_eq_add_of_root_eq_add b2_sum b2_double
  have hnotBot : (P).root (b2Index 0) - (P).root (b2Index 1) ∉ Set.range (P).root := by
    rw [range_root_typeBSimplyConnectedRootDatum_two, root_b2Index, root_b2Index]
    decide
  have hbot : (P).chainBotCoeff (b2Index 1) (b2Index 0) = 0 :=
    (P).chainBotCoeff_eq_zero_iff.mpr (.inr hnotBot)
  have hnotTop : (P).root (b2Index 0) + 3 • (P).root (b2Index 1) ∉ Set.range (P).root := by
    rw [range_root_typeBSimplyConnectedRootDatum_two, root_b2Index, root_b2Index]
    decide
  rw [(P).root_add_nsmul_mem_range_iff_le_chainTopCoeff hli] at hnotTop
  omega

variable (c : (P).ChevalleyConstants)

local notation "e" => (fun k : Fin 8 ↦ _root_.UniversalEnvelopingAlgebra.ι ℚ
  ((1 : ℚ) ⊗ₜ[ℤ] root c (b2Index k)))

/-- The short–long B₂ calculation: the final root vector carries the product of
`sign N_(short,long)` and `sign N_(short,short+long)`. -/
theorem short_two_mul_long :
    dividedPower 2 (e 1) * e 0 = e 0 * dividedPower 2 (e 1) +
      c.structConst (b2Index 1) (b2Index 0) • (e 2 * e 1) +
        ((c.structConst (b2Index 1) (b2Index 0)).sign *
          (c.structConst (b2Index 1) (b2Index 2)).sign) • e 3 :=
  dividedPower_two_root_mul_root_of_double_chain c b2_sum b2_double b2_length

/-- In the reversed B₂ product the final double-root term has the negative of the
product of the ordered first bracket coefficient and the short-root bracket sign. -/
theorem long_mul_short_two :
    e 0 * dividedPower 2 (e 1) = dividedPower 2 (e 1) * e 0 +
      c.structConst (b2Index 0) (b2Index 1) • (e 1 * e 2) -
        (c.structConst (b2Index 0) (b2Index 1) *
          (c.structConst (b2Index 1) (b2Index 2)).sign) • e 3 := by
  have hindex : chainLeTwoIndex 2 1 = {(0, 0), (1, 0), (0, 1)} := by
    ext ⟨b, k⟩
    simp only [mem_chainLeTwoIndex, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have h := dividedPower_root_mul_of_reverse_double_chain c
    (by simpa only [add_comm] using b2_sum) b2_double b2_length 1 2
  simpa [hindex, add_assoc, sub_eq_add_neg] using h

end TauCeti.Examples.KostantRootCollection
