/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.RootString
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Rational

/-!
# Structure constants for short-root pairs and the full pinned table in type `G₂`

For two short roots of the pinned `G₂` datum whose sum is long, the descending root string has
length two. Thus the native integer Chevalley bracket coefficient is `±3`. This is the
coefficient-three phenomenon behind commutation of those root subgroups in characteristic three.
When their sum is short, the descending string has length one and the coefficient is `±2`,
the first coefficient in the three-factor short-pair Chevalley relation.

The root-string calculations are `g2_chainBotCoeff_eq_two_of_short_add_short_eq_long` and
`g2_chainBotCoeff_eq_one_of_short_add_short_eq_short`; the coefficient formula is
`structureConstant_eq_natCast_or_eq_neg_natCast`. We also compute the complete `12 × 12` integer
bracket table `TauCeti.DynkinType.g2StructureConstant` (`TauCeti.DynkinType.structureConstant_G2`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 1, Theorem 1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

namespace TauCeti.DynkinType

variable {ht : G2.Valid}

/-- The bracket coefficient of two short `G₂` roots with a short sum is `±2`. -/
theorem structureConstant_G2_eq_two_or_eq_neg_two {α β γ : Fin G2.numRoots}
    (hα : g2Length α = 1) (hβ : g2Length β = 1) (hγ : g2Length γ = 1)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β) :
    G2.structureConstant ht α β = 2 ∨ G2.structureConstant ht α β = -2 := by
  have hc : (G2.simplyConnectedRootDatum ht).chainBotCoeff α β = 1 := by
    rw [simplyConnectedRootDatum_G2]
    apply g2_chainBotCoeff_eq_one_of_short_add_short_eq_short α β γ hα hβ hγ
    rw [simplyConnectedRootDatum_G2] at hadd
    exact hadd
  have h := structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht) ⟨γ, hadd⟩
  rw [hc] at h
  norm_num at h
  exact h

/-- The bracket coefficient of two short `G₂` roots with a long sum is `±3`. -/
theorem structureConstant_G2_eq_three_or_eq_neg_three {α β γ : Fin G2.numRoots}
    (hβ : g2Length β = 1) (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β) :
    G2.structureConstant ht α β = 3 ∨ G2.structureConstant ht α β = -3 := by
  have hc : (G2.simplyConnectedRootDatum ht).chainBotCoeff α β = 2 := by
    rw [simplyConnectedRootDatum_G2]
    apply g2_chainBotCoeff_eq_two_of_short_add_short_eq_long α β γ hβ hγ
    rw [simplyConnectedRootDatum_G2] at hadd
    exact hadd.trans (add_comm _ _)
  have h := structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht) ⟨γ, hadd⟩
  rw [hc] at h
  norm_num at h
  exact h

/-- **The structure-constant table of the pinned `G₂` Chevalley system**, indexed by
`TauCeti.DynkinType.g2Root` (`α₁, α₂, α₁ + α₂, 2α₁ + α₂, 3α₁ + α₂, 3α₁ + 2α₂` then negatives). -/
def g2StructureConstant : Fin 12 → Fin 12 → ℤ := ![
  ![0, 1, 2, 3, 0, 0, 0, 0, -3, -2, -1, 0], ![-1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1],
  ![-2, 0, 0, -3, 0, 0, -3, 1, 0, 2, 0, 1], ![-3, 0, 3, 0, 0, 0, -2, 0, 2, 0, 1, -1],
  ![0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 0],
  ![0, 0, 3, 2, 1, 0, 0, -1, -2, -3, 0, 0], ![0, 0, -1, 0, 0, 1, 1, 0, 0, 0, -1, 0],
  ![3, -1, 0, -2, 0, -1, 2, 0, 0, 3, 0, 0], ![2, 0, -2, 0, -1, 1, 3, 0, -3, 0, 0, 0],
  ![1, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0], ![0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0]]

/-- Explicit matrix presentation of `TauCeti.DynkinType.g2StructureConstant`. -/
theorem g2StructureConstant_def (α β : Fin 12) :
    g2StructureConstant α β = ![
      ![0, 1, 2, 3, 0, 0, 0, 0, -3, -2, -1, 0], ![-1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1],
      ![-2, 0, 0, -3, 0, 0, -3, 1, 0, 2, 0, 1], ![-3, 0, 3, 0, 0, 0, -2, 0, 2, 0, 1, -1],
      ![0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 0],
      ![0, 0, 3, 2, 1, 0, 0, -1, -2, -3, 0, 0], ![0, 0, -1, 0, 0, 1, 1, 0, 0, 0, -1, 0],
      ![3, -1, 0, -2, 0, -1, 2, 0, 0, 3, 0, 0], ![2, 0, -2, 0, -1, 1, 3, 0, -3, 0, 0, 0],
      ![1, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0], ![0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0]] α β :=
  (rfl)

private noncomputable def g2SC (ht : G2.Valid) (α β : Fin 12) : ℤ := G2.structureConstant ht α β

private theorem g2SC_skew (α β : Fin 12) : g2SC ht β α = -g2SC ht α β :=
  structureConstant_skew (t := G2) (ht := ht) α β

private theorem g2SC_add_six (α β : Fin 12) : g2SC ht (α + 6) (β + 6) = -g2SC ht α β := by
  simpa only [g2SC, reflectionPerm_self_G2] using
    structureConstant_reflectionPerm_self_reflectionPerm_self (t := G2) (ht := ht) α β

private theorem g2SC_add_six_skew (α β : Fin 12) : g2SC ht (β + 6) (α + 6) = g2SC ht α β := by
  rw [g2SC_add_six, g2SC_skew, neg_neg]

private theorem g2_chainBotCoeff_eq {α β γ : Fin 12} {r : ℕ}
    (hadd : g2Root γ = g2Root α + g2Root β) (hmem : g2Root β - r • g2Root α ∈ Set.range g2Root)
    (hnot : g2Root β - (r + 1) • g2Root α ∉ Set.range g2Root) :
    (G2.simplyConnectedRootDatum ht).chainBotCoeff α β = r := by
  have hli := g2SimplyConnectedRootDatum.linearIndependent_of_add_mem_range_root'
    ⟨γ, by rwa [g2SimplyConnectedRootDatum_root]⟩
  have hle := (g2SimplyConnectedRootDatum.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli
    (n := r)).1 (by rwa [g2SimplyConnectedRootDatum_root])
  have hgt := mt (g2SimplyConnectedRootDatum.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli
    (n := r + 1)).2 (by rwa [g2SimplyConnectedRootDatum_root])
  rw [simplyConnectedRootDatum_G2]
  -- Expose `g2SimplyConnectedRootDatum.chainBotCoeff` so `omega` closes the integer inequalities.
  change g2SimplyConnectedRootDatum.chainBotCoeff α β = r; omega

private theorem g2_rat_root_eq_add_iff (α β γ : Fin G2.numRoots) :
    (G2.rationalRootSystem ht).root γ =
      (G2.rationalRootSystem ht).root α + (G2.rationalRootSystem ht).root β ↔
    g2Root γ = g2Root α + g2Root β := by
  have h := G2.root_rationalRootSystem_eq_add_zsmul_iff ht β α γ 1
  rwa [Int.cast_one, one_smul, one_zsmul, g2_root_add_iff] at h

private theorem g2SC_peel {i₀ : Fin 2} {β γ : Fin 12} {r : ℕ}
    (h : (γ : ℕ) < 6 ∧ 1 < (γ : ℕ) ∧ g2Root γ = g2Root (Fin.castAdd 10 i₀) + g2Root β ∧
      (∀ j : Fin 2, j < i₀ → ∀ β', g2Root γ ≠ g2Root (Fin.castAdd 10 j) + g2Root β') ∧
      g2Root β - r • g2Root (Fin.castAdd 10 i₀) ∈ Set.range g2Root ∧
      g2Root β - (r + 1) • g2Root (Fin.castAdd 10 i₀) ∉ Set.range g2Root) :
    g2SC ht (Fin.castAdd 10 i₀) β = (r + 1 : ℕ) := by
  rcases h with ⟨hpos, hns, hadd, hmin, hmem, hnot⟩
  have hisPos : (G2.rationalBase ht).IsPos γ :=
    (mem_posRoots _ _ _).1 ((mem_posRoots_rational_g2_iff ht γ).2 hpos)
  have hnotSupp : γ ∉ (G2.rationalBase ht).support := fun hs => by
    obtain ⟨j, rfl⟩ := exists_simpleIndex_eq_of_mem_support hs
    -- Expose `Fin 2` on `j : Fin G2.rank` so `simpleIndex_G2` evaluates its index.
    change Fin 2 at j; simp only [simpleIndex_G2, Fin.val_castAdd] at hns; omega
  obtain ⟨i, β₀, hsum, hlt, heq⟩ := exists_chevalleySystem_eq_inv_smul_lie hisPos hnotSupp
  -- Expose concrete types `Fin 2` and `Fin 12` on the witnesses `i` and `β₀`.
  change Fin 2 at i; change Fin 12 at β₀
  have hsum' : g2Root γ = g2Root (Fin.castAdd 10 i) + g2Root β₀ := by
    simpa only [simpleIndex_G2] using (g2_rat_root_eq_add_iff (G2.simpleIndex ht i) β₀ γ).1 hsum
  obtain rfl : i₀ = i := by
    rcases lt_trichotomy i i₀ with hi | rfl | hi
    · exact (hmin i hi β₀ hsum').elim
    · rfl
    · exact (hlt i₀ hi β ((g2_rat_root_eq_add_iff (G2.simpleIndex ht i₀) β γ).2
        (by simpa only [simpleIndex_G2] using hadd))).elim
  obtain rfl : β = β₀ := g2Root.injective (add_left_cancel (hadd.symm.trans hsum'))
  have hadd' := (g2_root_add_iff (ht := ht) (Fin.castAdd 10 i₀) β γ).mpr hadd
  have hbot := g2_chainBotCoeff_eq (ht := ht) hadd hmem hnot
  rw [← simpleIndex_G2 ht i₀] at hadd' hbot ⊢
  rw [chainBotCoeff_rootEquiv (t := G2) (ht := ht) ⟨γ, hadd'⟩, hbot,
    ← G2.chevalleySystem_simpleIndex ht i₀] at heq
  refine ((eq_structureConstant_iff (t := G2) (ht := ht) hadd' _).2 ?_).symm
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, heq, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)), one_smul]

private theorem g2_lie_reflectionPerm_self_lie (α β : Fin 12) :
    ⁅⁅G2.chevalleySystem ht α, G2.chevalleySystem ht (α + 6 : Fin 12)⁆,
        G2.chevalleySystem ht β⁆ =
      g2SimplyConnectedRootDatum.pairing β α • G2.chevalleySystem ht β := by
  have hrefl : ⁅G2.chevalleySystem ht α, G2.chevalleySystem ht (α + 6 : Fin 12)⁆ =
      ∑ i : Fin 2, g2Coroot α i • (G2.lieBasis ht).h i := by
    rw [← reflectionPerm_self_G2 ht α, G2.lie_chevalleySystem_reflectionPerm_self ht α]
    have hsum := G2.coroot_rootEquiv_eq_sum ht α; rwa [coroot_simplyConnectedRootDatum_G2] at hsum
  have hh (i : Fin 2) : ⁅(G2.lieBasis ht).h i, G2.chevalleySystem ht β⁆ =
      g2Root β i • G2.chevalleySystem ht β := by
    simpa only [root_simplyConnectedRootDatum_G2, Int.cast_smul_eq_zsmul] using
      G2.lie_lieBasis_h_chevalleySystem ht β i
  rw [hrefl, Fin.sum_univ_two, add_lie, zsmul_lie, zsmul_lie, hh, hh, smul_smul, smul_smul,
    ← add_smul, g2SimplyConnectedRootDatum_pairing, dotProduct, Fin.sum_univ_two]
  congr 1; ring

private theorem g2SC_neg_of_notMem {α α' β γ : Fin 12} {c q : ℤ} (hc : g2SC ht α β = c)
    (h : α' = α + 6 ∧ g2Root γ = g2Root α + g2Root β ∧
      g2Root α' + g2Root β ∉ Set.range g2Root ∧ g2Root α' + g2Root β ≠ 0 ∧
      c * q = -g2SimplyConnectedRootDatum.pairing β α ∧ c ≠ 0) :
    g2SC ht α' γ = q := by
  rcases h with ⟨rfl, hadd, hnot, hne, hcq, hc0⟩
  have hadd' := (g2_root_add_iff (ht := ht) α β γ).mpr hadd
  have hneg' := (g2_root_add_iff (ht := ht) (α + 6 : Fin 12) γ β).mpr
    (by rw [g2Root_add_six, hadd]; abel)
  have hz : ⁅G2.chevalleySystem ht (α + 6 : Fin 12), G2.chevalleySystem ht β⁆ = 0 :=
    lie_chevalleySystem_eq_zero ((g2_add_mem_range_iff (ht := ht) (α + 6 : Fin 12) β).not.mpr hnot)
      ((g2_add_eq_zero_iff (ht := ht) (α + 6 : Fin 12) β).not.mpr hne)
  have hjac := g2_lie_reflectionPerm_self_lie (ht := ht) α β
  rw [lie_lie, hz, lie_zero, zero_sub, lie_chevalleySystem_eq_structureConstant_zsmul hadd',
    lie_zsmul, lie_chevalleySystem_eq_structureConstant_zsmul hneg', smul_smul, ← neg_smul,
    ← sub_eq_zero, ← sub_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_zero, Int.cast_eq_zero] at hjac
  have heq := hjac.resolve_right (G2.isSl2Triple_chevalleySystem ht β).e_ne_zero
  dsimp only [g2SC] at hc ⊢; rw [hc] at heq; exact mul_left_cancel₀ hc0 (by linarith)

private theorem g2SC_neg_of_add {α α' β γ δ : Fin 12} {a b c q : ℤ}
    (ha : g2SC ht α' β = a) (hb : g2SC ht α δ = b) (hc : g2SC ht α β = c)
    (h : α' = α + 6 ∧ g2Root γ = g2Root α + g2Root β ∧ g2Root δ = g2Root α' + g2Root β ∧
      a * b - c * q = g2SimplyConnectedRootDatum.pairing β α ∧ c ≠ 0) :
    g2SC ht α' γ = q := by
  rcases h with ⟨rfl, hadd, hδ, habc, hc0⟩
  have hadd' := (g2_root_add_iff (ht := ht) α β γ).mpr hadd
  have hδ' := (g2_root_add_iff (ht := ht) (α + 6 : Fin 12) β δ).mpr hδ
  have hneg' := (g2_root_add_iff (ht := ht) (α + 6 : Fin 12) γ β).mpr
    (by rw [g2Root_add_six, hadd]; abel)
  have hαδ' := (g2_root_add_iff (ht := ht) α δ β).mpr (by rw [hδ, g2Root_add_six]; abel)
  have hjac := g2_lie_reflectionPerm_self_lie (ht := ht) α β
  rw [lie_lie, lie_chevalleySystem_eq_structureConstant_zsmul hδ', lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hαδ', smul_smul,
    lie_chevalleySystem_eq_structureConstant_zsmul hadd', lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hneg', smul_smul, ← sub_smul,
    ← sub_eq_zero, ← sub_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_zero, Int.cast_eq_zero] at hjac
  have heq := hjac.resolve_right (G2.isSl2Triple_chevalleySystem ht β).e_ne_zero
  dsimp only [g2SC] at ha hb hc ⊢; rw [ha, hb, hc] at heq; exact mul_left_cancel₀ hc0 (by linarith)

local macro "g2_dec" : tactic => `(tactic|
  (simp only [Set.mem_range, g2Root_apply, g2Coroot_apply,
    g2SimplyConnectedRootDatum_pairing]; decide))

private theorem g2SC_pos_seeds :
    g2SC ht 0 1 = 1 ∧ g2SC ht 0 2 = 2 ∧ g2SC ht 0 3 = 3 ∧ g2SC ht 1 4 = 1 ∧ g2SC ht 2 3 = -3 := by
  have s01 : g2SC ht 0 1 = 1 := g2SC_peel (i₀ := 0) (γ := 2) (r := 0) (by g2_dec)
  have s03 : g2SC ht 0 3 = 3 := g2SC_peel (i₀ := 0) (γ := 4) (r := 2) (by g2_dec)
  have s14 : g2SC ht 1 4 = 1 := g2SC_peel (i₀ := 1) (γ := 5) (r := 0) (by g2_dec)
  refine ⟨s01, g2SC_peel (i₀ := 0) (γ := 3) (r := 1) (by g2_dec), s03, s14, ?_⟩
  have leq {α β γ : Fin 12} (h : g2Root γ = g2Root α + g2Root β) :
      ⁅G2.chevalleySystem ht α, G2.chevalleySystem ht β⁆ = g2SC ht α β • G2.chevalleySystem ht γ :=
    lie_chevalleySystem_eq_structureConstant_zsmul ((g2_root_add_iff (ht := ht) α β γ).mpr h)
  have l13 : ⁅G2.chevalleySystem ht (1 : Fin 12), G2.chevalleySystem ht (3 : Fin 12)⁆ = 0 :=
    lie_chevalleySystem_eq_zero
      ((g2_add_mem_range_iff (ht := ht) (1 : Fin 12) (3 : Fin 12)).not.mpr (by g2_dec))
      ((g2_add_eq_zero_iff (ht := ht) (1 : Fin 12) (3 : Fin 12)).not.mpr (by g2_dec))
  refine ((eq_structureConstant_iff (t := G2) (ht := ht)
    ((g2_root_add_iff (ht := ht) (2 : Fin 12) (3 : Fin 12) (5 : Fin 12)).mpr (by g2_dec))
    (-3)).2 ?_).symm
  have l01 := leq (α := 0) (β := 1) (γ := 2) (by g2_dec); rw [s01, one_smul] at l01
  rw [← l01, lie_lie, l13, lie_zero, zero_sub, leq (γ := 4) (by g2_dec), s03, lie_zsmul,
    leq (γ := 5) (by g2_dec), s14, one_smul, neg_smul]

private def g2IsBasePair : Fin 12 → Fin 12 → Bool := fun α β =>
  decide (α = 0 ∧ β = 1 ∨ α = 6 ∧ β = 2 ∨ α = 7 ∧ β = 2 ∨ α = 0 ∧ β = 2 ∨ α = 6 ∧ β = 3 ∨
    α = 8 ∧ β = 3 ∨ α = 0 ∧ β = 3 ∨ α = 6 ∧ β = 4 ∨ α = 9 ∧ β = 4 ∨ α = 1 ∧ β = 4 ∨
    α = 7 ∧ β = 5 ∨ α = 10 ∧ β = 5 ∨ α = 2 ∧ β = 3 ∨ α = 8 ∧ β = 5 ∨ α = 9 ∧ β = 5)

private theorem g2StructureConstant_of_isBasePair {α β : Fin 12} (h : g2IsBasePair α β = true) :
    g2SC ht α β = g2StructureConstant α β := by
  have sk {i j : Fin 12} {c : ℤ} (hc : g2SC ht i j = c) : g2SC ht j i = -c := hc ▸ g2SC_skew i j
  obtain ⟨s01, s02, s03, s14, s23⟩ := g2SC_pos_seeds (ht := ht)
  have s62 : g2SC ht 6 2 = 3 := g2SC_neg_of_notMem s01 (by g2_dec)
  have s72 : g2SC ht 7 2 = -1 := g2SC_neg_of_notMem (sk s01) (by g2_dec)
  have s63 : g2SC ht 6 3 = 2 := g2SC_neg_of_add (δ := 1) s62 s01 s02 (by g2_dec)
  have s83 : g2SC ht 8 3 = -2 := g2SC_neg_of_add (δ := 7) ((g2SC_add_six_skew 6 2).trans s62)
    (sk s72) (sk s02) (by g2_dec)
  have s64 : g2SC ht 6 4 = 1 := g2SC_neg_of_add (δ := 2) s63 s02 s03 (by g2_dec)
  have s94 : g2SC ht 9 4 = -1 := g2SC_neg_of_add (δ := 8) ((g2SC_add_six_skew 6 3).trans s63)
    (sk s83) (sk s03) (by g2_dec)
  have s75 : g2SC ht 7 5 = 1 := g2SC_neg_of_notMem s14 (by g2_dec)
  have s105 : g2SC ht 10 5 = -1 := g2SC_neg_of_notMem (sk s14) (by g2_dec)
  have s85 : g2SC ht 8 5 = -1 := g2SC_neg_of_add (δ := 0) s83 (sk s02) s23 (by g2_dec)
  have s95 : g2SC ht 9 5 = 1 := g2SC_neg_of_add (δ := 6) ((g2SC_add_six_skew 8 3).trans s83)
    (sk s63) (sk s23) (by g2_dec)
  simp only [g2IsBasePair, decide_eq_true_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | exact s01 | exact s62 | exact s72 | exact s02 | exact s63 | exact s83 | exact s03 |
      exact s64 | exact s94 | exact s14 | exact s75 | exact s105 | exact s23 | exact s85 | exact s95

private theorem g2StructureConstant_cases (α β : Fin 12) :
    (g2Root α + g2Root β ∉ Set.range g2Root ∧ g2StructureConstant α β = 0) ∨
      g2IsBasePair α β = true ∨
      (g2IsBasePair β α = true ∧ g2StructureConstant α β = -g2StructureConstant β α) ∨
      (g2IsBasePair (α + 6) (β + 6) = true ∧
        g2StructureConstant α β = -g2StructureConstant (α + 6) (β + 6)) ∨
      (g2IsBasePair (β + 6) (α + 6) = true ∧
        g2StructureConstant α β = g2StructureConstant (β + 6) (α + 6)) := by
  simp only [Set.mem_range, not_exists, g2Root_apply, g2StructureConstant_def, g2IsBasePair]
  revert α β; decide +kernel

/-- **The structure constants of the pinned `G₂` Chevalley system** equal the explicit `12 × 12`
table `TauCeti.DynkinType.g2StructureConstant`. -/
theorem structureConstant_G2 (ht : G2.Valid) (α β : Fin G2.numRoots) :
    G2.structureConstant ht α β = g2StructureConstant α β := by
  -- Expose `Fin 12` on root indices so `g2SC` and `g2IsBasePair` apply directly.
  change g2SC ht α β = g2StructureConstant α β
  -- Unfold `G2.numRoots` to `12` on `α` and `β`.
  change Fin 12 at α β
  rcases g2StructureConstant_cases α β with ⟨hnot, hzero⟩ | hbase | ⟨hskew, hval⟩ |
      ⟨hneg, hval⟩ | ⟨hboth, hval⟩
  · exact hzero ▸ structureConstant_eq_zero ((g2_add_mem_range_iff (ht := ht) α β).not.mpr hnot)
  · exact g2StructureConstant_of_isBasePair hbase
  · rw [g2SC_skew, g2StructureConstant_of_isBasePair hskew, hval]
  · have h := g2SC_add_six (ht := ht) α β; rw [g2StructureConstant_of_isBasePair hneg] at h; omega
  · rw [← g2SC_add_six_skew, g2StructureConstant_of_isBasePair hboth, hval]

end TauCeti.DynkinType
