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
# Structure constants of the pinned Chevalley system in type `G₂`

For two short roots of the pinned `G₂` datum whose sum is long, the descending root string has
length two, so the native integer Chevalley bracket coefficient is `±3`, the coefficient-three
phenomenon behind commutation of those root subgroups in characteristic three. When their sum is
short, the descending string has length one and the coefficient is `±2`, the first coefficient in
the three-factor short-pair Chevalley relation.

Beyond the root-string magnitudes, `TauCeti.DynkinType.chevalleySystem` fixes a canonical choice of
sign at every root of `G₂`: positive non-simple root vectors are built from the least Bourbaki
summand by `(r + 1)⁻¹ • ⁅eᵢ, e_β⁆`, and negative root vectors by `-ω(e_{-γ})`. This file computes
the complete `12 × 12` table `TauCeti.DynkinType.g2StructureConstant` of integer structure constants
of that pinned Chevalley system:

* four positive seeds `N_{0,1} = 1`, `N_{0,2} = 2`, `N_{0,3} = 3`, `N_{1,4} = 1` read directly from
  the height recursion `TauCeti.DynkinType.exists_chevalleySystem_eq_inv_smul_lie`;
* the remaining positive bracket `N_{2,3} = -3` obtained from the Jacobi identity on
  `⁅⁅e₀, e₁⁆, e₃⁆`;
* the mixed-sign brackets along each root string determined from the Jacobi identity on
  `⁅⁅e_α, e_{-α}⁆, e_β⁆ = ⟨β, α^∨⟩ e_β`;
* all remaining entries deduced by skew-symmetry `N_{β,α} = -N_{α,β}`, the Chevalley involution
  relation `N_{-α,-β} = -N_{α,β}`, and vanishing at non-root sums.

## Main definitions

* `TauCeti.DynkinType.g2StructureConstant`: the `12 × 12` integer matrix of structure constants of
  the pinned `G₂` Chevalley system.

## Main results

* `TauCeti.DynkinType.structureConstant_G2_eq_two_or_eq_neg_two` and
  `TauCeti.DynkinType.structureConstant_G2_eq_three_or_eq_neg_three`: short-pair magnitudes from
  root-string lengths alone.
* `TauCeti.DynkinType.structureConstant_G2`: `G2.structureConstant ht α β = g2StructureConstant α β`
  for all root indices `α, β : Fin G2.numRoots`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 1, Theorem 1, and Chapter 10, Lemma 53.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and §12.4.
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

/-- **The structure-constant table of the pinned `G₂` Chevalley system**, indexed by the twelve
roots of `TauCeti.DynkinType.g2Root`: the six positive roots `α₁, α₂, α₁ + α₂, 2α₁ + α₂,
3α₁ + α₂, 3α₁ + 2α₂` followed by their negatives in the same order. -/
def g2StructureConstant : Fin 12 → Fin 12 → ℤ := ![
  ![ 0,  1,  2,  3,  0,  0,  0,  0, -3, -2, -1,  0],
  ![-1,  0,  0,  0,  1,  0,  0,  0,  1,  0,  0, -1],
  ![-2,  0,  0, -3,  0,  0, -3,  1,  0,  2,  0,  1],
  ![-3,  0,  3,  0,  0,  0, -2,  0,  2,  0,  1, -1],
  ![ 0, -1,  0,  0,  0,  0, -1,  0,  0,  1,  0,  1],
  ![ 0,  0,  0,  0,  0,  0,  0, -1,  1, -1,  1,  0],
  ![ 0,  0,  3,  2,  1,  0,  0, -1, -2, -3,  0,  0],
  ![ 0,  0, -1,  0,  0,  1,  1,  0,  0,  0, -1,  0],
  ![ 3, -1,  0, -2,  0, -1,  2,  0,  0,  3,  0,  0],
  ![ 2,  0, -2,  0, -1,  1,  3,  0, -3,  0,  0,  0],
  ![ 1,  0,  0, -1,  0, -1,  0,  1,  0,  0,  0,  0],
  ![ 0,  1, -1,  1, -1,  0,  0,  0,  0,  0,  0,  0]]

/-- Explicit matrix presentation of `TauCeti.DynkinType.g2StructureConstant` for rewriting in module
scope. -/
theorem g2StructureConstant_def (α β : Fin 12) :
    g2StructureConstant α β = ![
      ![ 0,  1,  2,  3,  0,  0,  0,  0, -3, -2, -1,  0],
      ![-1,  0,  0,  0,  1,  0,  0,  0,  1,  0,  0, -1],
      ![-2,  0,  0, -3,  0,  0, -3,  1,  0,  2,  0,  1],
      ![-3,  0,  3,  0,  0,  0, -2,  0,  2,  0,  1, -1],
      ![ 0, -1,  0,  0,  0,  0, -1,  0,  0,  1,  0,  1],
      ![ 0,  0,  0,  0,  0,  0,  0, -1,  1, -1,  1,  0],
      ![ 0,  0,  3,  2,  1,  0,  0, -1, -2, -3,  0,  0],
      ![ 0,  0, -1,  0,  0,  1,  1,  0,  0,  0, -1,  0],
      ![ 3, -1,  0, -2,  0, -1,  2,  0,  0,  3,  0,  0],
      ![ 2,  0, -2,  0, -1,  1,  3,  0, -3,  0,  0,  0],
      ![ 1,  0,  0, -1,  0, -1,  0,  1,  0,  0,  0,  0],
      ![ 0,  1, -1,  1, -1,  0,  0,  0,  0,  0,  0,  0]] α β := (rfl)

private def g2Neg (α : Fin 12) : Fin 12 := α + 6

private theorem g2Root_g2Neg (α : Fin 12) : g2Root (g2Neg α) = -g2Root α := by
  simp only [g2Neg, g2Root_apply]
  revert α
  decide

private theorem g2_reflectionPerm_self (ht : G2.Valid) (α : Fin 12) :
    (G2.simplyConnectedRootDatum ht).reflectionPerm α α = g2Neg α := by
  have h := ((G2.simplyConnectedRootDatum ht).root_reflectionPerm α α).trans
    ((G2.simplyConnectedRootDatum ht).reflection_apply_self α)
  refine (G2.simplyConnectedRootDatum ht).root.injective (h.trans ?_)
  simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
    rank, numRoots] using (g2Root_g2Neg α).symm

private noncomputable def g2SC (ht : G2.Valid) (α β : Fin 12) : ℤ :=
  G2.structureConstant ht α β

private theorem g2_structureConstant_skew (α β : Fin 12) :
    g2SC ht β α = -g2SC ht α β :=
  structureConstant_skew (t := G2) (ht := ht) α β

private theorem g2_structureConstant_g2Neg (α β : Fin 12) :
    g2SC ht (g2Neg α) (g2Neg β) = -g2SC ht α β := by
  simpa only [g2SC, g2_reflectionPerm_self] using
    structureConstant_reflectionPerm_self_reflectionPerm_self (t := G2) (ht := ht) α β

private theorem g2_structureConstant_g2Neg_of_eq {α β α' β' : Fin 12}
    (hα : α' = g2Neg α) (hβ : β' = g2Neg β) :
    g2SC ht α' β' = -g2SC ht α β :=
  hα ▸ hβ ▸ g2_structureConstant_g2Neg α β

private theorem g2_root_eq_add_of_g2Root {α β γ : Fin 12} (h : g2Root γ = g2Root α + g2Root β) :
    (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β := by
  simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
    rank, numRoots] using h

private theorem g2_chainBotCoeff_eq {α β γ : Fin 12} {r : ℕ}
    (hadd : g2Root γ = g2Root α + g2Root β)
    (hmem : g2Root β - r • g2Root α ∈ Set.range g2Root)
    (hnot : g2Root β - (r + 1) • g2Root α ∉ Set.range g2Root) :
    (G2.simplyConnectedRootDatum ht).chainBotCoeff α β = r := by
  have hadd' : g2SimplyConnectedRootDatum.root γ =
      g2SimplyConnectedRootDatum.root α + g2SimplyConnectedRootDatum.root β := by
    rwa [g2SimplyConnectedRootDatum_root]
  have hmem' : g2SimplyConnectedRootDatum.root β - r • g2SimplyConnectedRootDatum.root α ∈
      Set.range g2SimplyConnectedRootDatum.root := by
    rwa [g2SimplyConnectedRootDatum_root]
  have hnot' : g2SimplyConnectedRootDatum.root β - (r + 1) • g2SimplyConnectedRootDatum.root α ∉
      Set.range g2SimplyConnectedRootDatum.root := by
    rwa [g2SimplyConnectedRootDatum_root]
  have hli := g2SimplyConnectedRootDatum.linearIndependent_of_add_mem_range_root' ⟨γ, hadd'⟩
  have hle := (g2SimplyConnectedRootDatum.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli
    (n := r)).1 hmem'
  have hgt := mt (g2SimplyConnectedRootDatum.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli
    (n := r + 1)).2 hnot'
  have heq : g2SimplyConnectedRootDatum.chainBotCoeff α β = r := by omega
  rwa [simplyConnectedRootDatum_G2]

private theorem g2_rat_root_eq_add_iff (α β γ : Fin G2.numRoots) :
    (G2.rationalRootSystem ht).root γ =
      (G2.rationalRootSystem ht).root α + (G2.rationalRootSystem ht).root β ↔
    g2Root γ = g2Root α + g2Root β := by
  simpa +instances only [one_smul, Int.cast_one, simplyConnectedRootDatum_G2,
    g2SimplyConnectedRootDatum_root, rank, numRoots] using
    G2.root_rationalRootSystem_eq_add_zsmul_iff ht β α γ 1

private theorem g2StructureConstant_peel {i₀ : Fin 2} {β γ : Fin 12} {r : ℕ}
    (hpos : (γ : ℕ) < 6) (hns : 1 < (γ : ℕ))
    (hadd : g2Root γ = g2Root (G2.simpleIndex ht i₀) + g2Root β)
    (hmin : ∀ j : Fin 2, j < i₀ → ∀ β' : Fin 12,
      g2Root γ ≠ g2Root (G2.simpleIndex ht j) + g2Root β')
    (hbot : (G2.simplyConnectedRootDatum ht).chainBotCoeff (G2.simpleIndex ht i₀) β = r) :
    G2.structureConstant ht (G2.simpleIndex ht i₀) β = (r + 1 : ℕ) := by
  have hisPos : (G2.rationalBase ht).IsPos γ :=
    (mem_posRoots _ _ _).1 ((mem_posRoots_rational_g2_iff ht γ).2 hpos)
  have hnotSupp : γ ∉ (G2.rationalBase ht).support := by
    intro hs
    obtain ⟨j, rfl⟩ := exists_simpleIndex_eq_of_mem_support hs
    -- `j : Fin G2.rank` is definitionally `Fin 2`; expose that to apply `simpleIndex_G2`.
    change Fin 2 at j
    have hj : (G2.simpleIndex ht j : ℕ) = j := by simp [simpleIndex_G2]
    omega
  obtain ⟨i, β₀, hsum, hlt, heq⟩ := exists_chevalleySystem_eq_inv_smul_lie hisPos hnotSupp
  -- Expose the concrete rank and root-count types on the witnesses `i` and `β₀`.
  change Fin 2 at i
  -- Unfold `G2.numRoots` to `12` on `β₀`.
  change Fin 12 at β₀
  have hsum' : g2Root γ = g2Root (G2.simpleIndex ht i) + g2Root β₀ :=
    (g2_rat_root_eq_add_iff (G2.simpleIndex ht i) β₀ γ).1 hsum
  have hi₀ : i = i₀ := by
    rcases lt_trichotomy i i₀ with hi | rfl | hi
    · exact (hmin i hi β₀ hsum').elim
    · rfl
    · exact (hlt i₀ hi β ((g2_rat_root_eq_add_iff (G2.simpleIndex ht i₀) β γ).2 hadd)).elim
  subst hi₀
  have hβ₀ : β₀ = β := g2Root.injective (add_left_cancel (hsum'.symm.trans hadd))
  subst hβ₀
  have hadd' := g2_root_eq_add_of_g2Root (ht := ht) hadd
  rw [chainBotCoeff_rootEquiv (t := G2) (ht := ht) ⟨γ, hadd'⟩, hbot,
    ← G2.chevalleySystem_simpleIndex ht i] at heq
  have hne : ((r + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
  refine ((eq_structureConstant_iff (t := G2) (ht := ht) hadd' _).2 ?_).symm
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, heq, smul_smul, mul_inv_cancel₀ hne, one_smul]

private theorem g2_lie_reflectionPerm_self_lie (α β : Fin 12) :
    ⁅⁅G2.chevalleySystem ht α, G2.chevalleySystem ht (g2Neg α)⁆, G2.chevalleySystem ht β⁆ =
      g2SimplyConnectedRootDatum.pairing β α • G2.chevalleySystem ht β := by
  have hrefl : ⁅G2.chevalleySystem ht α, G2.chevalleySystem ht (g2Neg α)⁆ =
      ∑ i : Fin 2, (G2.simplyConnectedRootDatum ht).coroot α i • (G2.lieBasis ht).h i := by
    rw [← g2_reflectionPerm_self ht α, G2.lie_chevalleySystem_reflectionPerm_self ht α]
    exact G2.coroot_rootEquiv_eq_sum ht α
  have hh (i : Fin 2) : ⁅(G2.lieBasis ht).h i, G2.chevalleySystem ht β⁆ =
      (G2.simplyConnectedRootDatum ht).root β i • G2.chevalleySystem ht β :=
    G2.lie_lieBasis_h_chevalleySystem ht β i
  rw [hrefl, Fin.sum_univ_two, add_lie, zsmul_lie, zsmul_lie, hh 0, hh 1,
    smul_smul, smul_smul, ← add_smul]
  congr 1
  simp +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_coroot,
    g2SimplyConnectedRootDatum_root, g2SimplyConnectedRootDatum_pairing, dotProduct,
    Fin.sum_univ_two, mul_comm]
  rfl

private theorem g2StructureConstant_mul_neg_of_notMem {α α' β γ : Fin 12}
    (hα' : α' = g2Neg α)
    (hadd : g2Root γ = g2Root α + g2Root β)
    (hnot : g2Root α' + g2Root β ∉ Set.range g2Root)
    (hne : g2Root α' + g2Root β ≠ 0) :
    g2SC ht α β * g2SC ht α' γ = -g2SimplyConnectedRootDatum.pairing β α := by
  subst hα'
  have hadd' := g2_root_eq_add_of_g2Root (ht := ht) hadd
  have hneg' := g2_root_eq_add_of_g2Root (ht := ht)
    (show g2Root β = g2Root (g2Neg α) + g2Root γ by rw [g2Root_g2Neg, hadd]; abel)
  have hz : ⁅G2.chevalleySystem ht (g2Neg α), G2.chevalleySystem ht β⁆ = 0 := by
    apply lie_chevalleySystem_eq_zero
    · simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
        rank, numRoots] using hnot
    · simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
        rank, numRoots, Pi.zero_def] using hne
  have hjac := g2_lie_reflectionPerm_self_lie (ht := ht) α β
  rw [lie_lie, hz, lie_zero, zero_sub, lie_chevalleySystem_eq_structureConstant_zsmul hadd',
    lie_zsmul, lie_chevalleySystem_eq_structureConstant_zsmul hneg', smul_smul, ← neg_smul,
    ← sub_eq_zero, ← sub_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_zero, Int.cast_eq_zero] at hjac
  have heq : -(G2.structureConstant ht α β * G2.structureConstant ht (g2Neg α) γ) -
      g2SimplyConnectedRootDatum.pairing β α = 0 :=
    hjac.resolve_right (G2.isSl2Triple_chevalleySystem ht β).e_ne_zero
  dsimp only [g2SC]
  omega

private theorem g2StructureConstant_mul_neg_of_add {α α' β γ δ : Fin 12}
    (hα' : α' = g2Neg α)
    (hadd : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α' + g2Root β) :
    g2SC ht α' β * g2SC ht α δ - g2SC ht α β * g2SC ht α' γ =
      g2SimplyConnectedRootDatum.pairing β α := by
  subst hα'
  have hadd' := g2_root_eq_add_of_g2Root (ht := ht) hadd
  have hδ' := g2_root_eq_add_of_g2Root (ht := ht) hδ
  have hneg' := g2_root_eq_add_of_g2Root (ht := ht)
    (show g2Root β = g2Root (g2Neg α) + g2Root γ by rw [g2Root_g2Neg, hadd]; abel)
  have hαδ' := g2_root_eq_add_of_g2Root (ht := ht)
    (show g2Root β = g2Root α + g2Root δ by rw [hδ, g2Root_g2Neg]; abel)
  have hjac := g2_lie_reflectionPerm_self_lie (ht := ht) α β
  rw [lie_lie, lie_chevalleySystem_eq_structureConstant_zsmul hδ', lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hαδ', smul_smul,
    lie_chevalleySystem_eq_structureConstant_zsmul hadd', lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hneg', smul_smul, ← sub_smul,
    ← sub_eq_zero, ← sub_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_zero, Int.cast_eq_zero] at hjac
  have heq : G2.structureConstant ht (g2Neg α) β * G2.structureConstant ht α δ -
      G2.structureConstant ht α β * G2.structureConstant ht (g2Neg α) γ -
      g2SimplyConnectedRootDatum.pairing β α = 0 :=
    hjac.resolve_right (G2.isSl2Triple_chevalleySystem ht β).e_ne_zero
  dsimp only [g2SC]
  omega

private theorem g2StructureConstant_zero_one : g2SC ht 0 1 = 1 := by
  simpa [g2SC, simpleIndex_G2] using g2StructureConstant_peel (ht := ht) (i₀ := 0) (β := 1)
    (γ := 2) (r := 0) (by decide) (by decide) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
    (by simp) (g2_chainBotCoeff_eq (γ := 2) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide))

private theorem g2StructureConstant_zero_two : g2SC ht 0 2 = 2 := by
  simpa [g2SC, simpleIndex_G2] using g2StructureConstant_peel (ht := ht) (i₀ := 0) (β := 2)
    (γ := 3) (r := 1) (by decide) (by decide) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
    (by simp) (g2_chainBotCoeff_eq (γ := 3) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide))

private theorem g2StructureConstant_zero_three : g2SC ht 0 3 = 3 := by
  simpa [g2SC, simpleIndex_G2] using g2StructureConstant_peel (ht := ht) (i₀ := 0) (β := 3)
    (γ := 4) (r := 2) (by decide) (by decide) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
    (by simp) (g2_chainBotCoeff_eq (γ := 4) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide))

private theorem g2StructureConstant_one_four : g2SC ht 1 4 = 1 := by
  simpa [g2SC, simpleIndex_G2] using g2StructureConstant_peel (ht := ht) (i₀ := 1) (β := 4)
    (γ := 5) (r := 0) (by decide) (by decide) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
    (fun j hj β' => by
      obtain rfl : j = 0 := by omega
      simp only [simpleIndex_G2, g2Root_apply]
      revert β'
      decide)
    (g2_chainBotCoeff_eq (γ := 5) (by simp only [simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide)
      (by simp only [Set.mem_range, simpleIndex_G2, g2Root_apply]; decide))

private theorem g2StructureConstant_two_three : g2SC ht 2 3 = -3 := by
  have h01 : ⁅G2.chevalleySystem ht (0 : Fin 12), G2.chevalleySystem ht (1 : Fin 12)⁆ =
      G2.chevalleySystem ht (2 : Fin 12) := by
    have h := g2StructureConstant_zero_one (ht := ht)
    dsimp only [g2SC] at h
    simpa [h] using lie_chevalleySystem_eq_structureConstant_zsmul (t := G2) (ht := ht)
      (g2_root_eq_add_of_g2Root (α := 0) (β := 1) (γ := 2) (by simp only [g2Root_apply]; decide))
  have h03 : ⁅G2.chevalleySystem ht (0 : Fin 12), G2.chevalleySystem ht (3 : Fin 12)⁆ =
      (3 : ℤ) • G2.chevalleySystem ht (4 : Fin 12) := by
    have h := g2StructureConstant_zero_three (ht := ht)
    dsimp only [g2SC] at h
    simpa [h] using lie_chevalleySystem_eq_structureConstant_zsmul (t := G2) (ht := ht)
      (g2_root_eq_add_of_g2Root (α := 0) (β := 3) (γ := 4) (by simp only [g2Root_apply]; decide))
  have h14 : ⁅G2.chevalleySystem ht (1 : Fin 12), G2.chevalleySystem ht (4 : Fin 12)⁆ =
      G2.chevalleySystem ht (5 : Fin 12) := by
    have h := g2StructureConstant_one_four (ht := ht)
    dsimp only [g2SC] at h
    simpa [h] using lie_chevalleySystem_eq_structureConstant_zsmul (t := G2) (ht := ht)
      (g2_root_eq_add_of_g2Root (α := 1) (β := 4) (γ := 5) (by simp only [g2Root_apply]; decide))
  have h13 : ⁅G2.chevalleySystem ht (1 : Fin 12), G2.chevalleySystem ht (3 : Fin 12)⁆ = 0 := by
    apply lie_chevalleySystem_eq_zero
    · have hnot : g2Root 1 + g2Root 3 ∉ Set.range g2Root := by
        simp only [Set.mem_range, g2Root_apply]; decide
      simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
        rank, numRoots] using hnot
    · have hne : g2Root 1 + g2Root 3 ≠ 0 := by simp only [g2Root_apply]; decide
      simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
        rank, numRoots, Pi.zero_def] using hne
  refine ((eq_structureConstant_iff (t := G2) (ht := ht)
    (g2_root_eq_add_of_g2Root (ht := ht) (α := 2) (β := 3) (γ := 5)
      (by simp only [g2Root_apply]; decide)) (-3)).2 ?_).symm
  rw [← h01, lie_lie, h13, lie_zero, zero_sub, h03, lie_zsmul, h14, neg_smul]

private theorem g2StructureConstant_six_two : g2SC ht 6 2 = 3 := by
  have h := g2StructureConstant_mul_neg_of_notMem (ht := ht) (α := 0) (α' := 6) (β := 1) (γ := 2)
    rfl (by simp only [g2Root_apply]; decide)
    (by simp only [Set.mem_range, g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 1 0 = -3 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2StructureConstant_zero_one, hp] at h
  omega

private theorem g2StructureConstant_seven_two : g2SC ht 7 2 = -1 := by
  have h := g2StructureConstant_mul_neg_of_notMem (ht := ht) (α := 1) (α' := 7) (β := 0) (γ := 2)
    rfl (by simp only [g2Root_apply]; decide)
    (by simp only [Set.mem_range, g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 0 1 = -1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2_structureConstant_skew 0 1, g2StructureConstant_zero_one, hp] at h
  omega

private theorem g2StructureConstant_six_three : g2SC ht 6 3 = 2 := by
  have h := g2StructureConstant_mul_neg_of_add (ht := ht) (α := 0) (α' := 6) (β := 2) (γ := 3)
    (δ := 1) rfl (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 2 0 = -1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2StructureConstant_six_two, g2StructureConstant_zero_one, g2StructureConstant_zero_two, hp]
    at h
  omega

private theorem g2StructureConstant_eight_three : g2SC ht 8 3 = -2 := by
  have h := g2StructureConstant_mul_neg_of_add (ht := ht) (α := 2) (α' := 8) (β := 0) (γ := 3)
    (δ := 7) rfl (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 0 2 = -1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  have h80 : g2SC ht 8 0 = 3 := by
    have hr := g2_structureConstant_g2Neg_of_eq (ht := ht) (α := 2) (β := 6) (α' := 8) (β' := 0)
      rfl rfl
    rw [g2_structureConstant_skew 6 2, g2StructureConstant_six_two] at hr
    omega
  rw [h80, g2_structureConstant_skew 7 2, g2StructureConstant_seven_two,
    g2_structureConstant_skew 0 2, g2StructureConstant_zero_two, hp] at h
  omega

private theorem g2StructureConstant_six_four : g2SC ht 6 4 = 1 := by
  have h := g2StructureConstant_mul_neg_of_add (ht := ht) (α := 0) (α' := 6) (β := 3) (γ := 4)
    (δ := 2) rfl (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 3 0 = 1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2StructureConstant_six_three, g2StructureConstant_zero_two, g2StructureConstant_zero_three,
    hp] at h
  omega

private theorem g2StructureConstant_nine_four : g2SC ht 9 4 = -1 := by
  have h := g2StructureConstant_mul_neg_of_add (ht := ht) (α := 3) (α' := 9) (β := 0) (γ := 4)
    (δ := 8) rfl (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 0 3 = 1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  have h90 : g2SC ht 9 0 = 2 := by
    have hr := g2_structureConstant_g2Neg_of_eq (ht := ht) (α := 3) (β := 6) (α' := 9) (β' := 0)
      rfl rfl
    rw [g2_structureConstant_skew 6 3, g2StructureConstant_six_three] at hr
    omega
  rw [h90, g2_structureConstant_skew 8 3, g2StructureConstant_eight_three,
    g2_structureConstant_skew 0 3, g2StructureConstant_zero_three, hp] at h
  omega

private theorem g2StructureConstant_seven_five : g2SC ht 7 5 = 1 := by
  have h := g2StructureConstant_mul_neg_of_notMem (ht := ht) (α := 1) (α' := 7) (β := 4) (γ := 5)
    rfl (by simp only [g2Root_apply]; decide)
    (by simp only [Set.mem_range, g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 4 1 = -1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2StructureConstant_one_four, hp] at h
  omega

private theorem g2StructureConstant_ten_five : g2SC ht 10 5 = -1 := by
  have h := g2StructureConstant_mul_neg_of_notMem (ht := ht) (α := 4) (α' := 10) (β := 1) (γ := 5)
    rfl (by simp only [g2Root_apply]; decide)
    (by simp only [Set.mem_range, g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 1 4 = -1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2_structureConstant_skew 1 4, g2StructureConstant_one_four, hp] at h
  omega

private theorem g2StructureConstant_eight_five : g2SC ht 8 5 = -1 := by
  have h := g2StructureConstant_mul_neg_of_add (ht := ht) (α := 2) (α' := 8) (β := 3) (γ := 5)
    (δ := 0) rfl (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 3 2 = 1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  rw [g2StructureConstant_eight_three, g2_structureConstant_skew 0 2, g2StructureConstant_zero_two,
    g2StructureConstant_two_three, hp] at h
  omega

private theorem g2StructureConstant_nine_five : g2SC ht 9 5 = 1 := by
  have h := g2StructureConstant_mul_neg_of_add (ht := ht) (α := 3) (α' := 9) (β := 2) (γ := 5)
    (δ := 6) rfl (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
  have hp : g2SimplyConnectedRootDatum.pairing 2 3 = 1 := by
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]; decide
  have h92 : g2SC ht 9 2 = -2 := by
    have hr := g2_structureConstant_g2Neg_of_eq (ht := ht) (α := 3) (β := 8) (α' := 9) (β' := 2)
      rfl rfl
    rw [g2_structureConstant_skew 8 3, g2StructureConstant_eight_three] at hr
    omega
  rw [h92, g2_structureConstant_skew 6 3, g2StructureConstant_six_three,
    g2_structureConstant_skew 2 3, g2StructureConstant_two_three, hp] at h
  omega

private def g2IsBasePair : Fin 12 → Fin 12 → Bool := fun α β =>
  decide (α = 0 ∧ β = 1 ∨ α = 6 ∧ β = 2 ∨ α = 7 ∧ β = 2 ∨
    α = 0 ∧ β = 2 ∨ α = 6 ∧ β = 3 ∨ α = 8 ∧ β = 3 ∨
    α = 0 ∧ β = 3 ∨ α = 6 ∧ β = 4 ∨ α = 9 ∧ β = 4 ∨
    α = 1 ∧ β = 4 ∨ α = 7 ∧ β = 5 ∨ α = 10 ∧ β = 5 ∨
    α = 2 ∧ β = 3 ∨ α = 8 ∧ β = 5 ∨ α = 9 ∧ β = 5)

private theorem g2StructureConstant_of_isBasePair {α β : Fin 12}
    (h : g2IsBasePair α β = true) :
    g2SC ht α β = g2StructureConstant α β := by
  simp only [g2IsBasePair, decide_eq_true_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact g2StructureConstant_zero_one
  · exact g2StructureConstant_six_two
  · exact g2StructureConstant_seven_two
  · exact g2StructureConstant_zero_two
  · exact g2StructureConstant_six_three
  · exact g2StructureConstant_eight_three
  · exact g2StructureConstant_zero_three
  · exact g2StructureConstant_six_four
  · exact g2StructureConstant_nine_four
  · exact g2StructureConstant_one_four
  · exact g2StructureConstant_seven_five
  · exact g2StructureConstant_ten_five
  · exact g2StructureConstant_two_three
  · exact g2StructureConstant_eight_five
  · exact g2StructureConstant_nine_five

private theorem g2StructureConstant_cases (α β : Fin 12) :
    (g2Root α + g2Root β ∉ Set.range g2Root ∧ g2StructureConstant α β = 0) ∨
      g2IsBasePair α β = true ∨
      (g2IsBasePair β α = true ∧ g2StructureConstant α β = -g2StructureConstant β α) ∨
      (g2IsBasePair (g2Neg α) (g2Neg β) = true ∧
        g2StructureConstant α β = -g2StructureConstant (g2Neg α) (g2Neg β)) ∨
      (g2IsBasePair (g2Neg β) (g2Neg α) = true ∧
        g2StructureConstant α β = g2StructureConstant (g2Neg β) (g2Neg α)) := by
  simp only [Set.mem_range, not_exists, g2Root_apply, g2StructureConstant_def, g2IsBasePair, g2Neg]
  revert α β
  decide +kernel

/-- **The structure constants of the pinned `G₂` Chevalley system** equal the explicit `12 × 12`
table `TauCeti.DynkinType.g2StructureConstant`. -/
theorem structureConstant_G2 (ht : G2.Valid) (α β : Fin G2.numRoots) :
    G2.structureConstant ht α β = g2StructureConstant α β := by
  -- Expose `Fin 12` on the root indices so `g2SC`, `g2Neg`, and `g2IsBasePair` apply directly.
  change g2SC ht α β = g2StructureConstant α β
  -- Unfold `G2.numRoots` to `12` on `α` and `β`.
  change Fin 12 at α β
  rcases g2StructureConstant_cases α β with ⟨hnot, hzero⟩ | hbase | ⟨hskew, hval⟩ |
      ⟨hneg, hval⟩ | ⟨hboth, hval⟩
  · rw [hzero]
    apply structureConstant_eq_zero
    simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
      rank, numRoots] using hnot
  · exact g2StructureConstant_of_isBasePair hbase
  · rw [g2_structureConstant_skew, g2StructureConstant_of_isBasePair hskew, hval]
  · have h := g2_structureConstant_g2Neg (ht := ht) α β
    rw [g2StructureConstant_of_isBasePair hneg] at h
    omega
  · have h := g2_structureConstant_g2Neg (ht := ht) β α
    rw [g2StructureConstant_of_isBasePair hboth, g2_structureConstant_skew] at h
    omega

end TauCeti.DynkinType
