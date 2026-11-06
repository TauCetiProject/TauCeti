/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.RootString
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.G2.Basic

/-!
# The short–long G₂ root-subgroup product

For a short root α and a long root β with α + β a root, the positive roots in their
rank-two subsystem are α, β, α + β, 2α + β, 3α + β and 3α + 2β. This file proves the
four-factor straightening formula for the native pinned root subgroups on any Kostant-stable
lattice, over every commutative value ring. All bracket hypotheses are discharged from the
integral root datum and the pinned integer structure constants.

The coefficients are computed in ℤ before mapping to the value ring. In particular, the
divisions by two and three below do not require these numbers to be invertible in that ring.
The formula retains the signs of the chosen Chevalley system.

The transport of scaled root operators follows
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul`;
the integral exponential identity is
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

private theorem short_long_exclusions (i j : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 3)
    (hadd : g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i ∈
      Set.range g2SimplyConnectedRootDatum.root) (a b : ℕ)
    (hab : (a, b) ∈ ({(4, 1), (4, 2), (1, 2), (5, 2), (4, 3), (5, 3), (6, 3)} :
      Finset (ℕ × ℕ))) :
    a • g2SimplyConnectedRootDatum.root i + b • g2SimplyConnectedRootDatum.root j ∉
        Set.range g2SimplyConnectedRootDatum.root ∧
      a • g2SimplyConnectedRootDatum.root i + b • g2SimplyConnectedRootDatum.root j ≠ 0 := by
  have hpair : g2SimplyConnectedRootDatum.pairing j i = -3 := by
    obtain ⟨k, hk⟩ := hadd
    simp only [g2SimplyConnectedRootDatum_root, g2SimplyConnectedRootDatum_pairing,
      g2Root_apply, g2Coroot_apply] at hk ⊢
    rw [g2Length_apply] at hi hj
    revert i j k
    decide +kernel
  clear hadd
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hab
  rcases hab with h | h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
    simp only [Set.mem_range, not_exists, g2SimplyConnectedRootDatum_root,
      g2Root_apply] <;>
    simp only [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply] at hpair <;>
    rw [g2Length_apply] at hi hj <;> revert i j <;> decide +kernel

private theorem short_long_constants (i j k l m o : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 3)
    (hk : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i)
    (hl : g2SimplyConnectedRootDatum.root l =
      g2SimplyConnectedRootDatum.root k + g2SimplyConnectedRootDatum.root i)
    (hm : g2SimplyConnectedRootDatum.root m =
      g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root i)
    (ho : g2SimplyConnectedRootDatum.root o =
      g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root k) :
    2 ∣ G2.structureConstant valid_G2 i k ∧
      3 ∣ G2.structureConstant valid_G2 i l ∧
      3 ∣ G2.structureConstant valid_G2 l k := by
  let P := g2SimplyConnectedRootDatum
  have hroot : P.root i + P.root j ∈ Set.range P.root := ⟨k, hk.trans (add_comm _ _)⟩
  have hlin := P.linearIndependent_of_add_mem_range_root' hroot
  have hbot : P.chainBotCoeff i j = 0 :=
    P.chainBotCoeff_eq_zero_iff.mpr
      (.inr (g2_root_sub_not_mem_range_of_short_add_long_eq_root i j k hi hj hk))
  have hbotk : P.chainBotCoeff i k = 1 := by
    rw [P.chainBotCoeff_of_add hlin hk, hbot]
  have hlin' := P.linearIndependent_of_add_mem_range_root' ⟨l, hl.trans (add_comm _ _)⟩
  have hbotl : P.chainBotCoeff i l = 2 := by
    rw [P.chainBotCoeff_of_add hlin' hl, hbotk]
  have hklen := g2Length_eq_one_of_long_add_short_eq_root j i k hj hi hk
  have hllen := g2Length_eq_one_of_two_smul_short_add_long_eq_root i j l hi hj
    (by rw [hl, hk]; module)
  have holen := g2Length_eq_three_of_three_smul_short_add_two_smul_long_eq_root i j o hi hj
    (by rw [ho, hl, hk]; module)
  have hbotlk : P.chainBotCoeff l k = 2 :=
    g2_chainBotCoeff_eq_two_of_short_add_short_eq_long l k o hllen hklen holen
      (ho.trans (add_comm _ _))
  have hc := structureConstant_eq_natCast_or_eq_neg_natCast
    (t := G2) (ht := valid_G2) (α := i) (β := k)
    (by rw [simplyConnectedRootDatum_G2]; exact ⟨l, hl.trans (add_comm _ _)⟩)
  have hd := structureConstant_eq_natCast_or_eq_neg_natCast
    (t := G2) (ht := valid_G2) (α := i) (β := l)
    (by rw [simplyConnectedRootDatum_G2]; exact ⟨m, hm.trans (add_comm _ _)⟩)
  have he := structureConstant_eq_natCast_or_eq_neg_natCast
    (t := G2) (ht := valid_G2) (α := l) (β := k)
    (by rw [simplyConnectedRootDatum_G2]; exact ⟨o, ho⟩)
  have hbk : (G2.simplyConnectedRootDatum valid_G2).chainBotCoeff i k = 1 := by
    rw [simplyConnectedRootDatum_G2]
    exact hbotk
  have hbl : (G2.simplyConnectedRootDatum valid_G2).chainBotCoeff i l = 2 := by
    rw [simplyConnectedRootDatum_G2]
    exact hbotl
  have hblk : (G2.simplyConnectedRootDatum valid_G2).chainBotCoeff l k = 2 := by
    rw [simplyConnectedRootDatum_G2]
    exact hbotlk
  rw [hbk] at hc
  rw [hbl] at hd
  rw [hblk] at he
  constructor
  · rcases hc with h | h <;> rw [h] <;> norm_num
  constructor
  · rcases hd with h | h <;> rw [h] <;> norm_num
  · rcases he with h | h <;> rw [h] <;> norm_num

section Configuration

variable (i j k l m o : Fin G2.numRoots) (hi : g2Length i = 1) (hj : g2Length j = 3)
variable (hk : g2SimplyConnectedRootDatum.root k =
  g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i)
variable (hl : g2SimplyConnectedRootDatum.root l =
  g2SimplyConnectedRootDatum.root k + g2SimplyConnectedRootDatum.root i)
variable (hm : g2SimplyConnectedRootDatum.root m =
  g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root i)
variable (ho : g2SimplyConnectedRootDatum.root o =
  g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root k)

include hi hj hk hl hm ho in
private theorem short_long_scaled_brackets :
    let e := G2.chevalleySystem valid_G2
    let N := G2.structureConstant valid_G2
    let c := N i j
    let d := c * (N i k / 2)
    let a := d * (N i l / 3)
    let b := d * c * (N l k / 3)
    ⁅e i, e j⁆ = c • e k ∧ c • ⁅e i, e k⁆ = (2 * d) • e l ∧
      d • ⁅e i, e l⁆ = (3 * a) • e m ∧ (d * c) • ⁅e l, e k⁆ = (3 * b) • e o := by
  dsimp only
  obtain ⟨h2, h3, h3'⟩ := short_long_constants i j k l m o hi hj hk hl hm ho
  have bracket {p q r : Fin G2.numRoots}
      (h : g2SimplyConnectedRootDatum.root r =
        g2SimplyConnectedRootDatum.root p + g2SimplyConnectedRootDatum.root q) :
      ⁅G2.chevalleySystem valid_G2 p, G2.chevalleySystem valid_G2 q⁆ =
        G2.structureConstant valid_G2 p q • G2.chevalleySystem valid_G2 r :=
    lie_chevalleySystem_eq_structureConstant_zsmul
      (t := G2) (ht := valid_G2) (by rw [simplyConnectedRootDatum_G2]; exact h)
  refine ⟨bracket (hk.trans (add_comm _ _)), ?_, ?_, ?_⟩
  · rw [bracket (hl.trans (add_comm _ _)), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h2]
  · rw [bracket (hm.trans (add_comm _ _)), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h3]
  · rw [bracket ho, smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h3']

include hi hj hk hl hm ho in
private theorem short_long_zero_brackets :
    let e := G2.chevalleySystem valid_G2
    ⁅e i, e m⁆ = 0 ∧ ⁅e i, e o⁆ = 0 ∧ ⁅e j, e k⁆ = 0 ∧ ⁅e l, e m⁆ = 0 ∧
      ⁅e k, e o⁆ = 0 ∧ ⁅e l, e o⁆ = 0 ∧ ⁅e m, e o⁆ = 0 := by
  dsimp only
  have zeroBracket (p q : Fin G2.numRoots) (a b : ℕ)
      (hab : (a, b) ∈ ({(4, 1), (4, 2), (1, 2), (5, 2), (4, 3), (5, 3), (6, 3)} :
        Finset (ℕ × ℕ)))
      (heq : g2SimplyConnectedRootDatum.root p + g2SimplyConnectedRootDatum.root q =
        a • g2SimplyConnectedRootDatum.root i + b • g2SimplyConnectedRootDatum.root j) :
      ⁅G2.chevalleySystem valid_G2 p, G2.chevalleySystem valid_G2 q⁆ = 0 := by
    obtain ⟨hnot, hne⟩ := short_long_exclusions i j hi hj ⟨k, hk⟩ a b hab
    apply lie_chevalleySystem_eq_zero (t := G2) (ht := valid_G2)
    · rw [simplyConnectedRootDatum_G2]
      exact heq.symm ▸ hnot
    · rw [simplyConnectedRootDatum_G2]
      exact heq.symm ▸ hne
  exact ⟨zeroBracket i m 4 1 (by decide) (by rw [hm, hl, hk]; module),
    zeroBracket i o 4 2 (by decide) (by rw [ho, hl, hk]; module),
    zeroBracket j k 1 2 (by decide) (by rw [hk]; module),
    zeroBracket l m 5 2 (by decide) (by rw [hm, hl, hk]; module),
    zeroBracket k o 4 3 (by decide) (by rw [ho, hl, hk]; module),
    zeroBracket l o 5 3 (by decide) (by rw [ho, hl, hk]; module),
    zeroBracket m o 6 3 (by decide) (by rw [hm, ho, hl, hk]; module)⟩

end Configuration

-- Use the scalar structure carried by algebra-valued points for tensor products.
attribute [local instance high] Algebra.toModule

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra valid_G2) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (G2.lieBasis valid_G2).rootGenerator (G2.lieBasis valid_G2).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).rootGenerator i))))

/-- The short–long `G₂` straightening formula on any Kostant-stable lattice. The successive
indices are `α`, `β`, `α+β`, `2α+β`, `3α+β`, `3α+2β`, with `α` short and `β` long.
All four coefficients are integral, including in value characteristics two and three. -/
theorem chevalleyRootSubgroup_mul_of_g2_short_long
    (i j k l m o : Fin G2.numRoots) (hi : g2Length i = 1) (hj : g2Length j = 3)
    (hk : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i)
    (hl : g2SimplyConnectedRootDatum.root l =
      g2SimplyConnectedRootDatum.root k + g2SimplyConnectedRootDatum.root i)
    (hm : g2SimplyConnectedRootDatum.root m =
      g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root i)
    (ho : g2SimplyConnectedRootDatum.root o =
      g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root k)
    (A : CommAlgCat ℤ) (u v : A) :
    let c := G2.structureConstant valid_G2 i j
    let d := c * (G2.structureConstant valid_G2 i k / 2)
    let a := d * (G2.structureConstant valid_G2 i l / 3)
    let b := d * c * (G2.structureConstant valid_G2 l k / 3)
    chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil k A (Multiplicative.ofAdd ((c : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil l A (Multiplicative.ofAdd ((d : A) * (u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil m A (Multiplicative.ofAdd ((a : A) * (u ^ 3 * v))) *
        chevalleyRootSubgroup ρ M hM hnil o A (Multiplicative.ofAdd ((b : A) * (u ^ 3 * v ^ 2))) *
        chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) := by
  obtain ⟨hij, hik, hil, hlk⟩ := short_long_scaled_brackets i j k l m o hi hj hk hl hm ho
  obtain ⟨him, hio, hjk, hlm, hko, hlo, hmo⟩ :=
    short_long_zero_brackets i j k l m o hi hj hk hl hm ho
  let e := G2.chevalleySystem valid_G2
  let h := (G2.lieBasis valid_G2).h
  have hMall : ∀ z ∈ kostantForm e h, ∀ w ∈ M, ρ z w ∈ M := by
    intro z hz w hw
    refine kostantForm_apply_mem e h ρ M.toIntSubmodule ?_ ?_ z hz hw
    · intro r n w hw
      rw [Associative.map_dividedPower]
      exact dividedPower_chevalleySystem_smul_mem ρ M hM hnil r n w hw
    · intro r n w hw
      exact hM _ (ringChoose_mem_kostantForm _ _ r n) w hw
  let nil r := isNilpotent_apply_ι_chevalleySystem ρ hnil r
  have heq (r : Fin G2.numRoots) (w : Multiplicative A) :
      kostantRootSubgroupPoints e h ρ M hMall r (nil r)
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm w) =
        chevalleyRootSubgroup ρ M hM hnil r A w := by
    apply Units.ext
    simp only [kostantRootSubgroupPoints_val, chevalleyRootSubgroup_val,
      MulEquiv.apply_symm_apply, e]
  have H := kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul' e h ρ M hMall
    hij hik hil hlk him hio hjk hlm hko hlo hmo
    (nil i) (nil j) (nil k) (nil l) (nil m) (nil o)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u))
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd v))
  simpa only [heq, MulEquiv.apply_symm_apply, toAdd_ofAdd] using H

end

end TauCeti.DynkinType
