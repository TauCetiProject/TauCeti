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
straightening formula with four correction factors at α + β, 2α + β, 3α + β and 3α + 2β
for the native pinned root subgroups on any Kostant-stable lattice, over every commutative
value ring. All bracket hypotheses are discharged from the integral root datum and the pinned
integer structure constants.

The coefficients are computed in ℤ before mapping to the value ring. In particular, the
divisions by two and three below do not require these numbers to be invertible in that ring.
The formula retains the signs of the chosen Chevalley system.
`g2_short_long_coefficients_isUnit` shows that all four integer coefficients are units.

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

private theorem g2_root_eq_add {p q r : Fin G2.numRoots}
    (h : g2SimplyConnectedRootDatum.root r =
      g2SimplyConnectedRootDatum.root p + g2SimplyConnectedRootDatum.root q) :
    (G2.simplyConnectedRootDatum valid_G2).root r =
      (G2.simplyConnectedRootDatum valid_G2).root p +
        (G2.simplyConnectedRootDatum valid_G2).root q := by
  rw [simplyConnectedRootDatum_G2]
  exact h

private theorem g2_chainBotCoeff_eq (p q : Fin G2.numRoots) :
    (G2.simplyConnectedRootDatum valid_G2).chainBotCoeff p q =
      g2SimplyConnectedRootDatum.chainBotCoeff p q := by
  rw [simplyConnectedRootDatum_G2]
  rfl

section Configuration

variable (i j k l m o : Fin G2.numRoots) (hi : g2Length i = 1) (hj : g2Length j = 3)
variable (hk : g2SimplyConnectedRootDatum.root k =
  g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root j)
variable (hl : g2SimplyConnectedRootDatum.root l =
  g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root k)
variable (hm : g2SimplyConnectedRootDatum.root m =
  g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root l)
variable (ho : g2SimplyConnectedRootDatum.root o =
  g2SimplyConnectedRootDatum.root l + g2SimplyConnectedRootDatum.root k)

include hi hj hk hl hm ho in
private theorem short_long_constants :
    2 ∣ G2.structureConstant valid_G2 i k ∧
      3 ∣ G2.structureConstant valid_G2 i l ∧
      3 ∣ G2.structureConstant valid_G2 l k := by
  obtain ⟨_, hik, hil, hlk⟩ := g2_chainBotCoeff_of_short_add_long_eq_root i j k l o hi hj hk hl ho
  have dvd {p q r : Fin G2.numRoots}
      (h : g2SimplyConnectedRootDatum.root r =
        g2SimplyConnectedRootDatum.root p + g2SimplyConnectedRootDatum.root q) :=
    chainBotCoeff_add_one_dvd_structureConstant (t := G2) (ht := valid_G2)
      (α := p) (β := q) ⟨r, g2_root_eq_add h⟩
  simpa only [g2_chainBotCoeff_eq, hik, hil, hlk, Nat.reduceAdd, Nat.cast_ofNat] using
    And.intro (dvd hl) (And.intro (dvd hm) (dvd ho))

include hi hj hk hl hm ho in
/-- The four integer coefficients in the short–long `G₂` straightening formula are units
(that is, each is `1` or `-1`). The divisions are taken in `ℤ`, before any base change. -/
theorem g2_short_long_coefficients_isUnit :
    let c := G2.structureConstant valid_G2 i j
    let d := c * (G2.structureConstant valid_G2 i k / 2)
    let a := d * (G2.structureConstant valid_G2 i l / 3)
    let b := d * c * (G2.structureConstant valid_G2 l k / 3)
    IsUnit c ∧ IsUnit d ∧ IsUnit a ∧ IsUnit b := by
  obtain ⟨hij, hik, hil, hlk⟩ :=
    g2_chainBotCoeff_of_short_add_long_eq_root i j k l o hi hj hk hl ho
  have values {p q r : Fin G2.numRoots}
      (h : g2SimplyConnectedRootDatum.root r =
        g2SimplyConnectedRootDatum.root p + g2SimplyConnectedRootDatum.root q) :=
    structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := valid_G2)
      (α := p) (β := q) ⟨r, g2_root_eq_add h⟩
  have hc := values hk
  have hd := values hl
  have ha := values hm
  have hb := values ho
  simp only [g2_chainBotCoeff_eq, hij, hik, hil, hlk, Nat.reduceAdd, Nat.cast_ofNat]
    at hc hd ha hb
  rcases hc with hc | hc <;> rcases hd with hd | hd <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> norm_num [hc, hd, ha, hb]

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
      (t := G2) (ht := valid_G2) (g2_root_eq_add h)
  refine ⟨bracket hk, ?_, ?_, ?_⟩
  · rw [bracket hl, smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h2]
  · rw [bracket hm, smul_smul]
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
    obtain ⟨hnot, hne⟩ :=
      g2_smul_short_add_smul_long_notMem_range_root_and_ne_zero i j hi hj ⟨k, hk⟩ a b hab
    apply lie_chevalleySystem_eq_zero (t := G2) (ht := valid_G2) <;>
      rw [simplyConnectedRootDatum_G2]
    · exact heq.symm ▸ hnot
    · exact heq.symm ▸ hne
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
      g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root j)
    (hl : g2SimplyConnectedRootDatum.root l =
      g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root k)
    (hm : g2SimplyConnectedRootDatum.root m =
      g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root l)
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
  have hMall := kostantForm_apply_mem_of_chevalleySystem ρ M hM hnil
  let nil r := isNilpotent_apply_ι_chevalleySystem ρ hnil r
  have H := kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul' e h ρ M hMall
    hij hik hil hlk him hio hjk hlm hko hlo hmo
    (nil i) (nil j) (nil k) (nil l) (nil m) (nil o)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u))
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd v))
  simpa only [e, h, kostantRootSubgroupPoints_chevalleySystem_eq_chevalleyRootSubgroup ρ M hM hnil,
    MulEquiv.apply_symm_apply, toAdd_ofAdd] using H

end

end TauCeti.DynkinType
