/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.LongSum
import TauCeti.Algebra.Lie.UniversalEnveloping.Commutator.G2.ShortPair

/-!
# The native G₂ short-pair Chevalley relation

For short roots `α`, `β` whose sum `γ = α + β` is short, the other roots in their positive
cone are `δ = 2α + β` and `ε = α + 2β`. This file derives the three-factor Chevalley relation
from the pinned root datum and its integer structure constants, on any Kostant-stable lattice
and over every commutative value ring. The roots need not be positive in the pinned base.

The integral coefficients are `c = N_{α,β}/2`, `d = c (N_{α,γ}/3)` and
`a = c (N_{γ,β}/3)`. The divisions take place in ℤ before scalar extension. In the product
relation the three parameters are `2cuv`, `3du²v` and `3auv²` after the initial `x_β(v)`;
in the element commutator they are `2cuv`, `3du²v` and `-3auv²`. Moving the initial `x_β(v)`
past `x_γ(2cuv)` accounts for this last sign.

## Main results

* `TauCeti.DynkinType.chevalleyRootSubgroup_mul_of_g2_short_pair`: the product relation.
* `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_short_pair`: the ordered
  element-commutator formula.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {ht : G2.Valid} {i j k l m : Fin G2.numRoots}

private theorem g2_sum_excluded_iff (i j : Fin G2.numRoots) (a b : ℤ) :
    (a • (G2.simplyConnectedRootDatum ht).root i + b • (G2.simplyConnectedRootDatum ht).root j ∉
        Set.range (G2.simplyConnectedRootDatum ht).root ∧
      a • (G2.simplyConnectedRootDatum ht).root i +
        b • (G2.simplyConnectedRootDatum ht).root j ≠ 0) ↔
    (a • g2Root i + b • g2Root j ∉ Set.range g2Root ∧
      a • g2Root i + b • g2Root j ≠ 0) := by
  simp +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
    rank, numRoots, Pi.zero_def]

private theorem g2_short_pair_last_long {i j k m : Fin 12}
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : g2Root k = g2Root i + g2Root j)
    (hkj : g2Root m = g2Root k + g2Root j) : g2Length m = 3 := by
  simp only [g2Root_apply] at hij hkj
  simp only [g2Length_apply] at hi hj hk ⊢
  revert i j k m
  decide +kernel

private theorem g2_short_pair_excluded_sums {i j k : Fin 12}
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : g2Root k = g2Root i + g2Root j) (a b : ℤ)
    (hab : (a, b) ∈ ({(3, 1), (2, 2), (1, 3), (3, 2), (2, 3), (3, 3)} : Set (ℤ × ℤ))) :
    (a • g2Root i + b • g2Root j ∉ Set.range g2Root) ∧
      a • g2Root i + b • g2Root j ≠ 0 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
  rcases hab with h | h | h | h | h | h <;> cases h
  all_goals
    simp only [Set.mem_range, g2Root_apply] at hij ⊢
    simp only [g2Length_apply] at hi hj hk
    revert i j k
    decide +kernel

private theorem g2_short_pair_coefficients
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j) :
    2 * (G2.structureConstant ht i j / 2) = G2.structureConstant ht i j ∧
      3 * (G2.structureConstant ht i k / 3) = G2.structureConstant ht i k ∧
      3 * (G2.structureConstant ht k j / 3) = G2.structureConstant ht k j := by
  have hl := g2_short_pair_last_long hj hi hk
    ((g2_root_add_iff j i k).1 (hij.trans (add_comm _ _)))
    ((g2_root_add_iff k i l).1 (hik.trans (add_comm _ _)))
  have hm := g2_short_pair_last_long hi hj hk
    ((g2_root_add_iff i j k).1 hij) ((g2_root_add_iff k j m).1 hkj)
  have h₁ := structureConstant_G2_eq_two_or_eq_neg_two hi hj hk hij
  have h₂ := structureConstant_G2_eq_three_or_eq_neg_three hi hk hl hik
  have h₃ := structureConstant_G2_eq_three_or_eq_neg_three hk hj hm hkj
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ <;> simp_all

private theorem g2_short_pair_vanishing_brackets
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j) :
    ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht l⁆ = 0 ∧
      ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht m⁆ = 0 ∧
      ⁅G2.chevalleySystem ht j, G2.chevalleySystem ht l⁆ = 0 ∧
      ⁅G2.chevalleySystem ht j, G2.chevalleySystem ht m⁆ = 0 ∧
      ⁅G2.chevalleySystem ht k, G2.chevalleySystem ht l⁆ = 0 ∧
      ⁅G2.chevalleySystem ht k, G2.chevalleySystem ht m⁆ = 0 ∧
      ⁅G2.chevalleySystem ht l, G2.chevalleySystem ht m⁆ = 0 := by
  let P := G2.simplyConnectedRootDatum ht
  have hij' : g2Root k = g2Root i + g2Root j := by
    exact (g2_root_add_iff i j k).1 hij
  have H (r s : Fin G2.numRoots) (a b : ℤ)
      (heq : P.root r + P.root s = a • P.root i + b • P.root j)
      (hab : (a, b) ∈ ({(3, 1), (2, 2), (1, 3), (3, 2), (2, 3), (3, 3)} : Set (ℤ × ℤ))) :
      ⁅G2.chevalleySystem ht r, G2.chevalleySystem ht s⁆ = 0 := by
    have hex : (a • P.root i + b • P.root j ∉ Set.range P.root) ∧
        a • P.root i + b • P.root j ≠ 0 := by
      exact (g2_sum_excluded_iff i j a b).2 (g2_short_pair_excluded_sums hi hj hk hij' a b hab)
    exact lie_chevalleySystem_eq_zero (heq ▸ hex.1) (heq ▸ hex.2)
  refine ⟨H i l 3 1 ?_ (by simp), H i m 2 2 ?_ (by simp),
    H j l 2 2 ?_ (by simp), H j m 1 3 ?_ (by simp),
    H k l 3 2 ?_ (by simp), H k m 2 3 ?_ (by simp), H l m 3 3 ?_ (by simp)⟩
  all_goals simp only [P, hik, hkj, hij]; abel

private theorem g2_short_pair_scaled_brackets
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j) :
    let c := G2.structureConstant ht i j / 2
    let d := c * (G2.structureConstant ht i k / 3)
    let a := c * (G2.structureConstant ht k j / 3)
    ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht j⁆ = (2 * c) • G2.chevalleySystem ht k ∧
      c • ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht k⁆ = (3 * d) • G2.chevalleySystem ht l ∧
      c • ⁅G2.chevalleySystem ht k, G2.chevalleySystem ht j⁆ =
        (3 * a) • G2.chevalleySystem ht m := by
  obtain ⟨hc, hd, ha⟩ := g2_short_pair_coefficients hi hj hk hij hik hkj
  refine ⟨?_, ?_, ?_⟩
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul hij, hc]
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul hik, smul_smul]
    congr 1
    linear_combination -(G2.structureConstant ht i j / 2) * hd
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul hkj, smul_smul]
    congr 1
    linear_combination -(G2.structureConstant ht i j / 2) * ha

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ z ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ v ∈ M, ρ z v ∈ M)
variable (hnil : ∀ r, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator r))))

-- Match the tensor-product module to the algebra structure stored by the value ring.
attribute [local instance high] Algebra.toModule

/-- The three-factor product relation for any short-root pair in G₂ whose sum is short,
on every Kostant-stable lattice over every commutative value ring. All bracket and
nilpotence conditions are derived from the native root datum and simple generators. -/
theorem chevalleyRootSubgroup_mul_of_g2_short_pair
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j)
    (A : CommAlgCat ℤ) (u v : A) :
    let c := G2.structureConstant ht i j / 2
    let d := c * (G2.structureConstant ht i k / 3)
    let a := c * (G2.structureConstant ht k j / 3)
    chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil k A (Multiplicative.ofAdd ((c : A) * (2 * u * v))) *
        chevalleyRootSubgroup ρ M hM hnil l A (Multiplicative.ofAdd ((d : A) * (3 * u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil m A (Multiplicative.ofAdd ((a : A) * (3 * u * v ^ 2))) *
        chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) := by
  let c := G2.structureConstant ht i j / 2
  let d := c * (G2.structureConstant ht i k / 3)
  let a := c * (G2.structureConstant ht k j / 3)
  obtain ⟨hbrij, hbrik, hbrkj⟩ := g2_short_pair_scaled_brackets hi hj hk hij hik hkj
  obtain ⟨hil, him, _, hjm, hkl, hkm, hlm⟩ :=
    g2_short_pair_vanishing_brackets hi hj hk hij hik hkj
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  exact baseChangeExp_mul_baseChangeExp_of_g2_short_pair_lie (G2.chevalleySystem ht) ρ M
    hbrij hbrik hbrkj hil him hjm hkl hkm hlm
    (isNilpotent_apply_ι_chevalleySystem ρ hnil i)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil j)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil k)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil l)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil m)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil i)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil j)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil k)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil l)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil m) u v

/-- The Chevalley element-commutator formula for any two short G₂ roots with short sum.
The factors occur at `i+j`, `2i+j`, `i+2j`, in increasing total degree. The last coefficient
has the opposite sign from the product relation with an initial `x_j(v)`. -/
theorem commutatorElement_chevalleyRootSubgroup_of_g2_short_pair
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j)
    (A : CommAlgCat ℤ) (u v : A) :
    let c := G2.structureConstant ht i j / 2
    let d := c * (G2.structureConstant ht i k / 3)
    let a := c * (G2.structureConstant ht k j / 3)
    ⁅chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil k A (Multiplicative.ofAdd ((c : A) * (2 * u * v))) *
        chevalleyRootSubgroup ρ M hM hnil l A (Multiplicative.ofAdd ((d : A) * (3 * u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil m A
          (Multiplicative.ofAdd (-(a : A) * (3 * u * v ^ 2))) := by
  let c := G2.structureConstant ht i j / 2
  let d := c * (G2.structureConstant ht i k / 3)
  let a := c * (G2.structureConstant ht k j / 3)
  let x r (s : A) := chevalleyRootSubgroup ρ M hM hnil r A (Multiplicative.ofAdd s)
  obtain ⟨_, _, hjl, hjm, _, _, hlm⟩ :=
    g2_short_pair_vanishing_brackets hi hj hk hij hik hkj
  have H (r s) (hrs : ⁅G2.chevalleySystem ht r, G2.chevalleySystem ht s⁆ = 0) (p q : A) :
      Commute (x r p) (x s q) :=
    commute_chevalleyRootSubgroup ρ M hM hnil hrs A _ _
  have hmLong := g2_short_pair_last_long hi hj hk
    ((g2_root_add_iff i j k).1 hij) ((g2_root_add_iff k j m).1 hkj)
  let t := (G2.structureConstant ht j k : A) * (v * ((c : A) * (2 * u * v)))
  have hswap : x j v * x k ((c : A) * (2 * u * v)) =
      x k ((c : A) * (2 * u * v)) * x m t * x j v :=
    chevalleyRootSubgroup_mul_G2_of_long_sum ρ M hM hnil hmLong
      (hkj.trans (add_comm _ _)) A v ((c : A) * (2 * u * v))
  have hprod := chevalleyRootSubgroup_mul_of_g2_short_pair ρ M hM hnil hi hj hk hij hik hkj A u v
  have hm : x m t * x m ((a : A) * (3 * u * v ^ 2)) =
      x m (-(a : A) * (3 * u * v ^ 2)) := by
    rw [← map_mul, ← ofAdd_add]
    congr 2
    obtain ⟨_, _, ha⟩ := g2_short_pair_coefficients hi hj hk hij hik hkj
    have hn : (G2.structureConstant ht j k : A) =
        -3 * (G2.structureConstant ht k j / 3 : ℤ) := by
      rw [G2.structureConstant_skew (ht := ht) k j, Int.cast_neg, ← ha, Int.cast_mul]
      simp
    dsimp [t, a]
    rw [hn, Int.cast_mul]
    ring
  calc
    ⁅x i u, x j v⁆ = MulAut.conj (x j v)
        (x k ((c : A) * (2 * u * v)) * x l ((d : A) * (3 * u ^ 2 * v)) *
          x m ((a : A) * (3 * u * v ^ 2))) := by
      rw [commutatorElement_def, hprod]
      simp [x, c, d, a, MulAut.conj_apply, mul_assoc]
    _ = (x k ((c : A) * (2 * u * v)) * x m t) *
        x l ((d : A) * (3 * u ^ 2 * v)) * x m ((a : A) * (3 * u * v ^ 2)) := by
      simp only [map_mul, MulAut.conj_apply]
      rw [hswap, (H j l hjl _ _).eq, (H j m hjm _ _).eq]
      simp only [mul_inv_cancel_right]
    _ = x k ((c : A) * (2 * u * v)) * x l ((d : A) * (3 * u ^ 2 * v)) *
        x m (-(a : A) * (3 * u * v ^ 2)) := by
      -- The long-root factors commute; combine the two parameters in the last root subgroup.
      rw [mul_assoc _ (x m t), (H l m hlm _ _).symm.eq, ← mul_assoc, mul_assoc, hm]

end

end TauCeti.DynkinType
