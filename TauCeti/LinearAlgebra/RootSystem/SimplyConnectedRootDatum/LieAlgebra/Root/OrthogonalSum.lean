/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.LinearAlgebra.RootSystem.RootString
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator

/-!
# Chevalley commutators for orthogonal roots with a root sum

Orthogonal roots need not have commuting root subgroups: if their sum is a root, the
commutator is the subgroup of that sum with coefficient `N = ±2`. This file proves that
formula for the numbered pinned Chevalley system on any Kostant-stable lattice, over every
commutative value ring. In characteristic two these root subgroups do commute.

The root-string calculation discharges the vanishing-bracket hypotheses of the integral
class-two exponential identity. The transport follows
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_eq`, using the
all-root divided-power integrality of `TauCeti.DynkinType.chevalleyRootSubgroup`.
See Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, and Carter,
*Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieModule TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {α β γ : Fin t.numRoots}

private theorem orthogonal_sum_brackets
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (horth : (t.simplyConnectedRootDatum ht).pairingIn ℤ β α = 0) :
    ⁅t.chevalleySystem ht α, t.chevalleySystem ht γ⁆ = 0 := by
  let P := t.rationalRootSystem ht
  have hsum : P.root α + P.root β ∈ Set.range P.root := by
    refine ⟨γ, ?_⟩
    simpa [P, add_comm] using (t.root_rationalRootSystem_eq_add_zsmul_iff ht α β γ 1).2
      (by simpa [add_comm] using hγ)
  have hli := P.linearIndependent_of_add_mem_range_root' hsum
  have htop := (P.chainBotCoeff_eq_one_and_chainTopCoeff_eq_one_of_pairingIn_eq_zero
    hsum (by simpa [P] using horth)).2
  apply lie_chevalleySystem_eq_zero
  · rintro ⟨δ, hδ⟩
    have hδ' : P.root δ = P.root β + (2 : ℚ) • P.root α := by
      apply (t.root_rationalRootSystem_eq_add_zsmul_iff ht α β δ 2).2
      rw [hδ, hγ]
      module
    have : 2 ≤ P.chainTopCoeff α β :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).1 ⟨δ, hδ'⟩
    omega
  · intro hz
    have hp := congrArg ((t.simplyConnectedRootDatum ht).coroot' α) hz
    simp only [map_add, hγ, map_add, RootPairing.root_coroot'_eq_pairing, map_zero] at hp
    have horth' : (t.simplyConnectedRootDatum ht).pairing β α = 0 := by
      simpa using (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ β α |>.symm.trans
        (congrArg (algebraMap ℤ ℤ) horth)
    simp [horth'] at hp

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
    ∀ v ∈ M, ρ u v ∈ M)
  (hnil : ∀ i, IsNilpotent
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- Orthogonal roots with a root sum satisfy the one-factor Chevalley commutator formula,
with the native signed structure constant, over every commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_pairingIn_eq_zero
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (horth : (t.simplyConnectedRootDatum ht).pairingIn ℤ β α = 0)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) := by
  have hαγ := orthogonal_sum_brackets hγ horth
  have hβα : (t.simplyConnectedRootDatum ht).pairingIn ℤ α β = 0 :=
    (t.simplyConnectedRootDatum ht).pairingIn_eq_zero_iff.mp horth
  have hβγ := orthogonal_sum_brackets (hγ.trans (add_comm _ _)) hβα
  let c := t.structureConstant ht α β
  have hxy := mul_eq_mul_add_zsmul_of_lie_eq ρ
    (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
  have hxz := commute_of_lie_eq_zero ρ hαγ
  have hyz := commute_of_lie_eq_zero ρ hβγ
  have hdp := dividedPower_chevalleySystem_smul_mem ρ M hM hnil
  have hscaled (n : ℕ) (z : V) (hz : z ∈ M) :
      Associative.dividedPower n
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))) • z ∈ M := by
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (hdp γ n z hz) _
  have hprod :
      chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((c : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) := by
    apply Units.ext
    simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
    rw [← baseChangeExp_zsmul c M (hdp γ) hscaled
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ)]
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy
      (hxz.smul_right c) (hyz.smul_right c)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil β) (hdp α) (hdp β) hscaled u v
  have hcomm (w : A) : Commute
      (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v))
      (chevalleyRootSubgroup ρ M hM hnil γ A (Multiplicative.ofAdd w)) := by
    apply Units.ext
    simpa only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd] using
      (commute_baseChangeExp M hyz (hdp β) (hdp γ) v w).eq
  rw [commutatorElement_def, hprod, mul_inv_cancel_right, (hcomm _).eq]
  simp [c]

/-- In characteristic two, orthogonal root subgroups with a root sum commute. -/
theorem commute_chevalleyRootSubgroup_of_pairingIn_eq_zero_of_char_two
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (horth : (t.simplyConnectedRootDatum ht).pairingIn ℤ β α = 0)
    (A : CommAlgCat ℤ) [CharP A 2] (u v : A) :
    Commute (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))
      (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)) := by
  rw [← commutatorElement_eq_one_iff_commute,
    commutatorElement_chevalleyRootSubgroup_of_pairingIn_eq_zero ρ M hM hnil hγ horth]
  have htwo : (2 : A) = 0 := by simpa using CharP.cast_eq_zero (↑A) 2
  rcases structureConstant_eq_two_or_neg_two_of_pairingIn_eq_zero ⟨γ, hγ⟩ horth with hc | hc <;>
    simp [hc, htwo, ofAdd_zero]

end

end TauCeti.DynkinType
