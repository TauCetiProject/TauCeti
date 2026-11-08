/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Chevalley commutators for orthogonal roots with a root sum

Orthogonal roots need not have commuting root subgroups: if their sum is a root, the
commutator is the subgroup of that sum with coefficient `N = ±2`. This file proves that
formula for the numbered pinned Chevalley system on any Kostant-stable lattice, over every
commutative value ring. In characteristic two these root subgroups do commute.

For `γ = α + β`, the orthogonal root-string facts show that neither `2α + β` nor `α + 2β` is a
root, and the structure constant is `N_{α,β} = ±2`. The commutator formula is the orthogonal-sum
case of `TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_add`.
See Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, and Carter,
*Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieModule TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {α β γ : Fin t.numRoots}

private theorem two_nsmul_add_notMem_range_of_pairingIn_eq_zero
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (horth : (t.simplyConnectedRootDatum ht).pairingIn ℤ β α = 0) :
    2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root := by
  have := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  have hsum : P.root α + P.root β ∈ Set.range P.root := ⟨γ, hγ⟩
  have hli := P.linearIndependent_of_add_mem_range_root' hsum
  have htop := (P.chainBotCoeff_eq_one_and_chainTopCoeff_eq_one_of_pairingIn_eq_zero
    hsum horth).2
  rintro ⟨δ, hδ⟩
  have hδ' : P.root δ = P.root β + (2 : ℕ) • P.root α := by
    rw [hδ]
    module
  have : 2 ≤ P.chainTopCoeff α β :=
    (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).1 ⟨δ, hδ'⟩
  omega

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
  have hβα : (t.simplyConnectedRootDatum ht).pairingIn ℤ α β = 0 :=
    (t.simplyConnectedRootDatum ht).pairingIn_eq_zero_iff.mp horth
  refine commutatorElement_chevalleyRootSubgroup_of_root_eq_add ρ M hM hnil hγ
    (two_nsmul_add_notMem_range_of_pairingIn_eq_zero hγ horth) ?_ A u v
  rw [add_comm]
  exact two_nsmul_add_notMem_range_of_pairingIn_eq_zero (hγ.trans (add_comm _ _)) hβα

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
