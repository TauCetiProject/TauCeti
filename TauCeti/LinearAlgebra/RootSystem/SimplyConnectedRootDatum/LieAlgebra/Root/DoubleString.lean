/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.RingTheory.Nilpotent.RootString.Basic
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator

/-!
# Chevalley commutators along a double root string

For a pinned root string with positive root combinations `α + β` and `2α + β`, this proves the
commutator formula on every Kostant-stable lattice over every commutative ring. The string
hypotheses are read in the integral root datum, not assumed equations between Lie brackets:
the `α`-string through `β` has bottom coefficient zero and top coefficient two. The
`β`-string through `α` then has top coefficient one. These are the double-string configurations
in types `B`, `C` and `F₄`, with no restriction to simple roots.
The second coefficient is `N_{α,β} N_{α,α+β} / 2`, computed in the integers before passage to
the value ring. In particular the formula also applies in characteristic two.

The root-vector construction and the integral exponential identity used here are respectively
`DynkinType.chevalleySystem` and
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul`.
The resulting relation is one of the rank-two relations used to reorder root-subgroup products.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieModule TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {α β γ δ : Fin t.numRoots}

/-- Along a root string starting at `β`, the bracket at its next step has even structure
constant. Division by two here is in `ℤ`, not in a value ring. -/
theorem two_mul_structureConstant_div_two_of_chainBotCoeff_eq_zero
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0) :
    2 * (t.structureConstant ht α γ / 2) = t.structureConstant ht α γ := by
  let := t.isReduced_simplyConnectedRootDatum ht
  have hli := (t.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hnext := (t.simplyConnectedRootDatum ht).chainBotCoeff_of_add hli
    (hγ.trans (add_comm _ _))
  rcases structureConstant_eq_natCast_or_eq_neg_natCast (Set.mem_range.mpr ⟨δ, hδ⟩) with h | h
  all_goals simp only [hbot, zero_add] at hnext
  all_goals rw [hnext] at h
  all_goals norm_num at h ⊢; omega

/-- The second bracket along `β, α + β, 2α + β` has the integral divided-power coefficient
`N_{α,β} (N_{α,α+β} / 2)`. -/
theorem lie_lie_chevalleySystem_of_chainBotCoeff_eq_zero
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0) :
    ⁅t.chevalleySystem ht α, ⁅t.chevalleySystem ht α, t.chevalleySystem ht β⁆⁆ =
      (2 * (t.structureConstant ht α β * (t.structureConstant ht α γ / 2))) •
        t.chevalleySystem ht δ := by
  rw [lie_chevalleySystem_eq_structureConstant_zsmul hγ, lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul]
  congr 1
  have := two_mul_structureConstant_div_two_of_chainBotCoeff_eq_zero hγ hδ hbot
  linear_combination -t.structureConstant ht α β * this

private theorem doubleString_brackets
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (htop : (t.simplyConnectedRootDatum ht).chainTopCoeff α β = 2) :
    ⁅t.chevalleySystem ht α, t.chevalleySystem ht δ⁆ = 0 ∧
      ⁅t.chevalleySystem ht β, t.chevalleySystem ht γ⁆ = 0 ∧
      ⁅t.chevalleySystem ht β, t.chevalleySystem ht δ⁆ = 0 := by
  let P := t.simplyConnectedRootDatum ht
  let : P.IsReduced := t.isReduced_simplyConnectedRootDatum ht
  have hli : LinearIndependent ℤ ![P.root α, P.root β] :=
    P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hli' : LinearIndependent ℤ ![P.root β, P.root α] :=
    LinearIndependent.pair_symm_iff.mp hli
  have hrev : P.chainTopCoeff β α = 1 := by
    have hbot' : P.chainBotCoeff β α = 0 := by
      apply P.chainBotCoeff_eq_zero_iff.mpr
      right
      rw [← P.neg_mem_range_root_iff, neg_sub]
      exact (P.chainBotCoeff_eq_zero_iff.mp hbot).resolve_left (not_not.mpr hli)
    have hne : P.root α ≠ P.root β := by
      intro h
      exact one_ne_zero (hli.eq_zero_of_pair' (s := 1) (t := 1) (by simpa using h)).1
    have hneg : P.root α ≠ -P.root β := by
      intro h
      exact one_ne_zero (hli.eq_zero_of_pair' (s := 1) (t := -1) (by simpa using h)).1
    have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' α β hne hneg
    have hp := P.chainBotCoeff_sub_chainTopCoeff hli
    have hp' := P.chainTopCoeff_sub_chainBotCoeff hli'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpair
    rw [hbot, htop] at hp
    rw [hbot'] at hp'
    omega
  have hn (a b : ℤ) (hb : b ≠ 0) : a • P.root α + b • P.root β ≠ 0 :=
    fun hz ↦ hb (LinearIndependent.pair_iff.mp hli a b hz).2
  have hthree : P.root β + 3 • P.root α ∉ Set.range P.root := by
    rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli, htop]
    omega
  have htwo : P.root α + 2 • P.root β ∉ Set.range P.root := by
    rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli', hrev]
    omega
  have hdouble : P.root γ + P.root γ ∉ Set.range P.root := by
    intro h
    have hi := P.linearIndependent_of_add_mem_range_root' h
    have := LinearIndependent.pair_iff.mp hi (1 : ℤ) (-1) (by simp)
    norm_num at this
  have had : P.root α + P.root δ = 3 • P.root α + P.root β := by
    rw [hδ, hγ]; module
  have hbg : P.root β + P.root γ = P.root α + 2 • P.root β := by
    rw [hγ]; module
  have hbd : P.root β + P.root δ = P.root γ + P.root γ := by
    rw [hδ, hγ]; module
  dsimp only [P] at had hbg hbd hn hthree htwo hdouble
  refine ⟨lie_chevalleySystem_eq_zero ?_ ?_, lie_chevalleySystem_eq_zero ?_ ?_,
    lie_chevalleySystem_eq_zero ?_ ?_⟩
  · simpa only [had, add_comm] using hthree
  · rw [had]
    convert hn 3 1 (by decide) using 1
    module
  · simpa only [hbg] using htwo
  · rw [hbg]
    convert hn 1 2 (by decide) using 1
    module
  · simpa only [hbd] using hdouble
  · rw [hbd, hγ]
    convert hn 2 2 (by decide) using 1
    module

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- Reorder two root-subgroup elements along a double string. The two correction factors
have roots `α + β` and `2α + β`, with coefficients computed integrally before scalar extension. -/
theorem chevalleyRootSubgroup_mul_of_doubleString
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (htop : (t.simplyConnectedRootDatum ht).chainTopCoeff α β = 2)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        (chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd
            (((t.structureConstant ht α β * (t.structureConstant ht α γ / 2) : ℤ) : A) *
              (u ^ 2 * v)))) *
        chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) := by
  obtain ⟨had, hbg, _⟩ := doubleString_brackets hγ hδ hbot htop
  let x (k : Fin t.numRoots) := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
    (t.chevalleySystem ht k))
  let c := t.structureConstant ht α β
  let d := c * (t.structureConstant ht α γ / 2)
  have hij := lie_chevalleySystem_eq_structureConstant_zsmul hγ
  have hiij := lie_lie_chevalleySystem_of_chainBotCoeff_eq_zero hγ hδ hbot
  have hxy := mul_eq_mul_add_zsmul_of_lie_eq ρ hij
  have hxz : x α * (c • x γ) = c • x γ * x α + 2 • (d • x δ) := by
    rw [hij, lie_zsmul] at hiij
    simpa only [one_zsmul, one_mul] using
      (zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
        (p := 1) (q := c) (r := d) (n := 2) (by simpa [c, d] using hiij))
  -- Form the two scaled root vectors integrally, before extending scalars to the value ring.
  have hscaled (z : ℤ) (k : Fin t.numRoots) (n : ℕ) :
      ∀ w ∈ M, Associative.dividedPower n (z • x k) • w ∈ M := by
    intro w hw
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil k n w hw) _
  have hMc := hscaled c γ
  have hMd := hscaled d δ
  have hmul := baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M hxy hxz
    ((commute_of_lie_eq_zero ρ had).smul_right d)
    ((commute_of_lie_eq_zero ρ hbg).smul_right c)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
    ((isNilpotent_apply_ι_chevalleySystem ρ hnil γ).smul c)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil α)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil β) hMc hMd u v
  rw [baseChangeExp_zsmul c M
      (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ) hMc
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ),
    baseChangeExp_zsmul d M
      (dividedPower_chevalleySystem_smul_mem ρ M hM hnil δ) hMd
      (isNilpotent_apply_ι_chevalleySystem ρ hnil δ)] at hmul
  apply Units.ext
  simpa only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd, mul_assoc] using hmul

/-- The Chevalley element-commutator formula for a double string. Its root-string conditions
specify the positive rank-two combinations `α + β` and `2α + β`; no Lie-bracket conditions or
restrictions on the characteristic of the commutative value ring are required. -/
theorem commutatorElement_chevalleyRootSubgroup_of_doubleString
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (htop : (t.simplyConnectedRootDatum ht).chainTopCoeff α β = 2)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
      chevalleyRootSubgroup ρ M hM hnil δ A
        (Multiplicative.ofAdd
          (((t.structureConstant ht α β * (t.structureConstant ht α γ / 2) : ℤ) : A) *
            (u ^ 2 * v))) := by
  obtain ⟨_, hbg, hbd⟩ := doubleString_brackets hγ hδ hbot htop
  let c := t.structureConstant ht α β
  let d := c * (t.structureConstant ht α γ / 2)
  -- The β-factor commutes with both correction factors in the product relation.
  have hcomm : Commute
      (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v))
      (chevalleyRootSubgroup ρ M hM hnil γ A (Multiplicative.ofAdd ((c : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd ((d : A) * (u ^ 2 * v)))) := by
    apply Commute.mul_right
    all_goals apply Units.ext
    all_goals simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
    · exact (commute_baseChangeExp M (commute_of_lie_eq_zero ρ hbg) _ _ _ _).eq
    · exact (commute_baseChangeExp M (commute_of_lie_eq_zero ρ hbd) _ _ _ _).eq
  rw [commutatorElement_def,
    chevalleyRootSubgroup_mul_of_doubleString ρ M hM hnil hγ hδ hbot htop,
    mul_inv_cancel_right, hcomm.eq, mul_inv_cancel_right]

end

end TauCeti.DynkinType
