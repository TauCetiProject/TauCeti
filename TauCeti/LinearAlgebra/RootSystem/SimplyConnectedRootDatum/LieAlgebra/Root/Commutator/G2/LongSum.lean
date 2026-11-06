/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant.G2
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Chevalley commutators with a long sum in type `G₂`

When `γ = α + β` is a long root of the pinned `G₂` datum, neither `α + γ` nor `β + γ` is a
root or zero. Thus the root operators form a class-two system and the native root subgroups
satisfy `⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β}uv)` over every commutative coefficient ring.
The representation needs only nilpotence of the simple generators and a Kostant-stable additive
subgroup; no weight basis or faithfulness is required.

For two short summands the coefficient is `±3`, so the subgroups commute in characteristic
three. The proof uses the integral exponential identity
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq`, with divided-power stability from
the native all-root subgroup construction.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra TensorProduct
open scoped commutatorElement

noncomputable section

variable {ht : G2.Valid}

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ a ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ v ∈ M, ρ a v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator i))))

-- Match the scalar action on tensor products to the value algebra's stored instance.
attribute [local instance high] Algebra.toModule

/-- If the sum of two `G₂` roots is long, their native root-subgroup commutator has the single
factor `x_{α+β}(N_{α,β}uv)`, over any commutative coefficient ring. -/
theorem commutatorElement_chevalleyRootSubgroup_G2_of_long_sum {α β γ : Fin G2.numRoots}
    (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((G2.structureConstant ht α β : A) * (u * v))) := by
  let := G2.isReduced_simplyConnectedRootDatum ht
  -- The long-sum geometry makes the third root vector central for both summands.
  have hcentral (i j : Fin G2.numRoots)
      (hij : (G2.simplyConnectedRootDatum ht).root γ =
        (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j) :
      ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht γ⁆ = 0 := by
    apply lie_chevalleySystem_eq_zero
    · simpa +instances only [numRoots_G2, rank_G2, simplyConnectedRootDatum_G2] using
        g2_root_add_not_mem_range_of_add_eq_long i j γ hγ
          (by simpa +instances only [numRoots_G2, rank_G2, simplyConnectedRootDatum_G2] using hij)
    · intro hz
      have hli := (G2.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root'
        ⟨γ, hij⟩
      have hcoeff := (LinearIndependent.pair_iff.mp hli) (2 : ℤ) 1
        (by simpa only [hij, two_smul, one_smul, add_assoc] using hz)
      norm_num at hcoeff
  have hαγ := hcentral α β hadd
  have hβγ := hcentral β α (hadd.trans (add_comm _ _))
  have hαβ := lie_chevalleySystem_eq_structureConstant_zsmul hadd
  -- Absorb the integral structure constant into the exponential parameter.
  have hscaled : ∀ n, ∀ w ∈ M, Associative.dividedPower n
      (G2.structureConstant ht α β •
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (G2.chevalleySystem ht γ))) • w ∈ M := by
    intro n w hw
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ n w hw) _
  -- The existing integral exponential identity supplies the product relation.
  -- Using preserved divided powers directly avoids requiring a finite-dimensional Lie module.
  have hprod :
      chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
          chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) =
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
          chevalleyRootSubgroup ρ M hM hnil γ A
            (Multiplicative.ofAdd ((G2.structureConstant ht α β : A) * (u * v))) *
          chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) := by
    apply Units.ext
    simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
    rw [← baseChangeExp_zsmul (G2.structureConstant ht α β) M
      (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ) hscaled
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ)]
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M
      (mul_eq_mul_add_zsmul_of_lie_eq ρ hαβ)
      ((commute_of_lie_eq_zero ρ hαγ).smul_right _)
      ((commute_of_lie_eq_zero ρ hβγ).smul_right _)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil β) _ _ hscaled u v
  -- The central third factor turns that product relation into the canonical commutator.
  have hcomm : Commute
      (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v))
      (chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((G2.structureConstant ht α β : A) * (u * v)))) := by
    apply Units.ext
    simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
    exact commute_baseChangeExp M (commute_of_lie_eq_zero ρ hβγ) _ _ _ _
  rw [commutatorElement_def, hprod, mul_inv_cancel_right, hcomm.eq, mul_inv_cancel_right]

/-- Short `G₂` root subgroups whose sum is long commute in characteristic three. -/
theorem commute_chevalleyRootSubgroup_G2_of_short_add_short_eq_long {α β γ : Fin G2.numRoots}
    (hα : g2Length α = 1) (hβ : g2Length β = 1) (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (A : CommAlgCat ℤ) [CharP A 3] (u v : A) :
    Commute (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))
      (chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutatorElement_chevalleyRootSubgroup_G2_of_long_sum ρ M hM hnil hγ hadd]
  have hzero : (G2.structureConstant ht α β : A) = 0 := by
    have hthree : (3 : A) = 0 := by exact_mod_cast CharP.cast_eq_zero A 3
    rcases structureConstant_G2_eq_three_or_eq_neg_three hα hβ hγ hadd with h | h <;>
      simp [h, hthree]
  simp [hzero]

end

end TauCeti.DynkinType
