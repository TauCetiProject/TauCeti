/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant.G2
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup

/-!
# Chevalley commutators with a long sum in type `G₂`

When `γ = α + β` is a long root of the pinned `G₂` datum, neither `α + γ` nor `β + γ` is a
root or zero. Thus the root operators form a class-two system and the native root subgroups
satisfy `⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β}uv)` over every commutative coefficient ring.
The representation needs only nilpotence of the simple generators and a Kostant-stable additive
subgroup; no weight basis or faithfulness is required.

For two short summands the coefficient is `±3`, so the subgroups commute in characteristic
three. The proof specializes the type-independent native class-two commutator formula
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_lie_eq` using the long-sum
root geometry.

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

private theorem g2_root_add_notMem_range_of_long_sum {α β γ : Fin G2.numRoots}
    (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β) :
    (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ ∉
      Set.range (G2.simplyConnectedRootDatum ht).root := by
  rw [simplyConnectedRootDatum_G2] at hadd ⊢
  exact g2_root_add_notMem_range_of_add_eq_long α β γ hγ hadd

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
  apply commutatorElement_chevalleyRootSubgroup_of_lie_eq ρ M hM hnil
    (lie_chevalleySystem_eq_structureConstant_zsmul hadd)
  · exact lie_chevalleySystem_eq_zero_of_add_eq hadd
      (g2_root_add_notMem_range_of_long_sum hγ hadd)
  · exact lie_chevalleySystem_eq_zero_of_add_eq (hadd.trans (add_comm _ _))
      (g2_root_add_notMem_range_of_long_sum hγ (hadd.trans (add_comm _ _)))

/-- Short `G₂` root subgroups whose sum is long commute in characteristic three. -/
theorem commute_chevalleyRootSubgroup_G2_of_short_add_short_eq_long_of_char_three
    {α β γ : Fin G2.numRoots}
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
