/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.MultiplyLacedRelations
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The doubly-laced Chevalley commutator formula

For the pinned root vectors on a Kostant-stable lattice, this file proves the Chevalley
commutator formula when the root string consists of `β`, `α + β`, `2α + β` and there is no
root `α + 2β`. The coefficients are the native integer structure constants:
`c₁₁ = N_{α,β}` and `c₂₁ = N_{α,β} N_{α,α+β} / 2`. The division is exact in the integers;
no factorial is inverted in the value ring. The result therefore holds over every commutative
ring, including characteristic two, and for any Kostant-stable lattice with nilpotent simple
root operators.

The proof specializes
`TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq'`
to the pinned Chevalley system, discharging its bracket hypotheses from the integral root datum.
The all-root Kostant form preserves the same lattice, and its parametrized root subgroups agree
with the native all-root maps.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, with the convention
  `⁅x, y⁆ = x y x⁻¹ y⁻¹`.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid}

private theorem doublyLaced_vanishing_brackets {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root) :
    ⁅t.chevalleySystem ht α, t.chevalleySystem ht δ⁆ = 0 ∧
      ⁅t.chevalleySystem ht β, t.chevalleySystem ht γ⁆ = 0 ∧
      ⁅t.chevalleySystem ht β, t.chevalleySystem ht δ⁆ = 0 := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hlin := (t.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root'
    (i := α) (j := β) ⟨γ, hγ⟩
  have hind := LinearIndependent.pair_iff.mp hlin
  refine ⟨lie_chevalleySystem_eq_zero hαδ fun hz => ?_,
    lie_chevalleySystem_eq_zero hβγ fun hz => ?_, ?_⟩
  · have := (hind 3 1 (by rw [hδ, hγ] at hz; linear_combination hz)).1
    norm_num at this
  · have := (hind 1 2 (by rw [hγ] at hz; linear_combination hz)).1
    norm_num at this
  · have hsum : (t.simplyConnectedRootDatum ht).root β +
        (t.simplyConnectedRootDatum ht).root δ =
          2 • (t.simplyConnectedRootDatum ht).root γ := by
      rw [hδ, hγ]
      module
    refine lie_chevalleySystem_eq_zero ?_ fun hz => ?_
    · rw [hsum]
      exact (t.simplyConnectedRootDatum ht).nsmul_notMem_range_root (n := 2)
    · have := (hind 2 2 (by rw [hδ, hγ] at hz; linear_combination hz)).1
      norm_num at this

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- The Chevalley commutator formula for the roots `α + β` and `2α + β`, with the native
structure constants and the exact integral coefficient `N_{α,β} N_{α,α+β} / 2`. -/
theorem commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd
            (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
              (u ^ 2 * v))) := by
  obtain ⟨hil, hjk, hjl⟩ := doublyLaced_vanishing_brackets hγ hδ hαδ hβγ
  let e := t.chevalleySystem ht
  let d := t.structureConstant ht α β * t.structureConstant ht α γ / 2
  have hdiv : 2 * d = t.structureConstant ht α β * t.structureConstant ht α γ :=
    Int.mul_ediv_cancel' (two_dvd_structureConstant_mul_structureConstant hγ)
  have hiij : ⁅e α, ⁅e α, e β⁆⁆ = (2 * d) • e δ := by
    rw [lie_chevalleySystem_eq_structureConstant_zsmul hγ, lie_zsmul,
      lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul, hdiv]
  -- The same lattice is stable under the all-root Kostant form.
  have hM' : ∀ z ∈ kostantForm e (t.lieBasis ht).h, ∀ w ∈ M, ρ z w ∈ M := by
    intro z hz w hw
    refine kostantForm_apply_mem e (t.lieBasis ht).h ρ M.toIntSubmodule ?_ ?_ z hz hw
    · intro η n w hw
      rw [Associative.map_dividedPower]
      exact dividedPower_chevalleySystem_smul_mem ρ M hM hnil η n w hw
    · intro i n w hw
      exact hM _ (ringChoose_mem_kostantForm _ _ i n) w hw
  have heq (η : Fin t.numRoots) : chevalleyRootSubgroup ρ M hM hnil η A =
      kostantRootSubgroupParam e (t.lieBasis ht).h ρ M hM' η
        (isNilpotent_apply_ι_chevalleySystem ρ hnil η) A := by
    refine MonoidHom.ext fun w => Units.ext <| LinearMap.ext fun z => ?_
    rw [chevalleyRootSubgroup_val, kostantRootSubgroupParam_val_apply]
  simp_rw [heq, kostantRootSubgroupParam_apply]
  -- Normalize the stored integer algebra to match the generic Kostant relation.
  obtain ⟨R, _, _⟩ := A
  rename_i hR hA
  cases Subsingleton.elim hA (Ring.toIntAlgebra R)
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq' e (t.lieBasis ht).h ρ M hM'
      (A := R)
      (lie_chevalleySystem_eq_structureConstant_zsmul hγ) hiij hil hjk hjl
      (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil δ)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := R)).symm (Multiplicative.ofAdd u))
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := R)).symm (Multiplicative.ofAdd v))

end

end TauCeti.DynkinType
