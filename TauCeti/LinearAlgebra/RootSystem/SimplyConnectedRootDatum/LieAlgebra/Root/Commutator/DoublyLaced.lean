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
import TauCeti.LinearAlgebra.RootSystem.Finite.DoubleChain

/-!
# The doubly-laced Chevalley commutator formula

For the pinned root vectors on a Kostant-stable lattice, this file proves the Chevalley
commutator formula when the root string consists of `β`, `α + β`, `2α + β` and there is no
root `α + 2β`. The coefficients are the native integer structure constants:
`c₁₁ = N_{α,β}` and `c₂₁ = N_{α,β} N_{α,α+β} / 2`. The division is exact in the integers;
no factorial is inverted in the value ring. The result therefore holds over every commutative
ring, including characteristic two, and for any Kostant-stable lattice with nilpotent simple
root operators.

The multiplication identity specializes
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_lie_eq'`
to the pinned Chevalley system, discharging its bracket hypotheses from the integral root datum.
The all-root Kostant form preserves the same lattice, and its parametrized root subgroups agree
with the native all-root maps. The commutator formula follows by cancellation and commutation
of the correction factors with the initial root subgroup.

Outside type `G₂`, the double chain implies that `3α + β` and `α + 2β` are not roots,
so `commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq` applies. The non-root
exclusions are proved in `TauCeti.LinearAlgebra.RootSystem.Finite.DoubleChain`, using the
Cartan-integer bound outside `G₂` from
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational`.
Alternatively, the root-string conditions `chainBotCoeff α β = 0` and
`chainTopCoeff α β = 2` supply the same non-root hypotheses, without excluding `G₂`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, with the convention
  `⁅x, y⁆ = x y x⁻¹ y⁻¹`.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra RootPairing
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
  obtain ⟨h₁, h₂⟩ :=
    root_initial_add_last_notMem_range_root_and_ne_zero_of_double_chain
      (t.simplyConnectedRootDatum ht) hγ hδ
  exact ⟨lie_chevalleySystem_eq_zero_of_add_eq hδ hαδ,
    lie_chevalleySystem_eq_zero_of_add_eq (hγ.trans (add_comm _ _)) hβγ,
    lie_chevalleySystem_eq_zero h₁ h₂⟩

private theorem doublyLaced_iterated_bracket {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ) :
    ⁅t.chevalleySystem ht α, ⁅t.chevalleySystem ht α, t.chevalleySystem ht β⁆⁆ =
      (2 * (t.structureConstant ht α β * t.structureConstant ht α γ / 2)) •
        t.chevalleySystem ht δ := by
  rw [lie_chevalleySystem_eq_structureConstant_zsmul hγ, lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul,
    Int.mul_ediv_cancel' (two_dvd_structureConstant_mul_structureConstant hγ)]

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- Reordering root-subgroup elements with sum roots `α + β` and `2α + β`, when the
further sums `3α + β` and `α + 2β` are not roots, uses the integral Chevalley coefficients. -/
theorem chevalleyRootSubgroup_mul_of_add_eq_of_add_eq
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
    chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
            (u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) := by
  obtain ⟨hil, hjk, _⟩ := doublyLaced_vanishing_brackets hγ hδ hαδ hβγ
  have hM' := kostantForm_chevalleySystem_smul_mem ρ M hM hnil
  simp_rw [chevalleyRootSubgroup_eq_kostantRootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    kostantRootSubgroupPoints_mul_of_lie_lie_eq' (t.chevalleySystem ht) (t.lieBasis ht).h ρ M hM'
      (A := A)
      (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
      (doublyLaced_iterated_bracket hγ hδ) hil hjk
      (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil δ)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (.ofAdd u))
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (.ofAdd v))

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
  obtain ⟨_, hjk, hjl⟩ := doublyLaced_vanishing_brackets hγ hδ hαδ hβγ
  have hprod := chevalleyRootSubgroup_mul_of_add_eq_of_add_eq ρ M hM hnil hγ hδ hαδ hβγ A u v
  have hcomm := (commute_chevalleyRootSubgroup_of_lie_eq_zero ρ M hM hnil hjk A v
    ((t.structureConstant ht α β : A) * (u * v))).mul_right
      (commute_chevalleyRootSubgroup_of_lie_eq_zero ρ M hM hnil hjl A v
        (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) * (u ^ 2 * v)))
  rw [commutatorElement_def, hprod, mul_inv_cancel_right,
    mul_assoc (chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v)), hcomm.eq, mul_inv_cancel_right]

/-- Reorder two root-subgroup elements along a double string. The `α`-string through `β`
starts at `β` and has top coefficient two. The correction coefficients are computed in `ℤ`. -/
theorem chevalleyRootSubgroup_mul_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (htop : (t.simplyConnectedRootDatum ht).chainTopCoeff α β = 2)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
            (u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) := by
  let := t.isReduced_simplyConnectedRootDatum ht
  exact chevalleyRootSubgroup_mul_of_add_eq_of_add_eq ρ M hM hnil hγ hδ
    (root_step_add_last_notMem_range_root_of_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ htop.le)
    (root_initial_add_middle_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
      (t.simplyConnectedRootDatum ht) hγ hbot htop) A u v

/-- The Chevalley element-commutator formula when the `α`-string through `β` starts at `β`
and has top coefficient two. No restriction on the characteristic of the value ring is needed. -/
theorem commutatorElement_chevalleyRootSubgroup_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (htop : (t.simplyConnectedRootDatum ht).chainTopCoeff α β = 2)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
      chevalleyRootSubgroup ρ M hM hnil δ A
        (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
          (u ^ 2 * v))) := by
  let := t.isReduced_simplyConnectedRootDatum ht
  exact commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq ρ M hM hnil hγ hδ
    (root_step_add_last_notMem_range_root_of_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ htop.le)
    (root_initial_add_middle_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
      (t.simplyConnectedRootDatum ht) hγ hbot htop) A u v

/-- Outside `G₂`, the double chain itself supplies the non-root hypotheses of the
root-subgroup reordering formula. -/
theorem chevalleyRootSubgroup_mul_of_ne_G2_of_double_chain (h : t ≠ .G2)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
            (u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) := by
  let := t.isReduced_simplyConnectedRootDatum ht
  exact chevalleyRootSubgroup_mul_of_add_eq_of_add_eq ρ M hM hnil hγ hδ
    (root_step_add_last_notMem_range_root_of_pairingIn_mem_zero_one_two_of_double_chain
      (t.simplyConnectedRootDatum ht) (pairingIn_mem_zero_one_two_of_ne_G2 ht h) hγ hδ)
    (root_initial_add_middle_notMem_range_root_of_pairingIn_mem_zero_one_two_of_double_chain
      (t.simplyConnectedRootDatum ht) (pairingIn_mem_zero_one_two_of_ne_G2 ht h) hγ hδ) A u v

/-- Outside `G₂`, the double chain implies that `3α + β` and `α + 2β` are not roots,
so `commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq` applies over every
commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_ne_G2_of_double_chain (h : t ≠ .G2)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
      chevalleyRootSubgroup ρ M hM hnil δ A
        (.ofAdd (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
          (u ^ 2 * v))) := by
  let := t.isReduced_simplyConnectedRootDatum ht
  exact commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq ρ M hM hnil hγ hδ
    (root_step_add_last_notMem_range_root_of_pairingIn_mem_zero_one_two_of_double_chain
      (t.simplyConnectedRootDatum ht) (pairingIn_mem_zero_one_two_of_ne_G2 ht h) hγ hδ)
    (root_initial_add_middle_notMem_range_root_of_pairingIn_mem_zero_one_two_of_double_chain
      (t.simplyConnectedRootDatum ht) (pairingIn_mem_zero_one_two_of_ne_G2 ht h) hγ hδ) A u v

end

end TauCeti.DynkinType
