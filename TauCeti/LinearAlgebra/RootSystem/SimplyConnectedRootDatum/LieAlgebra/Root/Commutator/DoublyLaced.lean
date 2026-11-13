/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic
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

The multiplication and commutator identities specialize the two-factor formulas in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic`,
discharging their non-root hypotheses from the integral root datum.

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

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

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
    (root_add_root_notMem_range_root_of_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ htop.le)
    (root_add_root_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
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
    (root_add_root_notMem_range_root_of_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ htop.le)
    (root_add_root_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
      (t.simplyConnectedRootDatum ht) hγ hbot htop) A u v

/-- Outside `G₂`, the double chain itself supplies the non-root hypotheses of the
root-subgroup reordering formula. -/
theorem chevalleyRootSubgroup_mul_of_ne_G2_of_add_eq_of_add_eq (h : t ≠ .G2)
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
    (root_add_root_notMem_range_root_left_of_root_eq_add_of_root_eq_add
      (t.simplyConnectedRootDatum ht)
      (pairingIn_simplyConnectedRootDatum_mem_zero_one_two_of_ne_G2 ht h) hγ hδ)
    (root_add_root_notMem_range_root_right_of_root_eq_add_of_root_eq_add
      (t.simplyConnectedRootDatum ht)
      (pairingIn_simplyConnectedRootDatum_mem_zero_one_two_of_ne_G2 ht h) hγ hδ) A u v

/-- Outside `G₂`, the double chain implies that `3α + β` and `α + 2β` are not roots,
so `commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq` applies over every
commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_ne_G2_of_add_eq_of_add_eq (h : t ≠ .G2)
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
    (root_add_root_notMem_range_root_left_of_root_eq_add_of_root_eq_add
      (t.simplyConnectedRootDatum ht)
      (pairingIn_simplyConnectedRootDatum_mem_zero_one_two_of_ne_G2 ht h) hγ hδ)
    (root_add_root_notMem_range_root_right_of_root_eq_add_of_root_eq_add
      (t.simplyConnectedRootDatum ht)
      (pairingIn_simplyConnectedRootDatum_mem_zero_one_two_of_ne_G2 ht h) hγ hδ) A u v

end

end TauCeti.DynkinType
