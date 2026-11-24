/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2
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
so `commutatorElement_chevalleyRootSubgroup_of_root_eq_add_of_root_eq_add` applies. The non-root
exclusions are proved in `TauCeti.LinearAlgebra.RootSystem.Finite.DoubleChain`, using Mathlib's
root-string length bound outside `G₂` and the rational root system from
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2`.
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
  exact chevalleyRootSubgroup_mul_of_root_eq_add_of_root_eq_add ρ M hM hnil hγ hδ
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
  exact commutatorElement_chevalleyRootSubgroup_of_root_eq_add_of_root_eq_add
    ρ M hM hnil hγ hδ
    (root_add_root_notMem_range_root_of_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ htop.le)
    (root_add_root_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
      (t.simplyConnectedRootDatum ht) hγ hbot htop) A u v

/-- Outside `G₂`, reorder `x_α(u) x_β(v)` as `x_β(v) x_γ(N_{α,β} u v)` times
`x_δ((N_{α,β} N_{α,γ} / 2) u² v) x_α(u)` along `γ = α + β`, `δ = α + γ`.
The coefficients are integral and the value ring is any commutative ring. -/
theorem chevalleyRootSubgroup_mul_of_ne_G2_of_root_eq_add_of_root_eq_add (h : t ≠ .G2)
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
  let := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) h
  have hlen : (t.simplyConnectedRootDatum ht).chainBotCoeff α β +
      (t.simplyConnectedRootDatum ht).chainTopCoeff α β ≤ 2 := by
    simpa using (t.rationalRootSystem ht).chainBotCoeff_add_chainTopCoeff_le_two α β
  exact chevalleyRootSubgroup_mul_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    ρ M hM hnil hγ hδ
    (chainBotCoeff_eq_zero_of_chainBotCoeff_add_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ hlen)
    ((t.simplyConnectedRootDatum ht).chainTopCoeff_eq_two_of_chainTopCoeff_le_two
      hγ hδ (by omega)) A u v

/-- Outside `G₂`, the double chain `γ = α + β`, `δ = α + γ` has commutator formula
`⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ((N_{α,β} N_{α,γ} / 2) u² v)`.
The coefficients are integral and the formula holds over every commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_ne_G2_of_root_eq_add_of_root_eq_add (h : t ≠ .G2)
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
  let := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) h
  have hlen : (t.simplyConnectedRootDatum ht).chainBotCoeff α β +
      (t.simplyConnectedRootDatum ht).chainTopCoeff α β ≤ 2 := by
    simpa using (t.rationalRootSystem ht).chainBotCoeff_add_chainTopCoeff_le_two α β
  exact commutatorElement_chevalleyRootSubgroup_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    ρ M hM hnil hγ hδ
    (chainBotCoeff_eq_zero_of_chainBotCoeff_add_chainTopCoeff_le_two
      (t.simplyConnectedRootDatum ht) hγ hδ hlen)
    ((t.simplyConnectedRootDatum ht).chainTopCoeff_eq_two_of_chainTopCoeff_le_two
      hγ hδ (by omega)) A u v

end

end TauCeti.DynkinType
