/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.ContinuousHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.ZMod
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# First continuous cohomology of the p-adic integers

Evaluation at `1` identifies the continuous additive homomorphisms from `ℤ_[p]` to
`ZMod (p ^ k)` with `ZMod (p ^ k)`: the character with value `a` at `1` is
`x ↦ PadicInt.toZModPow k x * a`. For trivial coefficients this computes first continuous
cohomology, as a `ZMod (p ^ k)`-module. The exponent `k` may be zero.

Density of the ordinary integers gives uniqueness; continuity of the truncation map gives
existence. This contrasts with discrete integer coefficients: compactness of `ℤ_[p]` and
torsion-freeness of `ℤ` imply that every continuous additive homomorphism is zero, hence
first cohomology vanishes. The final examples use the existing compact-group vanishing theorem.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §2: first cohomology with trivial coefficients
  is the group of continuous homomorphisms.
-/

public section

namespace TauCeti

open ContCohomology

variable {p : ℕ} [Fact p.Prime] (k : ℕ)
  [DistribMulAction (Multiplicative ℤ_[p]) (ZMod (p ^ k))]
  [ContinuousSMul (Multiplicative ℤ_[p]) (ZMod (p ^ k))]
  (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : ZMod (p ^ k)), g • a = a)

/-- With trivial coefficients, first continuous cohomology of `ℤ_[p]` modulo `p ^ k`
is the coefficient ring, by evaluation of a character at the additive generator `1`. -/
noncomputable def padicIntH1ZModPowEquiv :
    H1 (Multiplicative ℤ_[p]) (ZMod (p ^ k)) ≃ₗ[ZMod (p ^ k)] ZMod (p ^ k) :=
  (h1EquivContinuousZModHom htriv).trans (PadicInt.continuousZModDualEquiv k)

/-- The cohomology equivalence evaluates the continuous character associated with a class
at the additive generator `1`. -/
@[simp] theorem padicIntH1ZModPowEquiv_apply (c : H1 (Multiplicative ℤ_[p]) (ZMod (p ^ k))) :
    padicIntH1ZModPowEquiv k htriv c =
      Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv c).toMul
        (Multiplicative.ofAdd (1 : ℤ_[p]))) := by
  simp [padicIntH1ZModPowEquiv]

/-- The class of a continuous one-cocycle maps to its value at the additive generator `1`. -/
theorem padicIntH1ZModPowEquiv_apply_mk (c : Z1 (Multiplicative ℤ_[p]) (ZMod (p ^ k))) :
    padicIntH1ZModPowEquiv k htriv (c : H1 (Multiplicative ℤ_[p]) (ZMod (p ^ k))) =
      (c : Multiplicative ℤ_[p] → ZMod (p ^ k)) (Multiplicative.ofAdd (1 : ℤ_[p])) := by
  simp [Z1EquivOfSmulEqSelf_apply]

/-- The class with parameter `a` has character `x ↦ (x mod p ^ k) * a`. -/
-- Pre-simplification preserves the exponent presentation before normalizing the arguments.
@[simp↓]
theorem padicIntH1ZModPowEquiv_symm_character (a : ZMod (p ^ k)) (x : ℤ_[p]) :
    Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv
      ((padicIntH1ZModPowEquiv k htriv).symm a)).toMul (Multiplicative.ofAdd x)) =
      PadicInt.toZModPow k x * a := by
  simp [padicIntH1ZModPowEquiv]

end TauCeti

namespace TauCeti

open ContCohomology

/-- Modulo `9`, the class with value `5` at the additive generator is nonzero and its
character takes the value `1` at the p-adic integer `2`. -/
example [Fact (Nat.Prime 3)]
    [DistribMulAction (Multiplicative ℤ_[3]) (ZMod (3 ^ 2))]
    [ContinuousSMul (Multiplicative ℤ_[3]) (ZMod (3 ^ 2))]
    (htriv : ∀ (g : Multiplicative ℤ_[3]) (a : ZMod (3 ^ 2)), g • a = a) :
    ∃ c : H1 (Multiplicative ℤ_[3]) (ZMod (3 ^ 2)), c ≠ 0 ∧
      padicIntH1ZModPowEquiv 2 htriv c = 5 ∧
      Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv c).toMul
        (Multiplicative.ofAdd (2 : ℤ_[3]))) = 1 := by
  let e := padicIntH1ZModPowEquiv 2 htriv
  refine ⟨e.symm 5, ?_, e.apply_symm_apply 5, ?_⟩
  · intro h
    have : (5 : ZMod (3 ^ 2)) = 0 := by
      rw [← e.apply_symm_apply 5, h, map_zero]
    exact (by decide : (5 : ZMod (3 ^ 2)) ≠ 0) this
  · rw [padicIntH1ZModPowEquiv_symm_character]
    rw [map_ofNat]
    decide

end TauCeti

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- Continuous integer-valued characters of the p-adic integers vanish. -/
example (φ : ℤ_[p] →ₜ+ ℤ) : φ = 0 :=
  φ.eq_zero_of_isAddTorsionFree

/-- First continuous cohomology with trivial discrete integer coefficients vanishes. -/
example [DistribMulAction (Multiplicative ℤ_[p]) ℤ]
    [ContinuousSMul (Multiplicative ℤ_[p]) ℤ]
    (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : ℤ), g • a = a) :
    Subsingleton (TauCeti.ContCohomology.H1 (Multiplicative ℤ_[p]) ℤ) :=
  TauCeti.ContCohomology.subsingleton_H1_of_isAddTorsionFree htriv

end PadicInt
