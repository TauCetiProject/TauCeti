/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.ContinuousHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.ZMod
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.TypeTags
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# First continuous cohomology of the p-adic integers

Evaluation at `1` identifies the continuous additive homomorphisms from `ℤ_[p]` to
`ZMod (p ^ k)` with `ZMod (p ^ k)`: the character with value `a` at `1` is
`x ↦ PadicInt.toZModPow k x * a`. For trivial coefficients this computes first continuous
cohomology, as a `ZMod (p ^ k)`-module. The exponent `k` may be zero. Density of the ordinary
integers gives uniqueness; continuity of the truncation map gives existence.

More generally, for trivial coefficients in a Hausdorff topological `ℤ_[p]`-module `A`, such
as `ℤ_[p]` or `ℚ_[p]`, evaluation at `1` identifies `H¹(ℤ_[p], A)` with `A`
(`TauCeti.padicIntH1Equiv`), `ℤ_[p]`-linearly (`TauCeti.padicIntH1LinearEquiv`). Here density of
the ordinary integers again gives uniqueness, and continuity of scalar multiplication `x ↦ x • a`
gives existence.

These contrast with discrete integer coefficients: compactness of `ℤ_[p]` and
torsion-freeness of `ℤ` imply that every continuous additive homomorphism is zero, hence
first cohomology vanishes. The final examples use the existing compact-group vanishing theorem.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §2: first cohomology with trivial coefficients
  is the group of continuous homomorphisms.
-/

public section

namespace TauCeti

open ContCohomology

section Module

variable {p : ℕ} [Fact p.Prime] {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [ContinuousSMul ℤ_[p] A]
  [DistribMulAction (Multiplicative ℤ_[p]) A] [ContinuousSMul (Multiplicative ℤ_[p]) A]
  (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : A), g • a = a)

include htriv

/-- With trivial coefficients in a Hausdorff topological `ℤ_[p]`-module `A`, first continuous
cohomology of `ℤ_[p]` is `A`, by evaluation of a character at the additive generator `1`. -/
noncomputable def padicIntH1Equiv : H1 (Multiplicative ℤ_[p]) A ≃+ A :=
  (H1EquivOfSmulEqSelf htriv).trans
    (ContinuousAddMonoidHom.toMultiplicativeAddEquiv.symm.trans
      (PadicInt.continuousAddHomEquiv A))

/-- The equivalence evaluates the continuous character associated with a class at the additive
generator `1`. -/
@[simp] theorem padicIntH1Equiv_apply (c : H1 (Multiplicative ℤ_[p]) A) :
    padicIntH1Equiv htriv c =
      Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv c).toMul
        (Multiplicative.ofAdd (1 : ℤ_[p]))) := by
  simp [padicIntH1Equiv]

/-- The class of a continuous one-cocycle maps to its value at the additive generator `1`. -/
theorem padicIntH1Equiv_apply_mk (c : Z1 (Multiplicative ℤ_[p]) A) :
    padicIntH1Equiv htriv (c : H1 (Multiplicative ℤ_[p]) A) =
      (c : Multiplicative ℤ_[p] → A) (Multiplicative.ofAdd (1 : ℤ_[p])) := by
  simp

/-- The class with value `a` at `1` has character `x ↦ x • a`. -/
@[simp] theorem padicIntH1Equiv_symm_character (a : A) (x : ℤ_[p]) :
    Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv
      ((padicIntH1Equiv htriv).symm a)).toMul (Multiplicative.ofAdd x)) = x • a := by
  simp [padicIntH1Equiv]

variable [SMulCommClass (Multiplicative ℤ_[p]) ℤ_[p] A]

/-- The equivalence `padicIntH1Equiv` is `ℤ_[p]`-linear for the module structure of
`H¹(ℤ_[p], A)` induced by the coefficients. -/
noncomputable def padicIntH1LinearEquiv : H1 (Multiplicative ℤ_[p]) A ≃ₗ[ℤ_[p]] A :=
  (padicIntH1Equiv htriv).toLinearEquiv fun r c ↦ by
    induction c using QuotientAddGroup.induction_on with
    | H z => simp [padicIntH1Equiv_apply_mk, -padicIntH1Equiv_apply, Pi.smul_apply]

/-- The linear equivalence has the same underlying map as `padicIntH1Equiv`. -/
@[simp] theorem padicIntH1LinearEquiv_apply (c : H1 (Multiplicative ℤ_[p]) A) :
    padicIntH1LinearEquiv htriv c = padicIntH1Equiv htriv c := (rfl)

/-- The inverse of the linear equivalence is the inverse of `padicIntH1Equiv`. -/
@[simp] theorem padicIntH1LinearEquiv_symm_apply (a : A) :
    (padicIntH1LinearEquiv htriv).symm a = (padicIntH1Equiv htriv).symm a := (rfl)

end Module

section ZModPow

variable {p : ℕ} [Fact p.Prime] (k : ℕ)
  [DistribMulAction (Multiplicative ℤ_[p]) (ZMod (p ^ k))]
  [ContinuousSMul (Multiplicative ℤ_[p]) (ZMod (p ^ k))]
  (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : ZMod (p ^ k)), g • a = a)

/-- With trivial coefficients, first continuous cohomology of `ℤ_[p]` modulo `p ^ k`
is the coefficient ring, by evaluation of a character at the additive generator `1`. This is
`padicIntH1Equiv` for `ZMod (p ^ k)`, a `ℤ_[p]`-module through the truncation map. -/
noncomputable def padicIntH1ZModPowEquiv :
    H1 (Multiplicative ℤ_[p]) (ZMod (p ^ k)) ≃ₗ[ZMod (p ^ k)] ZMod (p ^ k) :=
  letI := (PadicInt.toZModPow (p := p) k).toModule
  haveI : ContinuousSMul ℤ_[p] (ZMod (p ^ k)) :=
    MulAction.continuousSMul_compHom (PadicInt.continuous_toZModPow k)
  (padicIntH1Equiv htriv).toLinearEquiv (ZMod.map_smul _)

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
  simp

/-- The class with parameter `a` has character `x ↦ (x mod p ^ k) * a`. -/
-- Pre-simplification preserves the exponent presentation before normalizing the arguments.
@[simp↓]
theorem padicIntH1ZModPowEquiv_symm_character (a : ZMod (p ^ k)) (x : ℤ_[p]) :
    Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv
      ((padicIntH1ZModPowEquiv k htriv).symm a)).toMul (Multiplicative.ofAdd x)) =
      PadicInt.toZModPow k x * a := by
  simp [padicIntH1ZModPowEquiv, RingHom.toModule_smul]

end ZModPow

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
