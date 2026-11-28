/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Tame
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Archimedean
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Weights and tame parts of norm-one idele characters for CM fields

For a CM field `E` with maximal real subfield `E⁺`, an automorphic character `μ` of the norm-one
ideles `U(1)(𝔸_{E⁺})` has weight `e : InfinitePlace E → ℤ` and tame part `ψ` (a family of
characters of the residue-field units `𝔽_wˣ`, trivial for almost all finite places `w`) if on
every norm-one idele `x` with integral finite components, `μ x` equals the archimedean weight
character `normOneWeightCharacter e x` times `∏ᶠ w, ψ w (u_w mod w)`.

This file records the calculus of weights and tame parts (products, integer powers, and
compatibility with `NormOneTameCharacter`) and derives the weights and tame parts of the
untwisted lift characters `μ♭ * (υ ^ (-Δ : ℤ) * χ) ^ j` and their twists by a
`NormOneTameCharacter`.

## Main results

* `TauCeti.GlobalNumberFields.HasNormOneWeight`: the weight-and-tame-part predicate on norm-one
  idele characters.
* `TauCeti.GlobalNumberFields.HasNormOneWeight.mul` and `.zpow`: weights add and tame parts
  multiply under products and integer powers.
* `TauCeti.GlobalNumberFields.NormOneTameCharacter.hasNormOneWeight`: every weight-zero tame
  character `ξ` has weight `0` and tame part `ξ.residueCharacterAt`.
* `TauCeti.GlobalNumberFields.HasNormOneWeight.liftChar`: the twisted lift character
  `μ♭ * (υ ^ (-Δ : ℤ) * χ) ^ j * ξ` has weight `-(κ + j • Δ)` and tame part
  `ω ^ j * ξ.residueCharacterAt`.

## Provenance

Adapted from `New.Data.untwistedLiftChar_hasWeight`, `New.Data.hasWeight_liftChar`, and
`New.Data.chainChar` in `grh/src/New/Reduction/Data/LevelAndTwists.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField
open IsDedekindDomain.FiniteAdeleRing (integralUnits)

namespace TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "E⁺" => maximalRealSubfield E
local notation "U" => MonoidHom.ker (ContinuousMonoidHom.toMonoidHom (ideleNormMap E⁺ E))

/-- A continuous character `μ` of the CM norm-one ideles has weight `e : InfinitePlace E → ℤ`
and tame part `ψ` if `ψ w = 1` for all but finitely many finite places `w` and `μ` factors on
integral norm-one ideles as `normOneWeightCharacter e` times the finite product of `ψ w`. -/
def HasNormOneWeight (μ : U →ₜ* Circle) (e : InfinitePlace E → ℤ)
    (ψ : (w : HeightOneSpectrum (𝓞 E)) →
      (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle) : Prop :=
  ({w : HeightOneSpectrum (𝓞 E) | ψ w ≠ 1}).Finite ∧
    ∀ (x : U) (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E),
      μ x = normOneWeightCharacter e x *
        ∏ᶠ w : HeightOneSpectrum (𝓞 E),
          ψ w (w.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)

/-- Multiplying two characters adds their weights and multiplies their tame parts. -/
theorem HasNormOneWeight.mul {μ₁ μ₂ : U →ₜ* Circle} {e₁ e₂ : InfinitePlace E → ℤ}
    {ψ₁ ψ₂ : (w : HeightOneSpectrum (𝓞 E)) →
      (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    (h₁ : HasNormOneWeight μ₁ e₁ ψ₁) (h₂ : HasNormOneWeight μ₂ e₂ ψ₂) :
    HasNormOneWeight (μ₁ * μ₂) (e₁ + e₂) (ψ₁ * ψ₂) := by
  refine ⟨(h₁.left.union h₂.left).subset fun w hw ↦ ?_, fun x hx ↦ ?_⟩
  · by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hnot
    exact hw (by simp [Pi.mul_apply, hnot.left, hnot.right])
  · have hf₁ : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) ↦
        ψ₁ w (w.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)).Finite :=
      h₁.left.subset fun w hw h1 ↦ hw (by simp [h1])
    have hf₂ : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) ↦
        ψ₂ w (w.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)).Finite :=
      h₂.left.subset fun w hw h1 ↦ hw (by simp [h1])
    rw [ContinuousMonoidHom.mul_apply, h₁.right x hx, h₂.right x hx,
      normOneWeightCharacter_add, ContinuousMonoidHom.mul_apply, mul_mul_mul_comm,
      ← finprod_mul_distrib hf₁ hf₂]
    rfl

/-- Raising a character to an integer power scales its weight and raises its tame part to the
same power. -/
theorem HasNormOneWeight.zpow {μ : U →ₜ* Circle} {e : InfinitePlace E → ℤ}
    {ψ : (w : HeightOneSpectrum (𝓞 E)) →
      (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    (h : HasNormOneWeight μ e ψ) (n : ℤ) :
    HasNormOneWeight (μ ^ n) (n • e) (fun w ↦ ψ w ^ n) := by
  refine ⟨h.left.subset fun w hw ↦ ?_, fun x hx ↦ ?_⟩
  · by_contra hnot
    simp only [Set.mem_ofPred_eq, not_not] at hnot
    exact hw (by simp [hnot])
  · have hwt : normOneWeightCharacter (n • e) x = normOneWeightCharacter e x ^ n := by
      simp only [normOneWeightCharacter_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [mul_comm, zpow_mul]
    have hf : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) ↦
        ψ w (w.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)).Finite :=
      h.left.subset fun w hw h1 ↦ hw (by simp [h1])
    rw [ContinuousMonoidHom.zpow_apply, h.right x hx, mul_zpow, hwt]
    congr 1
    exact map_finprod (zpowGroupHom n) hf

/-- Every weight-zero tame character `ξ` at modulus `Q` satisfies `HasNormOneWeight` with
weight `0` and tame part `ξ.residueCharacterAt`. -/
theorem NormOneTameCharacter.hasNormOneWeight {Q : Finset (HeightOneSpectrum (𝓞 E))}
    (ξ : NormOneTameCharacter E⁺ E Q) :
    HasNormOneWeight ξ.toContinuousMonoidHom 0 ξ.residueCharacterAt := by
  refine ⟨Q.finite_toSet.subset fun w hw ↦ ?_, fun x hx ↦ ?_⟩
  · by_contra hnot
    exact hw (ξ.residueCharacterAt_of_notMem hnot)
  · rw [normOneWeightCharacter_zero, show (1 : U →ₜ* Circle) x = 1 from rfl, one_mul,
      ξ.apply_integral x hx, finprod_eq_prod_of_mulSupport_subset _ (s := Q) (fun w hw ↦ by
        by_contra hnot
        exact hw (by simp [ξ.residueCharacterAt_of_notMem hnot]))]
    rw [← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [ξ.residueCharacterAt_of_mem w.property]

/-- **Weights and tame parts of twisted lift characters.** Given `μ♭` of weight `-κ₀` and trivial
tame part, `υ` of weight `1` and trivial tame part, `χ` of weight `0` and tame part `ω`, and a
weight-zero tame character `ξ`, the lift character `μ♭ * (υ ^ (-Δ) * χ) ^ j * ξ` has weight
`fun v ↦ -(κ₀ v + j * Δ)` and tame part `fun w ↦ ω w ^ (j : ℤ) * ξ.residueCharacterAt w`. -/
theorem HasNormOneWeight.liftChar {μ₀ υ χ : U →ₜ* Circle} {κ₀ : InfinitePlace E → ℤ}
    {Δ : ℤ} {ω : (w : HeightOneSpectrum (𝓞 E)) →
      (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (ξ : NormOneTameCharacter E⁺ E Q) (j : ℕ)
    (hμ₀ : HasNormOneWeight μ₀ (-κ₀) 1)
    (hυ : HasNormOneWeight υ (fun _ ↦ 1) 1)
    (hχ : HasNormOneWeight χ 0 ω) :
    HasNormOneWeight (μ₀ * (υ ^ (-Δ) * χ) ^ j * ξ.toContinuousMonoidHom)
      (fun v ↦ -(κ₀ v + (j : ℤ) * Δ)) (fun w ↦ ω w ^ (j : ℤ) * ξ.residueCharacterAt w) := by
  have hstep : HasNormOneWeight (υ ^ (-Δ) * χ) (fun _ ↦ -Δ) ω := by
    convert (hυ.zpow (-Δ)).mul hχ using 1
    · funext v; simp
    · funext w; simp
  have huntw : HasNormOneWeight (μ₀ * (υ ^ (-Δ) * χ) ^ j)
      (fun v ↦ -(κ₀ v + (j : ℤ) * Δ)) (fun w ↦ ω w ^ (j : ℤ)) := by
    have hpow : HasNormOneWeight ((υ ^ (-Δ) * χ) ^ j)
        ((j : ℤ) • fun _ ↦ -Δ) (fun w ↦ ω w ^ (j : ℤ)) := by
      simpa only [zpow_natCast] using hstep.zpow (j : ℤ)
    convert hμ₀.mul hpow using 1
    · funext v; simp; ring
    · funext w; simp
  convert huntw.mul ξ.hasNormOneWeight using 1
  funext v; simp

end TauCeti.GlobalNumberFields
