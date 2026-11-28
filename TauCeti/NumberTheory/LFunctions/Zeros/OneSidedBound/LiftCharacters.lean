/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Tame
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Archimedean

/-!
# Characters of the lifts in a theta chain

Starting with the character of weight `-(κ + g)`, the splitting character of weight one,
and the weight-zero level character, form the character of lift `j`. The splitting character
lowers the weight by `2 * j * g`, while the level character contributes the `j`-th power of its
residue characters. Twisting does not change the weight. The evaluation formula uses the
pointwise product of the powered residue characters over the union of their moduli.

The normalization is that of `New.Data.untwistedLiftChar` and `New.Data.chainChar`, in
`grh/src/New/Reduction/Data/LevelAndTwists.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField
open IsDedekindDomain.FiniteAdeleRing (integralUnits)
open TauCeti.GlobalNumberFields

namespace TauCeti.OneSidedBound

variable {E : Type*} [Field E] [NumberField E]

local notation "E⁺" => maximalRealSubfield E
local notation "U" => MonoidHom.ker (ContinuousMonoidHom.toMonoidHom (ideleNormMap E⁺ E))

/-- At lift `j`, multiply the initial character by `j` copies of the level character and of the
splitting character raised to minus twice the half-gap. -/
noncomputable def untwistedLiftCharacter (g j : ℕ) (μ υ : U →ₜ* Circle)
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (χ : NormOneTameCharacter E⁺ E Q) : U →ₜ* Circle :=
  μ * (υ ^ (-(2 * (g : ℤ))) * χ.toContinuousMonoidHom) ^ j

/-- Evaluation of the untwisted character in terms of the three input characters. -/
theorem untwistedLiftCharacter_apply (g j : ℕ) (μ υ : U →ₜ* Circle)
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (χ : NormOneTameCharacter E⁺ E Q) (x : U) :
    untwistedLiftCharacter g j μ υ χ x =
      μ x * ((υ x) ^ (-(2 * (g : ℤ))) * χ.toContinuousMonoidHom x) ^ j := by
  simp [untwistedLiftCharacter, ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply,
    ContinuousMonoidHom.zpow_apply]

/-- At index zero the lift-character formula recovers the initial character. -/
@[simp] theorem untwistedLiftCharacter_zero (g : ℕ) (μ υ : U →ₜ* Circle)
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (χ : NormOneTameCharacter E⁺ E Q) :
    untwistedLiftCharacter g 0 μ υ χ = μ := by
  simp [untwistedLiftCharacter]

/-- The lift character is trivial at a principal norm-one idele where the initial and
splitting characters are both trivial. -/
theorem untwistedLiftCharacter_apply_principal (g j : ℕ) {μ υ : U →ₜ* Circle}
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (χ : NormOneTameCharacter E⁺ E Q)
    (x : U) (hx : x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E) (hμ : μ x = 1) (hυ : υ x = 1) :
    untwistedLiftCharacter g j μ υ χ x = 1 := by
  rw [untwistedLiftCharacter_apply, hμ, hυ, χ.apply_principal x hx]
  simp

/-- The tame part of lift `j` twisted by the `n`-th power of the twist. The two residue
characters are extended by one outside their respective moduli. -/
noncomputable def liftTamePart (j n : ℕ) {Q R : Finset (HeightOneSpectrum (𝓞 E))}
    (χ : NormOneTameCharacter E⁺ E Q) (ξ : NormOneTameCharacter E⁺ E R)
    (w : HeightOneSpectrum (𝓞 E)) :
    (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle :=
  χ.residueCharacterAt w ^ j * ξ.residueCharacterAt w ^ n

/-- At each place the tame part is the product of the two powered local characters. -/
theorem liftTamePart_def (j n : ℕ) {Q R : Finset (HeightOneSpectrum (𝓞 E))}
    (χ : NormOneTameCharacter E⁺ E Q) (ξ : NormOneTameCharacter E⁺ E R)
    (w : HeightOneSpectrum (𝓞 E)) :
    liftTamePart j n χ ξ w = χ.residueCharacterAt w ^ j * ξ.residueCharacterAt w ^ n := (rfl)

/-- Away from both moduli the tame part is trivial. -/
@[simp] theorem liftTamePart_of_notMem (j n : ℕ) {Q R : Finset (HeightOneSpectrum (𝓞 E))}
    (χ : NormOneTameCharacter E⁺ E Q) (ξ : NormOneTameCharacter E⁺ E R)
    {w : HeightOneSpectrum (𝓞 E)} (hQ : w ∉ Q) (hR : w ∉ R) : liftTamePart j n χ ξ w = 1 := by
  rw [liftTamePart_def, χ.residueCharacterAt_of_notMem hQ, ξ.residueCharacterAt_of_notMem hR]
  simp

variable [IsCMField E]

/-- On an idele with integral finite part the untwisted lift has weight
`-(κ + (2 * j + 1) * g)` and tame part the `j`-th power of the level character's tame part.
The premises give the initial and splitting character values on that idele, with no tame factor. -/
theorem untwistedLiftCharacter_apply_integral {μ υ : U →ₜ* Circle}
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (χ : NormOneTameCharacter E⁺ E Q)
    (κ : InfinitePlace E → ℕ) (g j : ℕ) (x : U)
    (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E)
    (hμ : μ x = normOneWeightCharacter (fun v ↦ -((κ v : ℤ) + g)) x)
    (hυ : υ x = normOneWeightCharacter (fun _ ↦ 1) x) :
    untwistedLiftCharacter g j μ υ χ x =
      normOneWeightCharacter (fun v ↦ -((κ v : ℤ) + (2 * (j : ℤ) + 1) * g)) x *
        ∏ w : Q, (χ.residueCharacter w
          (w.val.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)) ^ j := by
  rw [untwistedLiftCharacter_apply, hμ, hυ, χ.apply_integral x hx, mul_pow, ← mul_assoc,
    ← Finset.prod_pow]
  congr 1
  simp only [normOneWeightCharacter_apply, ← Finset.prod_zpow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, zpow_one]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [← zpow_natCast _ j, ← zpow_mul, ← zpow_add]
  congr 1
  ring

open scoped Classical in
/-- Multiplying lift `j` by the `n`-th power of a weight-zero tame twist preserves its weight.
Its tame part is `liftTamePart j n χ ξ` on the union of the two moduli. In particular `n = 1`
is a single twisted lift and `n = j` is the twist used at step `j` of the chain. -/
theorem untwistedLiftCharacter_mul_twist_apply_integral {μ υ : U →ₜ* Circle}
    {Q R : Finset (HeightOneSpectrum (𝓞 E))} (χ : NormOneTameCharacter E⁺ E Q)
    (ξ : NormOneTameCharacter E⁺ E R) (κ : InfinitePlace E → ℕ) (g j n : ℕ) (x : U)
    (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E)
    (hμ : μ x = normOneWeightCharacter (fun v ↦ -((κ v : ℤ) + g)) x)
    (hυ : υ x = normOneWeightCharacter (fun _ ↦ 1) x) :
    (untwistedLiftCharacter g j μ υ χ * (ξ ^ n).toContinuousMonoidHom) x =
      normOneWeightCharacter (fun v ↦ -((κ v : ℤ) + (2 * (j : ℤ) + 1) * g)) x *
        ∏ w ∈ Q ∪ R, liftTamePart j n χ ξ w
          (w.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩) := by
  rw [ContinuousMonoidHom.mul_apply, untwistedLiftCharacter_apply_integral χ κ g j x hx hμ hυ,
    (ξ ^ n).apply_integral x hx, mul_assoc]
  congr 1
  simp only [liftTamePart_def, NormOneTameCharacter.residueCharacter_pow, MonoidHom.mul_apply,
    MonoidHom.pow_apply, Finset.prod_mul_distrib]
  congr 1
  · rw [← Finset.prod_subset Finset.subset_union_left (fun w _ hw ↦ by
      simp [χ.residueCharacterAt_of_notMem hw])]
    rw [← Finset.prod_coe_sort Q]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [χ.residueCharacterAt_of_mem w.property]
  · rw [← Finset.prod_subset Finset.subset_union_right (fun w _ hw ↦ by
      simp [ξ.residueCharacterAt_of_notMem hw])]
    rw [← Finset.prod_coe_sort R]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [ξ.residueCharacterAt_of_mem w.property]

end TauCeti.OneSidedBound
