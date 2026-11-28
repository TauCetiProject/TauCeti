/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Tame
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Archimedean

/-!
# Weight and tame part of a theta-lift character

An automorphic character of the CM norm-one ideles has prescribed weight and tame part if
its restriction to ideles with integral finite components is the product of the archimedean
weight character and the prescribed residue characters. Multiplication adds weights and
multiplies residue characters, even when the factors have different tame moduli.

The application is the calculation for the characters of a theta-lift chain: the character
in the `j`-th position has weight `-κ₀ - jΔ`, and twisting changes only the tame part. The
normalization is that of `New.Data.hasWeight_liftChar` and `New.Data.chainChar` in
`New/Reduction/Data/LevelAndTwists.lean` of lsernau/grh-lean, revision `72fead1`.
-/

public section

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open IsDedekindDomain.FiniteAdeleRing (integralUnits)

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "U" => MonoidHom.ker
  (ContinuousMonoidHom.toMonoidHom (ideleNormMap (maximalRealSubfield E) E))
local notation "W" => InfinitePlace E → ℤ
local notation "P" => HeightOneSpectrum (𝓞 E)

namespace ContinuousMonoidHom

/-- `χ` is automorphic with archimedean weight `e` and residue characters `ψ` supported on `Q`.
The prescribed product specifies its restriction to the norm-one ideles that are integral
at every finite place; it does not prescribe the character away from that subgroup. -/
@[mk_iff]
structure HasWeightAndTamePart (χ : U →ₜ* Circle) (e : W) (Q : Finset P)
    (ψ : (w : P) → (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle) : Prop where
  /-- The character is trivial on rational norm-one points. -/
  apply_principal (x : U) : x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E → χ x = 1
  /-- The residue characters are trivial outside `Q`. -/
  residueCharacter_eq_one_of_notMem (w : P) : w ∉ Q → ψ w = 1
  /-- The specified product formula on ideles with integral finite components. -/
  apply_integral (x : U)
      (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E) :
    χ x = normOneWeightCharacter e x * ∏ w ∈ Q, ψ w
      (w.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)

namespace HasWeightAndTamePart

/-- Extra places may be included in the modulus without changing the residue characters. -/
theorem mono {χ : U →ₜ* Circle} {e : W} {Q Q' : Finset P}
    {ψ : (w : P) → (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    (h : HasWeightAndTamePart (E := E) χ e Q ψ) (hQ : Q ⊆ Q') :
    HasWeightAndTamePart (E := E) χ e Q' ψ := by
  obtain ⟨hprincipal, hout, hint⟩ := h
  refine ⟨hprincipal, fun w hw ↦ hout w (fun hm ↦ hw (hQ hm)), fun x hx ↦ ?_⟩
  rw [hint x hx, Finset.prod_subset hQ fun w _ hw ↦ by simp [hout w hw]]

/-- The product has the sum of the weights and the pointwise product of the tame parts,
supported on the union of the two moduli. -/
theorem mul [DecidableEq P] {χ χ' : U →ₜ* Circle} {e e' : W} {Q Q' : Finset P}
    {ψ ψ' : (w : P) → (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    (h : HasWeightAndTamePart (E := E) χ e Q ψ)
    (h' : HasWeightAndTamePart (E := E) χ' e' Q' ψ') :
    HasWeightAndTamePart (E := E) (χ * χ') (e + e') (Q ∪ Q') (ψ * ψ') := by
  obtain ⟨hprincipal, hout, hint⟩ := h.mono (Finset.subset_union_left (s₂ := Q'))
  obtain ⟨hprincipal', hout', hint'⟩ := h'.mono (Finset.subset_union_right (s₁ := Q))
  refine ⟨fun x hx ↦ by simp [hprincipal x hx, hprincipal' x hx],
    fun w hw ↦ by simp [hout w hw, hout' w hw], fun x hx ↦ ?_⟩
  rw [ContinuousMonoidHom.mul_apply, hint x hx, hint' x hx, normOneWeightCharacter_add,
    ContinuousMonoidHom.mul_apply]
  simp only [Pi.mul_apply, MonoidHom.mul_apply, Finset.prod_mul_distrib]
  ac_rfl

/-- Integer powers scale the weight and raise each residue character to the same power. -/
theorem zpow {χ : U →ₜ* Circle} {e : W} {Q : Finset P}
    {ψ : (w : P) → (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    (h : HasWeightAndTamePart (E := E) χ e Q ψ) (n : ℤ) :
    HasWeightAndTamePart (E := E) (χ ^ n) (n • e) Q (ψ ^ n) := by
  obtain ⟨hprincipal, hout, hint⟩ := h
  refine ⟨fun x hx ↦ by simp [hprincipal x hx], fun w hw ↦ by simp [hout w hw], fun x hx ↦ ?_⟩
  rw [ContinuousMonoidHom.zpow_apply, hint x hx, normOneWeightCharacter_zsmul, mul_zpow,
    ContinuousMonoidHom.zpow_apply, ← Finset.prod_zpow]
  simp only [Pi.pow_apply, MonoidHom.zpow_apply]

/-- Natural powers scale the weight and raise each residue character to the same power. -/
theorem pow {χ : U →ₜ* Circle} {e : W} {Q : Finset P}
    {ψ : (w : P) → (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ →* Circle}
    (h : HasWeightAndTamePart (E := E) χ e Q ψ) (n : ℕ) :
    HasWeightAndTamePart (E := E) (χ ^ n) (n • e) Q (ψ ^ n) := by
  simpa only [zpow_natCast, natCast_zsmul] using h.zpow (n : ℤ)

end HasWeightAndTamePart

end ContinuousMonoidHom

namespace TauCeti.GlobalNumberFields

/-- A weight-zero tame datum gives a character of weight zero with exactly its prescribed
residue characters, extended trivially outside the modulus. -/
theorem NormOneTameCharacter.hasWeightAndTamePart {Q : Finset P}
    (ξ : NormOneTameCharacter (maximalRealSubfield E) E Q) :
    ContinuousMonoidHom.HasWeightAndTamePart ξ.toContinuousMonoidHom 0 Q ξ.residueCharacterAt := by
  classical
  refine ⟨ξ.apply_principal, fun _ ↦ ξ.residueCharacterAt_of_notMem, fun x hx ↦ ?_⟩
  rw [ξ.apply_integral x hx, normOneWeightCharacter_zero]
  simp only [ContinuousMonoidHom.coe_one, Pi.one_apply, one_mul]
  rw [Finset.prod_subtype Q (fun _ ↦ Iff.rfl)]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [ξ.residueCharacterAt_of_mem w.property]

/-- In position `j` of a theta-lift chain, multiply the weight-`-κ₀` character by the `j`-th power
of `υ ^ (-Δ) * χ`, where `υ` has pure weight one and `χ` has weight zero. An additional power `n`
of the twist `ξ` changes only the tame part. Taking `n = 1` gives the individual twisted lift;
taking `n = j` gives the character used in the chain. -/
theorem hasWeightAndTamePart_thetaLiftChain [DecidableEq P] {S Q : Finset P}
    {μ υ : U →ₜ* Circle} {κ₀ : W}
    (hμ : μ.HasWeightAndTamePart (-κ₀) ∅ 1)
    (hυ : υ.HasWeightAndTamePart 1 ∅ 1)
    (χ : NormOneTameCharacter (maximalRealSubfield E) E S)
    (ξ : NormOneTameCharacter (maximalRealSubfield E) E Q) (Δ : ℤ) (j n : ℕ) :
    ContinuousMonoidHom.HasWeightAndTamePart
      (μ * (υ ^ (-Δ) * χ.toContinuousMonoidHom) ^ j * ξ.toContinuousMonoidHom ^ n)
      (fun w ↦ -(κ₀ w + (j : ℤ) * Δ)) (S ∪ Q)
      (χ.residueCharacterAt ^ j * ξ.residueCharacterAt ^ n) := by
  have h := (hμ.mul (((hυ.zpow (-Δ)).mul χ.hasWeightAndTamePart).pow j)).mul
    (ξ.hasWeightAndTamePart.pow n)
  have hw : -κ₀ + j • (-Δ • (1 : W) + 0) + n • 0 = fun w ↦ -(κ₀ w + (j : ℤ) * Δ) := by
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.one_apply, Pi.zero_apply]
    simp
    ring
  simpa only [hw, Finset.empty_union, one_zpow, one_mul] using h

end TauCeti.GlobalNumberFields
