/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.PreAdicSpace
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen
public import TauCeti.RingTheory.WittVector.Window.Localization

/-!
# Windows of `𝒴` are the affinoid spectra `Spa(B^I, B^{I,+})`

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, and let `ϖ ∈ O` be a pseudouniformiser, `0 < v(ϖ) < 1`; for instance
`O = 𝒪_F` for a perfect nonarchimedean field `F` of characteristic `p`, so that `𝕎 O = A_inf`.
Give `𝕎 O` its `(p, [ϖ])`-adic topology. For nonnegative rationals `q = a / b ≠ 0` and
`q' = a' / b'` in lowest terms, the window `W = {v ∈ 𝒴 : q ≤ κ(v) ≤ q'}` of the Fargues–Fontaine
curve is a rational subset of `Spa(𝕎 O, 𝕎 O)`, and this file identifies the pre-adic space it
carries with the affinoid pre-adic space of the interval ring `B^I`, for the radii
`ρ₁ = v(ϖ) ^ (1 / q)` and `ρ₂ = v(ϖ) ^ (1 / q')`:

```text
W ≅ Spa(B^I, B^{I,+}).
```

The Frobenius windows `U_n` and `V_n` are the windows `q = p ^ n`, `q' = c p ^ n` and
`q = c p ^ n`, `q' = p ^ (n + 1)`, with `c = (p + 1) / 2`.

* The window is the rational subset `R(T/s)` presented by `T = {[ϖ] ^ (b + b'), p ^ (a + a')}` and
  `s = p ^ a [ϖ] ^ b'` (`TauCeti.WittVector.windowNumerators`,
  `TauCeti.WittVector.windowDenominator`): over `s`, the two numerators give the fractions
  `[ϖ] ^ b / p ^ a` and `p ^ a' / [ϖ] ^ b'`, which are at most `1` exactly on the window.
  Hence the open embedding `j : Spa(𝕎 O⟨T/s⟩, A_U⁺) → Spa(𝕎 O, 𝕎 O)` induced by the rational
  localisation has image `W`.
* Wedhorn's Remark 8.8 (`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceLocIso`) identifies
  the restriction of `Spa(𝕎 O, 𝕎 O)` along `j` with `Spa(𝕎 O⟨T/s⟩, A_U⁺)`.
* The isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` of complete topological rings
  (`TauCeti.WittVector.completionLocRingEquivIntervalRing`) carries `A_U⁺` onto
  `B^{I,+}` (`TauCeti.WittVector.map_completedPlusSubring_windowNumerators`), so it is an
  isomorphism of Huber pairs and induces an isomorphism of pre-adic spaces
  (`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComapIso`). Neither step needs a
  sheaf condition.

The pair of definition of `B^I` used to form its pre-adic space is arbitrary; any one of them gives
the same space up to this isomorphism.

## Main results

* `TauCeti.FarguesFontaine.rationalSubset_windowNumerators` : the window `{q ≤ κ ≤ q'}` is the
  rational subset `R(T/s)`.
* `TauCeti.FarguesFontaine.range_spaComapLoc_windowNumerators` : the open embedding
  `j : Spa(𝕎 O⟨T/s⟩, A_U⁺) → Spa(𝕎 O, 𝕎 O)` has image the window.
* `TauCeti.FarguesFontaine.windowPreAdicSpaceIso` : the restriction of `Spa(𝕎 O, 𝕎 O)` along `j`
  is isomorphic in `𝒱^pre` to `Spa(B^I, B^{I,+})`; on points it is pullback along
  `B^I ≃+* 𝕎 O⟨T/s⟩` (`windowPreAdicSpaceIso_hom_base_apply`).

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the interval rings `B^I` and the windows.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.8.
-/

public noncomputable section

universe u

namespace TauCeti.FarguesFontaine

open scoped NNReal
open _root_.WittVector TauCeti.Huber TauCeti.Localization TauCeti.ValuationSpectrum
  TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime]

/-! ### The window as a rational subset -/

section Rational

variable {R : Type u} [CommRing R] [TopologicalSpace (WittVector p R)] {ϖ : R} {q q' : ℚ≥0}

/-- **The window `{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}` is the rational subset `R(T/s)`**, for `q ≠ 0`, where
`T = {[ϖ] ^ (b + b'), p ^ (a + a')}` and `s = p ^ a [ϖ] ^ b'` for `q = a / b` and `q' = a' / b'` in
lowest terms. Off the support of `s`, the inequalities `v([ϖ] ^ (b + b')) ≤ v(s)` and
`v(p ^ (a + a')) ≤ v(s)` are the radius bounds `v([ϖ]) ^ b ≤ v(p) ^ a` and
`v(p) ^ a' ≤ v([ϖ]) ^ b'`. -/
theorem rationalSubset_windowNumerators (hq : q ≠ 0) :
    rationalSubset (⊤ : Subring (WittVector p R)) (windowNumerators p ϖ q q')
        (windowDenominator p ϖ q q') =
      {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} := by
  ext v
  let _ := v.toValuativeRel
  have ha := NNRat.num_ne_zero.mpr hq
  -- a positive power of `x` has positive valuation exactly when `x` is off the support
  have hpos {x : WittVector p R} {k : ℕ} (hk : k ≠ 0) : 0 <ᵥ x ^ k ↔ x ∉ v.supp := by
    rw [← ValuativeRel.not_vle, ← mem_supp_iff,
      Ideal.IsPrime.pow_mem_iff_mem inferInstance k (Nat.pos_of_ne_zero hk)]
  -- `s = p ^ a [ϖ] ^ b'` has positive valuation exactly when both factors do
  have hs : 0 <ᵥ windowDenominator p ϖ q q' ↔
      0 <ᵥ (p : WittVector p R) ^ q.num ∧ 0 <ᵥ teichmuller p ϖ ^ q'.den := by
    rw [windowDenominator_def, ← not_iff_not, ValuativeRel.not_vlt, not_and_or,
      ValuativeRel.not_vlt, ValuativeRel.not_vlt, ← mem_supp_iff, ← mem_supp_iff, ← mem_supp_iff]
    exact Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance
  rw [mem_rationalSubset_iff, Set.mem_ofPred_eq, mem_spaY_iff,
    isRadiusLowerBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm,
    isRadiusUpperBound_iff_of_eq_div q'.den_ne_zero (NNRat.num_div_den q').symm,
    ValuativeRel.not_vle, hs, hpos ha, hpos q'.den_ne_zero]
  simp only [mem_windowNumerators_iff, forall_eq_or_imp, forall_eq]
  refine ⟨fun ⟨hv, ⟨h₁, h₂⟩, hp, hϖ⟩ ↦ ⟨⟨hv, hp, hϖ⟩, ?_, ?_⟩,
    fun ⟨⟨hv, hp, hϖ⟩, h₁, h₂⟩ ↦ ⟨hv, ⟨?_, ?_⟩, hp, hϖ⟩⟩
  · rwa [pow_add, windowDenominator_def,
      ValuativeRel.mul_vle_mul_iff_left ((hpos q'.den_ne_zero).mpr hϖ)] at h₁
  · rwa [pow_add, windowDenominator_def,
      ValuativeRel.mul_vle_mul_iff_right ((hpos ha).mpr hp)] at h₂
  · rwa [pow_add, windowDenominator_def,
      ValuativeRel.mul_vle_mul_iff_left ((hpos q'.den_ne_zero).mpr hϖ)]
  · rwa [pow_add, windowDenominator_def,
      ValuativeRel.mul_vle_mul_iff_right ((hpos ha).mpr hp)]

/-- **The rational localisation at the window has image the window**: for `q ≠ 0`, the open
embedding `j : Spa(𝕎 R⟨T/s⟩, A_U⁺) → Spa(𝕎 R, 𝕎 R)` induced by the structure map has image
`{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`. -/
theorem range_spaComapLoc_windowNumerators [IsTopologicalRing (WittVector p R)]
    (P : PairOfDefinition (WittVector p R)) (S : Type u) [CommRing S] [Algebra (WittVector p R) S]
    [IsLocalization.Away (windowDenominator p ϖ q q') S]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') S)
    (hq : q ≠ 0) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') S hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ S hden
    letI := P.isTopologicalRing_locUniformSpace _ _ S hden
    Set.range (spaComapLoc P ⊤ (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') S hden) =
      Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} := by
  rw [range_spaComapLoc P ⊤ le_top, ← rationalSubset_windowNumerators hq]
  exact Set.ext fun _ ↦ mem_spaBasicOpen

end Rational

/-! ### The window as an affinoid pre-adic space -/

section Chart

variable {O : Type u} [CommRing O] {ϖ : O} {q q' : ℚ≥0} {K : Type*} [Field K] [Algebra O K]
  {v : Valuation K ℝ≥0} [CharP O p] [PerfectRing O p]
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)
  [TopologicalSpace (WittVector p O)] [IsTopologicalRing (WittVector p O)]
  (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ}))
  (P : PairOfDefinition (WittVector p O))
  [IsLocalization.Away (windowDenominator p ϖ q q') (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)]
  (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q')
    (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂))

local notation "L" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

/-- **A window of `𝒴` is the affinoid pre-adic space `Spa(B^I, B^{I,+})`**: the restriction of
`Spa(𝕎 O, 𝕎 O)` along the open embedding `j : Spa(𝕎 O⟨T/s⟩, A_U⁺) → Spa(𝕎 O, 𝕎 O)`, whose image
is the window `{q ≤ κ ≤ q'}` (`range_spaComapLoc_windowNumerators`), is isomorphic in `𝒱^pre` to
the pre-adic space of the interval ring `B^I` with plus ring `B^{I,+} = (B^I)°`, for the radii
`ρ₁ ^ a = v(ϖ) ^ b`, `ρ₂ ^ a' = v(ϖ) ^ b'`, `ρ₁ ≤ ρ₂` matching the window. It is Wedhorn's
Remark 8.8 for the window followed by the isomorphism of Huber pairs
`(𝕎 O⟨T/s⟩, A_U⁺) ≅ (B^I, B^{I,+})`. Here `P'` is any pair of definition of `B^I`. The hypothesis
that `𝕎 O[1/(p [ϖ])]` is a localisation away from `s = p ^ a [ϖ] ^ b'` holds when `q ≠ 0`
(`TauCeti.WittVector.isLocalization_away_windowDenominator`). -/
def windowPreAdicSpaceIso (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂)
    (P' : PairOfDefinition (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    (spaPreAdicSpace P hI).restrict
        (isOpenEmbedding_spaComapLocHom P ⊤ le_top (windowNumerators p ϖ q q')
          (windowDenominator p ϖ q q') L hden) ≅
      presentationLimitPreAdicSpace P' (powerBoundedSubring (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂))
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha) P'.le_powerBoundedSubring :=
  letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
  letI := P.isTopologicalRing_locUniformSpace _ _ L hden
  have hplus := map_completedPlusSubring_windowNumerators hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂
  have hpb : ∀ ⦃a⦄, a ∈ (⊤ : Subring (WittVector p O)) → IsPowerBounded a :=
    fun _ _ ↦ haveI := hI.isLinearTopology
      isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  presentationLimitPreAdicSpaceLocIso P ⊤ (windowNumerators p ϖ q q')
      (windowDenominator p ϖ q q') L hden hpb le_top (isOpen_span_windowNumerators hI) ≪≫
    presentationLimitPreAdicSpaceComapIso (P := P') (Aplus := powerBoundedSubring _)
      (P' := P.completionLocalization _ _ L hden) (Bplus := P.completedPlusSubring ⊤ _ _ L hden)
      ((completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).symm :
        IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ →+* _)
      (continuous_completionLocRingEquivIntervalRing_symm hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂)
      (fun b hb ↦ by
        rw [← hplus] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        rwa [RingHom.coe_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply])
      (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ : _ →+* _)
      (continuous_completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂)
      (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).apply_symm_apply
      (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).symm_apply_apply
      (fun a ha ↦ hplus ▸ Subring.mem_map.mpr ⟨a, ha, rfl⟩)
      (fun _ ha ↦ mem_powerBoundedSubring.mp ha)
      (PairOfDefinition.isPowerBounded_of_mem_completedPlusSubring P ⊤ hpb _ _ L hden)
      P'.le_powerBoundedSubring
      (PairOfDefinition.completionLocalization_ringOfDefinition_le_completedPlusSubring P ⊤ le_top
        _ _ L hden)

/-- **On points, `windowPreAdicSpaceIso` is pullback along `B^I ≃+* 𝕎 O⟨T/s⟩`**: a point `x` of
`Spa(𝕎 O⟨T/s⟩, A_U⁺)`, the source of `j`, goes to the valuation `x ∘ e⁻¹` of `B^I`, where
`e : 𝕎 O⟨T/s⟩ ≃+* B^I` is `completionLocRingEquivIntervalRing`. -/
theorem windowPreAdicSpaceIso_hom_base_apply (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂)
    (P' : PairOfDefinition (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    ∀ x : spa (P.completedPlusSubring ⊤ (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L
      hden),
    ((windowPreAdicSpaceIso hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ P').hom.base x).val =
      comap ((completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).symm :
        IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ →+* _) x.val := by
  intro x
  let _ := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  have _ := P.isUniformAddGroup_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have _ := P.isTopologicalRing_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  rw [windowPreAdicSpaceIso, _root_.CategoryTheory.Iso.trans_hom, PreAdicSpace.comp_base,
    presentationLimitPreAdicSpaceLocIso_hom_base]
  -- the carrier of the restriction is `spa A_U⁺` only after unfolding `spaPreAdicSpace`, so the
  -- remaining composite is matched up to that unfolding
  erw [presentationLimitPreAdicSpaceComapIso_hom_base, _root_.CategoryTheory.Category.id_comp]
  exact spaComap_val ..

end Chart

end TauCeti.FarguesFontaine
