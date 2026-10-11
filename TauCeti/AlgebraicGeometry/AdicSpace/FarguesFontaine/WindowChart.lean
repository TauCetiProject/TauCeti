/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Window
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen
public import TauCeti.RingTheory.WittVector.Window.Localization

/-!
# Window charts of the Fargues–Fontaine curve

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, let `ϖ ∈ O` be a pseudouniformiser, and give `𝕎 O` the `(p, [ϖ])`-adic
topology; for `O = 𝒪_F` this is `A_inf`. For nonnegative rationals `q = a / b ≠ 0` and
`q' = a' / b'` in lowest terms, the window `{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}` is the rational subset

```text
R(T/s),    T = {[ϖ] ^ (b + b'), p ^ (a + a')},    s = p ^ a [ϖ] ^ b'
```

of `Spa(𝕎 O, 𝕎 O)` (`TauCeti.FarguesFontaine.rationalSubset_windowNumerators`); in particular the
Frobenius windows `U_n` and `V_n` are of this form. This file proves that the window, with the
pre-adic structure it inherits from `Spa(𝕎 O, 𝕎 O)`, is isomorphic in `𝒱^pre` to the affinoid
pre-adic space `Spa(B^I, B^{I,+})` of the interval ring, when the radii `ρ₁ ≤ ρ₂` of `B^I` match
the window: `ρ₁ ^ a = v(ϖ) ^ b` and `ρ₂ ^ a' = v(ϖ) ^ b'`.

The isomorphism is the composite of two existing ones. Restricting `Spa(𝕎 O, 𝕎 O)` along the open
embedding `j : Spa(𝕎 O⟨T/s⟩, A_U⁺) → Spa(𝕎 O, 𝕎 O)`, whose image is `R(T/s)`, gives
`Spa(𝕎 O⟨T/s⟩, A_U⁺)` (`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceLocIso`). The
homeomorphic ring isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` carries `A_U⁺` onto `B^{I,+}`
(`TauCeti.WittVector.map_completedPlusSubring_completionLocRingEquivIntervalRing`), so it is an
isomorphism of Huber pairs and induces an isomorphism of pre-adic spaces
(`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComapIso`).

## Main definitions

* `TauCeti.FarguesFontaine.presentationLimitPreAdicSpaceWindowIso` : the isomorphism in `𝒱^pre`
  between the restriction of `Spa(𝕎 O, 𝕎 O)` along `j` and `Spa(B^I, B^{I,+})`.

## Main results

* `TauCeti.FarguesFontaine.rationalSubset_windowNumerators` : for `q ≠ 0`, the rational subset
  `R(T/s)` of the window presentation is `{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`.
* `TauCeti.FarguesFontaine.windowU_eq_rationalSubset` and its `V` analogue : the windows `U_n`
  and `V_n` are the rational subsets of their window presentations.
* `TauCeti.FarguesFontaine.range_spaComapLoc_windowNumerators` : the image of `j` is the window.
* `TauCeti.FarguesFontaine.presentationLimitPreAdicSpaceWindowIso_hom_base_val` : on points, the
  isomorphism is `v ↦ v ∘ e⁻¹` for the ring isomorphism `e : 𝕎 O⟨T/s⟩ ≃+* B^I`.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the interval rings `B^I` and the windows.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.8.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.FarguesFontaine

open _root_.CategoryTheory _root_.WittVector TauCeti.Huber TauCeti.Huber.PairOfDefinition
  TauCeti.ValuationSpectrum TauCeti.WittVector

universe u

variable {p : ℕ} [Fact p.Prime] {O : Type u} [CommRing O] {ϖ : O} {q q' : ℚ≥0}

local notation "𝕎" => _root_.WittVector p

/-! ### The window as a rational subset -/

section Rational

variable [TopologicalSpace (_root_.WittVector p O)]

/-- **The rational subset of the window presentation is the window**: for `q = a / b ≠ 0` and
`q' = a' / b'` in lowest terms, the rational subset `R(T/s)` of `Spa(𝕎 O, 𝕎 O)` with numerators
`T = {[ϖ] ^ (b + b'), p ^ (a + a')}` and denominator `s = p ^ a [ϖ] ^ b'` is
`{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`. -/
theorem rationalSubset_windowNumerators (hq : q ≠ 0) :
    rationalSubset (⊤ : Subring (𝕎 O)) (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') =
      {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} := by
  ext v
  simp only [mem_rationalSubset_iff, mem_windowNumerators_iff, forall_eq_or_imp, forall_eq,
    windowDenominator_def, Set.mem_ofPred_eq, mem_spaY_iff,
    isRadiusLowerBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm,
    isRadiusUpperBound_iff_of_eq_div q'.den_ne_zero (NNRat.num_div_den q').symm, mem_supp_iff,
    ← valuation_le_iff, map_pow, map_mul, map_zero, le_zero_iff, pow_add]
  -- write `x = v(p)` and `y = v([ϖ])`; the denominator `x ^ a y ^ b'` is nonzero exactly when
  -- `x` and `y` are, and then it cancels from both numerator conditions
  set x := v.valuation (p : 𝕎 O)
  set y := v.valuation (teichmuller p ϖ)
  have ha : q.num ≠ 0 := NNRat.num_ne_zero.mpr hq
  have hb : q'.den ≠ 0 := q'.den_ne_zero
  have hs : ¬x ^ q.num * y ^ q'.den = 0 ↔ ¬x = 0 ∧ ¬y = 0 := by
    simp [ha, hb]
  rw [hs]
  constructor
  · rintro ⟨hspa, ⟨h₁, h₂⟩, hx, hy⟩
    exact ⟨⟨hspa, hx, hy⟩,
      (mul_le_mul_iff_of_pos_right (pow_pos (zero_lt_iff.mpr hy) _)).mp h₁,
      (mul_le_mul_iff_of_pos_left (pow_pos (zero_lt_iff.mpr hx) _)).mp h₂⟩
  · rintro ⟨⟨hspa, hx, hy⟩, h₁, h₂⟩
    exact ⟨hspa, ⟨(mul_le_mul_iff_of_pos_right (pow_pos (zero_lt_iff.mpr hy) _)).mpr h₁,
      (mul_le_mul_iff_of_pos_left (pow_pos (zero_lt_iff.mpr hx) _)).mpr h₂⟩, hx, hy⟩

variable (p ϖ) in
/-- **`U_n` is the rational subset of its window presentation**, with `q = p ^ n` and
`q' = c p ^ n` for the breakpoint `c = (p + 1) / 2`. -/
theorem windowU_eq_rationalSubset (n : ℤ) :
    windowU p ϖ n = rationalSubset (⊤ : Subring (𝕎 O)) (windowNumerators p ϖ ((p : ℚ≥0) ^ n)
      ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n))
        (windowDenominator p ϖ ((p : ℚ≥0) ^ n) ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n)) := by
  rw [rationalSubset_windowNumerators
    (zpow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))]
  exact Set.ext fun v ↦ mem_windowU_iff n v

variable (p ϖ) in
/-- **`V_n` is the rational subset of its window presentation**, with `q = c p ^ n` and
`q' = p ^ (n + 1)` for the breakpoint `c = (p + 1) / 2`. -/
theorem windowV_eq_rationalSubset (n : ℤ) :
    windowV p ϖ n = rationalSubset (⊤ : Subring (𝕎 O))
      (windowNumerators p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) ((p : ℚ≥0) ^ (n + 1)))
        (windowDenominator p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) ((p : ℚ≥0) ^ (n + 1))) := by
  rw [rationalSubset_windowNumerators (mul_ne_zero (by positivity)
    (zpow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)))]
  exact Set.ext fun v ↦ mem_windowV_iff n v

/-- **The image of `j : Spa(𝕎 O⟨T/s⟩, A_U⁺) → Spa(𝕎 O, 𝕎 O)` is the window**: for the window
presentation with `q ≠ 0`, the range of `j` is the set of points of `Spa(𝕎 O, 𝕎 O)` lying in
`{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`. -/
theorem range_spaComapLoc_windowNumerators [IsTopologicalRing (𝕎 O)]
    (P : PairOfDefinition (𝕎 O)) (S : Type u) [CommRing S] [Algebra (𝕎 O) S]
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

/-! ### The window chart -/

section Chart

variable {K : Type*} [Field K] [Algebra O K] {v : Valuation K ℝ≥0} [CharP O p] [PerfectRing O p]
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "L" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

/-- **The window chart**: the window `{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`, with its pre-adic structure
restricted from `Spa(𝕎 O, 𝕎 O)`, is isomorphic in `𝒱^pre` to `Spa(B^I, B^{I,+})`. Here `𝕎 O`
carries the `(p, [ϖ])`-adic topology and any pair of definition `P`, `q = a / b` and `q' = a' / b'`
are in lowest terms, the radii of `B^I` satisfy `ρ₁ ^ a = v(ϖ) ^ b`, `ρ₂ ^ a' = v(ϖ) ^ b'` and
`ρ₁ ≤ ρ₂`, and `P'` is any pair of definition of `B^I`. The restriction is along the open embedding
`j : Spa(𝕎 O⟨T/s⟩, A_U⁺) → Spa(𝕎 O, 𝕎 O)` of the window presentation, whose image is the window
(`range_spaComapLoc_windowNumerators`). No sheaf condition is assumed. -/
def presentationLimitPreAdicSpaceWindowIso [TopologicalSpace (𝕎 O)] [IsTopologicalRing (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (P : PairOfDefinition (𝕎 O))
    [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂)
    (P' : PairOfDefinition (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    (presentationLimitPreAdicSpace P ⊤
        (fun _ _ ↦ haveI := hI.isLinearTopology
          isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) le_top).restrict
        (isOpenEmbedding_spaComapLocHom P ⊤ le_top _ _ L hden) ≅
      presentationLimitPreAdicSpace P' (powerBoundedSubring _)
        (fun _ hb ↦ mem_powerBoundedSubring.mp hb) P'.le_powerBoundedSubring :=
  letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  letI := P.isUniformAddGroup_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  letI := P.isTopologicalRing_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  let e := completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂
  have hmap := map_completedPlusSubring_completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P
    hden h₁ h₂ h₁₂
  presentationLimitPreAdicSpaceLocIso P ⊤ _ _ L hden _ le_top (isOpen_span_windowNumerators hI) ≪≫
    presentationLimitPreAdicSpaceComapIso (P := P') (P' := completionLocalization P _ _ L hden)
      (e.symm : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ →+* _)
      (continuous_completionLocRingEquivIntervalRing_symm hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂)
      (fun b hb ↦ by
        rw [← hmap] at hb
        obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hb
        simpa only [e, RingHom.coe_coe, RingEquiv.symm_apply_apply] using ha)
      (e : _ →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
      (continuous_completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂)
      e.apply_symm_apply e.symm_apply_apply
      (fun a ha ↦ hmap ▸ Subring.mem_map.mpr ⟨a, ha, rfl⟩) _ _ _ _

/-- On points, the window chart `presentationLimitPreAdicSpaceWindowIso` is `v ↦ v ∘ e⁻¹`, the map
of adic spectra induced by the inverse of the ring isomorphism `e : 𝕎 O⟨T/s⟩ ≃+* B^I`. -/
@[simp]
theorem presentationLimitPreAdicSpaceWindowIso_hom_base_val [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂)
    (P' : PairOfDefinition (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    ∀ y, ((presentationLimitPreAdicSpaceWindowIso hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂
        P').hom.base y).val =
      comap ((completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).symm :
        IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ →+* _) y.val := by
  let _ := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  have _ := P.isUniformAddGroup_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have _ := P.isTopologicalRing_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  intro y
  simp only [presentationLimitPreAdicSpaceWindowIso, Iso.trans_hom, PreAdicSpace.comp_base,
    presentationLimitPreAdicSpaceLocIso_hom_base]
  -- the identity on points of `presentationLimitPreAdicSpaceLocIso` lives on the underlying
  -- `TopCat` object of the restricted pre-adic space, which `Category.id_comp` matches only up to
  -- unfolding that coercion, hence `erw`
  erw [Category.id_comp, presentationLimitPreAdicSpaceComapIso_hom_base]
  exact spaComap_val _ _ _ _ _ _

end Chart

end TauCeti.FarguesFontaine
