/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.IntervalChart
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Plus

import TauCeti.Analysis.SpecialFunctions.Pow.NNRat

/-!
# Images of windows in `𝒳` are the affinoid spectra `Spa(B^I, B^{I,+})`

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, with a pseudouniformiser `ϖ`, `0 < v(ϖ) < 1`; for `O = 𝒪_F` this makes
`𝕎 O = A_inf`. Give `𝕎 O` its `(p, [ϖ])`-adic topology and suppose that the structure presheaf
`𝒪_𝒴` of `𝒴 = D(p) ∩ D([ϖ]) ⊆ Spa(𝕎 O, 𝕎 O)` is a sheaf, so that the Frobenius orbit space
`𝒳 = 𝒴 / φ^ℤ` is a pre-adic space (`TauCeti.FarguesFontaine.spaXPreAdicSpace`). This file shows that
the image in `𝒳` of a window

```text
W = {v ∈ 𝒴 : q ≤ κ(v) ≤ q'},        0 < q ≤ q',
```

meeting none of its nontrivial Frobenius translates, such as the windows `U_n` and `V_n`, is an
open affinoid subspace of `𝒳`, isomorphic in `𝒱^pre` to `Spa(B^I, B^{I,+})` for the interval ring
`B^I` of the radii `ρ₁ = v(ϖ) ^ (1 / q)` and `ρ₂ = v(ϖ) ^ (1 / q')`.

Two identifications already describe the pieces. `TauCeti.FarguesFontaine.windowPreAdicSpaceIso`
identifies the window, as a restriction of `Spa(𝕎 O, 𝕎 O)`, with `Spa(B^I, B^{I,+})`, and
`TauCeti.FarguesFontaine.isOpenImmersion_ofRestrict_comp_quotientPreAdicHom` makes `V → 𝒳` an open
immersion for every wandering open `V ⊆ 𝒴`. The window restriction of `Spa(𝕎 O, 𝕎 O)` and the
restriction of `𝒴` to `W` are open subspaces of `Spa(𝕎 O, 𝕎 O)` with the same image, hence
isomorphic, and composing gives the chart `Spa(B^I, B^{I,+}) ⟶ 𝒳` with image `q(W)`.

Since the images of `U_0` and `V_0` cover `𝒳`
(`TauCeti.FarguesFontaine.image_windowU_zero_union_image_windowV_zero`), `𝒳` is covered by two open
affinoid subspaces, each isomorphic to the adic spectrum of an interval ring.

## Main definitions

* `TauCeti.FarguesFontaine.spaXWindowChart` : the chart `Spa(B^I, B^{I,+}) ⟶ 𝒳` of a window.

## Main results

* `TauCeti.FarguesFontaine.isOpenImmersion_spaXWindowChart` : for a wandering window the chart is
  an open immersion.
* `TauCeti.FarguesFontaine.range_spaXWindowChart_base` : the image of the chart is `q(W)`.
* `TauCeti.FarguesFontaine.comap_presentationLimitPlusSubring_spaXWindowChart` : over an open of
  `q(W)`, the chart identifies the integral sections `𝒪_𝒳⁺` with the plus subrings of
  `Spa(B^I, B^{I,+})`.
* `TauCeti.FarguesFontaine.quotientMap_image_window_mem_affinoidOpens` : the image `q(W)` of a
  wandering window is an open affinoid subspace of `𝒳`.
* `TauCeti.FarguesFontaine.quotientMap_image_windowU_mem_affinoidOpens` and
  `TauCeti.FarguesFontaine.quotientMap_image_windowV_mem_affinoidOpens` : the same for the
  Frobenius windows `U_n` and `V_n`.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the interval rings `B^I`, the windows and the charts of the Fargues–Fontaine curve.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public noncomputable section

universe u

namespace TauCeti.FarguesFontaine

open scoped NNReal
open _root_.WittVector TauCeti.Huber TauCeti.ValuationSpectrum TauCeti.WittVector
open _root_.CategoryTheory _root_.TopologicalSpace Topology

variable {p : ℕ} [Fact p.Prime]

section Chart

variable {O : Type u} [CommRing O] {ϖ : O} {q q' : ℚ≥0} {K : Type*} [Field K] [Algebra O K]
  {v : Valuation K ℝ≥0}
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)
  [TopologicalSpace (WittVector p O)] [IsTopologicalRing (WittVector p O)]
  (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ}))
  (P : PairOfDefinition (WittVector p O))
  [IsLocalization.Away (windowDenominator p ϖ q q') (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)]
  (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q')
    (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂))

local notation "L" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

include hϖ' in
/-- The radius equation `ρ₁ ^ a = v(ϖ) ^ b` for `q = a / b` forces `q ≠ 0`, as `v(ϖ) ≠ 1`. -/
private theorem ne_zero_of_pow_num_eq (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den) :
    q ≠ 0 := by
  rintro rfl
  simp only [NNRat.num_zero, pow_zero, NNRat.den_zero, pow_one] at h₁
  exact hϖ'.ne h₁.symm

include hv hϖ hϖ' hρ₁ hρ₂ in
/-- The window restriction of `Spa(𝕎 O, 𝕎 O)` lands in the window `{q ≤ κ ≤ q'}`. -/
private theorem val_ofRestrict_window_base_mem (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    ∀ x, (((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaComapLocHom P ⊤ le_top
        (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden)).base x).val ∈
      {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} := by
  intro x
  have hx := range_spaComapLoc_windowNumerators P _ hden (ne_zero_of_pow_num_eq hϖ' h₁) ▸
    Set.mem_range_self (f := spaComapLoc P ⊤ (windowNumerators p ϖ q q')
      (windowDenominator p ϖ q q') L hden) x
  rwa [← congrFun (coe_spaComapLocHom P ⊤ (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden) x] at hx

include hv hϖ hϖ' hρ₁ hρ₂ in
/-- The window restriction of `Spa(𝕎 O, 𝕎 O)` maps into `𝒴`. -/
private theorem range_ofRestrict_window_subset (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    Set.range ((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaComapLocHom P ⊤ le_top
        (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden)).base ⊆
      Set.range ((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ)).base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨_, (val_ofRestrict_window_base_mem hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ x).1⟩,
    Subtype.ext (spaYInclusion_apply_val ϖ _)⟩

include hv hϖ hϖ' hρ₁ hρ₂ in
/-- Every point of `𝒴` in the window `{q ≤ κ ≤ q'}` is in the image of the window restriction of
`Spa(𝕎 O, 𝕎 O)`. -/
private theorem exists_ofRestrict_window_eq (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (y : spaY p ϖ)
    (hy : y.val ∈ {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v}) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    ∃ x, ((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaComapLocHom P ⊤ le_top
        (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden)).base x =
      ((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ)).base y := by
  have hq := ne_zero_of_pow_num_eq hϖ' h₁
  have hy' : spaYInclusion p ϖ y ∈ Set.range (spaComapLoc P ⊤ (windowNumerators p ϖ q q')
      (windowDenominator p ϖ q q') L hden) := by
    rw [range_spaComapLoc_windowNumerators P _ hden hq, Set.mem_preimage, spaYInclusion_apply_val]
    exact hy
  obtain ⟨x, hx⟩ := hy'
  refine ⟨x, ?_⟩
  exact (congrFun (coe_spaComapLocHom P ⊤ (windowNumerators p ϖ q q') (windowDenominator p ϖ q q')
    L hden) x).trans hx

variable [CharP O p] [PerfectRing O p] (hY : (spaYPresheaf P ϖ).IsSheaf)
  (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
  (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂)
  (P' : PairOfDefinition (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂))

/-- **The chart of `𝒳` on a window.** For the window `W = {v ∈ 𝒴 : q ≤ κ(v) ≤ q'}` and radii
`ρ₁ ^ a = v(ϖ) ^ b`, `ρ₂ ^ a' = v(ϖ) ^ b'` with `ρ₁ ≤ ρ₂`, where `q = a / b` and `q' = a' / b'` in
lowest terms, this is the morphism of pre-adic spaces `Spa(B^I, B^{I,+}) ⟶ 𝒳` obtained by
identifying `Spa(B^I, B^{I,+})` with `W` (`windowPreAdicSpaceIso`) and composing the inclusion
`W → 𝒴` with the projection `q : 𝒴 → 𝒳`. It needs `𝒪_𝒴` to be a sheaf, as `𝒳` does. When `W`
wanders it is an open immersion (`isOpenImmersion_spaXWindowChart`) with image `q(W)`
(`range_spaXWindowChart_base`). Here `P'` is any pair of definition of `B^I`. -/
def spaXWindowChart :
    presentationLimitPreAdicSpace P' (powerBoundedSubring (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂))
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha) P'.le_powerBoundedSubring ⟶
      spaXPreAdicSpace P hI hY :=
  letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
  letI := P.isTopologicalRing_locUniformSpace _ _ L hden
  haveI := PreAdicSpace.IsOpenImmersion.ofRestrict (spaPreAdicSpace P hI)
    (isOpenEmbedding_spaYInclusion p ϖ)
  (windowPreAdicSpaceIso hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ P').inv ≫
    PreAdicSpace.IsOpenImmersion.lift
      ((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ))
      ((spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaComapLocHom P ⊤ le_top
        (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden))
      (range_ofRestrict_window_subset hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁) ≫
    quotientPreAdicHom P hI hY

/-- **The window chart of `𝒳` is an open immersion** when the window `W = {q ≤ κ ≤ q'}` wanders,
that is, meets none of its nontrivial integer Frobenius translates, as the Frobenius windows `U_n`
and `V_n` do. It is then an isomorphism of `Spa(B^I, B^{I,+})` onto the restriction of `𝒳` to the
open image `q(W)` (`PreAdicSpace.IsOpenImmersion.isoRestrict`). -/
theorem isOpenImmersion_spaXWindowChart
    (hW : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} :
          Set (spaY p ϖ)))
      (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v})) :
    PreAdicSpace.IsOpenImmersion (spaXWindowChart hv hϖ hϖ' hρ₁ hρ₂ hI P hden hY h₁ h₂ h₁₂ P') := by
  have hq := ne_zero_of_pow_num_eq hϖ' h₁
  let _ := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  have _ := P.isUniformAddGroup_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have _ := P.isTopologicalRing_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have := PreAdicSpace.IsOpenImmersion.ofRestrict (spaPreAdicSpace P hI)
    (isOpenEmbedding_spaYInclusion p ϖ)
  -- the window, as an open of `𝒴`
  let W : Opens (spaY p ϖ) :=
    ⟨_, isOpen_val_preimage_setOf_isRadiusLowerBound_isRadiusUpperBound (q' := q') hI hq⟩
  let ι := (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ)
  let g := (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaComapLocHom P ⊤ le_top
    (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden)
  let f := (spaYPreAdicSpace P hI).ofRestrict W.isOpenEmbedding ≫ ι
  have : PreAdicSpace.IsOpenImmersion g := PreAdicSpace.IsOpenImmersion.ofRestrict _ _
  have : PreAdicSpace.IsOpenImmersion f := @PreAdicSpace.IsOpenImmersion.comp _ _ _ _ _
    (PreAdicSpace.IsOpenImmersion.ofRestrict _ _) (PreAdicSpace.IsOpenImmersion.ofRestrict _ _)
  -- the window restriction of `Spa(𝕎 O, 𝕎 O)` and the window of `𝒴` have the same image
  have e : Set.range g.base = Set.range f.base := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hx := val_ofRestrict_window_base_mem hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ x
      exact ⟨⟨⟨_, hx.1⟩, hx⟩, Subtype.ext (spaYInclusion_apply_val ϖ _)⟩
    · rintro ⟨⟨y, hy⟩, rfl⟩
      obtain ⟨x, hx⟩ := exists_ofRestrict_window_eq hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ y hy
      exact ⟨x, hx⟩
  have hlift : PreAdicSpace.IsOpenImmersion.lift ι g
      (range_ofRestrict_window_subset hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁) =
      (PreAdicSpace.IsOpenImmersion.isoOfRangeEq g f e).hom ≫
        (spaYPreAdicSpace P hI).ofRestrict W.isOpenEmbedding :=
    (PreAdicSpace.IsOpenImmersion.lift_uniq ι g _ _ ((Category.assoc _ _ _).trans
      (PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp g f e))).symm
  have hWq := isOpenImmersion_ofRestrict_comp_quotientPreAdicHom hY (V := W) hW
  have h₃ : PreAdicSpace.IsOpenImmersion (((PreAdicSpace.IsOpenImmersion.isoOfRangeEq g f e).hom ≫
      (spaYPreAdicSpace P hI).ofRestrict W.isOpenEmbedding) ≫ quotientPreAdicHom P hI hY) :=
    (Category.assoc (PreAdicSpace.IsOpenImmersion.isoOfRangeEq g f e).hom
      ((spaYPreAdicSpace P hI).ofRestrict W.isOpenEmbedding) (quotientPreAdicHom P hI hY)) ▸
      @PreAdicSpace.IsOpenImmersion.comp _ _ _ (PreAdicSpace.IsOpenImmersion.isoOfRangeEq g f e).hom
        _ (PreAdicSpace.IsOpenImmersion.of_isIso _) hWq
  unfold spaXWindowChart
  rw [hlift]
  exact @PreAdicSpace.IsOpenImmersion.comp _ _ _ _ _ (PreAdicSpace.IsOpenImmersion.of_isIso _) h₃

/-- **The image of the window chart is the image `q(W)` of the window** `W = {q ≤ κ ≤ q'}` under the
projection `q : 𝒴 → 𝒳`. -/
theorem range_spaXWindowChart_base :
    Set.range (spaXWindowChart hv hϖ hϖ' hρ₁ hρ₂ hI P hden hY h₁ h₂ h₁₂ P').base =
      quotientMap hI '' (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v}) := by
  let _ := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  have _ := P.isUniformAddGroup_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have _ := P.isTopologicalRing_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have := PreAdicSpace.IsOpenImmersion.ofRestrict (spaPreAdicSpace P hI)
    (isOpenEmbedding_spaYInclusion p ϖ)
  let ι := (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ)
  let g := (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaComapLocHom P ⊤ le_top
    (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden)
  let l := PreAdicSpace.IsOpenImmersion.lift ι g
    (range_ofRestrict_window_subset hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁)
  let i := windowPreAdicSpaceIso hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ P'
  -- the lift `W → 𝒴` does not change the underlying valuation
  have hl (x) : (l.base x).val = (g.base x).val :=
    (spaYInclusion_apply_val ϖ _).symm.trans (congrArg (fun φ ↦ (φ.base x).val)
      (PreAdicSpace.IsOpenImmersion.lift_fac ι g _))
  -- on points the projection is `quotientMap`
  have hq (y : spaY p ϖ) : (quotientPreAdicHom P hI hY).base y = quotientMap hI y := by
    have : (quotientPreAdicHom P hI hY).toHom.base y = quotientMap hI y := by
      rw [quotientPreAdicHom_toHom]
      rfl
    exact this
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨l.base (i.inv.base w), ?_, (hq _).symm⟩
    have hw := val_ofRestrict_window_base_mem hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ (i.inv.base w)
    rw [← hl] at hw
    exact hw
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := exists_ofRestrict_window_eq hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ y hy
    have hxy : l.base x = y :=
      Subtype.ext ((hl x).trans ((congrArg Subtype.val hx).trans (spaYInclusion_apply_val ϖ y)))
    -- `i.inv.base (i.hom.base x) = x`, as the base of `i.hom ≫ i.inv = 𝟙` at `x`
    have hix : i.inv.base (i.hom.base x) = x := congrArg (fun φ ↦ φ.base x) i.hom_inv_id
    refine ⟨i.hom.base x, ?_⟩
    rw [← hq, ← hxy]
    -- the chart is `i.inv ≫ l ≫ q`, and its base is the composite of the bases
    exact congrArg (fun z ↦ (quotientPreAdicHom P hI hY).base (l.base z)) hix

/-- **The window chart identifies integral sections.** Over an open `V ⊆ q(W)` of `𝒳`, a section of
`𝒪_𝒳` over `V` lies in `𝒪_𝒳⁺(V)` exactly when its pullback along the chart lies in the plus subring
`𝒪⁺(V')` of `Spa(B^I, B^{I,+})` over the preimage `V'` of `V`. On a rational open `V'` this plus
subring is the plus ring of the rational localisation of `(B^I, B^{I,+})`, by Wedhorn's
Proposition 8.16 (`map_completedPlusSubring_eq_presentationLimitPlusSubring`). -/
theorem comap_presentationLimitPlusSubring_spaXWindowChart {V : Opens (spaXPreAdicSpace P hI hY)}
    (hV : (V : Set (spaXPreAdicSpace P hI hY)) ⊆ quotientMap hI '' (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v})) :
    (presentationLimitPlusSubring (fun _ ha ↦ mem_powerBoundedSubring.mp ha)
        P'.le_powerBoundedSubring ((Opens.map
          (spaXWindowChart hv hϖ hϖ' hρ₁ hρ₂ hI P hden hY h₁ h₂ h₁₂ P').base).obj V)).comap
        ((PreAdicSpace.toRingPresheafedSpaceHom
          (spaXWindowChart hv hϖ hϖ' hρ₁ hρ₂ hI P hden hY h₁ h₂ h₁₂ P').toHom).c.app
            (Opposite.op V)).hom =
      (spaXPreAdicSpace P hI hY).plusSubring V := by
  -- the integral sections of `Spa(B^I, B^{I,+})` as a pre-adic space are its plus subrings
  refine (congrArg _ (presentationLimitPreAdicSpace_plusSubring P' _ _ P'.le_powerBoundedSubring
    _).symm).trans ?_
  exact PreAdicSpace.Hom.comap_plusSubring_of_subset_range
    (spaXWindowChart hv hϖ hϖ' hρ₁ hρ₂ hI P hden hY h₁ h₂ h₁₂ P') (hV.trans
      (range_spaXWindowChart_base hv hϖ hϖ' hρ₁ hρ₂ hI P hden hY h₁ h₂ h₁₂ P').ge)

end Chart

section Affinoid

variable {O : Type u} [CommRing O] {ϖ : O} {q q' : ℚ≥0} {K : Type*} [Field K] [Algebra O K]
  {v : Valuation K ℝ≥0} [CharP O p] [PerfectRing O p]
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1)
  [TopologicalSpace (WittVector p O)] [IsTopologicalRing (WittVector p O)]
  {hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})}
  {P : PairOfDefinition (WittVector p O)} (hY : (spaYPresheaf P ϖ).IsSheaf)

include hv hϖ hϖ' in
/-- **The image in `𝒳` of a wandering window is an open affinoid subspace.** Let `O` be the ring of
integers of `v`, perfect of characteristic `p`, with pseudouniformiser `ϖ`, and suppose `𝒪_𝒴` is a
sheaf. If `0 < q ≤ q'` and the window `W = {v ∈ 𝒴 : q ≤ κ(v) ≤ q'}` meets none of its nontrivial
integer Frobenius translates, then `𝒳` restricted to `q(W)` is affinoid: it is isomorphic to
`Spa(B^I, B^{I,+})` for the interval `I = [v(ϖ) ^ (1 / q), v(ϖ) ^ (1 / q')]`, through the window
chart `spaXWindowChart`. -/
theorem quotientMap_image_window_mem_affinoidOpens (hq : q ≠ 0) (hqq' : q ≤ q')
    (hW : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} :
          Set (spaY p ϖ)))
      (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v})) :
    (⟨quotientMap hI '' (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v}),
      (isOpenQuotientMap_quotientMap hI).isOpenMap _
        (isOpen_val_preimage_setOf_isRadiusLowerBound_isRadiusUpperBound hI hq)⟩ :
          Opens (spaX hI)) ∈ (spaXPreAdicSpace P hI hY).affinoidOpens := by
  have hϖ₀ : 0 < v (algebraMap O K ϖ) :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr ((map_ne_zero_iff _ hv.hom_inj).mpr hϖ))
  have hq' : q' ≠ 0 := ((pos_iff_ne_zero.mpr hq).trans_le hqq').ne'
  -- the radius `v(ϖ) ^ (1 / r)` of the interval matching the radius bound `r`
  have hρ {r : ℚ≥0} (hr : r ≠ 0) : v (algebraMap O K ϖ) ^ ((r : ℝ)⁻¹) ∈ Set.Ioo 0 1 :=
    ⟨NNReal.rpow_pos hϖ₀, NNReal.rpow_lt_one hϖ' (inv_pos.mpr (by positivity))⟩
  have hpow {r : ℚ≥0} (hr : r ≠ 0) :
      (v (algebraMap O K ϖ) ^ ((r : ℝ)⁻¹)) ^ r.num = v (algebraMap O K ϖ) ^ r.den := by
    rw [NNReal.rpow_inv_nnratCast, NNReal.rpow_inv_natCast_pow _ (NNRat.num_ne_zero.mpr hr)]
  have h₁₂ : v (algebraMap O K ϖ) ^ ((q : ℝ)⁻¹) ≤ v (algebraMap O K ϖ) ^ ((q' : ℝ)⁻¹) :=
    NNReal.rpow_le_rpow_of_exponent_ge hϖ₀ hϖ'.le
      (inv_anti₀ (by positivity) (by exact_mod_cast hqq'))
  have := isLocalization_away_windowDenominator (p := p) (ϖ := ϖ) (q' := q')
    (IntervalLocalization p hv hϖ hϖ' (hρ hq) (hρ hq')) hq
  have hden := hasDenominatorPower_windowNumerators (q := q) (q' := q')
    (B := IntervalLocalization p hv hϖ hϖ' (hρ hq) (hρ hq')) hI P
  let P' : PairOfDefinition (IntervalRing p hv hϖ hϖ' (hρ hq) (hρ hq')) :=
    IsHuberRing.nonempty_pairOfDefinition.some
  let f := spaXWindowChart hv hϖ hϖ' (hρ hq) (hρ hq') hI P hden hY (hpow hq) (hpow hq') h₁₂ P'
  have := isOpenImmersion_spaXWindowChart hv hϖ hϖ' (hρ hq) (hρ hq') hI P hden hY (hpow hq)
    (hpow hq') h₁₂ P' hW
  -- `𝒳` restricted to the image of the chart is `Spa(B^I, B^{I,+})`
  have hA := ObjectProperty.prop_of_iso PreAdicSpace.isAffinoid
    (PreAdicSpace.IsOpenImmersion.isoRestrict f)
    (PreAdicSpace.isAffinoid_presentationLimitPreAdicSpace
      ⟨_, Pair.powerBounded_plus (A := IntervalRing p hv hϖ hϖ' (hρ hq) (hρ hq')) ▸
        (Pair.powerBounded _).isRingOfIntegralElements⟩ P'
      P'.le_powerBoundedSubring)
  have hmem := (PreAdicSpace.mem_affinoidOpens_restrict_iff _ f.isOpenEmbedding ⊤).mp
    ((PreAdicSpace.top_mem_affinoidOpens_iff _).mpr hA)
  -- the image of the chart is `q(W)`
  have hU : f.isOpenEmbedding.isOpenMap.functor.obj ⊤ = ⟨quotientMap hI '' (Subtype.val ⁻¹'
      {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v}),
        (isOpenQuotientMap_quotientMap hI).isOpenMap _
          (isOpen_val_preimage_setOf_isRadiusLowerBound_isRadiusUpperBound hI hq)⟩ := by
    -- the open `functor.obj ⊤` is the image of `Set.univ` by definition
    refine Opens.ext (Set.image_univ.trans ?_)
    exact range_spaXWindowChart_base hv hϖ hϖ' (hρ hq) (hρ hq') hI P hden hY (hpow hq) (hpow hq')
      h₁₂ P'
  exact hU ▸ hmem

include hv hϖ hϖ' in
/-- **The image of the window `U_n = {p ^ n ≤ κ ≤ c p ^ n}` in `𝒳` is an open affinoid
subspace**, isomorphic to `Spa(B^I, B^{I,+})` for the matching interval `I`, when `𝒪_𝒴` is a
sheaf. -/
theorem quotientMap_image_windowU_mem_affinoidOpens (n : ℤ) :
    (⟨quotientMap hI '' (Subtype.val ⁻¹' windowU p ϖ n),
      (isOpenQuotientMap_quotientMap hI).isOpenMap _ (isOpen_val_preimage_windowU hI n)⟩ :
        Opens (spaX hI)) ∈ (spaXPreAdicSpace P hI hY).affinoidOpens := by
  have hpn : (p : ℚ≥0) ^ n ≠ 0 := zpow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hc : (1 : ℚ≥0) ≤ (p + 1 : ℚ≥0) / 2 := by
    rw [one_le_div two_pos]
    exact_mod_cast (Fact.out : p.Prime).two_le.trans (Nat.le_succ p)
  have hU : windowU p ϖ n = {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ n) v ∧
      IsRadiusUpperBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v} :=
    Set.ext fun v ↦ mem_windowU_iff n v
  have hW := fun k (hk : k ≠ 0) ↦ disjoint_preimage_zpow_windowU hI n hk
  simp only [hU] at hW ⊢
  exact quotientMap_image_window_mem_affinoidOpens hv hϖ hϖ' hY hpn
    (le_mul_of_one_le_left zero_le hc) hW

include hv hϖ hϖ' in
/-- **The image of the window `V_n = {c p ^ n ≤ κ ≤ p ^ (n + 1)}` in `𝒳` is an open affinoid
subspace**, isomorphic to `Spa(B^I, B^{I,+})` for the matching interval `I`, when `𝒪_𝒴` is a
sheaf. -/
theorem quotientMap_image_windowV_mem_affinoidOpens (n : ℤ) :
    (⟨quotientMap hI '' (Subtype.val ⁻¹' windowV p ϖ n),
      (isOpenQuotientMap_quotientMap hI).isOpenMap _ (isOpen_val_preimage_windowV hI n)⟩ :
        Opens (spaX hI)) ∈ (spaXPreAdicSpace P hI hY).affinoidOpens := by
  have hp : (0 : ℚ≥0) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hc : (p + 1 : ℚ≥0) / 2 ≤ p := by
    rw [div_le_iff₀ two_pos]
    rw [mul_two]
    exact add_le_add_right (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) _
  have hV : windowV p ϖ n = {v | v ∈ spaY p ϖ ∧
      IsRadiusLowerBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v ∧
        IsRadiusUpperBound p ϖ ((p : ℚ≥0) ^ (n + 1)) v} :=
    Set.ext fun v ↦ mem_windowV_iff n v
  have hW := fun k (hk : k ≠ 0) ↦ disjoint_preimage_zpow_windowV hI n hk
  simp only [hV] at hW ⊢
  refine quotientMap_image_window_mem_affinoidOpens hv hϖ hϖ' hY
    (mul_ne_zero (by positivity) (zpow_ne_zero n hp.ne')) ?_ hW
  rw [zpow_add_one₀ hp.ne', mul_comm ((p : ℚ≥0) ^ n)]
  exact mul_le_mul_of_nonneg_right hc zero_le

end Affinoid

end TauCeti.FarguesFontaine
