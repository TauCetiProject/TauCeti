/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Morrey
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.RellichKondrachov
public import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Rellich–Kondrachov and Morrey on isometric copies of Lipschitz domains

The Lipschitz-domain theorems are stated on the model space `WithLp 2 (ℝ × E)`. Transporting
`W^{k,p}` along a linear isometry `e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)`
(`TauCeti.Wkp.compLinearIsometryEquiv`) carries them to any open `Ω ⊆ F` whose image `e '' Ω` is
a Lipschitz domain; by `TauCeti.isLipschitzDomainWith_image_iff` this condition only involves
local graph charts of `Ω` itself. For `F = ℂ` the isometries are `Complex.equivRealProdL2` and
`Complex.equivRealProdL2Swap`; the planar discs and half-discs are treated in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar`.

This file proves, for a bounded such `Ω` of dimension `n`:

* the higher-order Rellich–Kondrachov theorem: forgetting the highest weak derivative is a
  compact operator `W^{k+1,p}(Ω) → W^{k,p}(Ω)` for every `k` and every `1 ≤ p ≤ ∞`;
* the higher-order Morrey and Hölder embeddings: for `n < q < ∞` with `1/p - k/n ≤ 1/q ≤ 1/p`,
  and for `n < k p`, members of `W^{k+1,p}(Ω)`, respectively `W^{k,p}(Ω)`, have Hölder
  representatives on `closure Ω`, depending linearly and boundedly on them, and the embeddings
  into Hölder spaces of smaller exponent are compact.

For the Hölder embeddings, the representative given on `closure (e '' Ω)` is composed with the
isometry `closure Ω → closure (e '' Ω)` induced by `e` (`TauCeti.HolderSpace.compLipschitzL`).

## Main declarations

* `TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image`: Rellich–Kondrachov
  on bounded open sets whose isometric image in the model space is a Lipschitz domain.
* `TauCeti.Wkp.exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith_image`: the
  sequential form.
* `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith_image`,
  `TauCeti.Wkp.exists_isCompactOperator_morrey_of_isLipschitzDomainWith_image`: Morrey's embedding
  `W^{k+1,p}(Ω) → C^{0,1-n/q}(closure Ω)` and its compactness below the exponent.
* `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith_image`,
  `TauCeti.Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith_image`: the Hölder
  embedding `W^{k,p}(Ω) → C^{0,1-n/(k p)}(closure Ω)` for `n < k p` and its compactness.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Filter MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- **Rellich–Kondrachov on isometric copies of Lipschitz domains.** Let
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` be a linear isometry and `Ω ⊆ F` a bounded open set whose image
`e '' Ω` is a Lipschitz domain. For `1 ≤ p ≤ ∞`, forgetting the highest weak derivative is a
compact operator `W^{k+1,p}(Ω) → W^{k,p}(Ω)` for every `k`. -/
theorem isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (k : ℕ) :
    IsCompactOperator (lowerOrderL (mu := volume) (Omega := Ω) (p := p) k) := by
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨e '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  have hUW : (Ω : Set F) = e ⁻¹' W := (e.toEquiv.preimage_image _).symm
  have hbW : IsBounded (W : Set (WithLp 2 (ℝ × E))) :=
    e.lipschitzWith.isBounded_image hb
  let T := compLinearIsometryEquiv (p := p) e.measurePreserving hUW
  have hK := ((isCompactOperator_lowerOrderL_of_isLipschitzDomainWith (p := p) hΩ hbW k).comp_clm
    (T (k + 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (T k).toContinuousLinearEquiv.toContinuousLinearMap
  convert hK using 1
  ext1 u
  obtain ⟨v, rfl⟩ := (T (k + 1)).surjective u
  rw [Function.comp_apply, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
    lowerOrderL_apply, lowerOrderL_apply]
  exact lowerOrder_compLinearIsometryEquiv _ hUW k v

/-- On a bounded open set whose isometric image in the model space is a Lipschitz domain, a
bounded sequence in `W^{k+1,p}(Ω)` has a subsequence whose lower-order parts converge in
`W^{k,p}(Ω)`, for `1 ≤ p ≤ ∞`. -/
theorem exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (k : ℕ)
    {u : ℕ → Wkp volume Ω p (k + 1)} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ w : Wkp volume Ω p k, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ lowerOrder k (u (φ n))) atTop (𝓝 w) := by
  obtain ⟨w, φ, hφ, hw⟩ :=
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb k).exists_subseq_tendsto
      hu
  refine ⟨w, φ, hφ, ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, lowerOrderL_apply k (u (φ _))] using hw

/-- Transport of a Hölder representative along a linear isometry `e`: if `M` sends
`W^{m,p}(e '' Ω)` to Hölder representatives on `closure (e '' Ω)`, then precomposing with the
transport along `e` and restricting along `e` gives a continuous linear map sending `W^{m,p}(Ω)` to
Hölder representatives on `closure Ω`, which is compact when `M` is. -/
private theorem exists_holderSpaceL_of_image (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    {W : Opens (WithLp 2 (ℝ × E))} (hW : (W : Set (WithLp 2 (ℝ × E))) = e '' (Ω : Set F))
    {m : ℕ} {γ : ℝ≥0}
    (M : Wkp volume W p m →L[ℝ] HolderSpace γ (closure (W : Set (WithLp 2 (ℝ × E)))) ℝ)
    (hM : ∀ v, ∀ᵐ y ∂volume, ∀ hy : y ∈ W, M v ⟨y, subset_closure hy⟩ = value m v y) :
    ∃ T : Wkp volume Ω p m →L[ℝ] HolderSpace γ (closure (Ω : Set F)) ℝ,
      (IsCompactOperator M → IsCompactOperator T) ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value m u x := by
  have hUW : (Ω : Set F) = e ⁻¹' W := hW ▸ (e.toEquiv.preimage_image _).symm
  let Tr := compLinearIsometryEquiv (p := p) e.measurePreserving hUW m
  have hmaps : ∀ x ∈ closure (Ω : Set F), e x ∈ closure (W : Set (WithLp 2 (ℝ × E))) :=
    fun x hx ↦ hW ▸ image_closure_subset_closure_image e.continuous (mem_image_of_mem e hx)
  let g : closure (Ω : Set F) → closure (W : Set (WithLp 2 (ℝ × E))) :=
    fun x ↦ ⟨e x, hmaps x x.2⟩
  have hg : LipschitzWith 1 g := LipschitzWith.of_dist_le_mul fun x y ↦ by
    simp [g, Subtype.dist_eq, e.dist_map]
  let R : Wkp volume Ω p m →L[ℝ] Wkp volume W p m :=
    Tr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨(HolderSpace.compLipschitzL g hg).comp (M.comp R), fun hK ↦ (hK.comp_clm R).clm_comp _,
    fun u ↦ ?_⟩
  have hu : u = Tr (Tr.symm u) := (Tr.apply_symm_apply u).symm
  filter_upwards [e.measurePreserving.quasiMeasurePreserving.ae (hM (Tr.symm u)),
    (ae_restrict_iff' Ω.isOpen.measurableSet).1
      (value_compLinearIsometryEquiv_ae e.measurePreserving hUW m (Tr.symm u))] with x h₁ h₂ hx
  have hxW : e x ∈ W := by
    rw [← SetLike.mem_coe, hW]
    exact mem_image_of_mem e hx
  rw [← hu] at h₂
  rw [h₂ hx, ← h₁ hxW, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    HolderSpace.compLipschitzL_apply]
  rfl

/-- **Higher-order Morrey embedding on isometric copies of Lipschitz domains.** Let
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` be a linear isometry and `Ω ⊆ F` a bounded open set of dimension
`n` whose image `e '' Ω` is a Lipschitz domain. If `1/p - k/n ≤ 1/q ≤ 1/p` with `n < q < ∞`, then
every `u ∈ W^{k+1,p}(Ω)` agrees almost everywhere on `Ω` with a function on `closure Ω` which is
Hölder of exponent `1 - n/q`, depending linearly and boundedly on `u`. This is
`TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith` transported along `e`. -/
theorem exists_morreyEmbeddingL_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (k : ℕ)
    {q : ℝ≥0} (hq : (finrank ℝ F : ℝ≥0) < q)
    (hq₁ : p⁻¹ ≤ (q : ℝ≥0∞)⁻¹ + k * (finrank ℝ F : ℝ≥0∞)⁻¹) (hq₂ : (q : ℝ≥0∞)⁻¹ ≤ p⁻¹) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace (1 - finrank ℝ F / q) (closure (Ω : Set F)) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value (k + 1) u x := by
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨e '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  rw [e.toLinearEquiv.finrank_eq] at hq hq₁ ⊢
  obtain ⟨M, hM⟩ := exists_morreyEmbeddingL_of_isLipschitzDomainWith (Ω := W) k hq hq₁ hq₂ hΩ
    (e.lipschitzWith.isBounded_image hb)
  obtain ⟨T, -, hT⟩ := exists_holderSpaceL_of_image e (W := W) rfl M hM
  exact ⟨T, hT⟩

/-- **Higher-order Morrey compactness on isometric copies of Lipschitz domains.** Under the
hypotheses of `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith_image`, for every
`β < 1 - n/q` the Hölder representative gives a compact operator
`W^{k+1,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem exists_isCompactOperator_morrey_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (k : ℕ)
    {q : ℝ≥0} (hq : (finrank ℝ F : ℝ≥0) < q)
    (hq₁ : p⁻¹ ≤ (q : ℝ≥0∞)⁻¹ + k * (finrank ℝ F : ℝ≥0∞)⁻¹) (hq₂ : (q : ℝ≥0∞)⁻¹ ≤ p⁻¹)
    {β : ℝ≥0} (hβ : β < 1 - finrank ℝ F / q) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace β (closure (Ω : Set F)) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value (k + 1) u x := by
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨e '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  rw [e.toLinearEquiv.finrank_eq] at hq hq₁ hβ
  obtain ⟨M, hMc, hM⟩ := exists_isCompactOperator_morrey_of_isLipschitzDomainWith (Ω := W) k hq
    hq₁ hq₂ hΩ (e.lipschitzWith.isBounded_image hb) hβ
  obtain ⟨T, hTc, hT⟩ := exists_holderSpaceL_of_image e (W := W) rfl M hM
  exact ⟨T, hTc hMc, hT⟩

/-- **Hölder embedding of `W^{k,p}` with `n < k p` on isometric copies of Lipschitz domains.** Let
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` be a linear isometry and `Ω ⊆ F` a bounded open set of dimension
`n` whose image `e '' Ω` is a Lipschitz domain. If `1 ≤ p < ∞` and `n < k p`, every
`u ∈ W^{k,p}(Ω)` agrees almost everywhere on `Ω` with a function on `closure Ω` which is Hölder of
exponent `1 - n/(k p)`, depending linearly and boundedly on `u`. -/
theorem exists_holderEmbeddingL_of_isLipschitzDomainWith_image {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) {k : ℕ}
    (hkp : (finrank ℝ F : ℝ≥0) < k * p) :
    ∃ T : Wkp volume Ω p k →L[ℝ] HolderSpace (1 - finrank ℝ F / (k * p)) (closure (Ω : Set F)) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value k u x := by
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨e '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  rw [e.toLinearEquiv.finrank_eq] at hkp ⊢
  obtain ⟨M, hM⟩ := exists_holderEmbeddingL_of_isLipschitzDomainWith (Ω := W) hkp hΩ
    (e.lipschitzWith.isBounded_image hb)
  obtain ⟨T, -, hT⟩ := exists_holderSpaceL_of_image e (W := W) rfl M hM
  exact ⟨T, hT⟩

/-- **Hölder compactness of `W^{k,p}` with `n < k p` on isometric copies of Lipschitz domains.**
Under the hypotheses of `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith_image`, for
every `β < 1 - n/(k p)` the Hölder representative gives a compact operator
`W^{k,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem exists_isCompactOperator_holder_of_isLipschitzDomainWith_image {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) {k : ℕ}
    (hkp : (finrank ℝ F : ℝ≥0) < k * p) {β : ℝ≥0} (hβ : β < 1 - finrank ℝ F / (k * p)) :
    ∃ T : Wkp volume Ω p k →L[ℝ] HolderSpace β (closure (Ω : Set F)) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value k u x := by
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨e '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  rw [e.toLinearEquiv.finrank_eq] at hkp hβ
  obtain ⟨M, hMc, hM⟩ := exists_isCompactOperator_holder_of_isLipschitzDomainWith (Ω := W) hkp
    hΩ (e.lipschitzWith.isBounded_image hb) hβ
  obtain ⟨T, hTc, hT⟩ := exists_holderSpaceL_of_image e (W := W) rfl M hM
  exact ⟨T, hTc hMc, hT⟩

end Wkp

end TauCeti
