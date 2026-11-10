/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Inclusion
public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.W1p.SupercriticalMultiplication
public import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Morrey's embedding on bounded Lipschitz domains

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n` and let `n < p < ∞`. Every
`u ∈ W^{1,p}(Ω)` has a representative which extends continuously to the closure of `Ω` and is
Hölder there of exponent `1 - n/p`, and the resulting map `W^{1,p}(Ω) → C^{0,1-n/p}(closure Ω)` is
a bounded linear map. Unlike the interior statements, the estimate reaches the boundary.
Composed with the compact inclusion of Hölder spaces, the embedding into `C^{0,β}(closure Ω)` is
a compact operator for every `β < 1 - n/p`; this is the Hölder range of the Rellich–Kondrachov
theorem on Lipschitz domains. Finally `W^{1,p}(Ω)` is a Banach algebra under pointwise
multiplication: the product is a bounded bilinear map `W^{1,p}(Ω) × W^{1,p}(Ω) → W^{1,p}(Ω)`.

The boundary regularity enters only through the extension operator
`TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: each map factors as extension to
`W^{1,p}(ℝ × E)`, the whole-space theorem (Morrey's embedding `TauCeti.W1p.morreyEmbedding`, or
the product `TauCeti.W1p.mulL`), and restriction to `closure Ω` or to `Ω`. The representative is
unique (`IsOpen.ext_closure_of_ae_eq`): a continuous function on `closure Ω` is determined by its
values at almost every point of `Ω`, so the maps below do not depend on the extension chosen.

## Main declarations

* `TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith`: Morrey's embedding
  `W^{1,p}(Ω) →L[ℝ] C^{0,1-n/p}(closure Ω)`.
* `TauCeti.W1p.exists_isCompactOperator_holder_of_isLipschitzDomainWith`: the embedding into
  `C^{0,β}(closure Ω)` is compact for `β < 1 - n/p`.
* `TauCeti.W1p.exists_mulL_of_isLipschitzDomainWith`: multiplication on `W^{1,p}(Ω)` as a bounded
  bilinear map.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.2, Theorem 5, and §5.7.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part II, and
  Theorems 4.39 and 6.3.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- The value of a Sobolev function on a Lipschitz domain agrees almost everywhere on the domain
with the value of any extension. -/
private theorem W1p.value_ae_eq_of_restrictL_eq {u : W1p volume Ω p}
    {w : W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p} (hw : W1p.restrictL le_top w = u) :
    W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value w := by
  rw [← hw]
  exact W1p.value_restrictL_ae le_top w

/-- **Morrey's embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n` and `n < p < ∞`, then every `u ∈ W^{1,p}(Ω)` agrees almost everywhere on
`Ω` with a function on `closure Ω` which is Hölder of exponent `1 - n/p`, and this representative
depends linearly and boundedly on `u`. By `IsOpen.ext_closure_of_ae_eq` the representative is
unique. -/
theorem W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith
    (hp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : W1p volume Ω p →L[ℝ] HolderSpace (1 - finrank ℝ (WithLp 2 (ℝ × E)) / p)
        (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  obtain ⟨X, hX⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  refine ⟨(HolderSpace.compLipschitzL Subtype.val (LipschitzWith.subtype_val _)).comp
    ((W1p.morreyEmbedding hp).comp X), fun u => ?_⟩
  have hu : W1p.restrictL le_top (X u) = u := by
    simpa using congrArg (· u) hX
  have h₁ := (ae_restrict_iff' Ω.isOpen.measurableSet).1 (W1p.value_ae_eq_of_restrictL_eq hu)
  filter_upwards [h₁, W1p.value_ae_eq_morreyEmbedding (mu := volume) hp (X u)] with x hx₁ hx₂ hx
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    HolderSpace.compLipschitzL_apply, hx₁ hx, hx₂]

/-- **Hölder compactness on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n` and `n < p < ∞`, then for every `β < 1 - n/p` the Morrey representative
gives a compact operator `W^{1,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem W1p.exists_isCompactOperator_holder_of_isLipschitzDomainWith
    (hp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {β : ℝ≥0}
    (hβ : β < 1 - finrank ℝ (WithLp 2 (ℝ × E)) / p) :
    ∃ T : W1p volume Ω p →L[ℝ] HolderSpace β (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  have : CompactSpace (closure (Ω : Set (WithLp 2 (ℝ × E)))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  obtain ⟨T, hT⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith hp hΩ hb
  refine ⟨(HolderSpace.inclusionL hβ.le).comp T,
    (HolderSpace.isCompactOperator_inclusionL hβ).comp_clm T, fun u => ?_⟩
  filter_upwards [hT u] with x hx hxΩ
  rw [ContinuousLinearMap.comp_apply, HolderSpace.inclusionL_apply, hx hxΩ]

/-- **Supercritical multiplication on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n` and `n < p < ∞`, then the pointwise product of two functions in
`W^{1,p}(Ω)` lies in `W^{1,p}(Ω)` and depends on them through a bounded bilinear map, so that
`‖u v‖ ≤ C ‖u‖ ‖v‖`: `W^{1,p}(Ω)` is a Banach algebra up to the boundary. -/
theorem W1p.exists_mulL_of_isLipschitzDomainWith
    (hp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ M : W1p volume Ω p →L[ℝ] W1p volume Ω p →L[ℝ] W1p volume Ω p,
      ∀ u v, W1p.value (M u v) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x * W1p.value v x := by
  have hext := W1p.exists_extensionL_of_isLipschitzDomainWith (p := (p : ℝ≥0∞)) hΩ hb
  obtain ⟨X, hX⟩ := hext
  refine ⟨(ContinuousLinearMap.compL ℝ _ _ _
    (W1p.restrictL (mu := volume) (p := (p : ℝ≥0∞)) (le_top : Ω ≤ ⊤))).comp
      ((W1p.mulL (mu := volume) hp).bilinearComp X X), fun u v => ?_⟩
  have hu : W1p.restrictL le_top (X u) = u := by
    simpa using congrArg (· u) hX
  have hv : W1p.restrictL le_top (X v) = v := by
    simpa using congrArg (· v) hX
  have hmul := W1p.value_mul_ae (mu := volume) hp (X u) (X v)
  have hru := W1p.value_ae_eq_morreyRepresentative (mu := volume) (X u) hp
  have hrv := W1p.value_ae_eq_morreyRepresentative (mu := volume) (X v) hp
  filter_upwards [W1p.value_restrictL_ae le_top (W1p.mulL hp (X u) (X v)),
    ae_restrict_of_ae hmul, ae_restrict_of_ae hru, ae_restrict_of_ae hrv,
    W1p.value_ae_eq_of_restrictL_eq hu, W1p.value_ae_eq_of_restrictL_eq hv]
    with x h₀ h₁ h₂ h₃ h₄ h₅
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.bilinearComp_apply]
  rw [W1p.mulL_apply] at h₀ ⊢
  rw [h₀, h₁, ← h₂, ← h₃, ← h₄, ← h₅]

end TauCeti

end
