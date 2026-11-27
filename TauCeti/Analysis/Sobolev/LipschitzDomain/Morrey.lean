/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Inclusion
public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Intrinsic
public import TauCeti.Analysis.Sobolev.W1p.SupercriticalMultiplication
public import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Normed.Module.DiamFrontier
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Morrey's embedding on bounded Lipschitz domains

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n` and let `n < p < ∞`. Every
`u ∈ W^{1,p}(Ω)` has a representative which extends continuously to the closure of `Ω` and is
Hölder there of exponent `1 - n/p`, and the resulting map `W^{1,p}(Ω) → C^{0,1-n/p}(closure Ω)` is
a bounded linear map. Unlike the interior statements, the estimate reaches the boundary.
Composed with the compact inclusion of Hölder spaces, the embedding into `C^{0,β}(closure Ω)` is
a compact operator for every `β < 1 - n/p`; this is the Hölder range of the Rellich–Kondrachov
theorem on Lipschitz domains. The representative is continuous on `closure Ω`, and its
restriction to the frontier is the trace `TauCeti.W1p.frontierTrace u` almost everywhere for
surface measure, so for `p > n` the boundary values of `u` are pointwise values. Finally
`W^{1,p}(Ω)` is a Banach algebra under pointwise multiplication: the product is a bounded
bilinear map `W^{1,p}(Ω) × W^{1,p}(Ω) → W^{1,p}(Ω)`.

The boundary regularity enters only through the extension operator
`TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: each map factors as extension to
`W^{1,p}(ℝ × E)`, the whole-space theorem (Morrey's embedding `TauCeti.W1p.morreyEmbedding`, or
the product `TauCeti.W1p.mulL`), and restriction to `closure Ω` or to `Ω`. The representative is
unique (`IsOpen.ext_closure_of_ae_eq`): a continuous function on `closure Ω` is determined by its
values at almost every point of `Ω`, so the maps below do not depend on the extension chosen.

The embedding, its compactness, the continuous representative and its boundary values also hold on
a bounded Lipschitz domain `Ω` of a nontrivial finite-dimensional real inner product space `F`,
such as `EuclideanSpace ℝ (Fin n)`, in the sense of the intrinsic predicate
`Set.IsLipschitzDomain`, for every additive Haar measure `μ` on `F`, with the trace
`TauCeti.W1p.frontierTraceOfIsLipschitzDomain`. A boundary chart is an affine isometry
`g : F ≃ᵃⁱ[ℝ] ℝ × E` carrying `Ω` onto a bounded Lipschitz domain `W` of the model space
(`Set.IsLipschitzDomain.exists_isLipschitzDomainWith_image`); the Hölder representative of
`u ∘ g⁻¹` on `closure W`, read on `closure Ω` through the isometry `g`, is one of `u`, and
`W^{1,p}(Ω)` does not depend on the Haar measure (`TauCeti.W1p.addHaarEquivL`).

## Main declarations

* `TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith`: Morrey's embedding
  `W^{1,p}(Ω) →L[ℝ] C^{0,1-n/p}(closure Ω)`.
* `TauCeti.W1p.exists_isCompactOperator_holder_of_isLipschitzDomainWith`: the embedding into
  `C^{0,β}(closure Ω)` is compact for `β < 1 - n/p`.
* `TauCeti.W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomainWith`: a representative
  continuous on `closure Ω`.
* `TauCeti.W1p.exists_continuousOn_frontierTrace_ae_eq`: the trace is the boundary restriction of
  the continuous representative.
* `TauCeti.W1p.exists_mulL_of_isLipschitzDomainWith`: multiplication on `W^{1,p}(Ω)` as a bounded
  bilinear map.
* `TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomain`,
  `TauCeti.W1p.exists_isCompactOperator_holder_of_isLipschitzDomain`,
  `TauCeti.W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomain` and
  `TauCeti.W1p.exists_continuousOn_frontierTraceOfIsLipschitzDomain_ae_eq`: the same on bounded
  Lipschitz domains of a Euclidean space, for every additive Haar measure.

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

section ModelSpace

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
  obtain ⟨X, hX, _⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  refine ⟨(HolderSpace.compLipschitzL Subtype.val (LipschitzWith.subtypeVal _)).comp
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

/-- **Continuous representatives up to the boundary.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n` and `n < p < ∞`, then every `u ∈ W^{1,p}(Ω)` agrees almost everywhere on
`Ω` with a function continuous on `closure Ω`. -/
theorem W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomainWith
    (hp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω p) :
    ∃ f : WithLp 2 (ℝ × E) → ℝ, ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))) ∧
      W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f := by
  classical
  obtain ⟨T, hT⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith hp hΩ hb
  refine ⟨fun x => if hx : x ∈ closure (Ω : Set (WithLp 2 (ℝ × E))) then T u ⟨x, hx⟩ else 0,
    ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert (T u).continuous using 1
    ext x
    exact dite_eq_left x.property
  · refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hT u] with x hx hxΩ
    rw [dite_eq_left (subset_closure hxΩ)]
    exact (hx hxΩ).symm

/-- **The trace is the boundary value of the continuous representative.** If `Ω ⊆ ℝ × E` is a
bounded Lipschitz domain of dimension `n` and `n < p < ∞`, then every `u ∈ W^{1,p}(Ω)` agrees
almost everywhere on `Ω` with a function continuous on `closure Ω` whose restriction to the
frontier is the trace `W1p.frontierTrace u`, almost everywhere for surface measure. -/
theorem W1p.exists_continuousOn_frontierTrace_ae_eq
    (hp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω p) :
    ∃ f : WithLp 2 (ℝ × E) → ℝ, ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))) ∧
      W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f ∧
      W1p.frontierTrace ENNReal.coe_ne_top hΩ hb u
        =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f := by
  obtain ⟨f, hf, hu⟩ := W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomainWith hp hΩ hb u
  exact ⟨f, hf, hu, W1p.frontierTrace_ae_eq_of_continuousOn ENNReal.coe_ne_top hΩ hb hf hu⟩

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
  obtain ⟨X, hX, _⟩ := hext
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

end ModelSpace

/-! ### Bounded Lipschitz domains of a Euclidean space -/

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F] {Ω : Opens F} {mu : Measure F}
  [mu.IsAddHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- Morrey's embedding of `TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomain`, for Lebesgue
measure. -/
private theorem exists_morreyEmbeddingL_volume_of_isLipschitzDomain
    (hp : (finrank ℝ F : ℝ≥0) < p) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) :
    ∃ T : W1p volume Ω p →L[ℝ] HolderSpace (1 - finrank ℝ F / p) (closure (Ω : Set F)) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  rcases (frontier (Ω : Set F)).eq_empty_or_nonempty with hfr | hne
  · -- A bounded open set with empty frontier is empty.
    have hΩe := hb.eq_empty_of_frontier_eq_empty hfr
    exact ⟨0, fun u => Filter.Eventually.of_forall fun x hx =>
      absurd (SetLike.mem_coe.2 hx) (by simp [hΩe])⟩
  -- A boundary chart `g` carries `Ω` onto a bounded Lipschitz domain `W` of the model space, and
  -- the tangential model `E` inherits an inner product from `F`.
  obtain ⟨g, L, hL⟩ := hΩ.exists_isLipschitzDomainWith_image hb hne
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) := g.linearIsometryEquiv
  let _ : InnerProductSpace ℝ E := .ofLinearIsometry e.symmInr
  have _ : FiniteDimensional ℝ E := e.finiteDimensional_snd
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let W : Opens (WithLp 2 (ℝ × E)) :=
    ⟨g '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hL).1⟩
  have hWΩ : (W : Set (WithLp 2 (ℝ × E))) = g.symm ⁻¹' Ω :=
    g.toHomeomorph.image_eq_preimage_symm _
  rw [e.toLinearEquiv.finrank_eq] at hp ⊢
  obtain ⟨M, hM⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith (Ω := W) hp hL
    (g.lipschitzWith.isBounded_image hb)
  -- Read the representative of `u ∘ g⁻¹` on `closure W` back on `closure Ω` through `g`.
  let k : closure (Ω : Set F) → closure (W : Set (WithLp 2 (ℝ × E))) := fun x =>
    ⟨g x, image_closure_subset_closure_image g.continuous (mem_image_of_mem g x.property)⟩
  have hk : LipschitzWith 1 k := LipschitzWith.of_dist_le_mul fun x y => by
    simp [k, Subtype.dist_eq]
  refine ⟨(HolderSpace.compLipschitzL k hk).comp
    (M.comp (W1p.compAffineIsometryEquivL g.symm hWΩ)), fun u => ?_⟩
  have hv := (ae_restrict_iff' W.isOpen.measurableSet).1
    (W1p.value_compAffineIsometryEquivL_ae g.symm hWΩ u)
  filter_upwards [g.measurePreserving.quasiMeasurePreserving.ae
      (hM (W1p.compAffineIsometryEquivL g.symm hWΩ u)),
    g.measurePreserving.quasiMeasurePreserving.ae hv] with x h₁ h₂ hx
  have hxW : g x ∈ W := mem_image_of_mem g hx
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    HolderSpace.compLipschitzL_apply, h₁ hxW, h₂ hxW, g.symm_apply_apply]

/-- **Morrey's embedding on bounded Lipschitz domains of a Euclidean space.** Let `Ω` be a bounded
Lipschitz domain in a nontrivial finite-dimensional real inner product space `F` of dimension `n`,
such as `EuclideanSpace ℝ (Fin n)`, and let `μ` be an additive Haar measure on `F`. If
`n < p < ∞`, every `u ∈ W^{1,p}(Ω)` agrees `μ`-almost everywhere on `Ω` with a function on
`closure Ω` which is Hölder of exponent `1 - n/p`, and this representative depends linearly and
boundedly on `u`. By `IsOpen.ext_closure_of_ae_eq` the representative is unique. -/
theorem W1p.exists_morreyEmbeddingL_of_isLipschitzDomain (hp : (finrank ℝ F : ℝ≥0) < p)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    ∃ T : W1p mu Ω p →L[ℝ] HolderSpace (1 - finrank ℝ F / p) (closure (Ω : Set F)) ℝ,
      ∀ u, ∀ᵐ x ∂mu, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  obtain ⟨T, hT⟩ := exists_morreyEmbeddingL_volume_of_isLipschitzDomain hp hΩ hb
  refine ⟨T.comp ((W1p.addHaarEquivL mu volume : W1p mu Ω p ≃L[ℝ] W1p volume Ω p) :
    W1p mu Ω p →L[ℝ] W1p volume Ω p), fun u => ?_⟩
  -- Both statements hold Lebesgue-almost everywhere, and `μ` is absolutely continuous.
  have hA := (ae_restrict_iff' Ω.isOpen.measurableSet).1
    (W1p.value_addHaarEquivL_ae (p := (p : ℝ≥0∞)) mu volume u)
  refine (Measure.absolutelyContinuous_isAddHaarMeasure mu volume).ae_le ?_
  filter_upwards [hT (W1p.addHaarEquivL mu volume u), hA] with x h₁ h₂ hx
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, h₁ hx, h₂ hx]

/-- **Hölder compactness on bounded Lipschitz domains of a Euclidean space.** If `Ω` is a bounded
Lipschitz domain in a nontrivial finite-dimensional real inner product space `F` of dimension `n`
with an additive Haar measure and `n < p < ∞`, then for every `β < 1 - n/p` the Morrey
representative gives a compact operator `W^{1,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem W1p.exists_isCompactOperator_holder_of_isLipschitzDomain (hp : (finrank ℝ F : ℝ≥0) < p)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) {β : ℝ≥0}
    (hβ : β < 1 - finrank ℝ F / p) :
    ∃ T : W1p mu Ω p →L[ℝ] HolderSpace β (closure (Ω : Set F)) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂mu, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  have : CompactSpace (closure (Ω : Set F)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  obtain ⟨T, hT⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomain (mu := mu) hp hΩ hb
  refine ⟨(HolderSpace.inclusionL hβ.le).comp T,
    (HolderSpace.isCompactOperator_inclusionL hβ).comp_clm T, fun u => ?_⟩
  filter_upwards [hT u] with x hx hxΩ
  rw [ContinuousLinearMap.comp_apply, HolderSpace.inclusionL_apply, hx hxΩ]

/-- **Continuous representatives up to the boundary of a Euclidean Lipschitz domain.** If `Ω` is a
bounded Lipschitz domain in a nontrivial finite-dimensional real inner product space of dimension
`n` with an additive Haar measure `μ` and `n < p < ∞`, then every `u ∈ W^{1,p}(Ω)` agrees
`μ`-almost everywhere on `Ω` with a function continuous on `closure Ω`. -/
theorem W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomain
    (hp : (finrank ℝ F : ℝ≥0) < p) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) (u : W1p mu Ω p) :
    ∃ f : F → ℝ, ContinuousOn f (closure (Ω : Set F)) ∧
      W1p.value u =ᵐ[mu.restrict (Ω : Set F)] f := by
  classical
  obtain ⟨T, hT⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomain (mu := mu) hp hΩ hb
  refine ⟨fun x => if hx : x ∈ closure (Ω : Set F) then T u ⟨x, hx⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert (T u).continuous using 1
    ext x
    exact dite_eq_left x.property
  · refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hT u] with x hx hxΩ
    rw [dite_eq_left (subset_closure hxΩ)]
    exact (hx hxΩ).symm

/-- **The trace on a Euclidean Lipschitz domain is the boundary value of the continuous
representative.** If `Ω` is a bounded Lipschitz domain in a nontrivial finite-dimensional real
inner product space `F` of dimension `n` with an additive Haar measure `μ` and `n < p < ∞`, then
every `u ∈ W^{1,p}(Ω)` agrees `μ`-almost everywhere on `Ω` with a function continuous on
`closure Ω` whose restriction to the frontier is the trace
`TauCeti.W1p.frontierTraceOfIsLipschitzDomain u`, almost everywhere for surface measure. -/
theorem W1p.exists_continuousOn_frontierTraceOfIsLipschitzDomain_ae_eq
    (hp : (finrank ℝ F : ℝ≥0) < p) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) (u : W1p mu Ω p) :
    ∃ f : F → ℝ, ContinuousOn f (closure (Ω : Set F)) ∧
      W1p.value u =ᵐ[mu.restrict (Ω : Set F)] f ∧
      W1p.frontierTraceOfIsLipschitzDomain ENNReal.coe_ne_top hΩ hb u
        =ᵐ[(μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))] f := by
  obtain ⟨f, hf, hu⟩ := W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomain hp hΩ hb u
  exact ⟨f, hf, hu,
    W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn ENNReal.coe_ne_top hΩ hb hf hu⟩

end Intrinsic

end TauCeti

end
