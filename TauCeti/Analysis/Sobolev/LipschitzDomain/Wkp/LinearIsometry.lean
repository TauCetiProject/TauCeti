/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Plane
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.RellichKondrachov
public import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Rellich–Kondrachov on isometric copies of Lipschitz domains

The Lipschitz-domain theorems are stated on the model space `WithLp 2 (ℝ × E)`. Transporting
`W^{k,p}` along a linear isometry `e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)`
(`TauCeti.Wkp.compLinearIsometryEquiv`) carries them to any open `Ω ⊆ F` whose image `e '' Ω` is
a Lipschitz domain; by `TauCeti.isLipschitzDomainWith_image_iff` this condition only involves
local graph charts of `Ω` itself. For `F = ℂ` the isometries are `Complex.equivRealProdL2` and
`Complex.equivRealProdL2Swap`.

This file proves the higher-order Rellich–Kondrachov theorem in this generality: for a bounded such
`Ω`, forgetting the highest weak derivative is a compact operator `W^{k+1,p}(Ω) → W^{k,p}(Ω)` for
every `k` and every `1 ≤ p ≤ ∞`. The planar half-disc `{z | |z| < r, 0 < Im z}` is the preimage of
the model half-disc `TauCeti.halfDisc r` under `Complex.equivRealProdL2Swap`, which puts the normal
coordinate `Im z` first, so the theorem applies to it.

## Main declarations

* `TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image`: Rellich–Kondrachov
  on bounded open sets whose isometric image in the model space is a Lipschitz domain.
* `TauCeti.Wkp.exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith_image`: the
  sequential form.
* `TauCeti.Wkp.isCompactOperator_lowerOrderL_complexHalfDisc`: the planar half-disc.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Filter MeasureTheory Set TopologicalSpace
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

/-- **Rellich–Kondrachov on the planar half-disc.** On the half-disc
`{z | |z| < r, 0 < Im z} = Complex.equivRealProdL2Swap ⁻¹' halfDisc r` in `ℂ`, forgetting the
highest weak derivative is a compact operator `W^{k+1,p} → W^{k,p}` for every `k` and every
`1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_lowerOrderL_complexHalfDisc (r : ℝ) (k : ℕ) :
    IsCompactOperator (lowerOrderL (mu := volume) (p := p)
      (Omega := ⟨Complex.equivRealProdL2Swap ⁻¹' halfDisc r,
        (halfDisc r).isOpen.preimage Complex.equivRealProdL2Swap.continuous⟩) k) := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  refine isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image (L := L)
    Complex.equivRealProdL2Swap ?_ ?_ k
  · rwa [Opens.coe_mk, image_preimage_eq _ Complex.equivRealProdL2Swap.surjective]
  · refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := r)).subset fun z hz => ?_
    rw [Metric.mem_ball, dist_zero_right, ← Complex.equivRealProdL2Swap.norm_map]
    exact (mem_halfDisc.1 hz).1

end Wkp

end TauCeti
