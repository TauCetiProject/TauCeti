/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import TauCeti.Topology.Algebra.Indicator

/-!
# Spectral projections of self-adjoint operators

Let `T` be a self-adjoint operator on a real or complex Hilbert space `H`, over `RCLike 𝕜`. For a
set `Ω ⊆ ℝ` whose frontier avoids the spectrum of `T`, the indicator of `Ω` is continuous on the
spectrum, so the continuous functional calculus gives the spectral projection
`cfc (Ω.indicator 1) T` onto the part of the spectrum in `Ω`. This file proves the facts about
these projections from which the spectral flow of a path of self-adjoint Fredholm operators is
built:

* **The kernel projection.** If `0 ∈ Ω`, the spectrum meets `Ω` at most in `0` and the frontier of
  `Ω` avoids the spectrum, then the spectral projection for `Ω` is the orthogonal projection onto
  the kernel of `T`.
* **Stability.** Under the frontier condition, the spectral projection for `Ω` depends
  continuously on the self-adjoint operator (`IsSelfAdjoint.continuousWithinAt_cfc_indicator`,
  proved for C⋆-algebras), so the rank of its range is locally constant, and it
  is constant along a continuous path of self-adjoint operators over a preconnected parameter space
  as long as the frontier of `Ω` avoids every spectrum along the path.
* **Nested and disjoint sets.** Spectral projections grow with the set, those for disjoint sets are
  orthogonal, and the rank of the projection for a disjoint union is the sum of the two ranks.
* **The spectral gap.** At an operator with closed range, `0` is isolated in the spectrum, so the
  indicator of `Ω` is continuous on the spectrum as soon as the frontier of `Ω` meets the spectrum
  at most in `0`; the spectral projection for `[0, c)` is then defined even when `0` is an
  eigenvalue.

The real functional calculus on `H →L[𝕜] H` is taken as an assumption, as is its isometry for the
stability results. Mathlib provides both over `ℂ`, and
`TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus` provides them over `ℝ`.

Sets `Ω` meeting the spectrum at most in `0` come from the spectral gap of a self-adjoint operator
with closed range (`IsSelfAdjoint.exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range`).

## Main results

* `ContinuousLinearMap.cfc_indicator_eq_starProjection_range`: a spectral projection is the
  orthogonal projection onto its range.
* `IsSelfAdjoint.cfc_indicator_eq_starProjection_ker`: the spectral projection for a set meeting the
  spectrum only at `0` is the projection onto the kernel.
* `IsSelfAdjoint.eventually_rank_range_cfc_indicator_eq` and
  `IsPreconnected.rank_range_cfc_indicator_eq`: the rank of the spectral projection is locally
  constant, and constant along paths.
* `ContinuousLinearMap.range_cfc_indicator_mono`,
  `ContinuousLinearMap.cfc_indicator_mul_cfc_indicator_eq_zero`,
  `ContinuousLinearMap.range_cfc_indicator_union` and
  `ContinuousLinearMap.finrank_range_cfc_indicator_union`: spectral projections for nested and
  disjoint sets.
* `IsSelfAdjoint.continuousOn_indicator_spectrum_of_isClosed_range`: indicators across the spectral
  gap at `0`.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
-/

public section

open Filter Set Topology
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

section Projection

variable [Algebra ℝ (H →L[𝕜] H)] [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

/-- The range of a spectral projection of an operator on a Hilbert space admits an orthogonal
projection, since the spectral projection is idempotent and hence has closed range. -/
instance ContinuousLinearMap.hasOrthogonalProjection_range_cfc_indicator (T : H →L[𝕜] H)
    (Ω : Set ℝ) : (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range.HasOrthogonalProjection :=
  ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (TauCeti.isStarProjection_cfc_indicator T Ω).isIdempotentElem

/-- A spectral projection of an operator on a Hilbert space is the orthogonal projection onto its
own range. -/
theorem ContinuousLinearMap.cfc_indicator_eq_starProjection_range (T : H →L[𝕜] H) (Ω : Set ℝ) :
    cfc (Ω.indicator (1 : ℝ → ℝ)) T = (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range.starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (TauCeti.isStarProjection_cfc_indicator T Ω)).2

/-! ### The spectral projection onto the kernel -/

/-- If `0 ∈ Ω`, the spectrum of a self-adjoint operator `T` meets `Ω` at most in `0`, and the
frontier of `Ω` avoids the spectrum, then the spectral projection of `T` for `Ω` is the orthogonal
projection onto the kernel of `T`. -/
theorem IsSelfAdjoint.cfc_indicator_eq_starProjection_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    {Ω : Set ℝ} (h0 : (0 : ℝ) ∈ Ω) (hΩ : spectrum ℝ T ∩ Ω ⊆ {0})
    (hfr : Disjoint (frontier Ω) (spectrum ℝ T)) :
    cfc (Ω.indicator (1 : ℝ → ℝ)) T = T.ker.starProjection := by
  set f := Ω.indicator (1 : ℝ → ℝ)
  have hf : ContinuousOn f (spectrum ℝ T) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier hfr
  set P := cfc f T
  -- `T P = 0`, since `x f(x) = 0` on the spectrum.
  have hTP : T * P = 0 := by
    calc T * P = cfc (fun x ↦ x * f x) T := by rw [cfc_mul (fun x ↦ x) f T, cfc_id' ℝ T]
      _ = cfc (0 : ℝ → ℝ) T := cfc_congr fun x hx ↦ by
          by_cases hxΩ : x ∈ Ω
          · rw [mem_singleton_iff.1 (hΩ ⟨hx, hxΩ⟩), zero_mul, Pi.zero_apply]
          · simp only [f, indicator_of_notMem hxΩ, mul_zero, Pi.zero_apply]
      _ = 0 := cfc_zero ℝ T
  -- `1 - P = g(T) T` with `g(x) = (1 - f(x)) / x`, which is continuous on the spectrum because `0`
  -- is either not in the spectrum or isolated in it.
  set g : ℝ → ℝ := fun x ↦ (1 - f x) / x
  have hg : ContinuousOn g (spectrum ℝ T) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      have hint : (0 : ℝ) ∈ interior Ω := by
        by_contra hni
        exact hfr.notMem_of_mem_left ⟨subset_closure h0, hni⟩ hx
      refine (continuousWithinAt_const : ContinuousWithinAt (fun _ ↦ g 0) _ _).congr_of_eventuallyEq
        ?_ rfl
      filter_upwards [nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.1 hint), self_mem_nhdsWithin]
        with y hy hys
      rw [mem_singleton_iff.1 (hΩ ⟨hys, hy⟩)]
    · exact (continuousWithinAt_const.sub (hf x hx)).div continuousWithinAt_id hx0
  have hsub : 1 - P = cfc g T * T := by
    calc 1 - P = cfc (fun x ↦ 1 - f x) T := by rw [cfc_sub (fun _ ↦ 1) f T, cfc_const_one ℝ T]
      _ = cfc (fun x ↦ g x * x) T := cfc_congr fun x _ ↦ by
          by_cases hx0 : x = 0
          · simp [hx0, f, h0]
          · exact (div_mul_cancel₀ _ hx0).symm
      _ = cfc g T * T := by rw [cfc_mul g (fun x ↦ x) T, cfc_id' ℝ T]
  -- Hence the range of `P` is the kernel of `T`.
  have hrange : P.range = T.ker := by
    refine le_antisymm ?_ fun v hv ↦ ⟨v, ?_⟩
    · rintro _ ⟨v, rfl⟩
      exact congr($hTP v)
    · have hTv : T v = 0 := LinearMap.mem_ker.1 hv
      have h : v - P v = 0 := by simpa [hTv] using congr($hsub v)
      exact (sub_eq_zero.1 h).symm
  exact (T.cfc_indicator_eq_starProjection_range Ω).trans (Submodule.starProjection_inj.2 hrange)

/-! ### Spectral projections for nested and disjoint sets -/

namespace ContinuousLinearMap

variable {T : H →L[𝕜] H} {Ω Ω' : Set ℝ}

/-- The range of a spectral projection grows with the set. -/
theorem range_cfc_indicator_mono (h : Ω ⊆ Ω')
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range ≤ (cfc (Ω'.indicator (1 : ℝ → ℝ)) T).range := by
  have hmul : cfc (Ω.indicator (1 : ℝ → ℝ)) T =
      cfc (Ω'.indicator (1 : ℝ → ℝ)) T * cfc (Ω.indicator (1 : ℝ → ℝ)) T := by
    rw [← cfc_mul _ _ T hΩ' hΩ]
    refine cfc_congr fun x _ ↦ ?_
    by_cases hx : x ∈ Ω
    · simp [hx, h hx]
    · simp [hx]
  rintro _ ⟨v, rfl⟩
  exact ⟨cfc (Ω.indicator (1 : ℝ → ℝ)) T v, (congrArg (fun S ↦ S v) hmul).symm⟩

/-- Spectral projections for disjoint sets are orthogonal: their product vanishes. -/
theorem cfc_indicator_mul_cfc_indicator_eq_zero (hd : Disjoint Ω Ω')
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    cfc (Ω.indicator (1 : ℝ → ℝ)) T * cfc (Ω'.indicator (1 : ℝ → ℝ)) T = 0 := by
  rw [← cfc_mul _ _ T hΩ hΩ', ← cfc_zero ℝ T]
  refine cfc_congr fun x _ ↦ ?_
  by_cases hx : x ∈ Ω
  · simp [hx, hd.notMem_of_mem_left hx]
  · simp [hx]

/-- Spectral projections for disjoint sets have disjoint ranges. -/
theorem disjoint_range_cfc_indicator (hd : Disjoint Ω Ω')
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    Disjoint (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range
      (cfc (Ω'.indicator (1 : ℝ → ℝ)) T).range := by
  set P := cfc (Ω.indicator (1 : ℝ → ℝ)) T
  set Q := cfc (Ω'.indicator (1 : ℝ → ℝ)) T
  have hPQ : P * Q = 0 := cfc_indicator_mul_cfc_indicator_eq_zero hd hΩ hΩ'
  have hP : P * P = P := (TauCeti.isStarProjection_cfc_indicator T Ω).isIdempotentElem
  rw [Submodule.disjoint_def]
  rintro _ ⟨v, rfl⟩ ⟨w, hw⟩
  rw [coe_coe] at hw ⊢
  -- A vector `P v = Q w` in both ranges satisfies `P v = P (P v) = P (Q w) = 0`.
  have hPP : P (P v) = P v := congrArg (fun S ↦ S v) hP
  have hPQw : P (Q w) = 0 := by simpa using congrArg (fun S ↦ S w) hPQ
  calc P v = P (P v) := hPP.symm
    _ = P (Q w) := congrArg P hw.symm
    _ = 0 := hPQw

/-- The spectral projection for a union of two disjoint sets has the sum of the two ranges as its
range. -/
theorem range_cfc_indicator_union (hd : Disjoint Ω Ω')
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    (cfc ((Ω ∪ Ω').indicator (1 : ℝ → ℝ)) T).range =
      (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range ⊔ (cfc (Ω'.indicator (1 : ℝ → ℝ)) T).range := by
  set P := cfc (Ω.indicator (1 : ℝ → ℝ)) T
  set Q := cfc (Ω'.indicator (1 : ℝ → ℝ)) T
  have hsum : cfc ((Ω ∪ Ω').indicator (1 : ℝ → ℝ)) T = P + Q := by
    rw [indicator_union_of_disjoint hd, cfc_add (hf := hΩ) (hg := hΩ')]
  have hPQ : ∀ v, Q (P v) = 0 := fun v ↦ by
    simpa using congrArg (fun S ↦ S v) (cfc_indicator_mul_cfc_indicator_eq_zero hd.symm hΩ' hΩ)
  have hQP : ∀ v, P (Q v) = 0 := fun v ↦ by
    simpa using congrArg (fun S ↦ S v) (cfc_indicator_mul_cfc_indicator_eq_zero hd hΩ hΩ')
  have hP : ∀ v, P (P v) = P v := fun v ↦
    congrArg (fun S ↦ S v) (TauCeti.isStarProjection_cfc_indicator T Ω).isIdempotentElem
  have hQ : ∀ v, Q (Q v) = Q v := fun v ↦
    congrArg (fun S ↦ S v) (TauCeti.isStarProjection_cfc_indicator T Ω').isIdempotentElem
  rw [hsum]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨v, rfl⟩
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨P v, by rw [coe_coe, coe_coe, add_apply, hP, hPQ, add_zero]⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨Q v, by rw [coe_coe, coe_coe, add_apply, hQ, hQP, zero_add]⟩

/-- For disjoint sets with finite-rank spectral projections, the rank of the spectral projection
for their union is the sum of the two ranks. -/
theorem finrank_range_cfc_indicator_union (hd : Disjoint Ω Ω')
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    [FiniteDimensional 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range]
    [FiniteDimensional 𝕜 (cfc (Ω'.indicator (1 : ℝ → ℝ)) T).range] :
    Module.finrank 𝕜 (cfc ((Ω ∪ Ω').indicator (1 : ℝ → ℝ)) T).range =
      Module.finrank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range +
        Module.finrank 𝕜 (cfc (Ω'.indicator (1 : ℝ → ℝ)) T).range := by
  rw [range_cfc_indicator_union hd hΩ hΩ', ← Submodule.finrank_sup_add_finrank_inf_eq,
    (disjoint_range_cfc_indicator hd hΩ hΩ').eq_bot, finrank_bot, add_zero]

end ContinuousLinearMap

end Projection

/-! ### Indicators across the spectral gap at `0` -/

section Gap

variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- At a self-adjoint operator with closed range, such as a self-adjoint Fredholm operator, the
indicator of a set `Ω` is continuous on the spectrum as soon as the frontier of `Ω` meets the
spectrum at most in `0`: by the spectral gap, `0` is isolated in the spectrum if it lies there. -/
theorem IsSelfAdjoint.continuousOn_indicator_spectrum_of_isClosed_range {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (hR : IsClosed (T.range : Set H)) {Ω : Set ℝ}
    (hΩ : frontier Ω ∩ spectrum ℝ T ⊆ {0}) :
    ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T) := by
  obtain ⟨ε, hε, hgap⟩ := hT.exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range hR
  rw [spectrum.preimage_algebraMap] at hgap
  intro x hx
  by_cases hfx : x ∈ frontier Ω
  · obtain rfl : x = 0 := hΩ ⟨hfx, hx⟩
    refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (neg_neg_iff_pos.2 hε) hε),
      self_mem_nhdsWithin] with y hy hys
    rw [mem_singleton_iff.1 (hgap ⟨hys, hy⟩)]
  · exact (continuousOn_const.continuousAt_indicator hfx).continuousWithinAt

end Gap

/-! ### Continuity and rank of spectral projections -/

section Rank

variable [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace IsSelfAdjoint

variable {T : H →L[𝕜] H}

/-- The rank of the spectral projection for a set `Ω` is locally constant on the self-adjoint
operators whose spectrum avoids the frontier of `Ω`: nearby spectral projections are at distance
less than `1`. -/
theorem eventually_rank_range_cfc_indicator_eq (hT : IsSelfAdjoint T) {Ω : Set ℝ}
    (hΩ : Disjoint (frontier Ω) (spectrum ℝ T)) :
    ∀ᶠ S in 𝓝[{S | IsSelfAdjoint S}] T,
      Module.rank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range =
        Module.rank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range := by
  filter_upwards [hT.continuousWithinAt_cfc_indicator hΩ (Metric.ball_mem_nhds _ one_pos)]
    with S hS
  refine Submodule.rank_eq_of_projectionGap_lt_one _ _ ?_
  rw [Submodule.projectionGap_def, ← S.cfc_indicator_eq_starProjection_range Ω,
    ← T.cfc_indicator_eq_starProjection_range Ω, ← dist_eq_norm]
  exact Metric.mem_ball.1 hS

end IsSelfAdjoint

/-- The rank of the spectral projection for a set `Ω` is constant along a continuous path of
self-adjoint operators over a preconnected parameter set, as long as no spectrum along the path
meets the frontier of `Ω`. -/
theorem IsPreconnected.rank_range_cfc_indicator_eq {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {A : X → H →L[𝕜] H} (hA : ContinuousOn A s)
    (hsa : ∀ x ∈ s, IsSelfAdjoint (A x)) {Ω : Set ℝ}
    (hΩ : ∀ x ∈ s, Disjoint (frontier Ω) (spectrum ℝ (A x))) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) :
    Module.rank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) (A x)).range =
      Module.rank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) (A y)).range := by
  have := isPreconnected_iff_preconnectedSpace.mp hs
  let g : s → Cardinal := fun z ↦ Module.rank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) (A z)).range
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hz : Tendsto (fun w : s ↦ A w) (𝓝 z) (𝓝[{S | IsSelfAdjoint S}] (A z)) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuousOn_iff_continuous_domRestrict.1 hA).tendsto z,
        Eventually.of_forall fun w ↦ hsa w w.2⟩
    exact hz.eventually ((hsa z z.2).eventually_rank_range_cfc_indicator_eq (hΩ z z.2))
  exact hg.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

end Rank
