/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import TauCeti.Topology.Algebra.Indicator
import TauCeti.Topology.Order.Interval.Basic

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
* `IsSelfAdjoint.cfc_indicator_singleton_zero_eq_starProjection_ker`: when `0` is not an
  accumulation point of the spectrum, the spectral projection for `{0}` is the projection onto the
  kernel.
* `ContinuousLinearMap.re_inner_apply_self_nonneg_of_mem_range_cfc_indicator` and
  `ContinuousLinearMap.re_inner_apply_self_neg_of_mem_range_cfc_indicator`: the quadratic form
  `x ↦ re ⟪S x, x⟫` of an operator is nonnegative on its spectral subspace for a set of
  nonnegative numbers, and negative definite on that for a set of negative numbers.
* `IsSelfAdjoint.eventually_rank_range_cfc_indicator_eq` and
  `IsPreconnected.rank_range_cfc_indicator_eq`: the rank of the spectral projection is locally
  constant, and constant along paths; `IsPreconnected.finrank_range_cfc_indicator_eq` is the
  `Module.finrank` form of the latter.

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
    calc T * P = cfc (fun x ↦ x * f x) T := (TauCeti.cfc_id_mul f T hf).symm
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
      _ = cfc g T * T := TauCeti.cfc_mul_id g T hg
  -- Hence the range of `P` is the kernel of `T`.
  have hrange : P.range = T.ker := by
    refine le_antisymm ?_ fun v hv ↦ ⟨v, ?_⟩
    · rintro _ ⟨v, rfl⟩
      exact congr($hTP v)
    · have hTv : T v = 0 := LinearMap.mem_ker.1 hv
      have h : v - P v = 0 := by simpa [hTv] using congr($hsub v)
      exact (sub_eq_zero.1 h).symm
  exact (T.cfc_indicator_eq_starProjection_range Ω).trans (Submodule.starProjection_inj.2 hrange)

/-- If `0` is not an accumulation point of the spectrum of a self-adjoint operator `T`, the spectral
projection of `T` for `{0}` is the orthogonal projection onto the kernel of `T`. -/
theorem IsSelfAdjoint.cfc_indicator_singleton_zero_eq_starProjection_ker {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (h0 : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ∉ spectrum ℝ T) :
    cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) T = T.ker.starProjection := by
  -- Some `[-ε, ε]` meets the spectrum at most in `0`, and its endpoints avoid the spectrum.
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h0)
  have hsub : spectrum ℝ T ∩ Icc (-(ε / 2)) (ε / 2) ⊆ {0} := fun x ⟨hxσ, hx₁, hx₂⟩ ↦
    by_contra fun hx0 ↦ hball (by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
      hx0 hxσ
  have h0Ω : (0 : ℝ) ∈ Icc (-(ε / 2)) (ε / 2) := by constructor <;> linarith
  have hfr : Disjoint (frontier (Icc (-(ε / 2)) (ε / 2))) (spectrum ℝ T) :=
    TauCeti.disjoint_frontier_Icc
      (fun h ↦ by linarith [mem_singleton_iff.1 (hsub ⟨h, le_rfl, by linarith⟩)])
      (fun h ↦ by linarith [mem_singleton_iff.1 (hsub ⟨h, by linarith, le_rfl⟩)])
  rw [← hT.cfc_indicator_eq_starProjection_ker h0Ω hsub hfr]
  refine cfc_congr fun x hx ↦ ?_
  by_cases hxΩ : x ∈ Icc (-(ε / 2)) (ε / 2)
  · rw [mem_singleton_iff.1 (hsub ⟨hx, hxΩ⟩), indicator_of_mem (mem_singleton _),
      indicator_of_mem h0Ω]
  · rw [indicator_of_notMem hxΩ, indicator_of_notMem fun h ↦ hxΩ (by rwa [mem_singleton_iff.1 h])]

/-! ### The quadratic form of an operator on its spectral subspaces -/

namespace ContinuousLinearMap

variable (S : H →L[𝕜] H) {Ω : Set ℝ} {x : H}

/-- The spectral projection `E` of `S` for `Ω`, applied twice, is `E`. -/
@[simp]
theorem cfc_indicator_cfc_indicator_apply (Ω : Set ℝ) (y : H) :
    cfc (Ω.indicator (1 : ℝ → ℝ)) S (cfc (Ω.indicator (1 : ℝ → ℝ)) S y) =
      cfc (Ω.indicator (1 : ℝ → ℝ)) S y := by
  simpa using congr($((TauCeti.isStarProjection_cfc_indicator S Ω).isIdempotentElem.eq) y)

/-- **The form of a self-adjoint operator on a nonnegative spectral subspace.** On the range of
the spectral projection `cfc (Ω.indicator 1) S` of an operator `S` for a set `Ω` of nonnegative
numbers, the quadratic form `x ↦ re ⟪S x, x⟫` is nonnegative. (When `S` is not self-adjoint, or
the indicator is not continuous on its spectrum, the projection is `0`.) -/
theorem re_inner_apply_self_nonneg_of_mem_range_cfc_indicator (hΩ : Ω ⊆ Ici 0)
    (hx : x ∈ (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range) : 0 ≤ RCLike.re ⟪S x, x⟫_𝕜 := by
  by_cases h : IsSelfAdjoint S ∧ ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ S)
  swap
  · rw [cfc_apply_of_not_and S h] at hx
    obtain ⟨y, rfl⟩ := hx
    simp
  obtain ⟨hS, hf⟩ := h
  -- `S E = R²` for the spectral projection `E` and `R = cfc (√ ⬝ 1_Ω) S`.
  set r : ℝ → ℝ := Ω.indicator Real.sqrt
  have hr : ContinuousOn r (spectrum ℝ S) :=
    hf.continuousOn_indicator_of_continuousOn_indicator_one fun _ _ ↦
      Real.continuous_sqrt.continuousWithinAt
  have hSE : S * cfc (Ω.indicator (1 : ℝ → ℝ)) S = cfc r S * cfc r S := by
    calc S * cfc (Ω.indicator (1 : ℝ → ℝ)) S
        = cfc (fun y ↦ y * Ω.indicator (1 : ℝ → ℝ) y) S := (TauCeti.cfc_id_mul _ S hf hS).symm
      _ = cfc (fun y ↦ r y * r y) S := cfc_congr fun y _ ↦ by
          by_cases hy : y ∈ Ω
          · simp [r, hy, Real.mul_self_sqrt (hΩ hy)]
          · simp [r, hy]
      _ = cfc r S * cfc r S := cfc_mul r r S hr hr
  obtain ⟨y, hy⟩ := hx
  rw [ContinuousLinearMap.coe_coe] at hy
  subst hy
  set E := cfc (Ω.indicator (1 : ℝ → ℝ)) S
  have hR := (cfc_predicate r S : IsSelfAdjoint (cfc r S)).isSymmetric
  calc (0 : ℝ) ≤ RCLike.re ⟪cfc r S (E y), cfc r S (E y)⟫_𝕜 := inner_self_nonneg
    _ = RCLike.re ⟪(S * E) (E y), E y⟫_𝕜 := by
      rw [hSE, mul_def, ContinuousLinearMap.comp_apply]
      exact congrArg _ (hR _ _).symm
    _ = _ := by rw [mul_def, ContinuousLinearMap.comp_apply, cfc_indicator_cfc_indicator_apply]

/-- **The form of a self-adjoint operator on a negative spectral subspace.** On the range of the
spectral projection `cfc (Ω.indicator 1) S` of an operator `S` for a set `Ω` of negative numbers,
the quadratic form `x ↦ re ⟪S x, x⟫` is negative definite. -/
theorem re_inner_apply_self_neg_of_mem_range_cfc_indicator (hΩ : Ω ⊆ Iio 0)
    (hx : x ∈ (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range) (hx0 : x ≠ 0) :
    RCLike.re ⟪S x, x⟫_𝕜 < 0 := by
  by_cases h : IsSelfAdjoint S ∧ ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ S)
  swap
  · rw [cfc_apply_of_not_and S h] at hx
    obtain ⟨y, rfl⟩ := hx
    exact absurd (by simp) hx0
  obtain ⟨hS, hf⟩ := h
  -- `S E = -R²` for the spectral projection `E` and `R = cfc (√(-·) ⬝ 1_Ω) S`, and `E = R' R` for
  -- `R' = cfc ((√(-·))⁻¹ ⬝ 1_Ω) S`; both functions are continuous on the spectrum, since near a
  -- spectral value the spectrum lies either in `Ω`, where `√(-·)` does not vanish, or outside it.
  set r : ℝ → ℝ := Ω.indicator fun y ↦ √(-y)
  set k : ℝ → ℝ := Ω.indicator fun y ↦ (√(-y))⁻¹
  have hr : ContinuousOn r (spectrum ℝ S) :=
    hf.continuousOn_indicator_of_continuousOn_indicator_one fun _ _ ↦
      (continuous_neg.sqrt).continuousWithinAt
  have hk : ContinuousOn k (spectrum ℝ S) :=
    hf.continuousOn_indicator_of_continuousOn_indicator_one fun y hy ↦
      ((continuous_neg.sqrt.continuousAt).inv₀
        (Real.sqrt_pos.2 (neg_pos.2 (hΩ hy.1))).ne').continuousWithinAt
  have hSE : S * cfc (Ω.indicator (1 : ℝ → ℝ)) S = -(cfc r S * cfc r S) := by
    calc S * cfc (Ω.indicator (1 : ℝ → ℝ)) S
        = cfc (fun y ↦ y * Ω.indicator (1 : ℝ → ℝ) y) S := (TauCeti.cfc_id_mul _ S hf hS).symm
      _ = cfc (fun y ↦ -(r y * r y)) S := cfc_congr fun y _ ↦ by
          by_cases hy : y ∈ Ω
          · simp [r, hy, Real.mul_self_sqrt (neg_nonneg.2 (hΩ hy).le)]
          · simp [r, hy]
      _ = -(cfc r S * cfc r S) := by rw [cfc_neg _ S, cfc_mul r r S hr hr]
  have hEk : cfc (Ω.indicator (1 : ℝ → ℝ)) S = cfc k S * cfc r S := by
    rw [← cfc_mul k r S hk hr]
    refine cfc_congr fun y _ ↦ ?_
    by_cases hy : y ∈ Ω
    · simp [k, r, hy, inv_mul_cancel₀ (Real.sqrt_pos.2 (neg_pos.2 (hΩ hy))).ne']
    · simp [k, r, hy]
  obtain ⟨y, hy⟩ := hx
  rw [ContinuousLinearMap.coe_coe] at hy
  subst hy
  set E := cfc (Ω.indicator (1 : ℝ → ℝ)) S
  have hrx : cfc r S (E y) ≠ 0 := fun h ↦ hx0 <| by
    rw [← cfc_indicator_cfc_indicator_apply, congr($hEk (E y)), mul_def,
      ContinuousLinearMap.comp_apply, h, map_zero]
  have hR := (cfc_predicate r S : IsSelfAdjoint (cfc r S)).isSymmetric
  calc RCLike.re ⟪S (E y), E y⟫_𝕜 = RCLike.re ⟪(S * E) (E y), E y⟫_𝕜 := by
        rw [mul_def, ContinuousLinearMap.comp_apply, cfc_indicator_cfc_indicator_apply]
    _ = -RCLike.re ⟪cfc r S (E y), cfc r S (E y)⟫_𝕜 := by
        rw [hSE, neg_apply, mul_def, ContinuousLinearMap.comp_apply, inner_neg_left, map_neg]
        exact congrArg (fun z ↦ -RCLike.re z) (hR _ _)
    _ < 0 := neg_neg_iff_pos.2 (re_inner_self_pos.2 hrx)

end ContinuousLinearMap

end Projection

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
        Eventually.of_forall fun w ↦ hsa w w.property⟩
    exact hz.eventually ((hsa z z.property).eventually_rank_range_cfc_indicator_eq
        (hΩ z z.property))
  exact hg.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- The finite rank of the spectral projection for a set `Ω` is constant along a continuous path of
self-adjoint operators over a preconnected parameter set, as long as no spectrum along the path
meets the frontier of `Ω`. -/
theorem IsPreconnected.finrank_range_cfc_indicator_eq {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {A : X → H →L[𝕜] H} (hA : ContinuousOn A s)
    (hsa : ∀ x ∈ s, IsSelfAdjoint (A x)) {Ω : Set ℝ}
    (hΩ : ∀ x ∈ s, Disjoint (frontier Ω) (spectrum ℝ (A x))) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) :
    Module.finrank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) (A x)).range =
      Module.finrank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) (A y)).range := by
  rw [Module.finrank, Module.finrank, hs.rank_range_cfc_indicator_eq hA hsa hΩ hx hy]

end Rank
