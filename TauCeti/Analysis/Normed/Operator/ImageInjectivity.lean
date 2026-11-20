/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Injectivity on varying ranges of idempotents

If `p` and `q` are idempotents with `‖q - p‖ < 1` and `p` has finite-dimensional range, then
`q` restricts to an isomorphism from the range of `p` onto the range of `q`. In fact `q` is
injective on the range of `p`: on that range it differs from the inclusion by an operator of
norm less than one. Swapping `p` and `q` gives an injection in the other direction, so the two
ranges have the same finite dimension.

Thus for continuous families of operators `L` and idempotents `P`, injectivity of `L x` on a
finite-dimensional range of `P x` persists locally. No ambient completeness is needed.
-/

public section

open ContinuousLinearMap Filter Function Set Topology

namespace ContinuousLinearMap.IsIdempotentElem

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p q : E →L[𝕜] E}

/-- An operator at distance less than one from an idempotent is injective on its range. -/
theorem injOn_range_of_norm_sub_lt_one (hp : IsIdempotentElem p) (h : ‖q - p‖ < 1) :
    InjOn q p.range := by
  refine injOn_iff_injective.mpr ((injective_iff_map_eq_zero (q.domRestrict p.range)).mpr ?_)
  intro v hv
  suffices (v : E) = 0 by exact Subtype.ext this
  by_contra hne
  have hbound := (q - p).le_opNorm (v : E)
  have hv' : q (v : E) = 0 := hv
  rw [sub_apply, hp.apply_coe_range, hv', zero_sub, norm_neg] at hbound
  exact (not_le_of_gt (mul_lt_of_lt_one_left (norm_pos_iff.mpr hne) h)) hbound

/-- If two idempotents differ by less than one and the first has finite rank, the second maps
the range of the first bijectively onto its own range. -/
theorem bijective_rangeRestrict_comp_subtypeL_of_norm_sub_lt_one (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) [FiniteDimensional 𝕜 p.range] (h : ‖q - p‖ < 1) :
    Bijective (q.rangeRestrict ∘L p.range.subtypeL) := by
  let f := q.rangeRestrict ∘L p.range.subtypeL
  let g := p.rangeRestrict ∘L q.range.subtypeL
  have hf : Injective f := fun a b hab ↦ Subtype.ext
    (hp.injOn_range_of_norm_sub_lt_one h a.property b.property (congrArg Subtype.val hab))
  have hg : Injective g := fun a b hab ↦ Subtype.ext
    (hq.injOn_range_of_norm_sub_lt_one (by rwa [norm_sub_rev])
      a.property b.property (congrArg Subtype.val hab))
  let : FiniteDimensional 𝕜 q.range := FiniteDimensional.of_injective g.toLinearMap hg
  have hdim := le_antisymm (LinearMap.finrank_le_finrank_of_injective hf)
    (LinearMap.finrank_le_finrank_of_injective hg)
  exact ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hdim).mp hf⟩

end ContinuousLinearMap.IsIdempotentElem

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {P : X → E →L[𝕜] E} {L : X → E →L[𝕜] F} {x : X}

/-- A continuous family of idempotents near a finite-rank idempotent `P x` identifies the fixed
range `(P x).range` with each nearby range by applying `P y` to it. -/
theorem ContinuousAt.eventually_bijective_rangeRestrict_comp_subtypeL
    (hP : ContinuousAt P x) (hidem : ∀ᶠ y in 𝓝 x, IsIdempotentElem (P y))
    [FiniteDimensional 𝕜 (P x).range] :
    ∀ᶠ y in 𝓝 x, Bijective ((P y).rangeRestrict ∘L (P x).range.subtypeL) := by
  have hx : IsIdempotentElem (P x) := hidem.self_of_nhds
  have hnear : ∀ᶠ y in 𝓝 x, P y ∈ Metric.ball (P x) 1 :=
    hP (Metric.ball_mem_nhds (P x) one_pos)
  filter_upwards [hidem, hnear] with y hy hdist
  exact hx.bijective_rangeRestrict_comp_subtypeL_of_norm_sub_lt_one hy
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hdist)

variable [CompleteSpace 𝕜]

/-- Injectivity on the finite-dimensional range of `P x` persists on the nearby ranges of a
continuous family of idempotents. -/
theorem ContinuousAt.eventually_injOn_range (hL : ContinuousAt L x) (hP : ContinuousAt P x)
    (hidem : ∀ᶠ y in 𝓝 x, IsIdempotentElem (P y)) [FiniteDimensional 𝕜 (P x).range]
    (hinj : InjOn (L x) (P x).range) : ∀ᶠ y in 𝓝 x, InjOn (L y) (P y).range := by
  let A (y : X) := L y ∘L (P y ∘L (P x).range.subtypeL)
  have hA : ContinuousAt A x := hL.clm_comp (hP.clm_comp continuousAt_const)
  have hx : IsIdempotentElem (P x) := hidem.self_of_nhds
  have hinj' : Injective (L x ∘L (P x).range.subtypeL) := hinj.injective
  have hinjA : Injective (A x) := by simpa only [A, hx.comp_subtypeL] using hinj'
  have hAinj : ∀ᶠ y in 𝓝 x, Injective (A y) := hA (isOpen_injective.mem_nhds hinjA)
  filter_upwards [hAinj, hP.eventually_bijective_rangeRestrict_comp_subtypeL hidem] with y hy hbij
  have hinjComp : Injective (((P y).range : Set E).domRestrict (L y) ∘
      (⇑((P y).rangeRestrict ∘L (P x).range.subtypeL))) := hy
  exact injOn_iff_injective.mpr (hinjComp.of_comp_right hbij.surjective)

/-- Injectivity on the ranges of a continuous family of finite-rank idempotents is an open
condition. -/
theorem Continuous.isOpen_injOn_range (hL : Continuous L) (hP : Continuous P)
    (hidem : ∀ y, IsIdempotentElem (P y)) [∀ y, FiniteDimensional 𝕜 (P y).range] :
    IsOpen {y | InjOn (L y) (P y).range} :=
  isOpen_iff_mem_nhds.mpr fun _ hy ↦ hL.continuousAt.eventually_injOn_range
    hP.continuousAt (Eventually.of_forall hidem) hy
