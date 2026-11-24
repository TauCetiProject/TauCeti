/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval

/-!
# Closed derivative graphs for bounded continuous functions

The Fréchet derivative identity is closed under uniform convergence of bounded continuous value
and derivative fields. The derivative field may be read through a uniformly continuous map.
These results supply the closed graph used to construct complete spaces of differentiable maps.
For fields on an open set, the value field is extended by zero, which does not change its
derivatives at points of the set.
The corresponding one-dimensional graph on a closed interval includes the one-sided derivatives
at both endpoints.

On a convex set, which need not be open, a locally uniform limit of derivatives within the set is
the derivative within the set of the pointwise limit
(`Convex.hasFDerivWithinAt_of_tendstoLocallyUniformlyOn`). This is the version of Mathlib's
`hasFDerivAt_of_tendstoLocallyUniformlyOn` needed on closed half-spaces and orthants, where the
mean value inequality along segments inside the set replaces the open balls of Mathlib's proof.

The proofs use Mathlib's `hasFDerivAt_of_tendstoUniformly` and
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`.
-/

public section

namespace TauCeti

open Filter Topology
open scoped BoundedContinuousFunction

universe u v

/-- **Uniform limits of derivatives on a convex set.** On a convex set `s`, if the derivatives
within `s` of a family of functions converge locally uniformly on `s` and the functions converge
pointwise on `s`, then the limit function has the limit derivative within `s` at every point of
`s`. Unlike `hasFDerivAt_of_tendstoLocallyUniformlyOn`, the set need not be open. -/
theorem _root_.Convex.hasFDerivWithinAt_of_tendstoLocallyUniformlyOn {𝕜 E G ι : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {s : Set E} (hs : Convex ℝ s)
    {l : Filter ι} [l.NeBot] {f : ι → E → G} {g : E → G} {f' : ι → E → E →L[𝕜] G}
    {g' : E → E →L[𝕜] G} (hf' : TendstoLocallyUniformlyOn f' g' l s)
    (hf : ∀ i, ∀ y ∈ s, HasFDerivWithinAt (f i) (f' i y) s y)
    (hfg : ∀ y ∈ s, Tendsto (fun i ↦ f i y) l (𝓝 (g y))) {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt g (g' x) s x := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set δ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  -- On a convex neighbourhood `c` of `x` in `s`, the derivatives are eventually `δ`-close
  -- to their limit.
  obtain ⟨t, ht, hunif⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp hf' δ hδ0 x hx
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.mp ht
  set c := s ∩ Metric.ball x r
  have hcc : Convex ℝ c := hs.inter (convex_ball x r)
  have hxc : x ∈ c := ⟨hx, Metric.mem_ball_self hr⟩
  -- For such an index `i`, the increments of `f i - g` on `c` are `2δ`-Lipschitz at `x`.
  have hinc : ∀ᶠ i in l, ∀ y ∈ c, ‖(f i y - g y) - (f i x - g x)‖ ≤ 2 * δ * ‖y - x‖ := by
    filter_upwards [hunif] with i hi y hy
    refine le_of_tendsto (((tendsto_const_nhds.sub (hfg y hy.1)).sub
      (tendsto_const_nhds.sub (hfg x hx))).norm) ?_
    filter_upwards [hunif] with j hj
    refine hcc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z ↦ f i z - f j z) (f' := fun z ↦ f' i z - f' j z)
      (fun z (hz : z ∈ c) ↦ ((hf i z hz.1).sub (hf j z hz.1)).mono Set.inter_subset_left)
      (fun z (hz : z ∈ c) ↦ ?_) hxc hy
    have h₁ := hi z (hrt ⟨hz.2, hz.1⟩)
    have h₂ := hj z (hrt ⟨hz.2, hz.1⟩)
    rw [dist_comm, dist_eq_norm] at h₁
    rw [dist_eq_norm] at h₂
    linarith [norm_sub_le_norm_sub_add_norm_sub (f' i z) (g' z) (f' j z)]
  -- Fix one such index and use the differentiability of `f i` at `x`.
  obtain ⟨i, hi, hiu⟩ := (hinc.and hunif).exists
  have hfi := hf i x hx
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hfi
  filter_upwards [hfi hδ0, inter_mem_nhdsWithin s (Metric.ball_mem_nhds x hr)] with y hy hyc
  have hlin : ‖(f' i x - g' x) (y - x)‖ ≤ δ * ‖y - x‖ := by
    have hx' := (hiu x (hrt ⟨hxc.2, hxc.1⟩)).le
    rw [dist_comm, dist_eq_norm] at hx'
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
  have hsplit : g y - g x - g' x (y - x) = (f i y - f i x - f' i x (y - x))
      - ((f i y - g y) - (f i x - g x)) + (f' i x - g' x) (y - x) := by
    simp only [sub_apply]
    abel
  rw [hsplit]
  have h₁ := norm_add_le (f i y - f i x - f' i x (y - x) - ((f i y - g y) - (f i x - g x)))
    ((f' i x - g' x) (y - x))
  have h₂ := norm_sub_le (f i y - f i x - f' i x (y - x)) ((f i y - g y) - (f i x - g x))
  have h₃ : ε * ‖y - x‖ = 4 * (δ * ‖y - x‖) := by rw [hδ]; ring
  linarith [hi y hyc]

/-- The set of bounded continuous fields satisfying a Fréchet derivative identity, with the
derivative read off the second field through a uniformly continuous map, is closed. -/
theorem isClosed_setOf_hasFDerivAt_comp {𝕜 : Type*} {E : Type u} {Y Z : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [PseudoMetricSpace Z]
    (L : Z → E →L[𝕜] Y) (hL : UniformContinuous L) :
    IsClosed {J : (E →ᵇ Y) × (E →ᵇ Z) | ∀ x, HasFDerivAt (J.1 : E → Y) (L (J.2 x)) x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim x
  apply hasFDerivAt_of_tendstoUniformly
      (f := fun n ↦ (J n).1) (f' := fun n y ↦ L ((J n).2 y))
      (g := j.1) (g' := fun y ↦ L (j.2 y)) (l := atTop)
  · exact hL.comp_tendstoUniformly
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
        ((continuous_snd.tendsto j).comp hjlim))
  · intro n y
    exact hJ n y
  · intro y
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_fst.tendsto j).comp hjlim)).tendsto_at y

/-- The set of bounded continuous fields satisfying the Fréchet derivative identity is closed. -/
theorem isClosed_setOf_hasFDerivAt {𝕜 : Type*} {E : Type u} {Y : Type v}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    IsClosed {J : (E →ᵇ Y) × (E →ᵇ (E →L[𝕜] Y)) |
      ∀ x, HasFDerivAt (J.1 : E → Y) (J.2 x) x} :=
  isClosed_setOf_hasFDerivAt_comp id uniformContinuous_id

/-- On an open set `s`, the set of bounded continuous fields on `s` satisfying a Fréchet derivative
identity at every point of `s` is closed. The value field is extended by zero outside `s`, which
does not affect derivatives at points of the open set, and the derivative is read off the second
field through a uniformly continuous map. -/
theorem isClosed_setOf_hasFDerivAt_extend_comp {𝕜 : Type*} {E : Type u} {Y Z : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [PseudoMetricSpace Z] {s : Set E} (hs : IsOpen s)
    (L : Z → E →L[𝕜] Y) (hL : UniformContinuous L) :
    IsClosed {J : (s →ᵇ Y) × (s →ᵇ Z) |
      ∀ x : s, HasFDerivAt (Function.extend Subtype.val (J.1 : s → Y) 0) (L (J.2 x)) x} := by
  classical
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim x
  -- The derivative fields, extended by zero outside `s`.
  let D : (s →ᵇ Z) → E → E →L[𝕜] Y := fun B y ↦ if h : y ∈ s then L (B ⟨y, h⟩) else 0
  have hD : ∀ (B : s →ᵇ Z) (y : s), D B y = L (B y) := fun B y ↦ dite_eq_left y.property
  have hext : ∀ (g : s → Y) (y : s), Function.extend Subtype.val g 0 (y : E) = g y :=
    fun g y ↦ Subtype.val_injective.extend_apply g 0 y
  have hv := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_fst.tendsto j).comp hjlim)
  have hd := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_snd.tendsto j).comp hjlim)
  rw [← hD]
  refine hasFDerivAt_of_tendstoUniformlyOn
    (f := fun n ↦ Function.extend Subtype.val ((J n).1 : s → Y) 0) (f' := fun n ↦ D (J n).2)
    (g' := D j.2) (l := atTop) hs ?_ ?_ ?_ x.property
  · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [Function.comp_def, hD] using hL.comp_tendstoUniformly hd
  · intro n y hy
    lift y to s using hy
    rw [hD]
    exact hJ n y
  · intro y hy
    lift y to s using hy
    simp only [hext]
    exact hv.tendsto_at y

/-- The derivative graph of bounded continuous fields on a nondegenerate closed interval is
closed, including the one-sided derivative identities at its endpoints. The value field is
extended outside the interval by projection onto the interval. -/
theorem isClosed_setOf_hasDerivWithinAt_Icc {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} (hab : a < b) :
    IsClosed {J : (Set.Icc a b →ᵇ F) × (Set.Icc a b →ᵇ F) |
      ∀ t : Set.Icc a b,
        HasDerivWithinAt (fun s : ℝ ↦ J.1 (Set.projIcc a b hab.le s))
          (J.2 t) (Set.Icc a b) t} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim t
  have hv := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_fst.tendsto j).comp hjlim)).comp (Set.projIcc a b hab.le)
  have hd := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_snd.tendsto j).comp hjlim)).comp (Set.projIcc a b hab.le)
  have hinter : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun s : ℝ ↦ j.1 (Set.projIcc a b hab.le s))
        (j.2 (Set.projIcc a b hab.le x)) x := by
    intro x hx
    apply hasDerivAt_of_tendstoUniformlyOn
      (f := fun n s ↦ (J n).1 (Set.projIcc a b hab.le s))
      isOpen_Ioo hd.tendstoUniformlyOn _ _ hx
    · filter_upwards [] with n y hy
      have h := (hJ n ⟨y, Set.Ioo_subset_Icc_self hy⟩).hasDerivAt
        (Icc_mem_nhds hy.1 hy.2)
      simpa only [Function.comp_def, Set.projIcc_of_mem hab.le
        (Set.Ioo_subset_Icc_self hy)] using h
    · intro y _
      exact hv.tendsto_at y
  simpa only [Function.comp_def, Set.projIcc_val] using
    hasDerivWithinAt_Icc_of_continuousOn
      (j.1.continuous.comp continuous_projIcc).continuousOn
      (j.2.continuous.comp continuous_projIcc).continuousOn hinter t.property

end TauCeti
