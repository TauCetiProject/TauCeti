/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Riemannian
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.VectorBundle.Hom

/-!
# Uniform comparison of metrics over compact sets

In a continuous Riemannian vector bundle, a continuously varying family of bilinear forms on the
fibres has locally bounded operator norm for the given fibre inner products, so it is uniformly
bounded over a compact set. When the fibres are finite-dimensional, a continuous family that is
positive definite at every point of a compact set is moreover uniformly coercive there:
`c ‖v‖² ≤ φ v v` for one constant `c > 0`. The families may lie over a map `b : X → B`, so that a
parameter of the family, such as the time of a family of metrics, can be part of the compact set.

For two continuous Riemannian metrics `g` and `g₀` on the same bundle this gives, over every
compact subset `K` of the base, constants `0 < λ` and `0 < Λ` with `λ g₀ ≤ g ≤ Λ g₀` on the fibres
over `K`. The upper bound is the operator norm bound for `g` with `g₀` installed as the fibre inner
product, and the lower bound is the upper bound for `g₀` with `g` installed. In particular, on a
compact base every continuous metric is uniformly equivalent to a fixed reference metric, which is
how norms of tensor fields measured by different metrics, or by the metrics of a family at
different times, are compared.

Each local bound is read off in the trivialization at a point, where the family of forms has
continuous coordinates and the trivialization and its inverse are locally bounded in norm. This
follows the coordinate argument of Mathlib's `eventually_norm_symmL_trivializationAt_self_comp_lt`.
The upper bounds need no finite dimensionality; the coercivity of the coordinate form at the
point uses `IsCompact.exists_pos_forall_mul_norm_sq_le` on the finite-dimensional model fibre.

## Main results

* `ContinuousWithinAt.exists_eventually_norm_le_bundle` and
  `IsCompact.exists_bound_of_continuousOn_bundle`: a continuous family of bilinear forms has
  locally bounded operator norm, and bounded operator norm on a compact set.
* `ContinuousWithinAt.exists_pos_eventually_mul_norm_sq_le_bundle` and
  `IsCompact.exists_pos_forall_mul_norm_sq_le_bundle`: a continuous family of positive definite
  bilinear forms on finite-dimensional fibres is locally uniformly coercive, and uniformly
  coercive on a compact set.
* `Bundle.ContinuousRiemannianMetric.exists_inner_le_mul_inner`: `g ≤ Λ g₀` over a compact set.
* `Bundle.ContinuousRiemannianMetric.exists_mul_inner_le_inner_and_inner_le_mul_inner`:
  `λ g₀ ≤ g ≤ Λ g₀` over a compact set.
-/

public section

open Bundle Filter Set ContinuousLinearMap
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]

section Norm

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {X : Type*} [TopologicalSpace X] {b : X → B} {φ : ∀ y, E (b y) →L[ℝ] E (b y) →L[ℝ] ℝ}

omit [IsContinuousRiemannianBundle F E] in
/-- Over the base set of the trivialization at `x₀`, an `ℝ`-valued bilinear form on a fibre is its
coordinate form evaluated on the coordinates of its arguments. -/
private theorem apply_eq_inCoordinates_apply {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet) (ψ : E x →L[ℝ] E x →L[ℝ] ℝ) (v w : E x) :
    ψ v w = inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x₀ x x₀ x ψ
      ((trivializationAt F E x₀).continuousLinearMapAt ℝ x v)
      ((trivializationAt F E x₀).continuousLinearMapAt ℝ x w) := by
  rw [inCoordinates_apply_continuousLinearMapAt₂ (E₃ := Bundle.Trivial B ℝ) hx hx]
  simp

/-- **Local boundedness of a continuous family of bilinear forms.** In a continuous Riemannian
bundle, a family of bilinear forms on the fibres over a map `b`, continuous within `s` at `y₀`, has
operator norm bounded on a neighbourhood of `y₀` within `s`. -/
theorem ContinuousWithinAt.exists_eventually_norm_le_bundle {s : Set X} {y₀ : X}
    (hφ : ContinuousWithinAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) (b y) (φ y)) s y₀) :
    ∃ C, ∀ᶠ y in 𝓝[s] y₀, ‖φ y‖ ≤ C := by
  rw [continuousWithinAt_hom_bundle] at hφ
  obtain ⟨hb, hG⟩ := hφ
  set e := trivializationAt F E (b y₀)
  -- `G y` is the form `φ y` read in the trivialization `e` at `b y₀`.
  set G : X → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) (b y₀) (b y) (b y₀) (b y) (φ y)
  obtain ⟨C, hC, hCe⟩ := eventually_norm_trivializationAt_lt F E (b y₀)
  have hbase : ∀ᶠ y in 𝓝[s] y₀, b y ∈ e.baseSet :=
    hb.eventually_mem (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  refine ⟨(‖G y₀‖ + 1) * C * C, ?_⟩
  filter_upwards [hb.eventually hCe, hbase, hG.norm.eventually (gt_mem_nhds (lt_add_one _))]
    with y hyC hyb hyG
  refine opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  have hev (u : E (b y)) : ‖e.continuousLinearMapAt ℝ (b y) u‖ ≤ C * ‖u‖ :=
    le_of_opNorm_le _ hyC.le u
  rw [apply_eq_inCoordinates_apply hyb]
  calc ‖G y (e.continuousLinearMapAt ℝ (b y) v) (e.continuousLinearMapAt ℝ (b y) w)‖
      ≤ ‖G y‖ * ‖e.continuousLinearMapAt ℝ (b y) v‖ * ‖e.continuousLinearMapAt ℝ (b y) w‖ :=
        le_opNorm₂ _ _ _
    _ ≤ (‖G y₀‖ + 1) * (C * ‖v‖) * (C * ‖w‖) := by
        gcongr
        exacts [hev v, hev w]
    _ = (‖G y₀‖ + 1) * C * C * ‖v‖ * ‖w‖ := by ring

/-- **A continuous family of bilinear forms is bounded on a compact set.** In a continuous
Riemannian bundle, a family of bilinear forms on the fibres over a map `b`, continuous on a compact
set `K`, has operator norm bounded on `K`. -/
theorem IsCompact.exists_bound_of_continuousOn_bundle {K : Set X} (hK : IsCompact K)
    (hφ : ContinuousOn (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) (b y) (φ y)) K) :
    ∃ C, ∀ y ∈ K, ‖φ y‖ ≤ C := by
  refine hK.induction_on (p := fun t ↦ ∃ C, ∀ y ∈ t, ‖φ y‖ ≤ C) ⟨0, fun _ h ↦ h.elim⟩
    (fun _ _ hst ⟨C, hC⟩ ↦ ⟨C, fun y hy ↦ hC y (hst hy)⟩)
    (fun _ _ ⟨C, hC⟩ ⟨D, hD⟩ ↦ ⟨max C D, fun y hy ↦ hy.elim
      (fun hy ↦ (hC y hy).trans (le_max_left _ _)) fun hy ↦ (hD y hy).trans (le_max_right _ _)⟩)
    fun y hy ↦ ?_
  obtain ⟨C, hC⟩ := (hφ y hy).exists_eventually_norm_le_bundle
  exact ⟨_, hC, C, fun _ h ↦ h⟩

variable [FiniteDimensional ℝ F]

/-- **Local uniform coercivity of a continuous family of bilinear forms.** In a continuous
Riemannian bundle with finite-dimensional fibres, let a family of bilinear forms on the fibres over
a map `b` be continuous within `s` at `y₀`, and positive definite at `y₀`. Then one constant
`c > 0` gives `c ‖v‖² ≤ φ y v v` for every `y` in a neighbourhood of `y₀` within `s`. -/
theorem ContinuousWithinAt.exists_pos_eventually_mul_norm_sq_le_bundle {s : Set X} {y₀ : X}
    (hφ : ContinuousWithinAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) (b y) (φ y)) s y₀)
    (hpos : ∀ v, v ≠ 0 → 0 < φ y₀ v v) :
    ∃ c > 0, ∀ᶠ y in 𝓝[s] y₀, ∀ v, c * ‖v‖ ^ 2 ≤ φ y v v := by
  rw [continuousWithinAt_hom_bundle] at hφ
  obtain ⟨hb, hG⟩ := hφ
  set e := trivializationAt F E (b y₀)
  set G : X → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) (b y₀) (b y) (b y₀) (b y) (φ y)
  have hy₀ : b y₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  -- The coordinate form at `y₀` is positive definite on the finite-dimensional model fibre.
  obtain ⟨c, hc, hcG⟩ := (isCompact_singleton (x := y₀)).exists_pos_forall_mul_norm_sq_le
    (continuousOn_singleton G y₀) fun y hy w hw ↦ by
      rw [mem_singleton_iff.1 hy]
      have hw' : e.symmL ℝ (b y₀) w ≠ 0 := by
        intro h
        have hsymm := e.continuousLinearMapAt_symmL (R := ℝ) hy₀ w
        rw [h, map_zero] at hsymm
        exact hw hsymm.symm
      have := hpos _ hw'
      rwa [apply_eq_inCoordinates_apply hy₀, e.continuousLinearMapAt_symmL (R := ℝ) hy₀] at this
  have hcG₀ (w : F) : c * ‖w‖ ^ 2 ≤ G y₀ w w := hcG y₀ rfl w
  obtain ⟨C, hC, hCe⟩ := eventually_norm_symmL_trivializationAt_lt F E (b y₀)
  have hbase : ∀ᶠ y in 𝓝[s] y₀, b y ∈ e.baseSet :=
    hb.eventually_mem (e.open_baseSet.mem_nhds hy₀)
  refine ⟨c / 2 / C ^ 2, by positivity, ?_⟩
  have hclose : ∀ᶠ y in 𝓝[s] y₀, ‖G y - G y₀‖ < c / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hG.tendsto).eventually (gt_mem_nhds (half_pos hc))
  filter_upwards [hb.eventually hCe, hbase, hclose] with y hyC hyb hyG v
  have hv : ‖v‖ ≤ C * ‖e.continuousLinearMapAt ℝ (b y) v‖ := by
    have h := le_of_opNorm_le _ hyC.le (e.continuousLinearMapAt ℝ (b y) v)
    rwa [e.symmL_continuousLinearMapAt (R := ℝ) hyb v] at h
  have hGw (w : F) : c / 2 * ‖w‖ ^ 2 ≤ G y w w := by
    have hdiff : |(G y - G y₀) w w| ≤ c / 2 * ‖w‖ ^ 2 := by
      rw [← Real.norm_eq_abs, sq, ← mul_assoc]
      exact (le_opNorm₂ _ _ _).trans (by gcongr)
    have hsplit : G y w w = G y₀ w w + (G y - G y₀) w w := by simp
    linarith [hcG₀ w, neg_abs_le ((G y - G y₀) w w)]
  rw [apply_eq_inCoordinates_apply hyb]
  calc c / 2 / C ^ 2 * ‖v‖ ^ 2
      ≤ c / 2 / C ^ 2 * (C * ‖e.continuousLinearMapAt ℝ (b y) v‖) ^ 2 := by gcongr
    _ = c / 2 * ‖e.continuousLinearMapAt ℝ (b y) v‖ ^ 2 := by field_simp
    _ ≤ _ := hGw _

/-- **Uniform coercivity of a continuous family of bilinear forms on a compact set.** In a
continuous Riemannian bundle with finite-dimensional fibres, let a family of bilinear forms on the
fibres over a map `b` be continuous on a compact set `K` and positive definite at every point of
`K`. Then one constant `c > 0` gives `c ‖v‖² ≤ φ y v v` for every `y ∈ K`. Symmetry of the forms
is not needed. -/
theorem IsCompact.exists_pos_forall_mul_norm_sq_le_bundle {K : Set X} (hK : IsCompact K)
    (hφ : ContinuousOn (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) (b y) (φ y)) K)
    (hpos : ∀ y ∈ K, ∀ v, v ≠ 0 → 0 < φ y v v) :
    ∃ c > 0, ∀ y ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ φ y v v := by
  refine hK.induction_on (p := fun t ↦ ∃ c > 0, ∀ y ∈ t, ∀ v, c * ‖v‖ ^ 2 ≤ φ y v v)
    ⟨1, one_pos, fun _ h ↦ h.elim⟩
    (fun _ _ hst ⟨c, hc, hle⟩ ↦ ⟨c, hc, fun y hy ↦ hle y (hst hy)⟩)
    (fun _ _ ⟨c, hc, hle⟩ ⟨d, hd, hle'⟩ ↦ ⟨min c d, lt_min hc hd, fun y hy v ↦ hy.elim
      (fun hy ↦ (mul_le_mul_of_nonneg_right (min_le_left c d) (by positivity)).trans (hle y hy v))
      fun hy ↦ (mul_le_mul_of_nonneg_right (min_le_right c d) (by positivity)).trans
        (hle' y hy v)⟩)
    fun y hy ↦ ?_
  obtain ⟨c, hc, hle⟩ := (hφ y hy).exists_pos_eventually_mul_norm_sq_le_bundle (hpos y hy)
  exact ⟨_, hle, c, hc, fun _ h ↦ h⟩

end Norm

namespace Bundle.ContinuousRiemannianMetric

variable [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **A metric is bounded by a multiple of another over a compact set.** For two continuous
Riemannian metrics `g` and `g₀` on a vector bundle and a compact subset `K` of the base, there is
`0 < Λ` with `g ≤ Λ g₀` on the fibres over `K`. -/
theorem exists_inner_le_mul_inner (g g₀ : ContinuousRiemannianMetric F E) {K : Set B}
    (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, ∀ v : E x, g.inner x v v ≤ C * g₀.inner x v v := by
  let _ : RiemannianBundle E := ⟨g₀.toRiemannianMetric⟩
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn_bundle (b := id) (φ := g.inner) g.continuous.continuousOn
  refine ⟨max C 1, by positivity, fun x hx v ↦ ?_⟩
  -- The squared norm of `v` for the installed metric is `g₀.inner x v v`.
  have hv : ‖v‖ ^ 2 = g₀.inner x v v := (real_inner_self_eq_norm_sq v).symm
  have hop := (le_opNorm₂ (g.inner x) v v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left C 1))
      (norm_nonneg v)) (norm_nonneg v))
  calc g.inner x v v ≤ ‖g.inner x v v‖ := Real.le_norm_self _
    _ ≤ max C 1 * ‖v‖ ^ 2 := by rw [sq, ← mul_assoc]; exact hop
    _ = max C 1 * g₀.inner x v v := by rw [hv]

/-- **Uniform equivalence of metrics over a compact set.** For two continuous Riemannian metrics
`g` and `g₀` on a vector bundle and a compact subset `K` of the base, there are `0 < λ` and `0 < Λ`
with `λ g₀ ≤ g ≤ Λ g₀` on the fibres over `K`. -/
theorem exists_mul_inner_le_inner_and_inner_le_mul_inner (g g₀ : ContinuousRiemannianMetric F E)
    {K : Set B} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v := by
  obtain ⟨C, hC, hgg₀⟩ := g.exists_inner_le_mul_inner g₀ hK
  obtain ⟨D, hD, hg₀g⟩ := g₀.exists_inner_le_mul_inner g hK
  refine ⟨D⁻¹, inv_pos.2 hD, C, hC, fun x hx v ↦ ⟨?_, hgg₀ x hx v⟩⟩
  rw [inv_mul_le_iff₀ hD]
  exact hg₀g x hx v

end Bundle.ContinuousRiemannianMetric
