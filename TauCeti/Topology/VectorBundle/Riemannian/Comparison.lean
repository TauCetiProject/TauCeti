/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Riemannian
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.VectorBundle.Bilinear
import TauCeti.Topology.VectorBundle.Hom

/-!
# Uniform comparison of metrics over compact sets

For continuous Riemannian vector bundles `E₁` and `E₂`, a continuously varying family of bilinear
maps from the fibres of `E₁` and `E₂` to a normed space has locally bounded operator norm for the
given fibre inner products, so it is uniformly bounded over a compact set. For bilinear forms on
the fibres of one bundle with finite-dimensional fibres, a continuous family that is positive
definite at every point of a compact set is moreover uniformly coercive there:
`c ‖v‖² ≤ φ v v` for one constant `c > 0`. The families may lie over a map `b : X → B`, so that a
parameter of the family, such as the time of a family of metrics, can be part of the compact set.

For two continuous Riemannian metrics `g` and `g₀` on the same bundle this gives, over every
compact subset `K` of the base, constants `0 < λ` and `0 < Λ` with `λ g₀ ≤ g ≤ Λ g₀` on the fibres
over `K`. The upper bound is the operator norm bound for `g` with `g₀` installed as the fibre inner
product, and the lower bound is the upper bound for `g₀` with `g` installed. In particular, on a
compact base every continuous metric is uniformly equivalent to a fixed reference metric, which is
how norms of tensor fields measured by different metrics, or by the metrics of a family at
different times, are compared.

Each local bound is read off in the trivializations at a point, where the family has continuous
coordinates and the trivializations and their inverses are locally bounded in norm. This follows
the coordinate argument of Mathlib's `eventually_norm_symmL_trivializationAt_self_comp_lt`.
The upper bounds need no finite dimensionality; the coercivity of the coordinate form at the
point uses `IsCompact.exists_pos_forall_mul_norm_sq_le` on the finite-dimensional model fibre.

## Main results

* `ContinuousWithinAt.exists_eventually_norm_le_bilinear_bundle` and
  `IsCompact.exists_bound_of_continuousOn_bilinear_bundle`: a continuous family of bilinear maps
  on the fibres of two continuous Riemannian bundles has locally bounded operator norm, and
  bounded operator norm on a compact set.
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

variable {X : Type*} [TopologicalSpace X] {b : X → B}

section Bound

variable
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] {E₁ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, NormedAddCommGroup (E₁ x)]
  [∀ x, InnerProductSpace ℝ (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [IsContinuousRiemannianBundle F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, NormedAddCommGroup (E₂ x)]
  [∀ x, InnerProductSpace ℝ (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsContinuousRiemannianBundle F₂ E₂]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {φ : ∀ y, E₁ (b y) →L[ℝ] E₂ (b y) →L[ℝ] G}

/-- **Local boundedness of a continuous family of bilinear maps.** For continuous Riemannian
bundles `E₁` and `E₂`, a family of bilinear maps `E₁ × E₂ → G` on the fibres over a map `b`,
continuous within `s` at `y₀`, has operator norm bounded on a neighbourhood of `y₀` within `s`. -/
theorem ContinuousWithinAt.exists_eventually_norm_le_bilinear_bundle {s : Set X} {y₀ : X}
    (hφ : ContinuousWithinAt (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] G)
      (E := fun x ↦ E₁ x →L[ℝ] E₂ x →L[ℝ] G) (b y) (φ y)) s y₀) :
    ∃ C, ∀ᶠ y in 𝓝[s] y₀, ‖φ y‖ ≤ C := by
  rw [continuousWithinAt_hom_bundle] at hφ
  obtain ⟨hb, hΦ⟩ := hφ
  set e₁ := trivializationAt F₁ E₁ (b y₀)
  set e₂ := trivializationAt F₂ E₂ (b y₀)
  -- `Φ y` is the map `φ y` read in the trivializations `e₁` and `e₂` at `b y₀`.
  set Φ : X → F₁ →L[ℝ] F₂ →L[ℝ] G := fun y ↦
    inCoordinates F₁ E₁ (F₂ →L[ℝ] G) (fun x ↦ E₂ x →L[ℝ] G) (b y₀) (b y) (b y₀) (b y) (φ y)
  obtain ⟨C₁, hC₁, hC₁e⟩ := eventually_norm_trivializationAt_lt F₁ E₁ (b y₀)
  obtain ⟨C₂, hC₂, hC₂e⟩ := eventually_norm_trivializationAt_lt F₂ E₂ (b y₀)
  have hbase₁ : ∀ᶠ y in 𝓝[s] y₀, b y ∈ e₁.baseSet :=
    hb.eventually_mem (e₁.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  have hbase₂ : ∀ᶠ y in 𝓝[s] y₀, b y ∈ e₂.baseSet :=
    hb.eventually_mem (e₂.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  refine ⟨(‖Φ y₀‖ + 1) * C₁ * C₂, ?_⟩
  filter_upwards [hb.eventually hC₁e, hb.eventually hC₂e, hbase₁, hbase₂,
    hΦ.norm.eventually (gt_mem_nhds (lt_add_one _))] with y hy₁ hy₂ hyb₁ hyb₂ hyΦ
  refine opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  rw [← inCoordinates_apply_continuousLinearMapAt₂_eq_apply hyb₁ hyb₂]
  calc ‖Φ y (e₁.continuousLinearMapAt ℝ (b y) v) (e₂.continuousLinearMapAt ℝ (b y) w)‖
      ≤ ‖Φ y‖ * ‖e₁.continuousLinearMapAt ℝ (b y) v‖ * ‖e₂.continuousLinearMapAt ℝ (b y) w‖ :=
        le_opNorm₂ _ _ _
    _ ≤ (‖Φ y₀‖ + 1) * (C₁ * ‖v‖) * (C₂ * ‖w‖) := by
        gcongr
        exacts [le_of_opNorm_le _ hy₁.le v, le_of_opNorm_le _ hy₂.le w]
    _ = (‖Φ y₀‖ + 1) * C₁ * C₂ * ‖v‖ * ‖w‖ := by ring

/-- **A continuous family of bilinear maps is bounded on a compact set.** For continuous
Riemannian bundles `E₁` and `E₂`, a family of bilinear maps `E₁ × E₂ → G` on the fibres over a map
`b`, continuous on a compact set `K`, has operator norm bounded on `K`. -/
theorem IsCompact.exists_bound_of_continuousOn_bilinear_bundle {K : Set X} (hK : IsCompact K)
    (hφ : ContinuousOn (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] G)
      (E := fun x ↦ E₁ x →L[ℝ] E₂ x →L[ℝ] G) (b y) (φ y)) K) :
    ∃ C, ∀ y ∈ K, ‖φ y‖ ≤ C :=
  hK.exists_forall_of_forall_exists_eventually (r := (· ≤ ·)) (p := fun C y ↦ ‖φ y‖ ≤ C)
    (fun _ _ hab _ h ↦ h.trans hab) fun y hy ↦
      (hφ y hy).exists_eventually_norm_le_bilinear_bundle

end Bound

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] [FiniteDimensional ℝ F]
  {φ : ∀ y, E (b y) →L[ℝ] E (b y) →L[ℝ] ℝ}

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
      exact (TauCeti.forall_inCoordinates_bilinear_apply_self_pos_iff hy₀ (φ y₀)).mpr hpos w hw
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
  rw [← inCoordinates_apply_continuousLinearMapAt₂_eq_apply hyb hyb]
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
  -- Positive constants are directed by `≥`, since a smaller constant gives a weaker bound.
  obtain ⟨⟨c, hc₀⟩, hc⟩ := hK.exists_forall_of_forall_exists_eventually (α := Ioi (0 : ℝ))
    (r := (· ≥ ·)) (p := fun c y ↦ ∀ v, (c : ℝ) * ‖v‖ ^ 2 ≤ φ y v v)
    (fun _ _ hab _ h v ↦ le_trans (by gcongr) (h v)) fun y hy ↦ by
      obtain ⟨c, hc, hle⟩ := (hφ y hy).exists_pos_eventually_mul_norm_sq_le_bundle (hpos y hy)
      exact ⟨⟨c, hc⟩, hle⟩
  exact ⟨c, hc₀, hc⟩

end Norm

namespace Bundle.ContinuousRiemannianMetric

variable [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **A metric is bounded by a multiple of another over a compact set.** For two continuous
Riemannian metrics `g` and `g₀` on a vector bundle and a compact subset `K` of the base, there is
`0 < Λ` with `g ≤ Λ g₀` on the fibres over `K`. -/
theorem exists_inner_le_mul_inner (g g₀ : ContinuousRiemannianMetric F E) {K : Set B}
    (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, ∀ v : E x, g.inner x v v ≤ C * g₀.inner x v v := by
  -- Each fibre is isomorphic to the model fibre as a topological vector space, which provides the
  -- instances needed to install `g₀` as the fibre inner product.
  have (x : B) : IsTopologicalAddGroup (E x) :=
    let e := (trivializationAt F E x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    e.toHomeomorph.isInducing.isTopologicalAddGroup e
  have (x : B) : ContinuousConstSMul ℝ (E x) :=
    let e := (trivializationAt F E x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    e.toHomeomorph.isInducing.continuousConstSMul id (map_smul e _ _)
  let _ : RiemannianBundle E := ⟨g₀.toRiemannianMetric⟩
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn_bilinear_bundle (b := id) (φ := g.inner)
      g.continuous.continuousOn
  refine ⟨max C 1, by positivity, fun x hx v ↦ ?_⟩
  -- The squared norm of `v` for the installed metric is `g₀.inner x v v`.
  have hv : ‖v‖ ^ 2 = g₀.inner x v v := (real_inner_self_eq_norm_sq v).symm
  calc g.inner x v v ≤ ‖g.inner x v v‖ := Real.le_norm_self _
    _ ≤ _ := le_opNorm₂ (g.inner x) v v
    _ ≤ max C 1 * ‖v‖ * ‖v‖ := by gcongr; exact (hC x hx).trans (le_max_left _ _)
    _ = max C 1 * g₀.inner x v v := by rw [mul_assoc, ← sq, hv]

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
