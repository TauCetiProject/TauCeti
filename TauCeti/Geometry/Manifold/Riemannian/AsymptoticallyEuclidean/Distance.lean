/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Riemannian distance on an asymptotically Euclidean end

Let `φ` be an asymptotically Euclidean end of order `t > 0` of a Riemannian manifold `M`. Its
pulled-back metric coefficients `g_ij` tend to `δ_ij`, so the differential of `φ` is asymptotically
an isometry: `‖dφ_x v‖` and `‖v‖` differ by at most `C ‖x‖ ^ (-t) ‖v‖`. Integrating this along
paths shows that the Riemannian distance from any fixed point `p` of `M` to `φ x` is
`‖x‖ (1 + o(1))` as `‖x‖ → ∞`.

The upper bound comes from the radial segment of the end from a large sphere to `x`. The lower
bound needs more care, since a path from `φ x` to `p` may leave the end and come back, and the
image of the end is not known a priori to be closed in `M`. We follow such a path from `φ x` for as
long as it stays in the image of the closed annulus `{b ≤ ‖y‖ ≤ 2 ‖x‖ - b}`, which is compact.
While it does, it is the image of a curve in the annulus. If the differential of `φ` stretches
vectors by at least `c > 0` there, the Euclidean displacement of that curve is at most `1 / c`
times the Riemannian length, so a path shorter than `c (‖x‖ - b)` reaches neither boundary sphere
of the annulus, and hence never leaves it. This continuity argument is the one Mathlib uses to
show that the Riemannian distance induces the manifold topology.

In particular the end goes off to infinity in `M`: on a Riemannian manifold whose distance is a
metric, `φ` tends to infinity along the cobounded filter of `ℝⁿ`.

## Main results

* `TauCeti.IsAsymptoticallyEuclideanEnd.exists_abs_norm_mfderiv_sub_norm_le`: the differential of
  an end of order `t` distorts lengths by at most `C ‖x‖ ^ (-t)`;
  `TauCeti.IsAsymptoticallyEuclideanEnd.eventually_abs_norm_mfderiv_sub_norm_le` is its
  consequence for `t > 0`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.ofReal_mul_sub_le_riemannianEDist`: if the differential
  stretches vectors by at least `c ≥ 0` outside the ball of radius `a`, then the Riemannian
  distance from `φ x` to a point outside the image of that exterior is at least `c (‖x‖ - a)`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.isLittleO_dist_sub_norm`: for `t > 0` and every point `p`,
  `d(p, φ x) = ‖x‖ + o(‖x‖)` as `‖x‖ → ∞`, and
  `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_dist_div_norm`: `d(p, φ x) / ‖x‖ → 1`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_cobounded`: for `t > 0`, `φ x` tends to infinity
  in `M` as `‖x‖ → ∞`.

## References

* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §8 and §9.
* `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` (S. Gouëzel),
  `setOfPred_riemannianEDist_lt_subset_nhds`: the continuity argument showing that a short path
  cannot leave a coordinate neighbourhood, adapted here to annuli of an end.
-/

public section

open Bornology Bundle Filter Manifold Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

namespace IsAsymptoticallyEuclideanEnd

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {t R : ℝ}

section Topological

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {φ : EuclideanSpace ℝ (Fin n) → M}

/-! ### The differential of an end is asymptotically isometric -/

/-- The differential of an asymptotically Euclidean end of order `t` changes the length of a
vector `v` at `x` by at most `C ‖x‖ ^ (-t) ‖v‖`: the squared lengths differ by the quadratic form
of `g_ij - δ_ij`, whose entries are `O(‖x‖ ^ (-t))`. -/
theorem exists_abs_norm_mfderiv_sub_norm_le (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    ∃ C, ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, ∀ v : EuclideanSpace ℝ (Fin n),
      |‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x v‖ - ‖v‖| ≤ C * ‖x‖ ^ (-t) * ‖v‖ := by
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  refine ⟨n * C, fun x hx v ↦ ?_⟩
  set L := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x
  set K := C * ‖x‖ ^ (-t)
  have hK (i j : Fin n) :
      |pullbackMetricCoeff I φ x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ K := by
    have := hC 0 (by norm_num) i j x hx
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Matrix.sub_apply, Nat.cast_zero,
      sub_zero] at this
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK ⟨0, h.dim_pos⟩ ⟨0, h.dim_pos⟩)
  -- The difference of the squared lengths is the quadratic form of `g - 1`.
  have hdiff : ‖L v‖ ^ 2 - ‖v‖ ^ 2 = ∑ i, ∑ j,
      (pullbackMetricCoeff I φ x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) * v i * v j := by
    rw [norm_mfderiv_sq_eq_sum_pullbackMetricCoeff, EuclideanSpace.real_norm_sq_eq]
    simp only [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, sq]
  -- That quadratic form is at most `n K ‖v‖²` in absolute value.
  have hsq : |‖L v‖ ^ 2 - ‖v‖ ^ 2| ≤ n * K * ‖v‖ ^ 2 := by
    rw [hdiff]
    calc _ ≤ ∑ i, ∑ j, |v i| * |v j| * K := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
          rw [abs_mul, abs_mul]
          exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left (hK i j) (by positivity))
      _ = (∑ i, |v i|) ^ 2 * K := by
          rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_mul]
      _ ≤ (n * ∑ i, |v i| ^ 2) * K := by
          refine mul_le_mul_of_nonneg_right ?_ hK0
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ |v i|)
      _ = n * K * ‖v‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp only [sq_abs]
          ring
  -- From squared lengths to lengths: `|a - b| (a + b) = |a² - b²|`.
  have ha := norm_nonneg (L v)
  have hmul : |‖L v‖ - ‖v‖| * (‖L v‖ + ‖v‖) ≤ n * K * ‖v‖ ^ 2 := by
    rw [← abs_of_nonneg (add_nonneg ha (norm_nonneg v)), ← abs_mul]
    exact (le_of_eq (by ring_nf)).trans hsq
  have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK0
  rw [mul_assoc (n : ℝ) C]
  rcases (norm_nonneg v).eq_or_lt with hb0 | hb0
  · rw [← hb0, sub_zero, abs_of_nonneg ha] at hmul ⊢
    nlinarith
  · nlinarith [abs_nonneg (‖L v‖ - ‖v‖)]

/-- On an asymptotically Euclidean end of positive order, the differential changes lengths by at
most any prescribed proportion `ε > 0` far enough out. -/
theorem eventually_abs_norm_mfderiv_sub_norm_le (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in cobounded (EuclideanSpace ℝ (Fin n)), ∀ v : EuclideanSpace ℝ (Fin n),
      |‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x v‖ - ‖v‖| ≤ ε * ‖v‖ := by
  obtain ⟨C, hC⟩ := h.exists_abs_norm_mfderiv_sub_norm_le
  have hlim : Tendsto (fun x : EuclideanSpace ℝ (Fin n) ↦ C * ‖x‖ ^ (-t)) (cobounded _) (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop ht).comp tendsto_norm_cobounded_atTop).const_mul C
  filter_upwards [hlim.eventually (ge_mem_nhds hε), eventually_cobounded_le_norm (R + 1)]
    with x hxε hxR v
  have hx : x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
    simpa using (lt_add_one R).trans_le hxR
  exact (hC x hx v).trans (mul_le_mul_of_nonneg_right hxε (norm_nonneg v))

/-! ### The lower bound -/

variable [IsManifold I ∞ M]

/-- A path from `φ x` that stays in the image of the closed annulus `b ≤ ‖y‖ ≤ 2 ‖x‖ - b`, on which
the differential of `φ` stretches vectors by at least `c > 0`, and that is shorter than
`c (‖x‖ - b)`, ends in the image of the open annulus: its coordinates have moved by less than
`‖x‖ - b`. -/
private theorem mem_image_annulus_of_pathELength_lt (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {b c : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hb : R < b) (hbx : b < ‖x‖) (hc0 : 0 < c)
    (hc : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * ‖x‖ - b) \ ball 0 b,
      ∀ v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ y v‖)
    {γ : ℝ → M} {s : ℝ} (hs : 0 ≤ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 s))
    (hγ0 : γ 0 = φ x) (hsub : Icc 0 s ⊆ γ ⁻¹' (φ '' (closedBall 0 (2 * ‖x‖ - b) \ ball 0 b)))
    (hlt : pathELength I γ 0 s < ENNReal.ofReal (c * (‖x‖ - b))) :
    γ s ∈ φ '' (ball 0 (2 * ‖x‖ - b) \ closedBall 0 b) := by
  set S : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 (2 * ‖x‖ - b) \ ball 0 b
  have hSR : S ⊆ (closedBall 0 R)ᶜ :=
    (sdiff_subset_compl _ _).trans (compl_subset_compl.2 (closedBall_subset_ball hb))
  -- Read the path in the coordinates of the end, through the inverse `ψ` of the end.
  set ψ := h.toPartialDiffeomorph.symm
  have hmem {r} (hr : r ∈ Icc 0 s) : ψ (γ r) ∈ S ∧ φ (ψ (γ r)) = γ r := by
    obtain ⟨y, hy, hyr⟩ := hsub hr
    rw [← hyr, h.toPartialDiffeomorph_symm_apply_apply (hSR hy)]
    exact ⟨hy, rfl⟩
  have hy : ContDiffOn ℝ 1 (ψ ∘ γ) (Icc 0 s) :=
    contMDiffOn_iff_contDiffOn.1 ((ψ.contMDiffOn.of_le (by simp)).comp hγ fun r hr ↦ by
      rw [mem_preimage, ← (hmem hr).2, PartialDiffeomorph.symm_toPartialEquiv,
        PartialEquiv.symm_source, toPartialDiffeomorph_target]
      exact mem_image_of_mem φ (hSR (hmem hr).1))
  have hdiff (r) (hr : r ∈ Icc 0 s) :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ (ψ (γ r)) :=
    (h.contMDiffOn.contMDiffAt (isClosed_closedBall.isOpen_compl.mem_nhds
      (hSR (hmem hr).1))).mdifferentiableAt (by simp)
  have hlen := Manifold.ofReal_mul_eNorm_sub_le_pathELength_comp hs hy hdiff
    fun r hr ↦ hc _ (hmem hr).1
  have hx : ψ (φ x) = x :=
    h.toPartialDiffeomorph_symm_apply_apply (by simpa using hb.trans hbx)
  rw [pathELength_congr (γ := φ ∘ ψ ∘ γ) (γ' := γ) fun r hr ↦ (hmem hr).2,
    Function.comp_apply, Function.comp_apply, hγ0, hx] at hlen
  -- The coordinates have moved by less than `‖x‖ - b`.
  have hdisp : ‖ψ (γ s) - x‖ < ‖x‖ - b := by
    have := hlen.trans_lt hlt
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hc0.le,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos hc0 (by linarith))] at this
    exact lt_of_mul_lt_mul_left this hc0.le
  refine ⟨ψ (γ s), ⟨?_, ?_⟩, (hmem (right_mem_Icc.2 hs)).2⟩
  · rw [mem_ball_zero_iff]
    linarith [norm_sub_norm_le (ψ (γ s)) x]
  · rw [mem_closedBall_zero_iff, not_le]
    linarith [norm_sub_norm_le x (ψ (γ s)), norm_sub_rev (ψ (γ s)) x]

/-- The lower bound for one annulus `b ≤ ‖y‖ ≤ 2 ‖x‖ - b`, `a < b < ‖x‖`: a path from `φ x` that
is shorter than `c (‖x‖ - b)` stays in the image of the annulus, so it cannot reach a point
outside the image of the exterior of the ball of radius `a`. -/
private theorem ofReal_mul_sub_le_riemannianEDist_of_lt [T2Space M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) {a b c : ℝ} (ha : R ≤ a) (hab : a < b)
    (hc : ∀ y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) a)ᶜ, ∀ v : EuclideanSpace ℝ (Fin n),
      c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ y v‖)
    {p : M} (hp : p ∉ φ '' (closedBall 0 a)ᶜ) {x : EuclideanSpace ℝ (Fin n)} (hbx : b < ‖x‖) :
    ENNReal.ofReal (c * (‖x‖ - b)) ≤ riemannianEDist I (φ x) p := by
  rcases le_or_gt c 0 with hc0 | hc0
  · simp [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc0 (sub_nonneg.2 hbx.le))]
  -- The closed annulus `S` and its open interior `U`, with images `φ '' S ⊇ φ '' U` in `M`.
  set S : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 (2 * ‖x‖ - b) \ ball 0 b
  set U : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (2 * ‖x‖ - b) \ closedBall 0 b
  have hSa : S ⊆ (closedBall 0 a)ᶜ :=
    (sdiff_subset_compl _ _).trans (compl_subset_compl.2 (closedBall_subset_ball hab))
  have hSR : S ⊆ (closedBall 0 R)ᶜ :=
    hSa.trans (compl_subset_compl.2 (closedBall_subset_closedBall ha))
  have hUS : U ⊆ S := sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall
  have hTc : IsClosed (φ '' S) :=
    (((isCompact_closedBall 0 _).diff isOpen_ball).image_of_continuousOn
      (h.contMDiffOn.continuousOn.mono hSR)).isClosed
  have hVo : IsOpen (φ '' U) :=
    h.isOpen_image_of_subset (isOpen_ball.sdiff isClosed_closedBall) (hUS.trans hSR)
  have hxS : x ∈ S := by
    simp only [S, Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt]
    constructor <;> linarith
  refine Manifold.le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦ ?_
  by_contra hlt
  rw [not_le] at hlt
  -- A path shorter than `c (‖x‖ - b)` never leaves the image of the annulus.
  suffices Icc 0 1 ⊆ γ ⁻¹' (φ '' S) from
    hp (image_mono hSa (hγ1 ▸ this (right_mem_Icc.2 zero_le_one)))
  have hγS0 : 0 ∈ γ ⁻¹' (φ '' S) := by
    rw [mem_preimage, hγ0]
    exact mem_image_of_mem φ hxS
  refine IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset ?_ hγS0 fun s hs hsub ↦ ?_
  · rw [inter_comm]
    exact hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hTc
  have hsU := h.mem_image_annulus_of_pathELength_lt (ha.trans_lt hab) hbx hc0
    (fun y hy ↦ hc y (hSa hy)) hs.1 (hγ.mono (Icc_subset_Icc_right hs.2.le)) hγ0 hsub
    ((pathELength_mono le_rfl hs.2.le).trans_lt hlt)
  have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[>] s :=
    mem_of_superset (Ioo_mem_nhdsGT hs.2) fun r hr ↦ ⟨hs.1.trans hr.1.le, hr.2.le⟩
  exact mem_of_superset (nhdsWithin_le_of_mem hIcc
    ((hγ.continuousOn s ⟨hs.1, hs.2.le⟩).preimage_mem_nhdsWithin (hVo.mem_nhds hsU)))
    (preimage_mono (image_mono hUS))

/-- **The Riemannian distance grows at least linearly along an end.** If the differential of an
asymptotically Euclidean end stretches vectors by at least the factor `c ≥ 0` outside the ball
of radius `a ≥ R`, then the Riemannian distance from `φ x` to any point `p` outside the image of
that exterior is at least `c (‖x‖ - a)`. The point `p` may lie outside the end altogether, and
the paths from `φ x` to `p` may leave the end. Every `p` satisfies the hypothesis for all large
`a`, by `eventually_notMem_image_compl_closedBall`. -/
theorem ofReal_mul_sub_le_riemannianEDist [T2Space M] (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {a c : ℝ} (ha : R ≤ a) (hc0 : 0 ≤ c)
    (hc : ∀ y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) a)ᶜ, ∀ v : EuclideanSpace ℝ (Fin n),
      c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ y v‖)
    {p : M} (hp : p ∉ φ '' (closedBall 0 a)ᶜ) (x : EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal (c * (‖x‖ - a)) ≤ riemannianEDist I (φ x) p := by
  rcases le_or_gt ‖x‖ a with hxa | hxa
  · simp [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc0 (sub_nonpos.2 hxa))]
  -- Let the inner radius `b` of the annulus decrease to `a`.
  have hlim : Tendsto (fun b ↦ ENNReal.ofReal (c * (‖x‖ - b))) (𝓝[>] a)
      (𝓝 (ENNReal.ofReal (c * (‖x‖ - a)))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).tendsto a).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT hxa) fun b hb ↦
    ofReal_mul_sub_le_riemannianEDist_of_lt h ha hb.1 hc hp hb.2)

end Topological

/-! ### Asymptotics of the distance -/

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] [IsManifold I ∞ M]
  {φ : EuclideanSpace ℝ (Fin n) → M}

/-- The lower half of the asymptotics: for `0 < ε ≤ 1`, the distance from a fixed point is at
least `(1 - ε) ‖x‖` up to an additive constant. -/
private theorem exists_sub_le_dist (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t)
    (p : M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K, ∀ x, (1 - ε) * ‖x‖ - K ≤ dist p (φ x) := by
  obtain ⟨r, -, hr⟩ :=
    (hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).eventually_iff.1
      (h.eventually_abs_norm_mfderiv_sub_norm_le ht hε)
  obtain ⟨a, ha, hpa⟩ := ((eventually_ge_atTop (max r R)).and
    (h.eventually_notMem_image_compl_closedBall p)).exists
  refine ⟨(1 - ε) * a, fun x ↦ ?_⟩
  have hc (y) (hy : y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) a)ᶜ)
      (v : EuclideanSpace ℝ (Fin n)) :
      (1 - ε) * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ y v‖ := by
    have := hr (compl_subset_compl.2 (closedBall_subset_closedBall
      ((le_max_left r R).trans ha)) hy) v
    linarith [neg_abs_le (‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ y v‖ - ‖v‖)]
  have := h.ofReal_mul_sub_le_riemannianEDist ((le_max_right r R).trans ha) (by linarith) hc hpa x
  rw [← IsRiemannianManifold.out, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg,
    dist_comm] at this
  linarith [mul_sub (1 - ε) ‖x‖ a]

omit [IsManifold I ∞ M] in
/-- The upper half of the asymptotics: for `ε > 0`, the distance from a fixed point is at most
`(1 + ε) ‖x‖` up to an additive constant, outside a large ball. -/
private theorem exists_dist_le (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) (p : M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a K, ∀ x, a < ‖x‖ → dist p (φ x) ≤ (1 + ε) * ‖x‖ + K := by
  obtain ⟨r, -, hr⟩ :=
    (hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).eventually_iff.1
      (h.eventually_abs_norm_mfderiv_sub_norm_le ht hε)
  -- Radial segments are drawn from the sphere of radius `a`.
  set a := max r R + 1
  have ha0 : 0 < a := by linarith [le_max_right r R, h.radius_pos]
  have hext {y : EuclideanSpace ℝ (Fin n)} (hy : a ≤ ‖y‖) :
      y ∈ (closedBall 0 r)ᶜ ∩ (closedBall 0 R)ᶜ := by
    simp only [mem_inter_iff, mem_compl_iff, mem_closedBall_zero_iff, not_le]
    exact ⟨by linarith [le_max_left r R], by linarith [le_max_right r R]⟩
  have hp : Continuous fun y : M ↦ dist p y := continuous_const.dist continuous_id
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) a).exists_bound_of_continuousOn
    (hp.comp_continuousOn (h.contMDiffOn.continuousOn.mono
      fun y hy ↦ (hext (mem_sphere_zero_iff_norm.1 hy).ge).2))
  refine ⟨a, K, fun x hx ↦ ?_⟩
  have hx0 : 0 < ‖x‖ := ha0.trans hx
  -- The radial segment from `x₀ = (a / ‖x‖) x` on the sphere of radius `a` to `x`.
  set x₀ := (a / ‖x‖) • x
  have hq0 : 0 ≤ a / ‖x‖ := div_nonneg ha0.le hx0.le
  have hq1 : a / ‖x‖ ≤ 1 := (div_le_one hx0).2 hx.le
  have hx₀ : ‖x₀‖ = a := by
    rw [norm_smul, Real.norm_of_nonneg hq0, div_mul_cancel₀ _ hx0.ne']
  have hseg {z} (hz : z ∈ segment ℝ x₀ x) : a ≤ ‖z‖ := by
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have hz : x₀ + θ • (x - x₀) = (a / ‖x‖ + θ * (1 - a / ‖x‖)) • x := by
      simp only [x₀]
      module
    have hθq : 0 ≤ θ * (1 - a / ‖x‖) := mul_nonneg hθ.1 (by linarith)
    beta_reduce
    rw [hz, norm_smul, Real.norm_of_nonneg (by linarith), add_mul, div_mul_cancel₀ _ hx0.ne']
    nlinarith
  have hnorm : ‖x - x₀‖ = ‖x‖ - a := by
    rw [show x - x₀ = (1 - a / ‖x‖) • x by simp only [x₀]; module, norm_smul,
      Real.norm_of_nonneg (by linarith), sub_mul, one_mul, div_mul_cancel₀ _ hx0.ne']
  have hseg_dist : dist (φ x₀) (φ x) ≤ (1 + ε) * ‖x‖ - (1 + ε) * a := by
    rw [dist_edist, ← mul_sub, ← hnorm, ← ENNReal.toReal_ofReal (by positivity :
      0 ≤ (1 + ε) * ‖x - x₀‖)]
    refine ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (IsRiemannianManifold.edist_le_of_norm_mfderiv_le (I := I) (fun z hz ↦ ?_) fun z hz ↦ ?_)
    · exact (h.contMDiffOn.contMDiffAt (isClosed_closedBall.isOpen_compl.mem_nhds
        (hext (hseg hz)).2)).of_le (by simp)
    · linarith [le_abs_self (‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z (x - x₀)‖ - ‖x - x₀‖),
        hr (hext (hseg hz)).1 (x - x₀)]
  have hKx : dist p (φ x₀) ≤ K := (Real.le_norm_self _).trans (hK x₀ (by simp [hx₀]))
  linarith [dist_triangle p (φ x₀) (φ x), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) ha0.le]

/-- **The Riemannian distance along an end.** On an asymptotically Euclidean end of positive
order, the distance from any fixed point `p` to `φ x` is `‖x‖ + o(‖x‖)` as `‖x‖ → ∞`. -/
theorem isLittleO_dist_sub_norm (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) (p : M) :
    (fun x ↦ dist p (φ x) - ‖x‖) =o[cobounded (EuclideanSpace ℝ (Fin n))] (fun x ↦ ‖x‖) := by
  refine Asymptotics.IsLittleO.of_bound fun δ hδ ↦ ?_
  set ε := min (δ / 2) 1
  have hε : 0 < ε := lt_min (by linarith) one_pos
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  obtain ⟨K₁, hK₁⟩ := h.exists_sub_le_dist ht p hε (min_le_right _ _)
  obtain ⟨a, K₂, hK₂⟩ := h.exists_dist_le ht p hε
  filter_upwards [eventually_cobounded_le_norm (a + 1),
    eventually_cobounded_le_norm (2 * max K₁ K₂ / δ)] with x hxa hxK
  have hK : 2 * max K₁ K₂ ≤ ‖x‖ * δ := (div_le_iff₀ hδ).1 hxK
  have h₁ := hK₁ x
  have h₂ := hK₂ x (by linarith)
  have hεx : ε * ‖x‖ ≤ δ / 2 * ‖x‖ := mul_le_mul_of_nonneg_right hεδ (norm_nonneg x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_le]
  constructor <;> nlinarith [le_max_left K₁ K₂, le_max_right K₁ K₂]

/-- On an asymptotically Euclidean end of positive order, the ratio of the distance from any fixed
point `p` to `φ x` and of `‖x‖` tends to `1` as `‖x‖ → ∞`. -/
theorem tendsto_dist_div_norm (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) (p : M) :
    Tendsto (fun x ↦ dist p (φ x) / ‖x‖) (cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  have := ((h.isLittleO_dist_sub_norm ht p).tendsto_div_nhds_zero).const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_cobounded_le_norm 1] with x hx
  rw [sub_div, div_self (by linarith : ‖x‖ ≠ 0)]
  ring

/-- An asymptotically Euclidean end of positive order goes off to infinity in `M`: `φ x` leaves
every bounded subset of `M` as `‖x‖ → ∞`. -/
theorem tendsto_cobounded (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    Tendsto φ (cobounded (EuclideanSpace ℝ (Fin n))) (cobounded M) := by
  refine (tendsto_dist_left_atTop_iff (φ 0)).1 (tendsto_atTop_mono' _ ?_
    (tendsto_norm_cobounded_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
  filter_upwards [(h.tendsto_dist_div_norm ht (φ 0)).eventually
      (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)), eventually_cobounded_le_norm 1] with x hx hx1
  rw [lt_div_iff₀ (by linarith)] at hx
  linarith

end Metric

end IsAsymptoticallyEuclideanEnd

end TauCeti
