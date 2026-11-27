/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.Global
public import TauCeti.Topology.Category.TopCat.GlueData.PartialHomeomorph
import TauCeti.Geometry.Manifold.IntegralCurve.SmoothFlow

/-!
# Continuity of the inward flow up to the boundary

Let `M` be a compact smooth Hausdorff manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)`
and `v` a smooth vector field on `M` pointing inward along the boundary. Its forward integral
curves exist for all positive time
(`TauCeti.exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg`), and this file shows that they
depend continuously on their initial point, up to and including the boundary: the flow
`(x, t) ↦ forwardIntegralCurve v x t` is continuous on `M × [0, ∞)`
(`TauCeti.continuousOn_forwardIntegralCurve_of_isOutwardPointing_neg`).

For a field `V` pointing outward along the boundary (`TauCeti.IsOutwardPointingField`), this is
the continuity of its backward flow `(x, t) ↦ forwardIntegralCurve (-V) x (-t)` on `M × (-∞, 0]`
(`TauCeti.IsOutwardPointingField.continuousOn_forwardIntegralCurve_neg`). Its restriction to
`∂M × (-∞, 0)` is the collar of the boundary inside the interior of `M`, and its restriction to
`∂M × {0}` is the inclusion of the boundary. So any open partial homeomorphism
`e : ℝ × ∂M ⇀ int M` with source `(-∞, 0) × ∂M` given by the backward flow extends continuously to
`(-∞, 0] × ∂M` in `M`, sending the slice `{0} × ∂M` outside the interior. Hence the space obtained
by gluing the cylinder `ℝ × ∂M` to the interior of `M` along `e`, which is `M` with the end
`[0, ∞) × ∂M` attached along the boundary, is Hausdorff
(`TauCeti.IsOutwardPointingField.t2Space_glueData`). For the Liouville field of a compact
Liouville domain `W` this is the underlying space of the completion of `W`.

The proof of continuity is local in time. Near an interior point, the integral curves are the
curves of a local flow continuous near time `0` (`TauCeti.Manifold.exists_contMDiffAt_localFlow`);
near a boundary point, they are the curves of the local inward flow, continuous on a neighbourhood
times `[0, ε)` (`TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`). By compactness,
the flow is continuous on `M × [0, ε)` for one `ε > 0`. The flow law
`φ (x, t) = φ (φ (x, t - ε / 2), ε / 2)` then propagates continuity to `M × [0, k ε / 2)` for
every `k` by induction.

## Main results

* `TauCeti.continuousOn_forwardIntegralCurve_of_isOutwardPointing_neg`: the forward flow of an
  inward field on a compact manifold with boundary is continuous on `M × [0, ∞)`.
* `TauCeti.IsOutwardPointingField.continuousOn_forwardIntegralCurve_neg`: the backward flow of an
  outward field is continuous on `M × (-∞, 0]`.
* `TauCeti.IsOutwardPointingField.t2Space_glueData`: the cylinder glued to the interior along the
  backward flow collar gives a Hausdorff space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.12 (the fundamental theorem on flows, for the continuity of the flow
  domain and the flow) and Theorem 9.25 (flowing the boundary inward).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 2(a) (the completion of a Liouville domain).
-/

public section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

section Inward

variable {v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}

/-- Near every point of a manifold with boundary, an inward-pointing smooth field has a local flow
for forward times which is continuous in time and initial point. -/
private theorem exists_continuousOn_localFlow
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∃ Φ : M → ℝ → M,
      ContinuousOn (fun p : M × ℝ ↦ Φ p.1 p.2) (U ×ˢ Ico 0 ε) ∧
      ∀ x ∈ U, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Ico 0 ε) := by
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x₀ with hx₀ | hx₀
  · -- Near an interior point, a local flow smooth at `(x₀, 0)`, hence continuous near it.
    obtain ⟨U, hU, s, hs, -, Φ, hΦ, hΦx⟩ :=
      Manifold.exists_contMDiffAt_localFlow v x₀ (V := univ) hv.contMDiffOn univ_mem hx₀
    obtain ⟨N, hN, hΦN⟩ := (contMDiffAt_iff_contMDiffOn_nhds (n := 1) (by simp)).1
      (hΦ.of_le (by simp))
    obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨δ, hδ, hδws⟩ := Metric.mem_nhds_iff.1 (inter_mem hw hs)
    have hIco : Ico 0 δ ⊆ w ∩ s := fun t ht ↦ hδws (by
      rw [Real.ball_eq_Ioo, zero_sub, zero_add]
      exact ⟨by linarith [ht.1], ht.2⟩)
    refine ⟨U ∩ u, inter_mem hU hu, δ, hδ, Φ,
      hΦN.continuousOn.mono fun p hp ↦ huw ⟨hp.1.2, (hIco hp.2).1⟩, fun x hx ↦
        ⟨(hΦx x hx.1).1, (hΦx x hx.1).2.1.mono fun t ht ↦ (hIco ht).2⟩⟩
  · -- Near a boundary point, the local inward flow.
    obtain ⟨U, hU, ε, hε, Φ, hΦ, hΦx⟩ := exists_contMDiffOn_localFlow_of_isOutwardPointing_neg v
      (V := univ) hv.contMDiffOn univ_mem (hin x₀ hx₀)
    exact ⟨U, hU, ε, hε, Φ, hΦ.continuousOn, fun x hx ↦ ⟨(hΦx x hx).1, (hΦx x hx).2.1⟩⟩

variable [T2Space M] [CompactSpace M]

/-- Near every point of a compact manifold with boundary, the forward flow of an inward-pointing
smooth field is continuous, within `M × [0, ∞)`, at every point of a neighbourhood times a short
time interval `[0, ε)`. -/
private theorem exists_mem_nhds_forall_continuousWithinAt_forwardIntegralCurve
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∀ x ∈ U, ∀ t ∈ Ico 0 ε,
      ContinuousWithinAt (fun p : M × ℝ ↦ forwardIntegralCurve v p.1 p.2) (univ ×ˢ Ici 0)
        (x, t) := by
  obtain ⟨U, hU, ε, hε, Φ, hΦ, hΦx⟩ := exists_continuousOn_localFlow hv hin x₀
  -- On `U × [0, ε)`, the local flow is the forward flow, by uniqueness of integral curves.
  have heq : EqOn (fun p : M × ℝ ↦ forwardIntegralCurve v p.1 p.2) (fun p ↦ Φ p.1 p.2)
      (U ×ˢ Ico 0 ε) := fun p hp ↦
    ((hΦx p.1 hp.1).2.eqOn_of_isPreconnected
      ((isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg hv hin p.1).mono
        Ico_subset_Ici_self) isPreconnected_Ico (left_mem_Ico.2 hε)
      (fun _ _ ↦ (hv _).of_le (by simp))
      (by rw [(hΦx p.1 hp.1).1, forwardIntegralCurve_zero]) hp.2).symm
  refine ⟨interior U, interior_mem_nhds.2 hU, ε, hε, fun x hx t ht ↦ ?_⟩
  have hmem : U ×ˢ Ico 0 ε ∈ 𝓝[univ ×ˢ Ici 0] (x, t) :=
    mem_nhdsWithin.2 ⟨interior U ×ˢ Iio ε, isOpen_interior.prod isOpen_Iio, ⟨hx, ht.2⟩,
      fun p hp ↦ ⟨interior_subset hp.1.1, hp.2.2, hp.1.2⟩⟩
  exact ((hΦ (x, t) ⟨interior_subset hx, ht⟩).congr heq
    (heq ⟨interior_subset hx, ht⟩)).mono_of_mem_nhdsWithin hmem

/-- **A uniform time of continuity.** On a compact manifold with boundary, the forward flow of an
inward-pointing smooth field is continuous, within `M × [0, ∞)`, at every point of `M × [0, ε)`,
for some `ε > 0`. -/
private theorem exists_pos_forall_continuousWithinAt_forwardIntegralCurve
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ∃ ε > (0 : ℝ), ∀ (x : M), ∀ t ∈ Ico 0 ε,
      ContinuousWithinAt (fun p : M × ℝ ↦ forwardIntegralCurve v p.1 p.2) (univ ×ˢ Ici 0)
        (x, t) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
  choose U hU ε hε h using exists_mem_nhds_forall_continuousWithinAt_forwardIntegralCurve hv hin
  -- Finitely many of the neighbourhoods cover `M`; take the least of their times.
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover U fun x _ ↦ hU x
  have hne : s.Nonempty := by
    obtain ⟨x⟩ := hM
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 (hs (mem_univ x))
    exact ⟨y, hy⟩
  refine ⟨s.inf' hne ε, (Finset.lt_inf'_iff hne).2 fun y _ ↦ hε y, fun x t ht ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hs (mem_univ x))
  exact h y x hxy t ⟨ht.1, ht.2.trans_le (Finset.inf'_le ε hy)⟩

/-- **Continuity of the inward flow.** On a compact Hausdorff manifold with boundary, the forward
flow `(x, t) ↦ forwardIntegralCurve v x t` of a smooth vector field `v` pointing inward along the
boundary is continuous on `M × [0, ∞)`. -/
theorem continuousOn_forwardIntegralCurve_of_isOutwardPointing_neg
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ContinuousOn (fun p : M × ℝ ↦ forwardIntegralCurve v p.1 p.2) (univ ×ˢ Ici 0) := by
  set φ := fun p : M × ℝ ↦ forwardIntegralCurve v p.1 p.2
  obtain ⟨ε, hε, hφε⟩ := exists_pos_forall_continuousWithinAt_forwardIntegralCurve hv hin
  -- Continuity at times `t < k ε / 2`, by induction on `k`: for `t ≥ ε`, the flow is the flow for
  -- time `ε / 2` after the flow for time `a = t - ε / 2`.
  have hk (k : ℕ) : ∀ (x : M), ∀ t ∈ Ico 0 (k * (ε / 2)),
      ContinuousWithinAt φ (univ ×ˢ Ici 0) (x, t) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro x t ht
      by_cases htε : t < ε
      · exact hφε x t ⟨ht.1, htε⟩
      set a := t - ε / 2 with ha_def
      have ha : a ∈ Ico 0 (k * (ε / 2)) := ⟨by linarith, by push_cast at ht; linarith [ht.2]⟩
      -- The flow from time `a`, read near `(x, t)`.
      have hg : ContinuousWithinAt (fun p : M × ℝ ↦ (φ (p.1, a), p.2 - a)) (univ ×ˢ Ici 0)
          (x, t) :=
        ((ih x a ha).comp (f := fun p : M × ℝ ↦ (p.1, a)) (x := (x, t))
          (continuous_fst.prodMk continuous_const).continuousWithinAt
          fun _ _ ↦ ⟨mem_univ _, ha.1⟩).prodMk
          (continuous_snd.sub continuous_const).continuousWithinAt
      have hcomp : ContinuousWithinAt (fun p : M × ℝ ↦ φ (φ (p.1, a), p.2 - a))
          ((univ ×ˢ Ici 0) ∩ {p | a ≤ p.2}) (x, t) :=
        (hφε (φ (x, a)) (t - a) ⟨sub_nonneg.2 (by linarith), by linarith⟩).comp (g := φ)
          (f := fun p : M × ℝ ↦ (φ (p.1, a), p.2 - a)) (t := univ ×ˢ Ici 0)
          (hg.mono inter_subset_left)
          fun p hp ↦ ⟨mem_univ _, sub_nonneg.2 hp.2⟩
      -- The flow law identifies the two near `(x, t)`.
      have hlaw : ∀ p ∈ (univ ×ˢ Ici 0) ∩ {p : M × ℝ | a ≤ p.2}, φ p = φ (φ (p.1, a), p.2 - a) :=
        fun p hp ↦ by
          simp only [φ]
          rw [forwardIntegralCurve_add_of_isOutwardPointing_neg hv hin _ ha.1
            (sub_nonneg.2 hp.2), add_sub_cancel]
      refine (hcomp.congr hlaw (hlaw _ ⟨⟨mem_univ _, ht.1⟩, by rw [mem_ofPred_eq]; linarith⟩))
        |>.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ ?_)
      exact (continuous_snd.tendsto (x, t)).eventually (le_mem_nhds (by linarith))
  rintro ⟨x, t⟩ ⟨-, ht⟩
  obtain ⟨k, hk'⟩ := exists_nat_gt (t / (ε / 2))
  exact hk k x t ⟨ht, (div_lt_iff₀ (by positivity)).1 hk'⟩

end Inward

namespace IsOutwardPointingField

variable [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hV : IsOutwardPointingField V)
include hV

/-- **Continuity of the backward flow of an outward field.** On a compact Hausdorff manifold with
boundary, for a smooth vector field `V` pointing outward along the boundary, the backward flow
`(x, t) ↦ forwardIntegralCurve (-V) x (-t)` is continuous on `M × (-∞, 0]`. -/
theorem continuousOn_forwardIntegralCurve_neg :
    ContinuousOn (fun p : M × ℝ ↦ forwardIntegralCurve (-V) p.1 (-p.2)) (univ ×ˢ Iic 0) :=
  (continuousOn_forwardIntegralCurve_of_isOutwardPointing_neg hV.contMDiff_neg
    hV.isOutwardPointing_neg_neg).comp (continuous_fst.prodMk continuous_snd.neg).continuousOn
    fun _ hp ↦ ⟨mem_univ _, neg_nonneg.2 hp.2⟩

/-- **The gluing along the backward flow collar is Hausdorff.** On a compact Hausdorff manifold
`M` with boundary, let `V` be a smooth vector field pointing outward along the boundary and `e` an
open partial homeomorphism from the cylinder `ℝ × ∂M` to the interior of `M`, with source
`(-∞, 0) × ∂M`, given there by the backward flow `(t, s) ↦ forwardIntegralCurve (-V) s (-t)`.
Then the space obtained by gluing `ℝ × ∂M` to the interior of `M` along `e`, which is `M` with
the end `[0, ∞) × ∂M` attached along the boundary, is Hausdorff. -/
theorem t2Space_glueData
    {e : OpenPartialHomeomorph (ℝ × (𝓡∂ (n + 1)).boundary M) ((𝓡∂ (n + 1)).interior M)}
    (hsource : e.source = Prod.fst ⁻¹' Iio 0)
    (he : ∀ p ∈ e.source, (e p : M) = forwardIntegralCurve (-V) p.2 (-p.1)) :
    T2Space e.glueData.toGlueData.glued := by
  -- The backward flow extends `e` continuously to `(-∞, 0] × ∂M` in `M`, by the inclusion of the
  -- boundary on `{0} × ∂M`, which lies outside the interior.
  refine e.t2Space_glueData_of_continuousOn continuous_subtypeVal Subtype.val_injective
    (c := fun p ↦ forwardIntegralCurve (-V) p.2 (-p.1)) (F := Prod.fst ⁻¹' Iic 0)
    (isClosed_Iic.preimage continuous_fst)
    (hV.continuousOn_forwardIntegralCurve_neg.comp
      ((continuous_subtypeVal.comp continuous_snd).prodMk continuous_fst).continuousOn
      fun _ hp ↦ ⟨mem_univ _, hp⟩)
    (by rw [hsource]; exact preimage_mono Iio_subset_Iic_self) (fun p hp ↦ (he p hp).symm) ?_
  rintro p ⟨hp, hps⟩ ⟨x, hx⟩
  rw [hsource, mem_preimage, mem_Iio, not_lt] at hps
  rw [le_antisymm hp hps, neg_zero, forwardIntegralCurve_zero] at hx
  exact (𝓡∂ (n + 1)).disjoint_interior_boundary.ne_of_mem x.property p.2.property hx

end IsOutwardPointingField

end TauCeti
