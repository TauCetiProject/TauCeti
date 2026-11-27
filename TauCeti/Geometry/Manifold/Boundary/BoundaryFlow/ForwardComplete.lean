/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.SmoothFlow
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-!
# The forward flow of an inward field on a compact manifold with boundary

Let `M` be a compact Hausdorff manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)` and `v`
a smooth vector field on `M` pointing inward at every boundary point, in the sense that `-v a`
points outward (`TauCeti.IsOutwardPointing`). Then the integral curve of `v` through every point
exists for all nonnegative times, and these curves form a forward flow `Φ x t`, `t ≥ 0`, with the
semigroup law `Φ x (t + u) = Φ (Φ x t) u`, whose curves lie in the interior of `M` at every
positive time (`TauCeti.exists_forwardFlow`). Running it backwards, the integral curves of a field
pointing outward at every boundary point exist for all nonpositive times
(`TauCeti.IsOutwardPointingField.exists_backwardFlow`), and the backward flow-out of the boundary
is injective on `∂M × (-∞, 0]`, by `TauCeti.injOn_flowOut_boundary` applied to the forward flow of
the negated field. For the Liouville field of a Liouville domain this is the backward Liouville
flow used to collar the boundary of the domain by the negative half of its symplectization; this
file supplies its global existence and the injectivity of its flow-out, not its smoothness.

The interior statement is local. An integral curve defined on a left neighbourhood of a time `t`
cannot arrive at a boundary point at which the field points strictly inward
(`IsMIntegralCurveOn.not_isOutwardPointing_neg`): run backwards from `t`, the curve leaves the
boundary point with the outward velocity `-v (γ t)`, which
`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici` excludes.

The existence statement follows the uniform-time argument for compact manifolds without boundary
(Lee, Lemma 9.15 and Theorem 9.16). Near an interior point the local flow of
`TauCeti.Manifold.exists_contMDiffAt_localFlow` provides integral curves for a common time, and
near a boundary point the forward local flow of
`TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg` does. By compactness one positive
time `ε` serves every point, and attaching curves of length `ε / 2` end to end gives forward curves
of every length. Integral curves through boundary points are unique
(`IsMIntegralCurveOn.eqOn_of_isPreconnected`), so these curves are compatible and assemble into
the forward flow.

## Main results

* `IsMIntegralCurveOn.not_isOutwardPointing_neg`: an integral curve on a left neighbourhood of `t`
  does not meet the boundary at time `t` at a point where the field points strictly inward.
* `IsMIntegralCurveOn.apply_mem_interior_of_isOutwardPointing_neg`: if the field points inward at
  every boundary point, such a curve is in the interior of `M` at time `t`.
* `TauCeti.exists_forwardFlow`: the forward flow of an inward field on a compact manifold.
* `TauCeti.IsOutwardPointingField.exists_backwardFlow`: the backward flow of an outward field on a
  compact manifold, with injective backward flow-out of the boundary.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 9.15,
  Theorem 9.16 and Theorem 9.34.
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §2(a) (the completion of a Liouville domain along the backward Liouville flow).
-/

public section

open Filter Function Manifold Set
open scoped ContDiff Manifold Pointwise Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

namespace IsMIntegralCurveOn

open TauCeti

variable {v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-- **Integral curves do not arrive at the boundary where the field points inward.** If `γ` is an
integral curve of `v` on a set `s` of times which is a neighbourhood of `t` on the left, then
`v` does not point strictly inward at `γ t`: either `γ t` is an interior point, or `-v (γ t)` is
not outward. -/
theorem not_isOutwardPointing_neg (hγ : IsMIntegralCurveOn γ v s) (ht : t ∈ s)
    (hs : s ∈ 𝓝[≤] t) : ¬IsOutwardPointing (γ t) (-v (γ t)) := by
  -- Reversed in time, `γ` runs for parameters `≥ -t` with velocity `-v (γ t)` at `-t`.
  have hs' : -s ∈ 𝓝[≥] (-t) := by
    obtain ⟨l, hl, hls⟩ := mem_nhdsLE_iff_exists_Ioc_subset.mp hs
    refine mem_of_superset (Ico_mem_nhdsGE (neg_lt_neg (mem_Iio.mp hl))) fun r hr ↦ hls ?_
    exact ⟨lt_neg_of_lt_neg hr.2, neg_le.mp hr.1⟩
  have hc := ((hγ.comp_neg) (-t) (by rwa [Set.mem_neg, neg_neg])).mono_of_mem_nhdsWithin hs'
  have h := not_isOutwardPointing_curveVelocityWithin_Ici (n := n) (fun r ↦ γ (-r)) (-t)
  rw [Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt hc (uniqueDiffWithinAt_Ici _)] at h
  simp only [Pi.neg_apply] at h
  rwa [neg_neg] at h

/-- **Integral curves stay off the boundary of an inward field.** If `v` points inward at every
boundary point and `γ` is an integral curve of `v` on a set of times which is a neighbourhood of
`t` on the left, then `γ t` is an interior point. -/
theorem apply_mem_interior_of_isOutwardPointing_neg (hγ : IsMIntegralCurveOn γ v s) (ht : t ∈ s)
    (hs : s ∈ 𝓝[≤] t) (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    γ t ∈ (𝓡∂ (n + 1)).interior M := by
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint (γ t) with h | h
  · exact h
  · exact absurd (hin _ h) (hγ.not_isOutwardPointing_neg ht hs)

end IsMIntegralCurveOn

namespace TauCeti

variable [IsManifold (𝓡∂ (n + 1)) ∞ M] {v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}

/-- On a compact manifold, the forward integral curves of an inward field exist for one common
positive time through every point. -/
private theorem exists_pos_forall_exists_isMIntegralCurveOn_Ico [CompactSpace M]
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ∃ ε > 0, ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ε) := by
  -- Near every point, the forward integral curves exist for a common time.
  have hloc (a : M) : ∃ U ∈ 𝓝 a, ∃ ε > 0, ∀ x ∈ U,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ε) := by
    rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint a with ha | ha
    · obtain ⟨U, hU, s, hs, -, Φ, -, hΦ⟩ :=
        Manifold.exists_contMDiffAt_localFlow v a hv.contMDiffOn univ_mem ha
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
      refine ⟨U, hU, ε, hε, fun x hx ↦ ⟨Φ x, (hΦ x hx).1, (hΦ x hx).2.1.mono fun r hr ↦ hball ?_⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [hr.1], hr.2⟩
    · obtain ⟨U, hU, ε, hε, Φ, -, hΦ⟩ :=
        exists_contMDiffOn_localFlow_of_isOutwardPointing_neg v hv.contMDiffOn univ_mem (hin a ha)
      exact ⟨U, hU, ε, hε, fun x hx ↦ ⟨Φ x, (hΦ x hx).1, (hΦ x hx).2.1⟩⟩
  choose U hU ε hε hγ using hloc
  -- Finitely many of these neighbourhoods cover `M`; take the least of their times.
  obtain ⟨T, -, hT⟩ := isCompact_univ.elim_nhds_subcover U fun a _ ↦ hU a
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
  have hTne : T.Nonempty := by
    obtain ⟨a, ha, -⟩ := mem_iUnion₂.mp (hT (mem_univ x₀))
    exact ⟨a, ha⟩
  refine ⟨T.inf' hTne ε, (Finset.lt_inf'_iff hTne).2 fun a _ ↦ hε a, fun x ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hT (mem_univ x))
  obtain ⟨γ, hγ0, hγc⟩ := hγ a x hxa
  exact ⟨γ, hγ0, hγc.mono (Ico_subset_Ico_right (Finset.inf'_le ε ha))⟩

/-- On a compact manifold, the forward integral curves of an inward field exist through every
point for every length of time. -/
private theorem exists_isMIntegralCurveOn_Icc [CompactSpace M]
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (T : ℝ) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Icc 0 T) := by
  obtain ⟨ε, hε, hloc⟩ := exists_pos_forall_exists_isMIntegralCurveOn_Ico hv hin
  -- Curves of length `k * (ε / 2)`, by attaching a curve of length `ε / 2` at the end point.
  have hstep (k : ℕ) (x : M) :
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Icc 0 (k * (ε / 2))) := by
    induction k generalizing x with
    | zero =>
      obtain ⟨γ, hγ0, hγ⟩ := hloc x
      exact ⟨γ, hγ0, hγ.mono fun t ht ↦ ⟨ht.1, ht.2.trans_lt (by simpa using hε)⟩⟩
    | succ k ih =>
      obtain ⟨γ, hγ0, hγ⟩ := ih x
      set L := (k : ℝ) * (ε / 2)
      have hL0 : 0 ≤ L := by positivity
      obtain ⟨c, hc0, hc⟩ := hloc (γ L)
      classical
      refine ⟨fun t ↦ if t ≤ L then γ t else c (t + -L), by simp [hL0, hγ0], ?_⟩
      rw [show ((k + 1 : ℕ) : ℝ) * (ε / 2) = L + ε / 2 by push_cast; ring,
        ← Icc_union_Icc_eq_Icc hL0 (by linarith)]
      refine IsMIntegralCurveOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
      · exact hγ.congr fun t ht ↦ by simp [ht.2]
      · refine ((hc.comp_add (-L)).mono fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩).congr
          fun t ht ↦ ?_
        rcases ht.1.lt_or_eq with h | h
        · simp [not_le.2 h]
        · simp [← h, hc0]
  obtain ⟨k, hk⟩ := exists_nat_ge (T / (ε / 2))
  obtain ⟨γ, hγ0, hγ⟩ := hstep k x
  exact ⟨γ, hγ0, hγ.mono (Icc_subset_Icc_right ((div_le_iff₀ (by positivity)).mp hk))⟩

/-- **The forward flow of an inward field.** Let `v` be a smooth vector field on a compact
Hausdorff manifold modeled on `𝓡∂ (n + 1)`, pointing inward at every boundary point. Then there is
a family `Φ x t` such that for every `x` the curve `t ↦ Φ x t` starts at `x`, is an integral curve
of `v` for all times `t ≥ 0`, and lies in the interior of `M` at every positive time, and
`Φ x (t + u) = Φ (Φ x t) u` for all `t, u ≥ 0`. Each of these curves is the only integral curve of
`v` on `[0, ∞)` from its starting point, by `IsMIntegralCurveOn.eqOn_of_isPreconnected`. -/
theorem exists_forwardFlow [CompactSpace M] [T2Space M]
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ∃ Φ : M → ℝ → M, ∀ x, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Ici 0) ∧
      (∀ t, 0 < t → Φ x t ∈ (𝓡∂ (n + 1)).interior M) ∧
      ∀ t, 0 ≤ t → ∀ u, 0 ≤ u → Φ x (t + u) = Φ (Φ x t) u := by
  have hv1 (y : M) : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) y :=
    (hv y).of_le (by simp)
  choose γ hγ0 hγ using fun (x : M) (k : ℕ) ↦ exists_isMIntegralCurveOn_Icc hv hin k x
  -- The curve on `[0, k]` from `x` extends the curves on the shorter intervals.
  have hagree (x : M) {k l : ℕ} (hkl : k ≤ l) : EqOn (γ x k) (γ x l) (Icc 0 k) :=
    (hγ x k).eqOn_of_isPreconnected ((hγ x l).mono (Icc_subset_Icc_right (by exact_mod_cast hkl)))
      isPreconnected_Icc (left_mem_Icc.2 (Nat.cast_nonneg k)) (fun t _ ↦ hv1 _)
      ((hγ0 x k).trans (hγ0 x l).symm)
  -- At time `t`, read the flow on the curve of length `⌈t⌉`.
  let Φ : M → ℝ → M := fun x t ↦ γ x ⌈t⌉₊ t
  have hΦ (x : M) (k : ℕ) : EqOn (Φ x) (γ x k) (Icc 0 k) := fun t ht ↦
    hagree x (Nat.ceil_le.2 ht.2) ⟨ht.1, Nat.le_ceil t⟩
  have hΦ0 (x : M) : Φ x 0 = x := by simp [Φ, hγ0]
  have hΦc (x : M) : IsMIntegralCurveOn (Φ x) v (Ici 0) := by
    intro t ht
    -- Near `t`, the flow is the curve of length `⌈t⌉ + 1`.
    have htk : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := (Nat.le_ceil t).trans_lt (by push_cast; linarith)
    have hmem : Icc 0 ((⌈t⌉₊ + 1 : ℕ) : ℝ) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds htk)
    exact (((hγ x _).congr (hΦ x _)) t ⟨ht, htk.le⟩).mono_of_mem_nhdsWithin hmem
  refine ⟨Φ, fun x ↦ ⟨hΦ0 x, hΦc x, fun t ht ↦ ?_, fun t ht u hu ↦ ?_⟩⟩
  · exact (hΦc x).apply_mem_interior_of_isOutwardPointing_neg ht.le
      (nhdsWithin_le_nhds (Ici_mem_nhds ht)) hin
  · -- Both sides are integral curves on `[0, ∞)` with the same value at `u = 0`.
    have hshift : IsMIntegralCurveOn (Φ x ∘ (· + t)) v (Ici 0) :=
      ((hΦc x).comp_add t).mono fun r hr ↦ add_nonneg hr ht
    have h := hshift.eqOn_of_isPreconnected (hΦc (Φ x t)) isPreconnected_Ici (mem_Ici.2 le_rfl)
      (fun r _ ↦ hv1 _) (by simp [hΦ0]) hu
    rw [add_comm]
    exact h

/-- **The backward flow of an outward field.** Let `V` be a smooth vector field on a compact
Hausdorff manifold modeled on `𝓡∂ (n + 1)`, pointing outward at every boundary point. Then there
is a family `Φ x t` such that for every `x` the curve `t ↦ Φ x t` starts at `x`, is an integral
curve of `V` for all times `t ≤ 0`, and lies in the interior of `M` at every negative time, and
`Φ x (t + u) = Φ (Φ x t) u` for all `t, u ≤ 0`. Moreover the backward flow-out
`(x, t) ↦ Φ x t` of the boundary is injective on `∂M × (-∞, 0]`. -/
theorem IsOutwardPointingField.exists_backwardFlow [CompactSpace M] [T2Space M]
    {V : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hV : IsOutwardPointingField V) :
    ∃ Φ : M → ℝ → M, (∀ x, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) V (Iic 0) ∧
      (∀ t, t < 0 → Φ x t ∈ (𝓡∂ (n + 1)).interior M) ∧
      ∀ t, t ≤ 0 → ∀ u, u ≤ 0 → Φ x (t + u) = Φ (Φ x t) u) ∧
      InjOn (fun p : M × ℝ ↦ Φ p.1 p.2) ((𝓡∂ (n + 1)).boundary M ×ˢ Iic 0) := by
  have hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, (-V) x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) :=
    fun x ↦ (hV.contMDiff x).neg_section
  obtain ⟨Ψ, hΨ⟩ := exists_forwardFlow hv fun a ha ↦ by simpa using hV.isOutwardPointing ha
  -- The forward flow-out of the boundary along `-V` is injective.
  have hinj := injOn_flowOut_boundary (W := univ) (Φ := Ψ) (hv.of_le (by simp))
    fun x _ t _ _ ↦ ⟨fun _ _ ↦ mem_univ _, (hΨ x).1, (hΨ x).2.1.mono Icc_subset_Ici_self,
      (hΨ x).2.2.1 t⟩
  refine ⟨fun x t ↦ Ψ x (-t), fun x ↦ ⟨by simpa using (hΨ x).1, ?_,
    fun t ht ↦ (hΨ x).2.2.1 (-t) (neg_pos.2 ht), fun t ht u hu ↦ ?_⟩, ?_⟩
  · simpa using (hΨ x).2.1.comp_neg
  · simp only [neg_add]
    exact (hΨ x).2.2.2 (-t) (neg_nonneg.2 ht) (-u) (neg_nonneg.2 hu)
  · rintro ⟨x, a⟩ ⟨hx, ha⟩ ⟨y, b⟩ ⟨hy, hb⟩ h
    have h' := @hinj (x, -a) ⟨mem_univ _, hx, neg_nonneg.2 ha⟩ (y, -b)
      ⟨mem_univ _, hy, neg_nonneg.2 hb⟩ h
    simp only [Prod.mk.injEq, neg_inj] at h'
    rw [h'.1, h'.2]

end TauCeti

end
