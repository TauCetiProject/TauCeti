/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.RadialLength

/-!
# The escape estimate for normal neighbourhoods

This module provides the escape estimate for normal neighbourhoods: a path that starts at the
centre and leaves the exponential image of the domain has length at least the radius of a smaller
tangent ball contained in that domain. It also provides a strict comparison with the radial segment
to a point in the smaller ball when the path leaves the larger domain.

Together with radial minimization, these estimates are used to obtain the local distance identity
on a normal ball. The first-exit organization follows the Apache-2.0
`frenzymath/Poincare-Conjecture` formalization, revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`, especially
`DoCarmoLib/Riemannian/Exponential/NormalBallEDist.lean` and
`DoCarmoLib/Riemannian/Exponential/MinimizingPathPiecewise.lean`; the proof here is written
against Tau Ceti's normal-domain and Riemannian path-length APIs.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Proposition 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, Prop. 6.11.
-/

public section

open Bundle Filter Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **The escape estimate for a normal neighbourhood.** If a `C¹` path starts at the centre
`p` of a normal domain `U` and meets the complement of `riemannianExp p '' U`, then its length is
at least `ENNReal.ofReal r` whenever `0 < r` and `Metric.closedBall 0 r ⊆ U`. -/
theorem IsNormalDomain.pathELength_escape
    {p : M} {U : Set (TangentSpace I p)} {r : ℝ}
    (h : IsNormalDomain I M p U)
    (hr : 0 < r) (hclosed : Metric.closedBall 0 r ⊆ U)
    {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγ0 : γ 0 = p)
    (hex : ∃ t ∈ Icc 0 1, γ t ∉ riemannianExp I M p '' U) :
    ENNReal.ofReal r ≤ Manifold.pathELength I γ 0 1 := by
  -- Shrink the normal domain to the open ball used for the first exit.
  have hsmall : IsNormalDomain I M p (Metric.ball 0 r) :=
    h.mono (Metric.ball_subset_closedBall.trans hclosed) Metric.isOpen_ball
      (Metric.mem_ball_self hr)
      ((convex_ball (0 : TangentSpace I p) r).starConvex
        (Metric.mem_ball_self hr))
  -- `V` is the open inner image and `K` is its compact closed image.
  set V : Set M := riemannianExp I M p '' Metric.ball 0 r
  set K : Set M := riemannianExp I M p '' Metric.closedBall 0 r
  have hVopen : IsOpen V := hsmall.isOpen_image
  have hKcompact : IsCompact K :=
    isCompact_riemannianExp_image_closedBall p (hclosed.trans h.subset_expDomain)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hVK : V ⊆ K := image_mono Metric.ball_subset_closedBall
  have hVouter : V ⊆ riemannianExp I M p '' U :=
    image_mono (Metric.ball_subset_closedBall.trans hclosed)
  have hKouter : K ⊆ riemannianExp I M p '' U := image_mono hclosed
  have h0 : γ 0 ∈ V := by
    rw [hγ0]
    exact hsmall.self_mem_image
  have hexV : ∃ t ∈ Icc 0 1, γ t ∉ V := by
    obtain ⟨t, ht, htU⟩ := hex
    refine ⟨t, ht, fun hmem => htU (hVouter hmem)⟩
  obtain ⟨t₀, ht₀, ht₀V⟩ := hexV
  -- The first time the path leaves `V` is the least point of this compact set.
  set A : Set ℝ := Icc 0 1 ∩ γ ⁻¹' Vᶜ
  have hA_closed : IsClosed A :=
    hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hVopen.isClosed_compl
  have hA_ne : A.Nonempty := ⟨t₀, ht₀, ht₀V⟩
  have hAcompact : IsCompact A :=
    isCompact_Icc.of_isClosed_subset hA_closed (fun t ht => ht.1)
  obtain ⟨T, hT⟩ := hAcompact.exists_isLeast hA_ne
  have hTA : T ∈ A := hT.1
  have hT01 : T ∈ Icc 0 1 := hTA.1
  have hTpos : 0 < T := by
    rcases eq_or_lt_of_le hTA.1.1 with h | h
    · subst T
      exact (hTA.2 h0).elim
    · exact h
  have hbefore : ∀ t, 0 ≤ t → t < T → γ t ∈ V := by
    intro t ht0 htT
    by_contra hnot
    have hmem : t ∈ A :=
      ⟨⟨ht0, htT.le.trans hT01.2⟩, hnot⟩
    exact (not_le.mpr htT) (hT.2 hmem)
  have hne : (𝓝[Ioo (0 : ℝ) T] T).NeBot :=
    right_nhdsWithin_Ioo_neBot hTpos
  have htend : Tendsto γ (𝓝[Ioo (0 : ℝ) T] T) (𝓝 (γ T)) :=
    ((hγ.continuousOn T hT01).mono
      (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hT01.2))).tendsto
  -- Continuity from the left puts the first exit in the closed exponential image.
  have hγT_K : γ T ∈ K :=
    hKclosed.mem_of_tendsto htend
      (eventually_nhdsWithin_of_forall fun t ht => hVK (hbefore t ht.1.le ht.2))
  obtain ⟨z, hz, hzγ⟩ := hγT_K
  have hznorm : ‖z‖ = r := by
    have hzle : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
    rcases lt_or_eq_of_le hzle with hlt | heq
    · exfalso
      apply hTA.2
      exact ⟨z, mem_ball_zero_iff.mpr hlt, hzγ⟩
    · exact heq
  have hzU : z ∈ U := hclosed hz
  have hγT_U : γ T ∈ riemannianExp I M p '' U := hKouter ⟨z, hz, hzγ⟩
  have hγT_eq : γ T = riemannianExp I M p z := hzγ.symm
  have hγprefix : MapsTo γ (Icc 0 T) (riemannianExp I M p '' U) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact hVouter (hbefore t ht.1 hlt)
    · simpa [heq] using hγT_U
  -- Apply the polar comparison to the prefix ending at the first exit.
  have hbound := h.ofReal_norm_riemannianLog_le_pathELength
    (a := 0) (b := T) hTpos.le
    (hγ.mono (Icc_subset_Icc le_rfl hT01.2)) hγprefix hγ0
  have hlog : riemannianLog I M p U (γ T) = z := by
    rw [hγT_eq]
    exact h.riemannianLog_riemannianExp hzU
  rw [hlog, hznorm] at hbound
  exact hbound.trans (Manifold.pathELength_mono (a := 0) (b := T)
    (a' := 0) (b' := 1) le_rfl hT01.2)

/-- A `C¹` competitor that starts at the centre and leaves the larger normal domain is strictly
longer than the radial segment to a point in a smaller normal ball. -/
theorem IsNormalDomain.pathELength_riemannianExp_smul_lt_of_not_mapsTo
    {p : M} {U : Set (TangentSpace I p)} {r : ℝ}
    {v : TangentSpace I p}
    (h : IsNormalDomain I M p U)
    (hclosed : Metric.closedBall 0 r ⊆ U)
    (hv : v ∈ Metric.ball 0 r)
    {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγ0 : γ 0 = p)
    (hleave : ¬ MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) :
    Manifold.pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1
      < Manifold.pathELength I γ 0 1 := by
  have hex : ∃ t ∈ Icc 0 1, γ t ∉ riemannianExp I M p '' U := by
    by_contra h
    apply hleave
    intro t ht
    by_contra hnot
    apply h
    exact ⟨t, ht, hnot⟩
  have hvU : v ∈ U := (Metric.ball_subset_closedBall.trans hclosed) hv
  have hr : 0 < r :=
    lt_of_le_of_lt (norm_nonneg v) (mem_ball_zero_iff.mp hv)
  have hesc := h.pathELength_escape hr hclosed hγ hγ0 hex
  have hrad := pathELength_riemannianExp_smul_zero_one h hvU
  have hnorm : ‖v‖ < r := mem_ball_zero_iff.mp hv
  have hrad_lt : Manifold.pathELength I
      (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 < ENNReal.ofReal r := by
    rw [hrad, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hnorm
  exact hrad_lt.trans_le hesc

end TauCeti.Manifold

end
