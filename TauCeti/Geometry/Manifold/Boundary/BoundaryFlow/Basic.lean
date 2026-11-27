/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.InwardFlow
public import TauCeti.Geometry.Manifold.IntegralCurve.Interval

/-!
# The inward flow of the whole boundary

Let `M` be a smooth Hausdorff manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)` and `v` a
smooth vector field on `M` pointing inward at every boundary point, in the sense that `-v a` points
outward (`TauCeti.IsOutwardPointing`); for instance the negative of a field given by
`TauCeti.exists_isOutwardPointingField`. The local forward flows of `v` near the boundary points
(`TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`) agree where they overlap, because
integral curves are unique through boundary points
(`IsMIntegralCurveOn.eqOn_of_isPreconnected`). They glue to one forward flow `Φ x t`, defined and
jointly smooth for `t ≥ 0` on an open set `W ⊆ M × ℝ` containing `∂M × {0}`, whose curves start at
their initial point, are integral curves of `v`, and lie in the interior of `M` at every positive
time (`TauCeti.exists_contMDiffOn_boundaryFlow`). The time slices of `W` in `[0, ∞)` are intervals
starting at `0`.

This is the first step of the flow construction of a smooth collar (Hirsch, *Differential
Topology*, Chapter 4, Theorem 6.1; Lee, *Introduction to Smooth Manifolds*, Theorem 9.25). The
next step is that the flow-out `(x, t) ↦ Φ x t` of the boundary is injective at nonnegative times
(`TauCeti.injOn_flowOut_boundary`): forward integral curves that start on the boundary and lie in
the interior at positive times meet only at equal times and from the same starting point
(`IsMIntegralCurveOn.eq_and_apply_zero_eq_of_apply_eq`). This holds for any model with corners
and a C¹ field.

## Main results

* `TauCeti.exists_contMDiffOn_boundaryFlow`: the forward flow of an inward-pointing smooth vector
  field along the whole boundary.
* `TauCeti.IsOutwardPointingField.exists_contMDiffOn_boundaryFlow`: the same for the negative of a
  smooth outward-pointing field.
* `TauCeti.injOn_flowOut_boundary`: the flow-out of the boundary along such a flow is injective.
-/

public section

open Bundle Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section HalfSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M]

/-- Two forward integral curves of a smooth vector field from the same point agree on the common
interval `[0, ε)`. -/
private theorem eqOn_Ico_of_isMIntegralCurveOn {v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    {γ δ : ℝ → M} {ε : ℝ} (hγ : IsMIntegralCurveOn γ v (Ico 0 ε))
    (hδ : IsMIntegralCurveOn δ v (Ico 0 ε)) (hε : 0 < ε) (h0 : γ 0 = δ 0) :
    EqOn γ δ (Ico 0 ε) :=
  hγ.eqOn_of_isPreconnected hδ isPreconnected_Ico (left_mem_Ico.2 hε)
    (fun t _ ↦ (hv (γ t)).of_le (by simp)) h0

/-- **The inward flow of the boundary.** Let `v` be a smooth vector field on a Hausdorff manifold
modeled on `𝓡∂ (n + 1)`, pointing inward at every boundary point. There are an open set
`W ⊆ M × ℝ` containing `(a, 0)` for every boundary point `a`, and a family `Φ x t`, jointly smooth
on the part of `W` with `t ≥ 0`, such that for every `(x, t) ∈ W` with `t ≥ 0`: the segment
`{x} × [0, t]` lies in `W`, the curve `s ↦ Φ x s` starts at `x` and is an integral curve of `v`
on `[0, t]`, and `Φ x t` is in the interior of `M` if `t > 0`. -/
theorem exists_contMDiffOn_boundaryFlow (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ∃ W : Set (M × ℝ), IsOpen W ∧ (∀ a ∈ (𝓡∂ (n + 1)).boundary M, (a, (0 : ℝ)) ∈ W) ∧
      ∃ Φ : M → ℝ → M,
        ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ)) (𝓡∂ (n + 1)) ∞ (fun p : M × ℝ ↦ Φ p.1 p.2)
          (W ∩ univ ×ˢ Ici 0) ∧
        ∀ x t, (x, t) ∈ W → 0 ≤ t →
          (∀ s ∈ Icc 0 t, (x, s) ∈ W) ∧ Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Icc 0 t) ∧
            (0 < t → Φ x t ∈ (𝓡∂ (n + 1)).interior M) := by
  -- The local flows at the boundary points.
  have hloc (a : (𝓡∂ (n + 1)).boundary M) := exists_contMDiffOn_localFlow_of_isOutwardPointing_neg
    v (V := univ) hv.contMDiffOn univ_mem (hin a a.property)
  choose U hU ε hε φ hφ hφx using hloc
  -- Open pieces `interior (U a) × (-ε a, ε a)`.
  set P : (𝓡∂ (n + 1)).boundary M → Set (M × ℝ) := fun a ↦
    interior (U a) ×ˢ Ioo (-ε a) (ε a)
  have hPopen (a) : IsOpen (P a) := isOpen_interior.prod isOpen_Ioo
  -- On a piece, the forward times lie in `[0, ε a)`.
  have hPIco {a} {x : M} {t : ℝ} (hp : (x, t) ∈ P a) (ht : 0 ≤ t) :
      (x, t) ∈ U a ×ˢ Ico 0 (ε a) :=
    ⟨interior_subset hp.1, ht, hp.2.2⟩
  -- Two local flows agree on their common forward domain.
  have hagree {a b} {x : M} (ha : x ∈ U a) (hb : x ∈ U b) {t : ℝ} (hta : t ∈ Ico 0 (ε a))
      (htb : t ∈ Ico 0 (ε b)) : φ a x t = φ b x t := by
    have hm : 0 < min (ε a) (ε b) := lt_min (hε a) (hε b)
    refine eqOn_Ico_of_isMIntegralCurveOn hv ((hφx a x ha).2.1.mono ?_)
      ((hφx b x hb).2.1.mono ?_) hm (by rw [(hφx a x ha).1, (hφx b x hb).1]) ⟨hta.1, ?_⟩
    · exact Ico_subset_Ico_right (min_le_left _ _)
    · exact Ico_subset_Ico_right (min_le_right _ _)
    · exact lt_min hta.2 htb.2
  -- The glued flow.
  classical
  let Φ : M → ℝ → M := fun x t ↦
    if h : ∃ a, x ∈ U a ∧ t ∈ Ico 0 (ε a) then φ h.choose x t else x
  have hΦeq {a} {x : M} {t : ℝ} (hx : x ∈ U a) (ht : t ∈ Ico 0 (ε a)) : Φ x t = φ a x t := by
    have h : ∃ a, x ∈ U a ∧ t ∈ Ico 0 (ε a) := ⟨a, hx, ht⟩
    simp only [Φ, dite_eq_left h]
    exact hagree h.choose_spec.1 hx h.choose_spec.2 ht
  refine ⟨⋃ a, P a, isOpen_iUnion hPopen, fun a ha ↦ mem_iUnion.2 ⟨⟨a, ha⟩,
    mem_interior_iff_mem_nhds.2 (hU ⟨a, ha⟩), by simpa using hε ⟨a, ha⟩⟩, Φ, ?_, ?_⟩
  · -- Smoothness: near a point of a piece, `Φ` is the local flow of that piece.
    rintro ⟨x, t⟩ ⟨hp, ht⟩
    obtain ⟨a, ha⟩ := mem_iUnion.1 hp
    have hxt : (x, t) ∈ U a ×ˢ Ico 0 (ε a) := hPIco ha (by simpa using ht)
    have hsub : P a ∩ ((⋃ a, P a) ∩ univ ×ˢ Ici 0) ⊆ U a ×ˢ Ico 0 (ε a) := fun q hq ↦
      hPIco hq.1 (by simpa using hq.2.2.2)
    have hmem : U a ×ˢ Ico 0 (ε a) ∈ 𝓝[(⋃ a, P a) ∩ univ ×ˢ Ici 0] (x, t) :=
      mem_nhdsWithin.2 ⟨P a, hPopen a, ha, hsub⟩
    exact ((hφ a (x, t) hxt).congr (fun q hq ↦ hΦeq hq.1 hq.2)
      (hΦeq hxt.1 hxt.2)).mono_of_mem_nhdsWithin hmem
  · intro x t hp ht
    obtain ⟨a, ha⟩ := mem_iUnion.1 hp
    obtain ⟨hxU, htI⟩ := hPIco ha ht
    have hIcc : Icc 0 t ⊆ Ico 0 (ε a) := Icc_subset_Ico_right htI.2
    refine ⟨fun s hs ↦ mem_iUnion.2 ⟨a, ha.1, by linarith [hε a, hs.1], hs.2.trans_lt htI.2⟩,
      ?_, ?_, fun htpos ↦ ?_⟩
    · rw [hΦeq hxU (left_mem_Ico.2 (hε a))]
      exact (hφx a x hxU).1
    · exact ((hφx a x hxU).2.1.mono hIcc).congr fun r hr ↦ hΦeq hxU (hIcc hr)
    · rw [hΦeq hxU htI]
      exact (hφx a x hxU).2.2 t ⟨htpos, htI.2⟩

/-- **The inward flow of the boundary along an outward field.** For a smooth field `V` pointing
outward at every boundary point, the conclusion of `TauCeti.exists_contMDiffOn_boundaryFlow` holds
for the inward field `-V`. On a Hausdorff sigma-compact manifold such a `V` exists by
`TauCeti.exists_isOutwardPointingField`. -/
theorem IsOutwardPointingField.exists_contMDiffOn_boundaryFlow
    {V : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hV : IsOutwardPointingField V) :
    ∃ W : Set (M × ℝ), IsOpen W ∧ (∀ a ∈ (𝓡∂ (n + 1)).boundary M, (a, (0 : ℝ)) ∈ W) ∧
      ∃ Φ : M → ℝ → M,
        ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ)) (𝓡∂ (n + 1)) ∞ (fun p : M × ℝ ↦ Φ p.1 p.2)
          (W ∩ univ ×ˢ Ici 0) ∧
        ∀ x t, (x, t) ∈ W → 0 ≤ t →
          (∀ s ∈ Icc 0 t, (x, s) ∈ W) ∧ Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) (-V) (Icc 0 t) ∧
            (0 < t → Φ x t ∈ (𝓡∂ (n + 1)).interior M) := by
  exact TauCeti.exists_contMDiffOn_boundaryFlow (-V)
    hV.contMDiff_neg hV.isOutwardPointing_neg_neg

end HalfSpace

section FlowOut

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
  {v : (x : M) → TangentSpace I x}

/-- **The flow-out of the boundary is injective.** Let `Φ x t` be a forward flow of a C¹ vector
field `v`, given on a set `W ⊆ M × ℝ` as by `TauCeti.exists_contMDiffOn_boundaryFlow`: for a
boundary point `x` and `(x, t) ∈ W` with `t ≥ 0`, the segment `{x} × [0, t]` lies in `W`, the
curve `s ↦ Φ x s` starts at `x` and is an integral curve of `v` on `[0, t]`, and `Φ x t` lies in
the interior of `M` if `t > 0`. Then `(x, t) ↦ Φ x t` is injective on the points of `W` over the
boundary of `M` at nonnegative times. -/
theorem injOn_flowOut_boundary {W : Set (M × ℝ)} {Φ : M → ℝ → M}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hΦ : ∀ x ∈ I.boundary M, ∀ t, (x, t) ∈ W → 0 ≤ t →
      (∀ s ∈ Icc 0 t, (x, s) ∈ W) ∧ Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Icc 0 t) ∧
        (0 < t → Φ x t ∈ I.interior M)) :
    InjOn (fun p : M × ℝ ↦ Φ p.1 p.2) (W ∩ I.boundary M ×ˢ Ici 0) := by
  rintro ⟨x, a⟩ ⟨hxa, hx, ha⟩ ⟨y, b⟩ ⟨hyb, hy, hb⟩ h
  obtain ⟨hxW, hx0, hxc, -⟩ := hΦ x hx a hxa ha
  obtain ⟨hyW, hy0, hyc, -⟩ := hΦ y hy b hyb hb
  -- Along each curve, the positive times stay in `W`, so the curve is in the interior there.
  obtain ⟨rfl, h0⟩ := hxc.eq_and_apply_zero_eq_of_apply_eq hyc ha hb (by rwa [hx0]) (by rwa [hy0])
    (fun t ht ↦ (hΦ x hx t (hxW t (Ioc_subset_Icc_self ht)) ht.1.le).2.2.2 ht.1)
    (fun t ht ↦ (hΦ y hy t (hyW t (Ioc_subset_Icc_self ht)) ht.1.le).2.2.2 ht.1)
    (fun t _ ↦ hv _) h
  rw [hx0, hy0] at h0
  rw [h0]

end FlowOut

end TauCeti
