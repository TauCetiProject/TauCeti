/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Global lower distance bounds on compact sets

For a continuous injection on a compact set, a uniform lower distance bound for nearby pairs
extends to all pairs. Away from the diagonal, compactness and injectivity supply the missing
positive lower bound. This lets local differential estimates give quantitative embeddings.
-/

public section

open Set Metric

namespace IsCompact

/-- A continuous injection on a compact set with a positive uniform lower distance bound for
nearby pairs is antilipschitz on that set. -/
theorem exists_antilipschitzWith_of_locally
    {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y] {s : Set X}
    (hs : IsCompact s) {f : X → Y} (hf : ContinuousOn f s)
    (hinj : InjOn f s)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hlocal : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ → c * dist x y ≤ dist (f x) (f y)) :
    ∃ K > 0, AntilipschitzWith K (s.domRestrict f) := by
  let T : Set (X × X) := (s ×ˢ s) ∩ {p | δ ≤ dist p.1 p.2}
  have hT : IsCompact T := (hs.prod hs).inter_right
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  have hfst : ContinuousOn (f ∘ Prod.fst) T :=
    hf.comp continuousOn_fst fun p hp => hp.1.1
  have hsnd : ContinuousOn (f ∘ Prod.snd) T :=
    hf.comp continuousOn_snd fun p hp => hp.1.2
  have hcont : ContinuousOn (fun p : X × X => dist (f p.1) (f p.2) / dist p.1 p.2) T := by
    refine (continuous_dist.comp_continuousOn (hfst.prodMk hsnd)).div
      (continuous_fst.dist continuous_snd).continuousOn ?_
    exact fun p hp => ne_of_gt (hδ.trans_le hp.2)
  obtain ⟨a, ha, hbound⟩ := hT.exists_forall_le' hcont (a := 0) fun p hp => by
    refine div_pos (dist_pos.mpr fun h => ?_) (hδ.trans_le hp.2)
    have heq := hinj hp.1.1 hp.1.2 h
    exact (ne_of_gt (hδ.trans_le hp.2)) (by rw [heq, dist_self])
  have hb : 0 < min c a := lt_min hc ha
  refine ⟨⟨(min c a)⁻¹, (inv_pos.mpr hb).le⟩, inv_pos.mpr hb,
    AntilipschitzWith.of_le_mul_dist ?_⟩
  intro x y
  -- Unwrap the restriction, subtype metric and chosen constant together: simplifying them
  -- separately can unfold NNReal to a subtype and invalidate the coercion's type.
  change dist (x : X) y ≤ (min c a)⁻¹ * dist (f x) (f y)
  rw [← div_eq_inv_mul, le_div_iff₀ hb, mul_comm]
  have hx := x.2
  have hy := y.2
  by_cases hxy : dist (x : X) y < δ
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) dist_nonneg).trans
      (hlocal x hx y hy hxy)
  · have h := hbound (x, y) ⟨⟨hx, hy⟩, le_of_not_gt hxy⟩
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) dist_nonneg).trans
      ((le_div_iff₀ (hδ.trans_le (le_of_not_gt hxy))).mp h)

end IsCompact
