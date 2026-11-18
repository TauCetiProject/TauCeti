/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.IsLocalHomeomorph.Lifting
import Mathlib.Topology.Compactness.Compact

/-!
# Compact continuation of interval lifts

Let `f : X → Y` be locally homeomorphic on an open set `U`, with `Y` preregular. A curve on a
closed interval lifts from `q ∈ U` if every lifted initial segment staying in `U` has endpoint
in one fixed compact set `K ⊆ U`. The resulting lift stays in `K` throughout the interval.
Neither space needs to be complete.

The limit-time theorem extends lifts from every proper initial segment to the closed interval
and puts its terminal value in `closure K`. For closed `K`, this is membership in `K`. In a
preregular space a compact set can omit points inseparable from its members, so terminal
membership in `K` cannot follow from proper-prefix confinement alone. Combined with right
continuation, this limit theorem gives full-interval lifting by Mathlib's continuous induction.

The Riemannian exponential-map consumer in `Geodesic.Lifting` derives the compact confinement
from the polar length inequality on a nonsingular tangent ball.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter Function
open scoped Topology

namespace IsLocalHomeomorphOn

/-- Compact endpoint confinement supplies an inverse chart meeting an initial lift and covering
the remaining curve. Its inverse sends the terminal curve value into the closure of the compact
set, even when the codomain is only preregular. -/
private theorem exists_chart_tail
    {α X Y : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y]
    {f : X → Y} {U : Set X} (hf : IsLocalHomeomorphOn f U) (hU : IsOpen U)
    {c : α → Y} {a T : α} (haT : a < T) (hc : ContinuousOn c (Icc a T))
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) {x : α → X}
    (hxK : ∀ t ∈ Ico a T, x t ∈ K) (hxproj : ∀ t ∈ Ico a T, f (x t) = c t) :
    ∃ e : OpenPartialHomeomorph X Y, e.source ⊆ U ∧ EqOn f e e.source ∧
      e.symm (c T) ∈ closure K ∧
      ∃ t ∈ Ico a T, x t ∈ e.source ∧ MapsTo c (Icc t T) e.target := by
  have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨a, haT⟩
  have hev : ∀ᶠ t in 𝓝[<] T, t ∈ Ico a T := Ico_mem_nhdsLT haT
  have hmapK : map x (𝓝[<] T) ≤ principal K := by
    rw [le_principal_iff, mem_map]
    filter_upwards [hev] with t ht using hxK t ht
  obtain ⟨r, hrK, hcl⟩ := hK.exists_clusterPt hmapK
  have hcont : ContinuousWithinAt c (Iic T) T :=
    (hc T ⟨haT.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE haT)
  have hprojlim : Tendsto (fun t ↦ f (x t)) (𝓝[<] T) (𝓝 (c T)) := by
    apply (hcont.mono Iio_subset_Iic_self).congr'
    filter_upwards [hev] with t ht using (hxproj t ht).symm
  have hclmap : ClusterPt (f r) (𝓝 (c T)) :=
    hcl.map (hf.continuousAt (hKU hrK)) (tendsto_map'_iff.mpr hprojlim)
  have hfr : Inseparable (f r) (c T) := .of_nhds_neBot hclmap.neBot
  obtain ⟨e, hr, heU, he⟩ := hf.exists_openPartialHomeomorph_source_subset hU (hKU hrK)
  rw [he hr] at hfr
  have ht : c T ∈ e.target := (hfr.mem_open_iff e.open_target).mp (e.map_source hr)
  have hterminal : e.symm (c T) ∈ closure K := by
    have hspec := hfr.specializes.map_of_continuousOn e.continuousOn_symm
      (e.map_source hr) ht
    rw [e.left_inv hr] at hspec
    exact hspec.mem_closed isClosed_closure (subset_closure hrK)
  obtain ⟨u, huT, hsub⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' haT).mp
    (hcont.preimage_mem_nhdsWithin (e.open_target.mem_nhds ht))
  have hfreq : ∃ᶠ t in 𝓝[<] T, x t ∈ e.source :=
    frequently_map.mp (hcl.frequently (e.open_source.mem_nhds hr))
  obtain ⟨t, hsrc, ht, hut⟩ :=
    (hfreq.and_eventually (hev.and (Ioo_mem_nhdsLT huT))).exists
  exact ⟨e, heU, he, hterminal, t, ht, hsrc,
    fun _ hz ↦ hsub ⟨hut.1.trans_le hz.1, hz.2⟩⟩

/-- Suppose `a < T` and the curve is continuous on `[a, T]`. If every proper initial segment
has a lift in `U` starting at `q` whose endpoint is in a fixed compact set `K ⊆ U`, then the
curve lifts on `[a, T]` in `U`. The terminal value belongs to `closure K`, hence to `K` when
`K` is closed. Preregularity alone cannot give terminal membership in an arbitrary compact set. -/
theorem exists_lift_Icc_of_isCompact_of_forall_lt
    {α X Y : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y]
    {f : X → Y} {U : Set X} (hf : IsLocalHomeomorphOn f U) (hU : IsOpen U)
    {c : α → Y} {a T : α} (haT : a < T) (hc : ContinuousOn c (Icc a T))
    {q : X} {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U)
    (hbefore : ∀ t ∈ Ico a T, ∃ l : α → X, ContinuousOn l (Icc a t) ∧ l a = q ∧
      EqOn (f ∘ l) c (Icc a t) ∧ MapsTo l (Icc a t) U ∧ l t ∈ K) :
    ∃ l : α → X, ContinuousOn l (Icc a T) ∧ l a = q ∧
      EqOn (f ∘ l) c (Icc a T) ∧ MapsTo l (Icc a T) U ∧ l T ∈ closure K := by
  classical
  have : Nonempty X := ⟨q⟩
  choose! l hl h0 hp hm hK' using hbefore
  obtain ⟨e, heU, he, hterminal, t, ht, hsrc, hmaps⟩ :=
    hf.exists_chart_tail hU haT hc hK hKU hK' (fun t ht ↦ hp t ht ⟨ht.1, le_rfl⟩)
  obtain ⟨l', hl', heq, hbranch, hp', hm'⟩ := e.exists_extend_lift_Icc he ht.1 (hl t ht)
    (hc.mono (Icc_subset_Icc ht.1 le_rfl)) (hp t ht) hsrc hmaps (hm t ht) heU
  exact ⟨l', hl', (heq ⟨le_rfl, ht.1⟩).trans (h0 t ht), hp', hm',
    (hbranch ⟨ht.2.le, le_rfl⟩).symm ▸ hterminal⟩

/-- A curve continuous on `[a, b]` lifts from `q ∈ U` through a map locally homeomorphic on the
open set `U` if every lifted initial segment in `U` has endpoint in a fixed compact set
`K ⊆ U`. The lift stays in `K` on the whole interval. -/
theorem exists_lift_Icc_of_isCompact
    {α X Y : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y]
    {f : X → Y} {U : Set X} (hf : IsLocalHomeomorphOn f U) (hU : IsOpen U)
    {c : α → Y} {a b : α} (hc : ContinuousOn c (Icc a b))
    {q : X} (hqU : q ∈ U) (hq : f q = c a) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U)
    (htrap : ∀ t ∈ Icc a b, ∀ l : α → X, ContinuousOn l (Icc a t) → l a = q →
      EqOn (f ∘ l) c (Icc a t) → MapsTo l (Icc a t) U → l t ∈ K) :
    ∃ l : α → X, ContinuousOn l (Icc a b) ∧ l a = q ∧
      EqOn (f ∘ l) c (Icc a b) ∧ MapsTo l (Icc a b) K := by
  classical
  by_cases hab : a ≤ b
  · let A : Set α := {t | ∃ l : α → X, ContinuousOn l (Icc a t) ∧ l a = q ∧
      EqOn (f ∘ l) c (Icc a t) ∧ MapsTo l (Icc a t) U}
    have h0A : a ∈ A := by
      refine ⟨fun _ ↦ q, continuousOn_const, rfl, ?_, fun _ _ ↦ hqU⟩
      rintro t ⟨hat, hta⟩
      simpa only [le_antisymm hta hat, comp_apply] using hq
    have hne : (A ∩ Icc a b).Nonempty := ⟨a, h0A, le_rfl, hab⟩
    have hbdd : BddAbove (A ∩ Icc a b) := ⟨b, fun _ ht ↦ ht.2.2⟩
    let T := sSup (A ∩ Icc a b)
    have hT0 : a ≤ T := le_csSup hbdd ⟨h0A, le_rfl, hab⟩
    have hT1 : T ≤ b := csSup_le hne (fun _ ht ↦ ht.2.2)
    have hTA : T ∈ A := by
      rcases eq_or_lt_of_le hT0 with hz | hpos
      · rwa [← hz]
      have hbefore : ∀ t ∈ Ico a T, ∃ l : α → X, ContinuousOn l (Icc a t) ∧ l a = q ∧
          EqOn (f ∘ l) c (Icc a t) ∧ MapsTo l (Icc a t) U ∧ l t ∈ K := by
        intro t ht
        obtain ⟨t', ⟨⟨l, hl, h0, hp, hm⟩, _⟩, htt'⟩ := exists_lt_of_lt_csSup hne ht.2
        have hsub : Icc a t ⊆ Icc a t' := Icc_subset_Icc le_rfl htt'.le
        exact ⟨l, hl.mono hsub, h0, hp.mono hsub, hm.mono_left hsub,
          htrap t ⟨ht.1, ht.2.le.trans hT1⟩ l (hl.mono hsub) h0
            (hp.mono hsub) (hm.mono_left hsub)⟩
      obtain ⟨l, hl, h0, hp, hm, _⟩ := hf.exists_lift_Icc_of_isCompact_of_forall_lt hU hpos
        (hc.mono (Icc_subset_Icc le_rfl hT1)) hK hKU hbefore
      exact ⟨l, hl, h0, hp, hm⟩
    have hbA : b ∈ A := mem_of_csSup_mem_of_forall_exists_gt hTA h0A hab fun t ht ↦ by
      obtain ⟨l, hl, h0, hp, hm⟩ := ht.1
      obtain ⟨u, hu, l', hl', heq, hp', hm'⟩ := hf.exists_extend_lift_Icc hU ht.2.1 ht.2.2
        (hc.mono (Icc_subset_Icc ht.2.1 le_rfl)) hl hp hm
      exact ⟨u, ⟨l', hl', (heq ⟨le_rfl, ht.2.1⟩).trans h0, hp', hm'⟩, hu⟩
    obtain ⟨l, hl, h0, hp, hm⟩ := hbA
    exact ⟨l, hl, h0, hp, fun t ht ↦ htrap t ht l
      (hl.mono (Icc_subset_Icc le_rfl ht.2)) h0
      (hp.mono (Icc_subset_Icc le_rfl ht.2)) (hm.mono_left (Icc_subset_Icc le_rfl ht.2))⟩
  · exact ⟨fun _ ↦ q, continuousOn_const, rfl,
      fun _ ht ↦ (hab (ht.1.trans ht.2)).elim, fun _ ht ↦ (hab (ht.1.trans ht.2)).elim⟩

end IsLocalHomeomorphOn

/-- A continuous curve on `[a, b]` lifts from `q` through a local homeomorphism if every lifted
initial segment has endpoint in a fixed compact set `K`. The full lift stays in `K`. -/
theorem IsLocalHomeomorph.exists_lift_Icc_of_isCompact
    {α X Y : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) {c : α → Y} {a b : α}
    (hc : ContinuousOn c (Icc a b)) {q : X} (hq : f q = c a) {K : Set X} (hK : IsCompact K)
    (htrap : ∀ t ∈ Icc a b, ∀ l : α → X, ContinuousOn l (Icc a t) → l a = q →
      EqOn (f ∘ l) c (Icc a t) → l t ∈ K) :
    ∃ l : α → X, ContinuousOn l (Icc a b) ∧ l a = q ∧
      EqOn (f ∘ l) c (Icc a b) ∧ MapsTo l (Icc a b) K :=
  hf.isLocalHomeomorphOn.exists_lift_Icc_of_isCompact isOpen_univ hc (mem_univ q) hq hK
    (subset_univ K) (fun t ht l hl h0 hp _ ↦ htrap t ht l hl h0 hp)
