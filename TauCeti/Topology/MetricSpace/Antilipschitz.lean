/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Inverse-Lipschitz restrictions and global lower distance bounds

For a continuous injection on a compact set, a uniform lower distance bound for nearby pairs
extends to all pairs. Away from the diagonal, compactness and injectivity supply the missing
positive lower bound. This lets local differential estimates give quantitative embeddings.

We also show that a map `x ↦ (f x, g x)` is antilipschitz, and uniformly inducing when `f` and
`g` are uniformly continuous, on a set where `dist x y` is bounded by a combination of
`dist (f x) (f y)` and `dist (g x) (g y)`.

`AntilipschitzWith.domRestrict_mono` restricts inverse-Lipschitz control on a set to any subset,
and `AntilipschitzWith.dist_le_add_one_mul_of_domRestrict` gives the strictly-positive-constant
distance bound `dist x y ≤ (L + 1) * dist (f x) (f y)` on `s`.

## Inverse-Lipschitz bounds at a point

The same local-to-global principle holds with one point held fixed. A map `f` is antilipschitz
from `x` with constant `K` (`TauCeti.AntilipschitzWithFrom`) when
`edist x y ≤ K * edist (f x) (f y)` for every `y` of the source: the ratio
`dist (f x) (f y) / dist x y` is at least `K⁻¹` for all `y ≠ x`
(`TauCeti.antilipschitzWithFrom_iff_inv_le_div`), the whole source included, and not only near
`x`. Such a bound makes `x` the only point with image `f x`
(`TauCeti.AntilipschitzWithFrom.eq_of_apply_eq`). In the transversality theory of
pseudoholomorphic curves this is the global self-point floor at an anchor point: it separates a
simple curve, whose anchor has no other preimage, from a multiple cover such as `z ↦ z²`, which is
an injective immersion near every anchor `z ≠ 0` but identifies `z` with `-z`.

* If the target is a metric space and `f` is continuous on a compact set `s`, a bound for the
  points `y ∈ s` near `x` extends to all `y ∈ s` as soon as `x` is the only point of `s` with
  image `f x`
  (`IsCompact.exists_forall_dist_le_mul_dist_of_eventually`,
  `Continuous.exists_antilipschitzWithFrom_of_eventually`): away from `x` compactness and the
  injectivity at `x` bound `dist (f x) (f y)` below, while `dist x y` stays bounded.
* The bound with a fixed constant passes to limits of maps and anchor points
  (`TauCeti.AntilipschitzWithFrom.of_tendsto`), so it defines a closed set of pairs of a map and an
  anchor (`TauCeti.isClosed_setOfPred_antilipschitzWithFrom`), and a limit anchor is still the only
  point of its fibre. With the Arzelà–Ascoli theorem this gives compact sets of Lipschitz maps with
  such an anchor (`TauCeti.isCompact_setOfPred_lipschitzWith_antilipschitzWithFrom`, in
  `TauCeti.Topology.ContinuousMap.Ascoli`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, §2.5 (simple curves and injective
  points) and §3.2 (transversality over simple curves).
-/

public section

open Filter Set Metric
open scoped NNReal ENNReal Topology

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
  have hx := x.property
  have hy := y.property
  by_cases hxy : dist (x : X) y < δ
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) dist_nonneg).trans
      (hlocal x hx y hy hxy)
  · have h := hbound (x, y) ⟨⟨hx, hy⟩, le_of_not_gt hxy⟩
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) dist_nonneg).trans
      ((le_div_iff₀ (hδ.trans_le (le_of_not_gt hxy))).mp h)

end IsCompact

namespace AntilipschitzWith

/-- Inverse-Lipschitz control on a set restricts to any subset. -/
theorem domRestrict_mono {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {L : ℝ≥0} {f : X → Y} {s t : Set X} (hi : AntilipschitzWith L (s.domRestrict f))
    (ht : t ⊆ s) : AntilipschitzWith L (t.domRestrict f) := by
  intro x y
  simpa only [Set.domRestrict_apply, Subtype.edist_eq, Subtype.edist_mk_mk] using
    hi ⟨x, ht x.property⟩ ⟨y, ht y.property⟩

/-- An `L`-antilipschitz restriction `s.domRestrict f` bounds source distances on `s` with the
strictly positive factor `(L : ℝ) + 1`. -/
theorem dist_le_add_one_mul_of_domRestrict {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {L : ℝ≥0} {f : X → Y} {s : Set X}
    (hi : AntilipschitzWith L (s.domRestrict f)) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    dist x y ≤ ((L : ℝ) + 1) * dist (f x) (f y) :=
  (hi.le_mul_dist ⟨x, hx⟩ ⟨y, hy⟩).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)

/-- If distances in `X` are controlled by the distances of the images under `f` and `g`, then
`x ↦ (f x, g x)` is antilipschitz, with constant `A + B`. -/
theorem prodMk_of_dist_le {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] {f : X → Y} {g : X → Z} {A B : ℝ≥0}
    (h : ∀ x y, dist x y ≤ A * dist (f x) (f y) + B * dist (g x) (g y)) :
    AntilipschitzWith (A + B) fun x => (f x, g x) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have hf : dist (f x) (f y) ≤ dist (f x, g x) (f y, g y) := le_max_left _ _
  have hg : dist (g x) (g y) ≤ dist (f x, g x) (f y, g y) := le_max_right _ _
  rw [NNReal.coe_add]
  nlinarith [h x y, mul_le_mul_of_nonneg_left hf A.coe_nonneg,
    mul_le_mul_of_nonneg_left hg B.coe_nonneg]

end AntilipschitzWith

namespace IsCompact

/-- Let `f` be continuous on a compact set `s`, with values in a metric space, and let `x` be the
only point of `s` with image `f x`. If `dist x y ≤ K * dist (f x) (f y)` for the points `y ∈ s`
near `x`, then the same bound holds for every `y ∈ s` with some constant `L`. -/
theorem exists_forall_dist_le_mul_dist_of_eventually {X Y : Type*} [PseudoMetricSpace X]
    [MetricSpace Y] {s : Set X} (hs : IsCompact s) {f : X → Y} (hf : ContinuousOn f s) {x : X}
    (hinj : ∀ y ∈ s, f y = f x → y = x) {K : ℝ≥0}
    (hK : ∀ᶠ y in 𝓝[s] x, dist x y ≤ K * dist (f x) (f y)) :
    ∃ L : ℝ≥0, ∀ y ∈ s, dist x y ≤ L * dist (f x) (f y) := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_nhdsWithin_iff.1 hK
  obtain ⟨r, hr⟩ := hs.isBounded.subset_closedBall x
  -- Away from `x`, the distance `dist (f x) (f y)` is bounded below by some `a > 0`.
  let T : Set X := s ∩ {y | δ ≤ dist y x}
  have hT : IsCompact T :=
    hs.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  obtain ⟨a, ha, haT⟩ := hT.exists_forall_le' (a := 0) (f := fun y ↦ dist (f x) (f y))
    (continuous_dist.comp_continuousOn (continuousOn_const.prodMk (hf.mono inter_subset_left)))
    fun y hy ↦ dist_pos.2 fun h ↦ by
      have hyx := hinj y hy.1 h.symm
      subst hyx
      exact (hδ.trans_le hy.2).ne' (dist_self y)
  refine ⟨max K (r / a).toNNReal, fun y hy ↦ ?_⟩
  rw [NNReal.coe_max]
  rcases lt_or_ge (dist y x) δ with hyx | hyx
  · exact (hnear ⟨mem_ball.2 hyx, hy⟩).trans (by gcongr; exact le_max_left _ _)
  · have hry : dist x y ≤ r := by rw [dist_comm]; exact hr hy
    have hr₀ : 0 ≤ r / a := div_nonneg (dist_nonneg.trans hry) ha.le
    calc dist x y ≤ r / a * a := by rwa [div_mul_cancel₀ _ ha.ne']
      _ ≤ (r / a).toNNReal * dist (f x) (f y) := by
        rw [Real.coe_toNNReal _ hr₀]; gcongr; exact haT y ⟨hy, hyx⟩
      _ ≤ _ := by gcongr; exact le_max_right _ _

end IsCompact

namespace TauCeti

variable {α β γ : Type*}

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {K L : ℝ≥0}
  {f : α → β} {x : α}

/-- A map `f` is **antilipschitz from** `x` with constant `K` if
`edist x y ≤ K * edist (f x) (f y)` for every point `y` of the source. Over the whole source, not
only near `x`, the ratio `dist (f x) (f y) / dist x y` is then at least `K⁻¹`
(`TauCeti.antilipschitzWithFrom_iff_inv_le_div`).
A map is antilipschitz with constant `K` exactly when it is antilipschitz from every point with
constant `K` (`TauCeti.antilipschitzWith_iff_forall_antilipschitzWithFrom`). -/
def AntilipschitzWithFrom (K : ℝ≥0) (f : α → β) (x : α) : Prop :=
  ∀ y, edist x y ≤ K * edist (f x) (f y)

theorem antilipschitzWithFrom_iff :
    AntilipschitzWithFrom K f x ↔ ∀ y, edist x y ≤ K * edist (f x) (f y) :=
  Iff.rfl

theorem AntilipschitzWithFrom.le_mul_edist (h : AntilipschitzWithFrom K f x) (y : α) :
    edist x y ≤ K * edist (f x) (f y) :=
  h y

theorem antilipschitzWith_iff_forall_antilipschitzWithFrom :
    AntilipschitzWith K f ↔ ∀ x, AntilipschitzWithFrom K f x :=
  Iff.rfl

theorem _root_.AntilipschitzWith.antilipschitzWithFrom (h : AntilipschitzWith K f) (x : α) :
    AntilipschitzWithFrom K f x :=
  h x

theorem AntilipschitzWithFrom.mono (h : AntilipschitzWithFrom K f x) (hKL : K ≤ L) :
    AntilipschitzWithFrom L f x :=
  fun y ↦ (h y).trans (by gcongr)

theorem AntilipschitzWithFrom.comp {Kf Kg : ℝ≥0} {g : β → γ} (hg : AntilipschitzWithFrom Kg g (f x))
    (hf : AntilipschitzWithFrom Kf f x) : AntilipschitzWithFrom (Kf * Kg) (g ∘ f) x := fun y ↦
  calc edist x y ≤ Kf * edist (f x) (f y) := hf y
    _ ≤ Kf * (Kg * edist (g (f x)) (g (f y))) := by gcongr; exact hg (f y)
    _ = (Kf * Kg : ℝ≥0) * edist ((g ∘ f) x) ((g ∘ f) y) := by
      rw [ENNReal.coe_mul, mul_assoc, Function.comp_apply, Function.comp_apply]

/-- A point at which a map is antilipschitz is the only point of the source with its image. -/
theorem AntilipschitzWithFrom.eq_of_apply_eq {α : Type*} [EMetricSpace α] {f : α → β} {x : α}
    (h : AntilipschitzWithFrom K f x) {y : α} (hy : f y = f x) : y = x := by
  simpa [hy, eq_comm] using h y

/-- The bound at a point with a fixed constant passes to the limit: if maps `F i` are
antilipschitz from points `xs i` with constant `K`, the points `xs i` tend to `x`, and `F i` tends
to `f` pointwise and along the points `xs i`, then `f` is antilipschitz from `x` with constant
`K`. -/
theorem AntilipschitzWithFrom.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → α → β}
    {xs : ι → α} (hx : Tendsto xs l (𝓝 x)) (hFx : Tendsto (fun i ↦ F i (xs i)) l (𝓝 (f x)))
    (hF : ∀ y, Tendsto (fun i ↦ F i y) l (𝓝 (f y)))
    (h : ∀ᶠ i in l, AntilipschitzWithFrom K (F i) (xs i)) : AntilipschitzWithFrom K f x := fun y ↦
  le_of_tendsto_of_tendsto (hx.edist tendsto_const_nhds)
    (ENNReal.Tendsto.const_mul (hFx.edist (hF y)) (Or.inr ENNReal.coe_ne_top))
    (h.mono fun _ hi ↦ hi y)

/-- For maps with continuous evaluation, such as continuous maps out of a locally compact space
with the compact-open topology, the pairs of a map and a point at which it is antilipschitz with
constant `K` form a closed set. -/
theorem isClosed_setOfPred_antilipschitzWithFrom {F : Type*} [FunLike F α β] [TopologicalSpace F]
    [ContinuousEval F α β] (K : ℝ≥0) : IsClosed {p : F × α | AntilipschitzWithFrom K p.1 p.2} := by
  refine isClosed_iff_clusterPt.2 fun p hp ↦ ?_
  have := hp.neBot
  exact AntilipschitzWithFrom.of_tendsto (F := fun q : F × α ↦ ⇑q.1) (xs := Prod.snd)
    (continuous_snd.tendsto p |>.mono_left inf_le_left)
    (continuous_eval.tendsto p |>.mono_left inf_le_left)
    (fun y ↦ ((continuous_eval_const y).comp continuous_fst).tendsto p |>.mono_left inf_le_left)
    (eventually_inf_principal (s := {p : F × α | AntilipschitzWithFrom K p.1 p.2}).2
      (.of_forall fun _ ↦ id))

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0} {f : α → β} {x : α}

theorem antilipschitzWithFrom_iff_le_mul_dist :
    AntilipschitzWithFrom K f x ↔ ∀ y, dist x y ≤ K * dist (f x) (f y) := by
  simp only [antilipschitzWithFrom_iff, edist_nndist, dist_nndist]
  norm_cast

alias ⟨AntilipschitzWithFrom.le_mul_dist, AntilipschitzWithFrom.of_le_mul_dist⟩ :=
  antilipschitzWithFrom_iff_le_mul_dist

/-- For a positive constant `K`, a map is antilipschitz from `x` with constant `K` exactly when the
ratio `dist (f x) (f y) / dist x y` is at least `K⁻¹` for every `y ≠ x`. -/
theorem antilipschitzWithFrom_iff_inv_le_div {α : Type*} [MetricSpace α] {f : α → β} {x : α}
    (hK : 0 < K) :
    AntilipschitzWithFrom K f x ↔ ∀ y ≠ x, (K : ℝ)⁻¹ ≤ dist (f x) (f y) / dist x y := by
  have hK' : (0 : ℝ) < K := hK
  rw [antilipschitzWithFrom_iff_le_mul_dist]
  refine forall_congr' fun y ↦ ?_
  rcases eq_or_ne y x with rfl | hy
  · simp
  · have hxy : 0 < dist x y := dist_pos.2 hy.symm
    rw [inv_le_iff_one_le_mul₀' hK', mul_div_assoc', one_le_div hxy]
    simp [hy]

/-- Let `f` be a continuous map from a compact space to a metric space, and `x` the only point with
image `f x`. If `f` is antilipschitz near `x`, that is `dist x y ≤ K * dist (f x) (f y)` for `y`
near `x`, then it is antilipschitz from `x` over the whole source, with some constant `L`. -/
theorem _root_.Continuous.exists_antilipschitzWithFrom_of_eventually {β : Type*} [MetricSpace β]
    [CompactSpace α] {f : α → β} (hf : Continuous f) (hinj : ∀ y, f y = f x → y = x)
    (hK : ∀ᶠ y in 𝓝 x, dist x y ≤ K * dist (f x) (f y)) : ∃ L, AntilipschitzWithFrom L f x := by
  obtain ⟨L, hL⟩ := isCompact_univ.exists_forall_dist_le_mul_dist_of_eventually hf.continuousOn
    (fun y _ ↦ hinj y) (by rwa [nhdsWithin_univ])
  exact ⟨L, .of_le_mul_dist fun y ↦ hL y (mem_univ y)⟩

end PseudoMetricSpace

end TauCeti
