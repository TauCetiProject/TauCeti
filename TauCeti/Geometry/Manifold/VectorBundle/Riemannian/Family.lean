/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smooth metric families on time sets

`TauCeti.IsSmoothMetricFamilyOn g s` expresses joint smoothness in time and space of a family
of native smooth Riemannian metrics on a real vector bundle. Its coefficient field takes values
in the bilinear-form bundle, and is smooth within `s × M`. In particular, this condition is stronger
than smoothness of each individual metric. The time set may be an interval, including its
endpoints, without choosing an extension of the family as part of the data.

The API supplies restriction, equality on the time set, smooth changes of time, and positive
rescaling in time and space using `Bundle.ContMDiffRiemannianMetric.rescale`. Pairing the metric
with smooth bundle-valued fields gives a jointly smooth scalar function.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A family of native smooth Riemannian metrics is smooth on a time set if its coefficient
field is jointly smooth in time and space within that set. No condition is imposed on the
family outside the time set. -/
def IsSmoothMetricFamilyOn
    (g : ℝ → ContMDiffRiemannianMetric I ∞ F V)
    (s : Set ℝ) : Prop :=
  ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun q : ℝ × M ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ)
      q.2 ((g q.1).inner q.2)) (s ×ˢ univ)

variable {g h : ℝ → ContMDiffRiemannianMetric I ∞ F V}
  {s r : Set ℝ}

/-- The characteristic criterion for joint smoothness of a metric family on a time set. -/
theorem isSmoothMetricFamilyOn_iff :
    IsSmoothMetricFamilyOn g s ↔
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ)
          q.2 ((g q.1).inner q.2)) (s ×ˢ univ) :=
  Iff.rfl

/-- Joint smoothness can equivalently be read in the native symmetric-tensor bundle. -/
theorem isSmoothMetricFamilyOn_iff_toSymmetricSection :
    IsSmoothMetricFamilyOn g s ↔
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, symmetricBilinearMaps ℝ F ℝ)) ∞
        (fun q : ℝ × M ↦ TotalSpace.mk' (symmetricBilinearMaps ℝ F ℝ)
          (E := fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ) q.2
          ((g q.1).toSymmetricSection q.2)) (s ×ˢ univ) := by
  rw [isSmoothMetricFamilyOn_iff]
  simpa only [ContMDiffRiemannianMetric.coe_toSymmetricSection_apply] using
    (Manifold.contMDiffOn_symmetricBilinearMaps_iff
      (f := fun q : ℝ × M ↦ TotalSpace.mk' (symmetricBilinearMaps ℝ F ℝ)
        (E := fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ) q.2
        ((g q.1).toSymmetricSection q.2))).symm

namespace IsSmoothMetricFamilyOn

/-- The coefficient field of a smooth metric family is jointly smooth on its time set. -/
theorem contMDiffOn (hg : IsSmoothMetricFamilyOn g s) :
    ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ)
        q.2 ((g q.1).inner q.2)) (s ×ˢ univ) :=
  isSmoothMetricFamilyOn_iff.mp hg

/-- The coefficient field is smooth at `(t, x)` whenever the time set is a neighborhood
of `t`, so the within-set condition can be removed there. -/
theorem contMDiffAt (hg : IsSmoothMetricFamilyOn g s) {t : ℝ} (hs : s ∈ 𝓝 t) (x : M) :
    ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ)
        q.2 ((g q.1).inner q.2)) (t, x) :=
  hg.contMDiffOn.contMDiffAt (prod_mem_nhds hs Filter.univ_mem)

/-- Restricting the time set preserves joint smoothness. -/
theorem mono (hg : IsSmoothMetricFamilyOn g s) (hrs : r ⊆ s) :
    IsSmoothMetricFamilyOn g r :=
  isSmoothMetricFamilyOn_iff.mpr (hg.contMDiffOn.mono (prod_mono_left hrs))

/-- A family agreeing with a smooth family on the time set is smooth there, regardless of its
values outside that set. -/
theorem congr (hg : IsSmoothMetricFamilyOn g s) (heq : EqOn h g s) :
    IsSmoothMetricFamilyOn h s := by
  apply isSmoothMetricFamilyOn_iff.mpr
  exact hg.contMDiffOn.congr fun q hq ↦ by rw [heq hq.1]

/-- Smooth reparametrization preserves smooth metric families when it maps the new time set
into the original one. -/
theorem comp (hg : IsSmoothMetricFamilyOn g s) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c r) (hcs : MapsTo c r s) :
    IsSmoothMetricFamilyOn (g ∘ c) r := by
  apply isSmoothMetricFamilyOn_iff.mpr
  exact hg.contMDiffOn.comp
    ((hc.contMDiffOn.comp (contMDiffOn_fst (s := r ×ˢ (univ : Set M)))
      (fun _ hq ↦ hq.1)).prodMk contMDiffOn_snd)
    (fun _ hq ↦ ⟨hcs hq.1, mem_univ _⟩)

/-- A change of time smooth on the preimage of the time set preserves joint smoothness
there; no regularity outside that preimage is required. -/
theorem comp_preimage (hg : IsSmoothMetricFamilyOn g s) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (c ⁻¹' s)) : IsSmoothMetricFamilyOn (g ∘ c) (c ⁻¹' s) :=
  hg.comp hc (fun _ ht ↦ ht)

/-- Translating time preserves joint smoothness on the translated time set. -/
theorem comp_add_const_preimage (hg : IsSmoothMetricFamilyOn g s) (a : ℝ) :
    IsSmoothMetricFamilyOn (fun t ↦ g (t + a)) ((fun t : ℝ ↦ t + a) ⁻¹' s) :=
  hg.comp_preimage (contDiff_id.add contDiff_const).contDiffOn

section Evaluation

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} {c : N → ℝ} {b : N → M} {u : Set N} {y : N}
  {v w : (z : N) → V (b z)}

/-- Evaluating a smooth metric family along `C^n` time and bundle-valued maps is `C^n`
within `u` at `y`, for `n ≤ ∞`. The time `c y` must belong to `s`, and nearby points of `u`
must eventually map into `s`; membership of `y` in `u` is not required. The base map's
regularity follows from either vector field. -/
theorem contMDiffWithinAt_inner_comp (hg : IsSmoothMetricFamilyOn g s) (hn : n ≤ ∞)
    (hc : ContMDiffWithinAt J 𝓘(ℝ) n c u y) (hcy : c y ∈ s)
    (hcs : ∀ᶠ z in 𝓝[u] y, c z ∈ s)
    (hv : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (b z) (v z)) u y)
    (hw : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (b z) (w z)) u y) :
    ContMDiffWithinAt J 𝓘(ℝ) n
      (fun z ↦ (g (c z)).inner (b z) (v z) (w z)) u y := by
  have hb := (contMDiffWithinAt_totalSpace_iff.mp hv).1
  have hcoeff := (((hg.contMDiffOn.of_le hn) (c y, b y) ⟨hcy, mem_univ _⟩).comp' (t := s ×ˢ univ) y
    (hc.prodMk hb)).mono_of_mem_nhdsWithin
      (Filter.inter_mem self_mem_nhdsWithin (hcs.mono fun _ hz ↦ ⟨hz, mem_univ _⟩))
  exact (contMDiffWithinAt_totalSpace_iff.mp
    (hcoeff.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hv hw)).2

/-- Evaluating a smooth metric family along `C^n` time and bundle-valued maps is `C^n`
at `y`, for `n ≤ ∞`, if the time map eventually takes values in `s` near `y`. The base
map's regularity follows from either vector field. -/
theorem contMDiffAt_inner_comp (hg : IsSmoothMetricFamilyOn g s) (hn : n ≤ ∞)
    (hc : ContMDiffAt J 𝓘(ℝ) n c y) (hcs : ∀ᶠ z in 𝓝 y, c z ∈ s)
    (hv : ContMDiffAt J (I.prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (b z) (v z)) y)
    (hw : ContMDiffAt J (I.prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (b z) (w z)) y) :
    ContMDiffAt J 𝓘(ℝ) n (fun z ↦ (g (c z)).inner (b z) (v z) (w z)) y := by
  apply contMDiffWithinAt_univ.mp
  exact hg.contMDiffWithinAt_inner_comp hn hc.contMDiffWithinAt hcs.self_of_nhds
    (by simpa only [nhdsWithin_univ] using hcs) hv.contMDiffWithinAt hw.contMDiffWithinAt

/-- Evaluating a smooth metric family along `C^n` time and bundle-valued maps is `C^n`
on `u`, for `n ≤ ∞`, when the time map sends all of `u` into `s`. The base map's regularity
follows from either vector field. -/
theorem contMDiffOn_inner_comp (hg : IsSmoothMetricFamilyOn g s) (hn : n ≤ ∞)
    (hc : ContMDiffOn J 𝓘(ℝ) n c u) (hcs : MapsTo c u s)
    (hv : ContMDiffOn J (I.prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (b z) (v z)) u)
    (hw : ContMDiffOn J (I.prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (b z) (w z)) u) :
    ContMDiffOn J 𝓘(ℝ) n (fun z ↦ (g (c z)).inner (b z) (v z) (w z)) u :=
  fun y hy ↦ hg.contMDiffWithinAt_inner_comp hn (hc y hy) (hcs hy)
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ hz ↦ hcs hz) (hv y hy) (hw y hy)

end Evaluation

/-- Pairing a smooth metric family with two jointly `C^n` bundle-valued fields gives a jointly
`C^n` real-valued function on `u`, for `n ≤ ∞`, provided `u` lies in the family's time-space
domain `s ×ˢ univ`. -/
theorem contMDiffOn_inner (hg : IsSmoothMetricFamilyOn g s) {n : ℕ∞ω} (hn : n ≤ ∞)
    {u : Set (ℝ × M)} (hu : u ⊆ s ×ˢ univ) {v w : (q : ℝ × M) → V q.2}
    (hv : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F q.2 (v q)) u)
    (hw : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F q.2 (w q)) u) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) n
      (fun q ↦ (g q.1).inner q.2 (v q) (w q)) u :=
  hg.contMDiffOn_inner_comp hn contMDiffOn_fst (fun _ hq ↦ (hu hq).1) hv hw

/-- At a fixed spatial point, pairing with fixed vectors is smooth in time within the time
set. This permits time derivatives without choosing local coordinates. -/
theorem contDiffOn_inner (hg : IsSmoothMetricFamilyOn g s) (x : M) (v w : V x) :
    ContDiffOn ℝ ∞ (fun t ↦ (g t).inner x v w) s := by
  intro t ht
  exact (hg.contMDiffWithinAt_inner_comp le_rfl contMDiffWithinAt_id ht self_mem_nhdsWithin
    (contMDiffWithinAt_const (c := TotalSpace.mk' F x v))
    (contMDiffWithinAt_const (c := TotalSpace.mk' F x w))).contDiffWithinAt

/-- A jointly smooth scalar multiple of a smooth family's coefficients is smooth. Only
coefficient equality at times in the time set is required; the target metrics are already given. -/
theorem of_inner_eq_smul (hg : IsSmoothMetricFamilyOn g s) {a : ℝ × M → ℝ}
    (ha : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ a (s ×ˢ univ))
    (heq : ∀ t ∈ s, ∀ x, (h t).inner x = a (t, x) • (g t).inner x) :
    IsSmoothMetricFamilyOn h s := by
  apply isSmoothMetricFamilyOn_iff.mpr
  exact (ha.smul_totalSpace hg.contMDiffOn).congr fun q hq ↦ by rw [heq q.1 hq.1 q.2]

/-- A time-dependent scalar multiple of a smooth family's coefficients is smooth when the
scalar is smooth on the time set. Coefficient equality is required only on that set; the target
metrics are already given, so no condition on the scalar outside the time set is needed. -/
theorem of_inner_eq_const_smul (hg : IsSmoothMetricFamilyOn g s) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a s)
    (heq : ∀ t ∈ s, ∀ x, (h t).inner x = a t • (g t).inner x) :
    IsSmoothMetricFamilyOn h s :=
  hg.of_inner_eq_smul (ha.contMDiffOn.comp
    (contMDiffOn_fst (s := s ×ˢ (univ : Set M))) (fun _ hq ↦ hq.1)) heq

variable [∀ x, ContinuousConstSMul ℝ (V x)]

/-- Rescaling by a positive function of time and space preserves smooth metric families.
Each time slice is globally smooth and positive to define native metrics, while joint regularity
is needed only on the time set. -/
theorem rescale (hg : IsSmoothMetricFamilyOn g s) {a : ℝ → M → ℝ}
    (ha : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun q ↦ a q.1 q.2) (s ×ˢ univ))
    (haslice : ∀ t, ContMDiff I 𝓘(ℝ) ∞ (a t)) (hapos : ∀ t x, 0 < a t x) :
    IsSmoothMetricFamilyOn (fun t ↦ (g t).rescale (a t) (haslice t) (hapos t)) s := by
  apply hg.of_inner_eq_smul ha
  intro t _ x
  ext v w
  simp

/-- Rescaling by a positive time-dependent scalar preserves smooth metric families. -/
theorem rescale_const (hg : IsSmoothMetricFamilyOn g s) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hapos : ∀ t, 0 < a t) :
    IsSmoothMetricFamilyOn
      (fun t ↦ (g t).rescale (fun _ ↦ a t) contMDiff_const (fun _ ↦ hapos t)) s :=
  hg.of_inner_eq_const_smul ha (fun t _ x ↦ by ext v w; simp)

end IsSmoothMetricFamilyOn

/-- Smoothness on the whole time axis is equivalent to unrestricted joint smoothness of
the coefficient field. -/
theorem isSmoothMetricFamilyOn_univ :
    IsSmoothMetricFamilyOn g univ ↔
      ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ)
          q.2 ((g q.1).inner q.2)) := by
  rw [isSmoothMetricFamilyOn_iff, univ_prod_univ, contMDiffOn_univ]

/-- Joint smoothness depends only on the metrics at times in the time set. -/
theorem isSmoothMetricFamilyOn_congr (heq : EqOn g h s) :
    IsSmoothMetricFamilyOn g s ↔ IsSmoothMetricFamilyOn h s :=
  ⟨fun hg ↦ hg.congr heq.symm, fun hh ↦ hh.congr heq⟩

/-- Every constant family of smooth metrics is jointly smooth on every time set. -/
@[simp]
theorem isSmoothMetricFamilyOn_const
    (g₀ : ContMDiffRiemannianMetric I ∞ F V) (s : Set ℝ) :
    IsSmoothMetricFamilyOn (fun _ ↦ g₀) s :=
  isSmoothMetricFamilyOn_iff.mpr (g₀.contMDiff.comp contMDiff_snd).contMDiffOn

/-- Every metric family is smooth on the empty time set. -/
@[simp]
theorem isSmoothMetricFamilyOn_empty : IsSmoothMetricFamilyOn g ∅ := by
  apply isSmoothMetricFamilyOn_iff.mpr
  simpa only [empty_prod] using (contMDiffOn_empty (f := fun q : ℝ × M ↦
    TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ) q.2 ((g q.1).inner q.2)))

/-- Every metric family is smooth on a singleton time set: its sole time slice is a smooth
metric, and no transverse time regularity is imposed by within-set smoothness. -/
@[simp]
theorem isSmoothMetricFamilyOn_singleton (t : ℝ) : IsSmoothMetricFamilyOn g {t} := by
  apply (isSmoothMetricFamilyOn_const (g t) {t}).congr
  intro u hu
  rw [mem_singleton_iff.mp hu]

/-- Joint smoothness on a time set is local for the relative topology on that time set. -/
theorem isSmoothMetricFamilyOn_iff_forall_exists_mem_nhdsWithin :
    IsSmoothMetricFamilyOn g s ↔
      ∀ t ∈ s, ∃ u ∈ 𝓝[s] t, IsSmoothMetricFamilyOn g u := by
  refine ⟨fun hg t _ ↦ ⟨s, self_mem_nhdsWithin, hg⟩, ?_⟩
  intro h
  apply isSmoothMetricFamilyOn_iff.mpr
  intro q hq
  obtain ⟨u, hu, hgu⟩ := h q.1 hq.1
  have hcoeff := hgu.contMDiffOn q ⟨mem_of_mem_nhdsWithin hq.1 hu, mem_univ _⟩
  exact hcoeff.mono_of_mem_nhdsWithin
    (mem_nhdsWithin_prod_iff.mpr ⟨u, hu, univ, Filter.univ_mem, subset_rfl⟩)

end TauCeti
