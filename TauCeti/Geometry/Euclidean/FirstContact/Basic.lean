/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# The first-contact lemma for translated graphs

Let `e` be a unit vector of a proper real inner product space `F`, `P` the orthogonal
projection onto `e^⊥`, `Ω` a closed subset of `e^⊥` and `g : e^⊥ → ℝ` continuous on `Ω`. The barrier
`S_t = {k + (g(k) + t) e : k ∈ Ω}` is the graph of `g` translated by `t e`, and its boundary
`∂S_t` is the part over the frontier of `Ω`. A point `y` lies on `S_t` exactly when `P y ∈ Ω` and
its height `⟪e, y⟫ - g(P y)` above the graph of `g` is `t`.

Let `f : Σ → F` be a proper map with `S_T ∩ f(Σ) = ∅` and `S_0 ∩ f(Σ) ≠ ∅`, such that no `∂S_t`
with `t ∈ [0, T]` meets `f(Σ)` and `⋃_{t ∈ [0, T]} S_t ∩ f(Σ)` is bounded. Then there is
a largest contact time `t₀ ∈ [0, T)`. At every contact point at time `t₀`, the projection
lies in the interior of `Ω` and `f` stays below `S_{t₀}` nearby. If `Σ` is a manifold without
boundary, `f` is differentiable and `g` is differentiable on the interior of `Ω`, the height has
a local maximum there, so `df` takes values in the tangent space `{k + dg(k) e}` of `S_{t₀}`.

## Main declarations

* `TauCeti.translatedGraph`: the barrier `S_t`.
* `TauCeti.mem_translatedGraph_iff`: `y ∈ S_t ↔ P y ∈ Ω ∧ ⟪e, y⟫ - g(P y) = t`.
* `TauCeti.exists_firstContact`: the largest contact time, and `f` lies on one side of `S_{t₀}`
  near each of its contact points.
* `TauCeti.exists_firstContact_tangent`: moreover `f` is tangent to `S_{t₀}` there.

## References

* Adapted from Giada Franz’s [formalization](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/fde0487c6fe0a19b628b05a2708d65e20ef239c9).
* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 20.1.
-/

public noncomputable section

open Filter Function Manifold Set Submodule Topology
open scoped InnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}

/-- The graph `{k + (g(k) + t) e : k ∈ Ω}` of `g` over a set `Ω` of `e^⊥`, translated by
`t e`. -/
def translatedGraph (e : F) (Ω : Set (ℝ ∙ e)ᗮ) (g : (ℝ ∙ e)ᗮ → ℝ) (t : ℝ) : Set F :=
  (fun k : (ℝ ∙ e)ᗮ ↦ (k : F) + (g k + t) • e) '' Ω

/-- The image description of a translated graph. -/
theorem translatedGraph_def (Ω : Set (ℝ ∙ e)ᗮ) (g : (ℝ ∙ e)ᗮ → ℝ) (t : ℝ) :
    translatedGraph e Ω g t = (fun k : (ℝ ∙ e)ᗮ ↦ (k : F) + (g k + t) • e) '' Ω := by
  rfl

/-- The height `⟪e, y⟫ - g(P y)` of a point `y` above the graph of `g`, where `P` is the
orthogonal projection onto `e^⊥`. -/
def heightAboveGraph (e : F) (g : (ℝ ∙ e)ᗮ → ℝ) (y : F) : ℝ :=
  ⟪e, y⟫_ℝ - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto y)

theorem heightAboveGraph_def (g : (ℝ ∙ e)ᗮ → ℝ) (y : F) :
    heightAboveGraph e g y = ⟪e, y⟫_ℝ - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto y) := by
  rfl

/-- The height of `k + c e` above the graph of `g` is `c - g(k)`. -/
@[simp]
theorem heightAboveGraph_add_smul (he : ‖e‖ = 1) (g : (ℝ ∙ e)ᗮ → ℝ) (k : (ℝ ∙ e)ᗮ) (c : ℝ) :
    heightAboveGraph e g ((k : F) + c • e) = c - g k := by
  rw [heightAboveGraph_def, orthogonalProjectionOnto_add_smul, inner_add_smul e he]

/-- **Points of the translated graph.** `y ∈ S_t` exactly when `P y ∈ Ω` and the height of `y`
above the graph of `g` is `t`. -/
@[simp]
theorem mem_translatedGraph_iff (he : ‖e‖ = 1) {Ω : Set (ℝ ∙ e)ᗮ} {g : (ℝ ∙ e)ᗮ → ℝ} {t : ℝ}
    {y : F} :
    y ∈ translatedGraph e Ω g t ↔
      (ℝ ∙ e)ᗮ.orthogonalProjectionOnto y ∈ Ω ∧ heightAboveGraph e g y = t := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [orthogonalProjectionOnto_add_smul, heightAboveGraph_add_smul he]
    exact ⟨hk, by ring⟩
  · rintro ⟨hΩ, ht⟩
    refine ⟨_, hΩ, ?_⟩
    dsimp only
    rw [coe_orthogonalProjectionOnto_orthogonal_singleton he, ← ht, heightAboveGraph_def]
    module

/-- Height above the zero graph is the longitudinal inner product. -/
@[simp]
theorem heightAboveGraph_zero (y : F) :
    heightAboveGraph e (fun _ ↦ 0) y = ⟪e, y⟫_ℝ := by
  rw [heightAboveGraph_def, sub_zero]

/-- A point lies on the hyperplane `S_t` exactly when `⟪e, y⟫ = t`. -/
theorem mem_translatedGraph_univ_zero_iff (he : ‖e‖ = 1) {t : ℝ} {y : F} :
    y ∈ translatedGraph e univ (fun _ ↦ 0) t ↔ ⟪e, y⟫_ℝ = t := by
  rw [mem_translatedGraph_iff he, heightAboveGraph_zero]
  simp

/-- A graph over the empty set is empty. -/
@[simp]
theorem translatedGraph_empty (g : (ℝ ∙ e)ᗮ → ℝ) (t : ℝ) :
    translatedGraph e ∅ g t = ∅ := by
  simp [translatedGraph_def]

/-- Every graph parameter in the domain gives a point of the translated graph. -/
theorem add_smul_mem_translatedGraph {Ω : Set (ℝ ∙ e)ᗮ} {g : (ℝ ∙ e)ᗮ → ℝ} {t : ℝ}
    {k : (ℝ ∙ e)ᗮ} (hk : k ∈ Ω) :
    (k : F) + (g k + t) • e ∈ translatedGraph e Ω g t :=
  mem_image_of_mem _ hk

/-- The height above the graph of `g` is continuous where `g` is. -/
theorem continuousOn_heightAboveGraph {Ω : Set (ℝ ∙ e)ᗮ} {g : (ℝ ∙ e)ᗮ → ℝ}
    (hg : ContinuousOn g Ω) :
    ContinuousOn (heightAboveGraph e g) ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto ⁻¹' Ω) :=
  (continuous_const.inner continuous_id).continuousOn.sub
    (hg.comp (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.continuous.continuousOn fun _ hy ↦ hy)

variable [ProperSpace F] {M : Type*} [TopologicalSpace M] {f : M → F}
  {Ω : Set (ℝ ∙ e)ᗮ} {g : (ℝ ∙ e)ᗮ → ℝ}
  {T : ℝ}

omit [ProperSpace F] in
private theorem eventually_heightAboveGraph_le_of_maximal
    (hf : Continuous f) (hg : ContinuousOn g Ω) {x : M} {t₀ : ℝ}
    (hint : (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x) ∈ interior Ω)
    (hxt : heightAboveGraph e g (f x) = t₀) (ht₀ : 0 ≤ t₀) (hT : t₀ < T)
    (hmax : ∀ y, (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f y) ∈ Ω →
      heightAboveGraph e g (f y) ∈ Icc 0 T → heightAboveGraph e g (f y) ≤ t₀) :
    ∀ᶠ y in 𝓝 x, (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f y) ∈ interior Ω ∧
      heightAboveGraph e g (f y) ≤ t₀ := by
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hPf : ContinuousAt (fun y ↦ P (f y)) x := (P.continuous.comp hf).continuousAt
  have hev := hPf.preimage_mem_nhds (isOpen_interior.mem_nhds hint)
  have hhx : ContinuousAt (fun y ↦ heightAboveGraph e g (f y)) x :=
    ((continuousOn_heightAboveGraph hg).continuousAt
      (P.continuous.continuousAt.preimage_mem_nhds
        (mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset))).comp hf.continuousAt
  have hevT := hhx.preimage_mem_nhds (Iio_mem_nhds (hxt.symm ▸ hT))
  filter_upwards [hev, hevT] with y hy hyT
  refine ⟨hy, le_of_not_gt fun hgt ↦ ?_⟩
  exact (not_le_of_gt hgt) (hmax y (interior_subset hy) ⟨ht₀.trans hgt.le, hyT.le⟩)

/-- **The first-contact lemma.** Let `f` be a proper map and `S_t` the graph of `g` over the closed
set `Ω` translated by `t e`. If `S_T` misses `f`, `S_0` meets it, no boundary `∂S_t` with
`t ∈ [0, T]` meets it and the contact set `⋃_{t ∈ [0, T]} S_t ∩ f(Σ)` is bounded, then there is
a largest contact time `t₀ ∈ [0, T)`. At every point `x` with `f(x) ∈ S_{t₀}`, the projection of
`f(x)` lies in the interior of `Ω` and, near `x`, `f` lies below `S_{t₀}`. -/
theorem exists_firstContact (hf : IsProperMap f) (he : ‖e‖ = 1) (hΩ : IsClosed Ω)
    (hg : ContinuousOn g Ω) (hT₀ : 0 ≤ T) (hT : Disjoint (translatedGraph e Ω g T) (range f))
    (h0 : (translatedGraph e Ω g 0 ∩ range f).Nonempty)
    (hbdry : ∀ t ∈ Icc 0 T, Disjoint (translatedGraph e (frontier Ω) g t) (range f))
    (hbdd : Bornology.IsBounded (⋃ t ∈ Icc 0 T, translatedGraph e Ω g t ∩ range f)) :
    ∃ t₀ ∈ Ico 0 T, (translatedGraph e Ω g t₀ ∩ range f).Nonempty ∧
      (∀ t ∈ Icc 0 T, (translatedGraph e Ω g t ∩ range f).Nonempty → t ≤ t₀) ∧
      ∀ x, f x ∈ translatedGraph e Ω g t₀ →
        (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x) ∈ interior Ω ∧
        ∀ᶠ y in 𝓝 x, (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f y) ∈ interior Ω ∧
          heightAboveGraph e g (f y) ≤ t₀ := by
  set P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  set h : M → ℝ := heightAboveGraph e g ∘ f
  have hh (x : M) : h x = heightAboveGraph e g (f x) := rfl
  set A := f ⁻¹' (P ⁻¹' Ω)
  have hA : IsClosed A := (hΩ.preimage P.continuous).preimage hf.continuous
  have hcont : ContinuousOn h A :=
    (continuousOn_heightAboveGraph hg).comp hf.continuous.continuousOn fun _ hx ↦ hx
  set C := A ∩ h ⁻¹' Icc 0 T
  have hmemC (x : M) : x ∈ C ↔ ∃ t ∈ Icc 0 T, f x ∈ translatedGraph e Ω g t := by
    simp only [C, A, mem_inter_iff, mem_preimage, mem_translatedGraph_iff he, hh]
    exact ⟨fun hx ↦ ⟨heightAboveGraph e g (f x), hx.2, hx.1, rfl⟩, fun ⟨_, ht, hx, hxt⟩ ↦
      ⟨hx, hxt ▸ ht⟩⟩
  have hCc : IsCompact C := by
    obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
    refine (hf.isCompact_preimage (isCompact_closedBall 0 R)).of_isClosed_subset
      (hcont.preimage_isClosed_of_isClosed hA isClosed_Icc) fun x hx ↦ ?_
    obtain ⟨t, ht, hxt⟩ := (hmemC x).1 hx
    exact hR (mem_iUnion₂.2 ⟨t, ht, hxt, mem_range_self x⟩)
  obtain ⟨_, hy0, x0, rfl⟩ := h0
  have hCne : C.Nonempty := ⟨x0, (hmemC x0).2 ⟨0, ⟨le_rfl, hT₀⟩, hy0⟩⟩
  obtain ⟨x₁, hx₁C, hmax⟩ := hCc.exists_isMaxOn hCne (hcont.mono inter_subset_left)
  have hx₁ : f x₁ ∈ translatedGraph e Ω g (h x₁) :=
    (mem_translatedGraph_iff he).2 ⟨hx₁C.1, rfl⟩
  have hle (y : M) (hy : y ∈ C) : h y ≤ h x₁ := hmax hy
  have hlt : h x₁ < T := lt_of_le_of_ne hx₁C.2.2 fun hT' ↦
    hT.ne_of_mem (hT' ▸ hx₁) (mem_range_self x₁) rfl
  refine ⟨h x₁, ⟨hx₁C.2.1, hlt⟩, ⟨f x₁, hx₁, mem_range_self x₁⟩, ?_, ?_⟩
  · rintro t ht ⟨_, hyt, x, rfl⟩
    have hx := (mem_translatedGraph_iff he).1 hyt
    have hxC : x ∈ C := (hmemC x).2 ⟨t, ht, hyt⟩
    have hxt : h x = t := (hh x).trans hx.2
    exact hxt ▸ hle x hxC
  · intro x hx
    obtain ⟨hxΩ, hxh⟩ := (mem_translatedGraph_iff he).1 hx
    have hint : P (f x) ∈ interior Ω := by
      rw [← self_sdiff_frontier]
      refine ⟨hxΩ, fun hfr ↦ ?_⟩
      have hb := hbdry (h x₁) ⟨hx₁C.2.1, hlt.le⟩
      exact hb.ne_of_mem ((mem_translatedGraph_iff he).2 ⟨hfr, hxh⟩) (mem_range_self x) rfl
    exact ⟨hint, eventually_heightAboveGraph_le_of_maximal hf.continuous hg hint hxh
      hx₁C.2.1 hlt (fun y hy hyt ↦ hle y ⟨hy, hyt⟩)⟩

section Tangency

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [I.Boundaryless]

omit [ProperSpace F] [I.Boundaryless] in
/-- **Tangency at a one-sided contact.** If the height of `f` above the graph of `g` has a local
extremum at an interior point `x` of the source manifold, `f` is differentiable at `x` and `g`
is differentiable at `P(f(x))`, then `df_x`
takes values in the tangent space `{k + dg(k) e}` of the graph: `⟪e, df_x v⟫ = dg(P(df_x v))`. -/
theorem inner_mvfderiv_eq_fderiv_of_isLocalExtr {x : M} (hx : I.IsInteriorPoint x)
    (hextr : IsLocalExtr (fun y ↦ heightAboveGraph e g (f y)) x)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (hg : DifferentiableAt ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)))
    (v : TangentSpace I x) :
    ⟪e, mvfderiv I f x v⟫_ℝ = fderiv ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x))
      ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (mvfderiv I f x v)) := by
  set P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hφ : HasFDerivAt (heightAboveGraph e g)
      (innerSL ℝ e - (fderiv ℝ g (P (f x))).comp (P : F →L[ℝ] (ℝ ∙ e)ᗮ)) (f x) :=
    (innerSL ℝ e).hasFDerivAt.sub (hg.hasFDerivAt.comp (f x) P.hasFDerivAt)
  have hc := mem_criticalPoints.1
    (hextr.mem_criticalPoints (I := I) hx)
  have h := mvfderiv_comp_apply x hφ.differentiableAt.mdifferentiableAt hf v
  rw [mvfderiv_eq_fderiv, hφ.fderiv] at h
  have h0 : mvfderiv I (heightAboveGraph e g ∘ f) x v = 0 := by
    rw [Function.comp_def, hc, zero_apply]
  rw [h0] at h
  simp only [sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  exact sub_eq_zero.mp h.symm

/-- **The first-contact lemma with tangency.** Under the hypotheses of `exists_firstContact`, if
moreover `Σ` is a manifold without boundary, `f` is differentiable and `g` is differentiable on
the interior of `Ω`, then at every contact point `x` at the largest contact time `t₀`, `f` lies
below `S_{t₀}` near `x` and `df_x` takes values in the tangent space of `S_{t₀}`. -/
theorem exists_firstContact_tangent (hf : IsProperMap f) (he : ‖e‖ = 1) (hΩ : IsClosed Ω)
    (hg : ContinuousOn g Ω) (hT₀ : 0 ≤ T) (hT : Disjoint (translatedGraph e Ω g T) (range f))
    (h0 : (translatedGraph e Ω g 0 ∩ range f).Nonempty)
    (hbdry : ∀ t ∈ Icc 0 T, Disjoint (translatedGraph e (frontier Ω) g t) (range f))
    (hbdd : Bornology.IsBounded (⋃ t ∈ Icc 0 T, translatedGraph e Ω g t ∩ range f))
    (hfd : MDifferentiable I 𝓘(ℝ, F) f) (hgd : DifferentiableOn ℝ g (interior Ω)) :
    ∃ t₀ ∈ Ico 0 T, (translatedGraph e Ω g t₀ ∩ range f).Nonempty ∧
      (∀ t ∈ Icc 0 T, (translatedGraph e Ω g t ∩ range f).Nonempty → t ≤ t₀) ∧
      ∀ x, f x ∈ translatedGraph e Ω g t₀ →
        (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x) ∈ interior Ω ∧
        (∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀) ∧
        ∀ v : TangentSpace I x, ⟪e, mvfderiv I f x v⟫_ℝ =
          fderiv ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x))
            ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (mvfderiv I f x v)) := by
  obtain ⟨t₀, ht₀, hne, hmax, hside⟩ := exists_firstContact hf he hΩ hg hT₀ hT h0 hbdry hbdd
  refine ⟨t₀, ht₀, hne, hmax, fun x hx ↦ ?_⟩
  obtain ⟨hint, hev⟩ := hside x hx
  have hev' : ∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀ := hev.mono fun _ hy ↦ hy.2
  have hxt : heightAboveGraph e g (f x) = t₀ := ((mem_translatedGraph_iff he).1 hx).2
  refine ⟨hint, hev', fun v ↦ inner_mvfderiv_eq_fderiv_of_isLocalExtr
    BoundarylessManifold.isInteriorPoint (Or.inr ?_) (hfd x)
    (hgd.differentiableAt (isOpen_interior.mem_nhds hint)) v⟩
  rw [← hxt] at hev'
  exact (hev' : IsLocalMax (fun y ↦ heightAboveGraph e g (f y)) x)

end Tangency

end TauCeti
