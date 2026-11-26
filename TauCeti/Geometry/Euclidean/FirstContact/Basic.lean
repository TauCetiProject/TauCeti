/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.FirstContact.Translate

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
open scoped InnerProductSpace Pointwise

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}
  [ProperSpace F] {M : Type*} [TopologicalSpace M] {f : M → F}
  {Ω : Set (ℝ ∙ e)ᗮ} {g : (ℝ ∙ e)ᗮ → ℝ} {T : ℝ}

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
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hS : IsClosed (translatedGraph e Ω g 0) := by
    have hclosed := (continuousOn_heightAboveGraph hg).preimage_isClosed_of_isClosed
      (hΩ.preimage P.continuous) (isClosed_singleton (x := (0 : ℝ)))
    convert hclosed using 1
    ext y
    simp only [mem_translatedGraph_iff he, mem_inter_iff, mem_preimage, mem_singleton_iff]
  obtain ⟨t₀, ht₀, hne, hmax, hside⟩ := hf.isClosed_range.exists_firstContact_translate
    he hS (by simpa using hT)
    ⟨0, ⟨le_rfl, hT₀⟩, by simpa using h0⟩ hbdd.isCompact_closure
    (fun t ht y hy ↦ subset_closure (mem_iUnion₂.2 ⟨t, ht, by simpa using hy⟩))
  refine ⟨t₀, ht₀, by simpa using hne, ?_, ?_⟩
  · intro t ht h
    exact hmax t ht (by simpa using h)
  · intro x hx
    obtain ⟨hxΩ, hxh⟩ := (mem_translatedGraph_iff he).1 hx
    have hint : P (f x) ∈ interior Ω := by
      rw [← self_sdiff_frontier]
      refine ⟨hxΩ, fun hfr ↦ ?_⟩
      exact disjoint_left.1 (hbdry t₀ ⟨ht₀.1, ht₀.2.le⟩)
        ((mem_translatedGraph_iff he).2 ⟨hfr, hxh⟩) (mem_range_self x)
    have hev := (P.continuous.continuousAt.comp hf.continuous.continuousAt).eventually
      (isOpen_interior.mem_nhds hint)
    have hle := hside x g (hg.continuousAt (mem_of_superset
      (isOpen_interior.mem_nhds hint) interior_subset))
      ((isOpen_interior.eventually_mem hint).mono fun k hk ↦
        by simpa only [add_zero] using
          (add_smul_mem_translatedGraph (e := e) (g := g) (t := 0) (interior_subset hk)))
      hxh hf.continuous.continuousAt
    exact ⟨hint, hev.and hle⟩

section Tangency

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [I.Boundaryless]

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
