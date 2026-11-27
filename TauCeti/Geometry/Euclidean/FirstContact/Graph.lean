/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Translated graphs and tangency at one-sided contact

This module describes translated graphs by orthogonal projection and height, and proves
tangency at a local extremum of the height. The first-contact existence results are in
`FirstContact.Translate` and `FirstContact.Basic`.

## References

* Adapted from Giada Franz’s [formalization](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/fde0487c6fe0a19b628b05a2708d65e20ef239c9).
* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 20.1.
-/

public noncomputable section

open Filter Function Manifold Set Submodule Topology
open scoped InnerProductSpace Pointwise

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

end TauCeti

open TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}

/-- Translating the zero-time graph by `t • e` gives the graph at time `t`. -/
@[simp]
theorem Set.vadd_translatedGraph_zero (Ω : Set (ℝ ∙ e)ᗮ) (g : (ℝ ∙ e)ᗮ → ℝ) (t : ℝ) :
    (t • e) +ᵥ translatedGraph e Ω g 0 = translatedGraph e Ω g t := by
  simp only [translatedGraph_def, ← image_vadd, image_image]
  congr 1
  funext k
  simp only [vadd_eq_add, add_zero, add_smul]
  abel

/-- Pointwise continuity of the height above a graph follows from continuity of its height
function at the projected point. -/
theorem ContinuousAt.continuousAt_heightAboveGraph {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {e : F} {g : (ℝ ∙ e)ᗮ → ℝ} {y : F}
    (hg : ContinuousAt g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto y)) :
    ContinuousAt (heightAboveGraph e g) y :=
  (continuous_const.inner continuous_id).continuousAt.sub
    (hg.comp (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.continuous.continuousAt)

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}
  {M : Type*} [TopologicalSpace M] {f : M → F} {g : (ℝ ∙ e)ᗮ → ℝ}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

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

end TauCeti
