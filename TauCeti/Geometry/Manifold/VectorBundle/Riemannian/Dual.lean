/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Regularity of metric dual covectors

Lowering a vector-bundle section with a regular metric preserves its regularity, including
for sections along a varying base map. This is the covector-valued version of Mathlib's
`ContMDiffWithinAt.inner_bundle`.
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {b : P → M} {σ : ∀ p, V (b p)} {s : Set P} {p : P}

/-- Metric duality preserves regularity along an arbitrary base map. -/
theorem ContMDiffWithinAt.innerSL_bundle {n : ℕ∞ω}
    [h : IsContMDiffRiemannianBundle I n F V]
    (hσ : ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (b q) (σ q)) s p) :
    ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] ℝ) (b q) (innerSL ℝ (σ q))) s p := by
  obtain ⟨g, hg, heq⟩ := h.exists_contMDiff
  have hb : ContMDiffWithinAt IP I n b s p :=
    (contMDiffWithinAt_totalSpace.mp hσ).1
  have hgb : ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (b q) (g (b q))) s p := by
    simpa only [Function.comp_def] using hg.contMDiffAt.comp_contMDiffWithinAt p hb
  have hd := hgb.clm_bundle_apply (F₂ := F →L[ℝ] ℝ)
    (E₂ := fun x ↦ V x →L[ℝ] ℝ) hσ
  have hdual (x : M) (v : V x) : g x v = innerSL ℝ v := by
    ext w
    exact (heq x v w).symm
  simpa only [hdual] using hd

/-- Lowering a differentiable section with a C¹ metric gives a differentiable covector
section, without assuming the section itself is C¹. -/
theorem MDifferentiableAt.innerSL_bundle [h : IsContMDiffRiemannianBundle I 1 F V]
    {σ : Π x, V x} {x : M} (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun z ↦ V z →L[ℝ] ℝ) y (innerSL ℝ (σ y))) x := by
  obtain ⟨g, hg, heq⟩ := h.exists_contMDiff
  have hd := (hg.mdifferentiableAt one_ne_zero).clm_bundle_apply hσ
  have hdual (y : M) (v : V y) : g y v = innerSL ℝ v := by
    ext w
    exact (heq y v w).symm
  simpa only [hdual] using hd

end Regularity
