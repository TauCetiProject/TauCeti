/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Analysis.InnerProductSpace.Dual

/-!
# Regularity of metric dual covectors

Lowering a vector-bundle section with a regular metric preserves its regularity, including
for sections along a varying base map. This is the covector-valued version of Mathlib's
`ContMDiffWithinAt.inner_bundle`. The metric itself is a regular section of the Hom bundle
to the continuous dual. In finite rank its inverse is a regular Hom-bundle section as well.
Lowering a finite family of sections at once gives a regular bundle map to a trivial bundle.
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

/-- The metric, viewed as a bundle map to the continuous dual, is as regular as the metric. -/
theorem IsContMDiffRiemannianBundle.contMDiff_innerSL {n : ℕ∞ω}
    [h : IsContMDiffRiemannianBundle I n F V] :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) x (innerSL ℝ)) := by
  obtain ⟨g, hg, heq⟩ := h.exists_contMDiff
  apply hg.congr
  intro x
  congr 1
  ext u v
  -- `erw` unfolds the metric-induced module projections on the fibre, allowing the generic
  -- Riesz evaluation lemma to match the ambient bundle structures.
  erw [innerSL_apply_apply]
  exact heq x u v

/-- On a finite-rank real Riemannian bundle, the inverse metric is a regular bundle map from
the continuous dual to the original bundle. The zero-rank case is included. -/
theorem IsContMDiffRiemannianBundle.contMDiff_innerSL_inverse {n : ℕ∞ω}
    [FiniteDimensional ℝ F]
    [h : IsContMDiffRiemannianBundle I n F V] :
    ContMDiff I (I.prod 𝓘(ℝ, (F →L[ℝ] ℝ) →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' ((F →L[ℝ] ℝ) →L[ℝ] F)
        (E := fun x ↦ (V x →L[ℝ] ℝ) →L[ℝ] V x) x (innerSL ℝ).inverse) := by
  apply IsContMDiffRiemannianBundle.contMDiff_innerSL.clm_bundle_inverse
  intro x
  let := VectorBundle.finiteDimensional ℝ F V x
  exact InnerProductSpace.isInvertible_innerSL

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
    (contMDiffWithinAt_totalSpace_iff.mp hσ).1
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

namespace TauCeti

/-- On a finite-rank Riemannian bundle, metric duality applied to a finite family of regular
sections `X i` gives a regular bundle map `v ↦ (⟪X i y, v⟫)ᵢ` to the trivial bundle with fibre
`ι → ℝ`. -/
theorem contMDiffWithinAt_pi_innerSL_bundle {n : ℕ∞ω} [FiniteDimensional ℝ F]
    [IsContMDiffRiemannianBundle I n F V] {ι : Type*} [Fintype ι] {X : ι → Π x, V x}
    {t : Set M} {x : M} (hX : ∀ i, CMDiffAt[t] n (T% (X i)) x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, F →L[ℝ] (ι → ℝ))) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] (ι → ℝ))
        (E := fun y ↦ V y →L[ℝ] Trivial M (ι → ℝ) y) y
        (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (X i y))) t x := by
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_id, TauCeti.contMDiffWithinAt_clm_apply.mpr fun u ↦
    contMDiffWithinAt_pi_module_iff.mpr fun i ↦ ?_⟩
  -- Each coordinate of the bundle map is the covector field `⟪X i ·, ·⟫`, which is `C^n`.
  have h := ((contMDiffWithinAt_hom_bundle _).mp (hX i).innerSL_bundle).2
  -- The trivializations of the trivial bundles are the identity, so in coordinates both sides
  -- are `u ↦ ⟪X i y, e⁻¹ u⟫` for the trivialization `e` of `V` at `x`.
  simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply] using
    TauCeti.contMDiffWithinAt_clm_apply.mp h u

end TauCeti

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
