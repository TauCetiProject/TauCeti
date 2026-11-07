/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Density
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Analysis.Calculus.FDeriv.Det
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth density line bundles

The density line of a finite-dimensional real smooth vector bundle is smooth: its
transition functions are absolute determinants of invertible vector transitions.
Smoothness of a density section is equivalent to smoothness of its scalar value on the
inverse local frames of the underlying vector-bundle charts. For tangent bundles this gives
the real density bundle of a manifold, without a choice of orientation or metric, and the
criterion uses the inverse local tangent frames.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Bundle Set FiberBundle
open scoped Manifold ContDiff Topology

variable {B F EB HB : Type*} [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [ChartedSpace HB B] {I : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

namespace Bundle.Trivialization

variable (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e]
  [MemTrivializationAtlas e']

/-- Density transitions have the regularity of the vector-bundle transitions, since their
absolute determinants are evaluated only at invertible maps. -/
theorem contMDiffOn_densityCoordChange :
    ContMDiffOn I 𝓘(ℝ, ℝ →L[ℝ] ℝ) n (e.densityCoordChange e')
      (e.baseSet ∩ e'.baseSet) := by
  have hd : ContMDiffOn I 𝓘(ℝ) n
      (fun x ↦ ((e'.coordChangeL ℝ e x : F →L[ℝ] F) : F →ₗ[ℝ] F).det)
      (e.baseSet ∩ e'.baseSet) := by
    exact ContinuousLinearMap.contDiff_det.contMDiff.comp_contMDiffOn
      ((contMDiffOn_coordChangeL (IB := I) (n := n) e' e).mono
        (fun x (hx : x ∈ e.baseSet ∩ e'.baseSet) ↦ ⟨hx.2, hx.1⟩))
  have ha : ContMDiffOn I 𝓘(ℝ) n
      (fun x ↦ |((e'.coordChangeL ℝ e x : F →L[ℝ] F) : F →ₗ[ℝ] F).det|)
      (e.baseSet ∩ e'.baseSet) := by
    intro x hx
    have hne : ((e'.coordChangeL ℝ e x : F →L[ℝ] F) : F →ₗ[ℝ] F).det ≠ 0 := by
      exact (e'.coordChangeL ℝ e x).toLinearEquiv.isUnit_det'.ne_zero
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      (contDiffAt_norm ℝ hne).comp_contMDiffWithinAt
        (f := fun y : B ↦ ((e'.coordChangeL ℝ e y : F →L[ℝ] F) : F →ₗ[ℝ] F).det)
        (hd x hx)
  refine (ha.smul (contMDiffOn_const (c := ContinuousLinearMap.id ℝ ℝ))).congr ?_
  intro x hx
  apply ContinuousLinearMap.ext
  intro c
  exact e.densityCoordChange_apply e' x c

end Bundle.Trivialization

namespace TauCeti.Density

/-- The density prebundle inherits smooth transition functions. -/
instance isContMDiff_vectorPrebundle : (vectorPrebundle F V).IsContMDiff I n where
  exists_contMDiffCoordChange := by
    intro d hd d' hd'
    obtain ⟨e, he, rfl⟩ := (mem_pretrivializationAtlas_iff F V d).1 hd
    obtain ⟨e', he', rfl⟩ := (mem_pretrivializationAtlas_iff F V d').1 hd'
    refine ⟨e.densityCoordChange e', ?_, ?_⟩
    · simpa only [Trivialization.densityPretrivialization_baseSet] using
        e.contMDiffOn_densityCoordChange (I := I) (n := n) e'
    · intro x hx c
      exact e.densityCoordChange_eq e'
        (by simpa only [Trivialization.densityPretrivialization_baseSet] using hx) c

/-- Top-dimensional densities on a smooth real vector bundle form a smooth real line bundle. -/
instance contMDiffVectorBundle :
    ContMDiffVectorBundle n ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F)) I :=
  (vectorPrebundle F V).contMDiffVectorBundle I

omit [ContMDiffVectorBundle n F V I] in
/-- Smoothness of a density section can be checked by evaluation on the inverse local frame
at each point. The criterion uses the original vector-bundle chart, so it does not ask callers
to unfold the construction of the density bundle. -/
theorem contMDiffAt_section_iff {s : ∀ x, Density (V x) (Module.finrank ℝ F)} (x₀ : B) :
    ContMDiffAt I (I.prod 𝓘(ℝ)) n (fun x ↦ TotalSpace.mk' ℝ x (s x)) x₀ ↔
      ContMDiffAt I 𝓘(ℝ) n
        (fun x ↦ s x (fun i ↦
          (trivializationAt F V x₀).symm x (Module.finBasis ℝ F i))) x₀ := by
  rw [Bundle.contMDiffAt_section_iff x₀, trivializationAt_eq]
  simp only [Trivialization.density_apply]

omit [ContMDiffVectorBundle n F V I] in
/-- A density section is smooth exactly when its values in the preferred local frames are
smooth at every point. -/
theorem contMDiff_section_iff {s : ∀ x, Density (V x) (Module.finrank ℝ F)} :
    ContMDiff I (I.prod 𝓘(ℝ)) n (fun x ↦ TotalSpace.mk' ℝ x (s x)) ↔
      ∀ x₀, ContMDiffAt I 𝓘(ℝ) n
        (fun x ↦ s x (fun i ↦
          (trivializationAt F V x₀).symm x (Module.finBasis ℝ F i))) x₀ :=
  forall_congr' contMDiffAt_section_iff

end TauCeti.Density

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The real density line of a manifold: the fibre at `x` is the space of top-dimensional
signed densities on its actual tangent space. -/
abbrev DensityBundle (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (x : M) :=
  Density (TangentSpace I x) (Module.finrank ℝ E)

end TauCeti
