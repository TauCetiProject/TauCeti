/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Smooth orthogonal projection onto a nowhere-zero complex section

For a smooth Hermitian bundle metric and a nowhere-zero smooth section, the native orthogonal
projection onto its complex span is smooth on the actual total space. No completeness of the
ambient fibres or finite-dimensionality is needed: the projected complex line is complete.
The real and complex module structures, fibre topology and metric norm remain unchanged.

This is the projection input for splitting off a trivial complex line. The smooth complement
bundle and its total-space splitting are not constructed here.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §2.6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Chapter 10.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω}

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

/-- Orthogonal projection onto the complex line of a nowhere-zero smooth section is smooth
on the entire bundle total space, for the given smoothly varying Hermitian metric. -/
theorem contMDiff_starProjection_span_singleton (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (s : ∀ x, V x)
    (hs : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s x⟩ : TotalSpace F V)))
    (hne : ∀ x, s x ≠ 0) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      (fun p : TotalSpace F V ↦
        (⟨p.proj, (ℂ ∙ s p.proj).starProjection (𝕜 := ℂ) p.2⟩ : TotalSpace F V)) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hb := Bundle.contMDiff_proj V (F := F) (IB := IB) (n := n)
  have hsp := hs.comp hb
  have hn := g.contMDiff_hermitianPairing hI hsp contMDiff_id
  have hd := hsp.inner_bundle hsp
  have hz (p : TotalSpace F V) : Inner.inner ℝ (s p.proj) (s p.proj) ≠ 0 :=
    inner_self_ne_zero.mpr (hne p.proj)
  have hc := (hd.inv₀ hz).smul hn
  apply (hc.smul_totalSpace hsp).congr
  intro p
  apply congrArg (TotalSpace.mk p.proj)
  simp [Submodule.starProjection_singleton, Complex.real_smul, div_eq_mul_inv, mul_comm,
    add_mul]

/-- The complementary native orthogonal projection is also smooth on total space. This does
not assert a smooth bundle structure on its range. -/
theorem contMDiff_starProjection_orthogonal_span_singleton
    (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (s : ∀ x, V x)
    (hs : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s x⟩ : TotalSpace F V)))
    (hne : ∀ x, s x ≠ 0) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      (fun p : TotalSpace F V ↦
        (⟨p.proj, (ℂ ∙ s p.proj)ᗮ.starProjection (𝕜 := ℂ) p.2⟩ : TotalSpace F V)) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hp := g.contMDiff_starProjection_span_singleton hI s hs hne
  have hn := (contMDiff_const (I := IB.prod 𝓘(ℝ, F)) (c := (-1 : ℝ))).smul_totalSpace hp
  apply (ContMDiff.add_sectionAlong contMDiff_id hn).congr
  intro p
  apply congrArg (TotalSpace.mk p.proj)
  simp [Submodule.starProjection_orthogonal', sub_eq_add_neg]

end Bundle.ContMDiffRiemannianMetric
