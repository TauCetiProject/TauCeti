/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Finite means of smooth bundle metrics

The arithmetic mean of a nonempty finite family of smooth Riemannian metrics on a real vector
bundle is again a smooth Riemannian metric. This construction applies to arbitrary model fibres:
the bounded-unit-set condition follows from convexity, without a finite-dimensionality assumption.
Reindexing does not change the mean. In particular, one can average the pullbacks of a metric by
a finite group of diffeomorphisms to obtain an invariant metric.

The construction uses `TauCeti.convex_setOfPred_symm_pos_isVonNBounded` and
`Convex.centerMass_mem` for the fibrewise metric conditions, and Mathlib's finite sums of smooth
sections for regularity.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι κ : Type*} [Fintype ι] [Nonempty ι]

/-- The arithmetic mean of a nonempty finite family of `C^n` Riemannian metrics. -/
def meanRiemannianMetric (g : ι → ContMDiffRiemannianMetric IB n F E) :
    ContMDiffRiemannianMetric IB n F E := by
  have hc (b : B) : Convex ℝ {q : E b →L[ℝ] E b →L[ℝ] ℝ |
      (∀ v w, q v w = q w v) ∧ (∀ v, v ≠ 0 → 0 < q v v) ∧
        Bornology.IsVonNBounded ℝ {v | q v v < 1}} :=
    convex_setOfPred_symm_pos_isVonNBounded
  have hm (b : B) (i : ι) : (g i).inner b ∈
      {q : E b →L[ℝ] E b →L[ℝ] ℝ | (∀ v w, q v w = q w v) ∧
        (∀ v, v ≠ 0 → 0 < q v v) ∧ Bornology.IsVonNBounded ℝ {v | q v v < 1}} :=
    ⟨(g i).symm b, (g i).pos b, (g i).isVonNBounded b⟩
  have h b := (hc b).centerMass_mem
    (t := Finset.univ) (w := fun _ : ι ↦ (1 : ℝ)) (z := fun i ↦ (g i).inner b)
    (by simp) (by simp [Fintype.card_pos]) (fun i _ ↦ hm b i)
  simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    one_smul] at h
  exact
    { inner := fun b ↦ (Fintype.card ι : ℝ)⁻¹ • ∑ i, (g i).inner b
      symm := fun b ↦ (h b).1
      pos := fun b ↦ (h b).2.1
      isVonNBounded := fun b ↦ (h b).2.2
      contMDiff := (ContMDiff.sum_section fun i _ ↦ (g i).contMDiff).const_smul_section }

/-- The mean metric evaluates to the arithmetic mean of the inner products. -/
@[simp]
theorem meanRiemannianMetric_inner (g : ι → ContMDiffRiemannianMetric IB n F E)
    (b : B) (v w : E b) :
    (meanRiemannianMetric g).inner b v w =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, (g i).inner b v w := by
  simp [meanRiemannianMetric]

/-- Averaging a constant family leaves its metric unchanged. -/
@[simp]
theorem meanRiemannianMetric_const (g : ContMDiffRiemannianMetric IB n F E) :
    meanRiemannianMetric (fun _ : ι ↦ g) = g := by
  ext b v w
  simp [Fintype.card_ne_zero]

/-- The mean of a family of metrics is independent of its finite indexing type. -/
theorem meanRiemannianMetric_equiv [Fintype κ] [Nonempty κ] (e : ι ≃ κ)
    (g : κ → ContMDiffRiemannianMetric IB n F E) :
    meanRiemannianMetric (g ∘ e) = meanRiemannianMetric g := by
  ext b v w
  simp only [meanRiemannianMetric_inner, Function.comp_apply, Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun i ↦ (g i).inner b v w)

end TauCeti
