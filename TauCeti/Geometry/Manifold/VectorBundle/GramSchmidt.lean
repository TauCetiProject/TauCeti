/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth Gram–Schmidt in Riemannian vector bundles

Gram–Schmidt preserves the differentiability of a family of sections wherever the input
vectors are linearly independent. These local statements apply without choosing a bundle
trivialization and allow the construction of smooth orthonormal frames from smooth frames.
The orthogonalization and normalization are Mathlib's `InnerProductSpace.gramSchmidt` and
`InnerProductSpace.gramSchmidtNormed`.

The sectionwise induction follows `ContinuousWithinAt.gramSchmidt_bundle` in
`TauCeti.Topology.VectorBundle.GramSchmidt`, which adapts Patrick Massot and Michael Rothgang's
construction in Mathlib PR [#26221](https://github.com/leanprover-community/mathlib4/pull/26221).
Here smooth section operations replace the coordinate calculations of the continuity proof.
-/

public section

open Bundle InnerProductSpace
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n F V]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {v : ι → Π x : M, V x} {x : M}

attribute [local instance] IsWellOrder.toHasWellFounded

/-- Fiberwise Gram–Schmidt preserves `C^n` regularity at a linearly independent family. -/
theorem ContMDiffAt.gramSchmidt_bundle
    (hv : ∀ i, CMDiffAt n (T% (v i)) x)
    (hli : LinearIndependent ℝ (fun i ↦ v i x)) (j : ι) :
    CMDiffAt n (T% (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j)) x := by
  classical
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hg (i : ι) (hi : i < j) := ih i hi
    have hc (i : ι) (hi : i < j) :
        CMDiffAt n (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
          inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
            (gramSchmidt ℝ (fun k ↦ v k y) i)) x :=
      ((hg i hi).inner_bundle (hv j)).div₀ ((hg i hi).inner_bundle (hg i hi))
        (inner_self_ne_zero.mpr (gramSchmidt_ne_zero i hli))
    have hformula : (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j) =
        v j - ∑ i ∈ Finset.Iio j,
          (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
            inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
              (gramSchmidt ℝ (fun k ↦ v k y) i)) •
            (fun y ↦ gramSchmidt ℝ (fun k ↦ v k y) i) := by
      funext y
      simp only [Pi.sub_apply, Finset.sum_apply, real_inner_self_eq_norm_sq]
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (fun i ↦ v i y) j).symm
    have hs := (hv j).sub_section (.sum_section fun i hi ↦
      (hc i (Finset.mem_Iio.mp hi)).smul_section (hg i (Finset.mem_Iio.mp hi)))
    apply hs.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro y
    apply congrArg (TotalSpace.mk' F y)
    simpa only [Pi.sub_apply, Finset.sum_apply] using congrFun hformula y

/-- Fiberwise normalized Gram–Schmidt preserves `C^n` regularity at a linearly independent
family. -/
theorem ContMDiffAt.gramSchmidtNormed_bundle
    (hv : ∀ i, CMDiffAt n (T% (v i)) x)
    (hli : LinearIndependent ℝ (fun i ↦ v i x)) (j : ι) :
    CMDiffAt n (T% (fun y ↦ gramSchmidtNormed ℝ (fun i ↦ v i y) j)) x := by
  have hg := ContMDiffAt.gramSchmidt_bundle hv hli j
  have hh : CMDiffAt n (fun y ↦ inner ℝ (gramSchmidt ℝ (fun i ↦ v i y) j)
      (gramSchmidt ℝ (fun i ↦ v i y) j)) x := hg.inner_bundle hg
  have hn : CMDiffAt n (fun y ↦ ‖gramSchmidt ℝ (fun i ↦ v i y) j‖) x := by
    have hr : ContDiffAt ℝ n Real.sqrt ((fun y : M ↦
        inner ℝ (gramSchmidt ℝ (fun i ↦ v i y) j)
          (gramSchmidt ℝ (fun i ↦ v i y) j)) x) :=
      Real.contDiffAt_sqrt (inner_self_ne_zero.mpr (gramSchmidt_ne_zero j hli))
    simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using hr.comp_contMDiffAt (I := I)
      (f := fun y : M ↦ inner ℝ (gramSchmidt ℝ (fun i ↦ v i y) j)
        (gramSchmidt ℝ (fun i ↦ v i y) j)) hh
  exact (hn.inv₀ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j hli))).smul_section hg

section Differentiable

variable [IsContMDiffRiemannianBundle I 1 F V]

omit [IsContMDiffRiemannianBundle I n F V] in
/-- Fiberwise Gram–Schmidt preserves differentiability at a linearly independent family. -/
theorem MDifferentiableAt.gramSchmidt_bundle
    (hv : ∀ i, MDiffAt (T% (v i)) x)
    (hli : LinearIndependent ℝ (fun i ↦ v i x)) (j : ι) :
    MDiffAt (T% (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j)) x := by
  classical
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hg (i : ι) (hi : i < j) := ih i hi
    have hc (i : ι) (hi : i < j) :
        MDiffAt (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
          inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
            (gramSchmidt ℝ (fun k ↦ v k y) i)) x :=
      ((hg i hi).inner_bundle (hv j)).div ((hg i hi).inner_bundle (hg i hi))
        (inner_self_ne_zero.mpr (gramSchmidt_ne_zero i hli))
    have hformula : (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j) =
        v j - ∑ i ∈ Finset.Iio j,
          (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
            inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
              (gramSchmidt ℝ (fun k ↦ v k y) i)) •
            (fun y ↦ gramSchmidt ℝ (fun k ↦ v k y) i) := by
      funext y
      simp only [Pi.sub_apply, Finset.sum_apply, real_inner_self_eq_norm_sq]
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (fun i ↦ v i y) j).symm
    have hs := mdifferentiableAt_sub_section (hv j) (MDifferentiableAt.sum_section fun i hi ↦
      (hc i (Finset.mem_Iio.mp hi)).smul_section (hg i (Finset.mem_Iio.mp hi)))
    apply hs.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro y
    apply congrArg (TotalSpace.mk' F y)
    simpa only [Pi.sub_apply, Finset.sum_apply] using congrFun hformula y

end Differentiable

end
