/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Frame
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap

/-!
# Connection one-forms and Cartan's second structure equation

In a local frame `s`, the scalar one-form `Aˡⱼ` is the coefficient of `∇sⱼ` along
`sₗ`. These one-forms are differentiable on the frame domain for a C¹ connection
and a C² frame. Their exterior derivatives give the curvature coefficients:
`Fˡⱼ = dAˡⱼ + ∑ₘ Aˡₘ ∧ Aᵐⱼ`.

Section coefficients are columns, so the matrix convention is `F = dA + A∧A`.
The formula uses the actual exterior derivative and wedge product of differential
forms. The direction fields need not commute, and no metric is required.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7.
* The expanded moving-frame calculation is `IsLocalFrameOn.coeff_curvatureOperator`;
  `TauCeti.mextDeriv_apply_one` identifies its differential terms.
-/

public section

open Bundle CovariantDerivative FiberBundle Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*} {s : ι → Π x, V x} {u : Set M}
  (hs : IsLocalFrameOn I F 2 s u) (cov : CovariantDerivative I F V)

/-- The connection coefficient one-form `Aˡⱼ` in a local frame. The input frame
index `j` precedes the output coefficient `l`, as in the Christoffel-symbol API. -/
def connectionForm (j l : ι) : TauCeti.RoughForm I M ℝ 1 := fun x ↦
  ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)
    (((hs.coeff l x).comp (cov (s j) x).toLinearMap).toContinuousLinearMap)

omit [VectorBundle ℝ F V] in
/-- A connection one-form evaluates to the corresponding frame coefficient of `∇sⱼ`. -/
@[simp]
theorem connectionForm_apply (j l : ι) (x : M) (v : Fin 1 → TangentSpace I x) :
    hs.connectionForm cov j l x v = hs.coeff l x (cov (s j) x (v 0)) := by
  rfl

variable [IsManifold I 2 M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle 2 F V I]
  (hu : IsOpen u) [ContMDiffCovariantDerivativeOn F 1 cov.toFun u]

include hu in
/-- The connection one-forms of a C¹ connection in a C² local frame are C¹
at every point of the open frame domain. -/
theorem contMDiffAt_connectionForm {x : M} (hx : x ∈ u) (j l : ι) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y
        (hs.connectionForm cov j l y)) x := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le one_le_two
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun v ↦ ?_⟩
  let e := trivializationAt E (TangentSpace I) x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hdir : CMDiff[e.baseSet] 1 (T% (fun y ↦ e.symmL ℝ y (v 0))) := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    exact (e.contMDiffAt_symmL hy).clm_bundle_apply (by
      rw [contMDiffAt_section_iff]
      exact contMDiffAt_const)
  have hd : CMDiff[u ∩ e.baseSet] 1
      (T% (fun y ↦ cov (s j) y (e.symmL ℝ y (v 0)))) :=
    ContMDiffOn.clm_bundle_apply
      ((ContMDiffCovariantDerivativeOn.contMDiff (hs.contMDiffOn j)).mono inter_subset_left)
      (hdir.mono inter_subset_right)
  have hc := (hs.mono inter_subset_left).contMDiffOn_coeff
    (hu.inter e.open_baseSet) one_le_two hd l
  refine (hc.contMDiffAt ((hu.inter e.open_baseSet).mem_nhds ⟨hx, he⟩)).congr_of_eventuallyEq ?_
  filter_upwards [(hu.inter e.open_baseSet).mem_nhds ⟨hx, he⟩] with y hy
  have hy' : y ∈ u ∩ (chartAt H x).source := hy
  simp [ContinuousAlternatingMap.inCoordinates, connectionForm,
    IsLocalFrameOn.coeff, hy.1, hy', e]
  -- Restricting a frame changes only membership proofs, so its pointwise basis is the same.
  rfl

variable [Fintype ι]

include hu in
/-- **Cartan's second structure equation**, evaluated on C¹ direction fields in
a C² local frame: `Fˡⱼ = dAˡⱼ + ∑ₘ Aˡₘ ∧ Aᵐⱼ`.
Section coefficients are columns, and the order of the wedge factors is matrix
multiplication order. -/
theorem coeff_curvatureOperator_eq_mextDeriv_add_wedge {x : M} (hx : x ∈ u)
    {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff[u] 1 (T% X)) (hY : CMDiff[u] 1 (T% Y)) (j l : ι) :
    hs.coeff l x (cov.curvatureOperator X Y (s j) x) =
      TauCeti.mextDeriv (hs.connectionForm cov j l) x ![X x, Y x] +
        ∑ m, ((hs.connectionForm cov m l).wedge (hs.connectionForm cov j m))
          x ![X x, Y x] := by
  rw [TauCeti.mextDeriv_apply_one
    ((hs.contMDiffAt_connectionForm cov hu hx j l).mdifferentiableAt one_ne_zero)
    ((hX.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt one_ne_zero)
    ((hY.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt one_ne_zero),
    hs.coeff_curvatureOperator hu cov hx hX hY j l]
  simp only [TauCeti.RoughForm.wedge_apply_one_one, connectionForm_apply,
    Matrix.cons_val_zero]
  simp only [mul_comm]
  abel

end IsLocalFrameOn
