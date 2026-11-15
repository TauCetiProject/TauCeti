/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Regular zeros of differentials

The differential `df` of a function `f` on a manifold without boundary is a section of the
cotangent bundle. This file computes its intrinsic linearization.

* In the canonical trivialization at `x`, the coordinate derivative of `df` at `x` is the critical
  Hessian (`TauCeti.mvfderiv_trivializationAt_mvfderiv_apply_apply`).
* Hence the linearization of `df` is the critical Hessian at every point where `f` is `C²`
  (`TauCeti.sectionLinearization_mvfderiv`). At a critical point it is onto exactly when the
  critical point is nondegenerate (`TauCeti.surjective_sectionLinearization_mvfderiv_iff`). The
  tangent and cotangent spaces have the same finite dimension, so this linearization is Fredholm
  of index zero (`TauCeti.index_sectionLinearization_of_finiteDimensional`).

The same comparison for zeros of locally exact one-forms, valued in alternating maps, is in
`TauCeti.Geometry.Manifold.Morse.OneForm.Linearization`.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 6,
  §1.
-/

public section

open Bundle Function Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I 2 M] {f : M → ℝ} {x : M}

/-- In the canonical trivialization at `x`, the coordinate derivative of `df` at `x`, evaluated
on `v` and then on `w`, is the critical Hessian `Hess_x f (v, w)`. -/
theorem mvfderiv_trivializationAt_mvfderiv_apply_apply (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TangentSpace I x) :
    mvfderiv I (fun y ↦ (trivializationAt (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) x
        ⟨y, mvfderiv I f y⟩).2) x v w = criticalHessian I f x v w := by
  set t := trivializationAt E (TangentSpace I) x
  -- The coordinates of `df` are those of Mathlib's `mfderiv` in tangent coordinates, which is `C¹`.
  have hd : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y ↦ mvfderiv I f y ∘L t.symmL ℝ y) x := by
    have h := (hf.mfderiv_const (m := 1) le_rfl).mdifferentiableAt one_ne_zero
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      TangentBundle.continuousLinearMapAt_model_space]
    -- `mvfderiv` is `mfderiv` with its values read in the model space `ℝ`. The two sides differ
    -- only by the identification `TangentSpace 𝓘(ℝ) (f y) = ℝ`, so `rw`/`simp` with
    -- `mvfderiv_apply_eq_mfderiv_apply` leaves a goal that is not type-correct; close it by `rfl`.
    rfl
  simp only [CotangentBundle.trivializationAt_mk_snd]
  rw [← mvfderiv_clm_apply_const hd w v, ← mvfderiv_mvfderiv_extend_eq_criticalHessian hf v w,
    Manifold.extend_eq_trivializationAt_symm]
  refine congrArg (· v) (EventuallyEq.mvfderiv_eq (F := ℝ) ?_)
  filter_upwards [t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)]
    with y hy
  exact congrArg (mvfderiv I f y) (t.symmL_apply (R := ℝ) hy w)

/-- **The linearization of a differential is the Hessian.** As a section of the cotangent bundle,
the differential `df` of a function which is `C²` at `x` has intrinsic linearization the critical
Hessian of `f` at `x`. This holds at every point, critical or not, since both sides are computed
in the preferred chart at `x`. -/
theorem sectionLinearization_mvfderiv (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    sectionLinearization (F := E →L[ℝ] ℝ) (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) I
      (fun y ↦ y) (mvfderiv I f) x = criticalHessian I f x := by
  ext v w
  rw [sectionLinearization_def, ContinuousLinearMap.comp_apply,
    CotangentBundle.symmL_trivializationAt_self]
  exact mvfderiv_trivializationAt_mvfderiv_apply_apply hf v w

/-- **Regular zeros of a differential are nondegenerate critical points.** At a critical point
`x` of a function `f` which is `C²` at `x`, the differential `df`, as a section of the cotangent
bundle, has surjective linearization exactly when `x` is a nondegenerate critical point. -/
theorem surjective_sectionLinearization_mvfderiv_iff [FiniteDimensional ℝ E]
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hx : x ∈ criticalPoints I f) :
    Surjective (sectionLinearization (F := E →L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) I (fun y ↦ y) (mvfderiv I f) x) ↔
      IsManifoldNondegenerateCriticalPoint I f x := by
  rw [sectionLinearization_mvfderiv hf, isManifoldNondegenerateCriticalPoint_iff_criticalHessian]
  -- The critical Hessian maps `TangentSpace I x`, which is `E`, to its dual, of the same
  -- dimension, so it is invertible exactly when it is onto.
  exact ⟨fun hs ↦ ⟨hf, mem_criticalPoints.1 hx,
      ContinuousLinearMap.isInvertible_of_surjective (E := E) hs⟩,
    fun ⟨_, _, hinv⟩ ↦ hinv.surjective⟩

end TauCeti
