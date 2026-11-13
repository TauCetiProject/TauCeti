/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.TimeDependentFlow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Time-dependent flows with zero first jet

A time-dependent vector field vanishing to first order at a point has a flow fixing that point
with identity differential on its full ambient tangent space. Vanishing of the first derivative
is expressed using an auxiliary connection. The conclusion concerns every time:
a stationary solution exists for all time even when the vector field is not complete.

This is the flow ingredient in the refinement of relative Moser's theorem which preserves the
ambient first jet along a submanifold, rather than just its points.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the variational equation).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, §7 (relative Moser theorem).
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  {X : ℝ → Π x : M, TangentSpace I x} {x : M}

/-- If a jointly `C²` time-dependent vector field and its covariant derivative vanish at `x`
at every time, its time map has identity differential at `x`. The identity is transported to
the target tangent space using the stationary-point equation. No completeness is required. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (hcov : ∀ u, cov (X u) x = 0) (s t : ℝ) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  have hX₁ := hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hfix (u : ℝ) := timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hx s u
  have hcurve : (fun u ↦ timeDependentFlowOf X s u x) = fun _ ↦ x := funext hfix
  have hopen := isOpen_timeDependentFlowDomain hX₁
  have hflow := contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX
  ext v
  -- On the stationary curve all fibres are read in the same chart. The model norm is used
  -- only inside the proof; the conclusion retains the original tangent-space carriers.
  let V : ℝ → E := fun u ↦ mfderiv I I (timeDependentFlowOf X s u) x v
  have hV : Differentiable ℝ V := by
    intro u
    have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2
        (fun p : ℝ × M ↦ timeDependentFlowOf X s p.1 p.2) (u, x) :=
      (hflow.contMDiffAt (hopen.mem_nhds
        (mem_timeDependentFlowDomain_of_forall_eq_zero hx s u))).comp (u, x)
          ((contMDiffAt_const.prodMk contMDiffAt_fst).prodMk contMDiffAt_snd)
    have hd := hf.mfderiv_apply (I := I) (I' := I) (E := E) (E' := E) (m := 1)
      (fun u y ↦ timeDependentFlowOf X s u y)
      (fun _ ↦ x) id (fun _ ↦ (v : E)) contMDiffAt_const contMDiffAt_id contMDiffAt_const
      (by norm_num)
    have heq : (fun r ↦ inTangentCoordinates I I (fun _ ↦ x)
        (fun r ↦ timeDependentFlowOf X s r x)
        (fun r ↦ mfderiv I I (timeDependentFlowOf X s r) x) u r v) = V := by
      funext r
      erw [inTangentCoordinates_eq _ _ _ (mem_chart_source H x) (by simp [hfix])]
      erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      simp only [hfix]
      erw [ContinuousLinearMap.comp_apply, tangentCoordChange_self (mem_extChartAt_source x),
        ContinuousLinearMap.comp_apply, tangentCoordChange_self (mem_extChartAt_source x)]
      rfl
    simp only [id_eq] at hd
    erw [heq] at hd
    exact hd.contDiffAt.differentiableAt (by norm_num)
  have hderiv (u : ℝ) : deriv V u = 0 := by
    -- Symmetrization preserves the first jet at a zero, so the existing torsion-free
    -- variational equation applies without restricting the auxiliary connection.
    have hv := cov.symmetrize.alongCurve_mfderiv_timeDependentFlowOf
      cov.isTorsionFree_symmetrize hX
      (mem_timeDependentFlowDomain_of_forall_eq_zero hx s u) v
    rw [hfix, cov.symmetrize_apply_of_eq_zero (hx u), hcov, zero_apply] at hv
    erw [hcurve, alongCurve_const] at hv
    exact hv
  have hconst := is_const_of_deriv_eq_zero hV hderiv t s
  have hid (y : M) (hy : x = y) :
      (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
        TangentSpace I x →L[ℝ] TangentSpace I y) =
          (ContinuousLinearMap.id ℝ E : E →L[ℝ] E) := by
    cases hy
    rfl
  erw [hid _ (hfix t).symm]
  exact hconst.trans (congrArg (fun A : E →L[ℝ] E ↦ A v)
    (mfderiv_timeDependentFlowOf_self X s x))

end CovariantDerivative
