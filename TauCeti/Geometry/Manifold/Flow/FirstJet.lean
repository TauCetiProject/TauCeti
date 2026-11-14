/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.TimeDependentFlow
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Time-dependent flows with zero first jet

A time-dependent vector field vanishing to first order at a point has a flow fixing that point
with identity differential on its full ambient tangent space. Vanishing of the first derivative
is expressed using an auxiliary connection. Both `HasMFDerivAt` and its differential and
pointwise consequences are provided. The conclusion concerns every time:
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

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  {X : ℝ → Π x : M, TangentSpace I x} {x : M}

/-- If a jointly `C²` time-dependent vector field and its covariant derivative vanish at `x`
at every time, its time map has identity derivative at `x`. The identity is transported to
the target tangent space using the stationary-point equation. No completeness is required. -/
theorem hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (hcov : ∀ u, cov (X u) x = 0) (s t : ℝ) :
    HasMFDerivAt I I (timeDependentFlowOf X s t) x
      ((timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
  have hX₁ := hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hfix (u : ℝ) := timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hx s u
  have hcurve : (fun u ↦ timeDependentFlowOf X s u x) = fun _ ↦ x := funext hfix
  have hopen := isOpen_timeDependentFlowDomain hX₁
  have hflow := contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX
  have hdiff : MDifferentiableAt I I (timeDependentFlowOf X s t) x :=
    ((hflow.contMDiffAt (hopen.mem_nhds
      (mem_timeDependentFlowDomain_of_forall_eq_zero hx s t))).comp x
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by norm_num)
  refine hdiff.hasMFDerivAt.congr_mfderiv ?_
  ext v
  -- Read the moving tangent vector in one fixed chart. In particular, the ordinary derivative
  -- below is taken in the normed model space, rather than between different tangent fibres.
  let γ : ℝ → M := fun u ↦ timeDependentFlowOf X s u x
  let Q : ∀ u, TangentSpace I (γ u) :=
    fun u ↦ mfderiv I I (timeDependentFlowOf X s u) x v
  have hγ (u : ℝ) : γ u = x := hfix u
  have hγfun : γ = fun _ ↦ x := hcurve
  let e := trivializationAt E (TangentSpace I) x
  have hmem (u : ℝ) : γ u ∈ e.baseSet := by
    rw [hγ]
    exact mem_baseSet_trivializationAt E (TangentSpace I) x
  let V : ℝ → E := sectionCoord (F := E) γ Q x
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
    have heq : (fun r ↦ inTangentCoordinates I I (fun _ ↦ x) γ
        (fun r ↦ mfderiv I I (timeDependentFlowOf X s r) x) u r v) = V := by
      funext r
      rw [inTangentCoordinates_eq_self_of_eq (x₀ := u) (x := r)
        _ _ _ rfl ((hfix r).trans (hfix u).symm)]
      dsimp only [V, γ, Q]
      rw [sectionCoord_apply]
      -- At a stationary point the fixed chart is also the chart at the vector's base point.
      have hread (y : M) (hy : y = x) (w : TangentSpace I y) :
          (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y w = w := by
        subst y
        exact continuousLinearMapAt_trivializationAt_self x w
      exact (hread _ (hfix r) _).symm
    simp only [id_eq] at hd
    rw [heq] at hd
    exact hd.contDiffAt.differentiableAt (by norm_num)
  have hderiv (u : ℝ) : deriv V u = 0 := by
    -- Symmetrization preserves the first jet at a zero, so no torsion hypothesis is needed.
    have hv := cov.symmetrize.alongCurve_mfderiv_timeDependentFlowOf
      cov.isTorsionFree_symmetrize hX
      (mem_timeDependentFlowDomain_of_forall_eq_zero hx s u) v
    have hcovzero : cov.symmetrize (X u) (γ u) = 0 := by
      rw [hγ, cov.symmetrize_apply_of_eq_zero (hx u), hcov]
    -- These local abbreviations pin the same dependent curve and section as the variational
    -- equation; no tangent vector is identified with a vector in a different fibre.
    change alongCurve cov.symmetrize γ Q u = _ at hv
    rw [hcovzero, zero_apply] at hv
    have hread := cov.symmetrize.continuousLinearMapAt_alongCurveWithin
      (γ := γ) (s := univ) (t := u) rfl Q
    rw [alongCurveWithin_univ, hv, map_zero] at hread
    have hchart : derivWithin (extChartAt I (γ u) ∘ γ) univ u = 0 := by
      rw [hγfun, Function.comp_def, derivWithin_fun_const, Pi.zero_apply]
    rw [hchart, map_zero, add_zero, derivWithin_univ] at hread
    rw [hγ u] at hread
    exact hread.symm
  have hconst : V t = V s := is_const_of_deriv_eq_zero hV hderiv t s
  have hVs : V s = e.continuousLinearMapAt ℝ x v := by
    dsimp only [V, Q, γ]
    rw [sectionCoord_apply, mfderiv_timeDependentFlowOf_self]
    -- Unfold only the chart abbreviation and evaluation of the identity map in this fibre.
    change e.continuousLinearMapAt ℝ (timeDependentFlowOf X s s x) v = _
    rw [timeDependentFlowOf_self]
  have htransport (y : M) (hy : x = y) :
      e.symmL ℝ y (e.continuousLinearMapAt ℝ x v) =
        (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
          TangentSpace I x →L[ℝ] TangentSpace I y) v := by
    subst y
    exact e.symmL_continuousLinearMapAt
      (mem_baseSet_trivializationAt E (TangentSpace I) x) v
  calc
    Q t = e.symmL ℝ (γ t) (V t) := by
      dsimp only [V]
      rw [sectionCoord_apply]
      exact (e.symmL_continuousLinearMapAt (hmem t) (Q t)).symm
    _ = e.symmL ℝ (γ t) (e.continuousLinearMapAt ℝ x v) := by rw [hconst, hVs]
    _ = _ := htransport _ (hfix t).symm

/-- A stationary zero first jet gives identity differential on the full tangent space.
The transport keeps the source and target tangent-space carriers explicit. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (hcov : ∀ u, cov (X u) x = 0) (s t : ℝ) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (cov.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero hX hx hcov s t).mfderiv

/-- The linearized flow fixes every tangent vector at a stationary zero first jet, transported
along the stationary-point equality to the tangent space at the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (hcov : ∀ u, cov (X u) x = 0) (s t : ℝ)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s t) x v =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸ v := by
  have happly (y : M) (hy : x = y) :
      (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
        TangentSpace I x →L[ℝ] TangentSpace I y) v = hy ▸ v := by
    subst y
    rfl
  rw [cov.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero hX hx hcov, happly]

end CovariantDerivative
