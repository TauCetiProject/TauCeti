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
# Time-dependent flows of fields with zero first jet

A time-dependent vector field stationary at a point and vanishing to first order there
between two times has a flow fixing that point with identity differential on its full ambient
tangent space. Vanishing of the first derivative is expressed using an auxiliary connection.
Both `HasMFDerivAt` and its differential and
pointwise consequences are provided. A stationary solution exists for all time even when the
vector field is not complete; vanishing of the covariant derivative is needed only between the
specified times.

This is the flow ingredient in the refinement of relative Moser's theorem which preserves the
ambient first jet along a submanifold, rather than just its points.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, §7 (relative Moser theorem).
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  {X : ℝ → Π x : M, TangentSpace I x} {x : M}

private theorem differentiable_sectionCoord_mfderiv_timeDependentFlowOf
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s : ℝ) (v : TangentSpace I x) :
    Differentiable ℝ (sectionCoord (F := E) (fun u ↦ timeDependentFlowOf X s u x)
      (fun u ↦ mfderiv I I (timeDependentFlowOf X s u) x v) x) := by
  have hX₁ := hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hfix (u : ℝ) := timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hx s u
  have hopen := isOpen_timeDependentFlowDomain hX₁
  have hflow := contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX
  let γ : ℝ → M := fun u ↦ timeDependentFlowOf X s u x
  let Q : ∀ u, TangentSpace I (γ u) :=
    fun u ↦ mfderiv I I (timeDependentFlowOf X s u) x v
  let V : ℝ → E := sectionCoord (F := E) γ Q x
  let e := trivializationAt E (TangentSpace I) x
  intro u
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2
      (fun p : ℝ × M ↦ timeDependentFlowOf X s p.1 p.2) (u, x) :=
    (hflow.contMDiffAt (hopen.mem_nhds
      (mem_timeDependentFlowDomain_of_forall_eq_zero hx s u))).comp (u, x)
        ((contMDiffAt_const.prodMk contMDiffAt_fst).prodMk contMDiffAt_snd)
  have hd := hf.mfderiv_apply (I := I) (I' := I) (E := E) (E' := E) (m := 1)
    (fun u y ↦ timeDependentFlowOf X s u y)
    (fun _ ↦ x) id (fun _ ↦ e.continuousLinearMapAt ℝ x v)
    contMDiffAt_const contMDiffAt_id contMDiffAt_const (by norm_num)
  have heq : (fun r ↦ inTangentCoordinates I I (fun _ ↦ x) γ
      (fun r ↦ mfderiv I I (timeDependentFlowOf X s r) x) u r
        (e.continuousLinearMapAt ℝ x v)) = V := by
    funext r
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    have hbase : γ u = x := hfix u
    have hcancel : e.symmL ℝ x (e.continuousLinearMapAt ℝ x v) = v :=
      e.symmL_continuousLinearMapAt
        (mem_baseSet_trivializationAt E (TangentSpace I) x) v
    rw [hbase, hcancel]
    exact (sectionCoord_apply γ Q x r).symm
  simp only [id_eq] at hd
  rw [heq] at hd
  exact hd.contDiffAt.differentiableAt (by norm_num)

omit [BoundarylessManifold I M] [T2Space M] in
private theorem deriv_sectionCoord_eq_zero_of_stationary
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (Q : ∀ u, TangentSpace I (γ u)) (hγ : ∀ u, γ u = x)
    (u : ℝ) (hQ : alongCurve cov γ Q u = 0) :
    deriv (sectionCoord (F := E) γ Q x) u = 0 := by
  have hread := cov.continuousLinearMapAt_alongCurveWithin
    (γ := γ) (s := univ) (t := u) rfl Q
  rw [alongCurveWithin_univ, hQ, map_zero] at hread
  have hchart : derivWithin (extChartAt I (γ u) ∘ γ) univ u = 0 := by
    have hcurve : γ = fun _ ↦ x := funext hγ
    rw [hcurve, Function.comp_def, derivWithin_fun_const, Pi.zero_apply]
  rw [hchart, map_zero, add_zero, derivWithin_univ, hγ u] at hread
  exact hread.symm

/-- If a jointly `C²` time-dependent vector field vanishes at `x` at every time and its
covariant derivative vanishes there between `s` and `t`, its time map has identity derivative.
The identity is transported to the target tangent space using the stationary-point equation. No
completeness is required. -/
theorem hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    HasMFDerivAt I I (timeDependentFlowOf X s t) x
      ((timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
  have hX₁ := hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
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
  have hγ (u : ℝ) : γ u = x :=
    timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hx s u
  let e := trivializationAt E (TangentSpace I) x
  have hmem (u : ℝ) : γ u ∈ e.baseSet := by
    rw [hγ]
    exact mem_baseSet_trivializationAt E (TangentSpace I) x
  let V : ℝ → E := sectionCoord (F := E) γ Q x
  have hV : Differentiable ℝ V :=
    differentiable_sectionCoord_mfderiv_timeDependentFlowOf hX hx s v
  have hderiv (u : ℝ) (hu : u ∈ uIcc s t) : deriv V u = 0 := by
    -- Symmetrization preserves the first jet at a zero, so no torsion hypothesis is needed.
    have hv : alongCurve cov.symmetrize γ Q u = cov.symmetrize (X u) (γ u) (Q u) :=
      cov.symmetrize.alongCurve_mfderiv_timeDependentFlowOf
        cov.isTorsionFree_symmetrize hX
        (mem_timeDependentFlowDomain_of_forall_eq_zero hx s u) v
    have hcovzero : cov.symmetrize (X u) (γ u) = 0 := by
      rw [hγ, cov.symmetrize_apply_of_eq_zero (hx u), hcov u hu]
    rw [hcovzero, zero_apply] at hv
    exact deriv_sectionCoord_eq_zero_of_stationary cov.symmetrize γ Q hγ u hv
  have hconst : V t = V s := by
    have hbound := (convex_uIcc s t).norm_image_sub_le_of_norm_deriv_le
      (fun u _ ↦ hV u) (fun u hu ↦ by rw [hderiv u hu, norm_zero])
      (left_mem_uIcc : s ∈ uIcc s t) (right_mem_uIcc : t ∈ uIcc s t)
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  have hVs : V s = e.continuousLinearMapAt ℝ x v := by
    dsimp only [V, Q, γ, e]
    rw [sectionCoord_apply, mfderiv_timeDependentFlowOf_self,
      timeDependentFlowOf_self, ContinuousLinearMap.id_apply]
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
    _ = _ := htransport _ (hγ t).symm

/-- A stationary field with zero first jet between `s` and `t` gives identity differential on
the full tangent space. The transport keeps the source and target tangent-space carriers
explicit. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (cov.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero hX hx s t hcov).mfderiv

/-- The linearized flow fixes every tangent vector of a stationary field with zero first jet
between `s` and `t`, transported to the tangent space at the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s t) x v =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero
        (hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hx s t).symm ▸ v := by
  have happly (y : M) (hy : x = y) :
      (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
        TangentSpace I x →L[ℝ] TangentSpace I y) v = hy ▸ v := by
    subst y
    exact ContinuousLinearMap.id_apply v
  rw [cov.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero hX hx s t hcov, happly]

end CovariantDerivative
