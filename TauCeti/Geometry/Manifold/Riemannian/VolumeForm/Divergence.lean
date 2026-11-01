/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The divergence and the Riemannian volume form

On an oriented Riemannian manifold with volume form `dV`, the divergence of a vector field `X`,
defined as the trace of its Levi-Civita covariant derivative `∇X`, is the rate at which the flow
of `X` changes volume:

`L_X dV = (div X) dV`  and  `d (ι_X dV) = (div X) dV`.

The second identity is the form-level definition of the divergence in Lee's *Introduction to
Smooth Manifolds*; together with Stokes' theorem it turns the integral of `div X` over a compact
oriented manifold with boundary into the flux of `X` through the boundary. Both identities hold at
every point where `X` is differentiable, including boundary and corner points, for a `C¹` metric
on a `C²` manifold.

## Main results

* `TauCeti.mlieDerivForm_riemannianVolumeForm_apply`, `TauCeti.mlieDerivForm_riemannianVolumeForm`:
  `L_X dV = (div X) dV`.
* `TauCeti.mextDeriv_interior_riemannianVolumeForm_apply`,
  `TauCeti.mextDeriv_interior_riemannianVolumeForm`: `d (ι_X dV) = (div X) dV`.

## Implementation notes

Both sides of `L_X dV = (div X) dV` are top-degree forms, so it suffices to evaluate them on the
chart frame `e₁, …, eₙ` at the point. There the volume form is `±ρ` with a locally constant sign,
where `ρ = √(det G)` is the chart volume density, and the bracket formula for the Lie derivative
reads

`L_X dV (e) = X (dV (e)) - ∑ᵢ dV (e₁, …, [X, eᵢ], …, eₙ) = dV (e) (X (log ρ) - ∑ᵢ [X, eᵢ]ⁱ)`.

Torsion-freeness gives `[X, eᵢ] = ∇_X eᵢ - ∇_{eᵢ} X`, and metric compatibility gives
`X (log ρ) = ∑ᵢ (∇_X eᵢ)ⁱ` (`TauCeti.mvfderiv_chartVolumeDensity`), so what remains is
`∑ᵢ (∇_{eᵢ} X)ⁱ = div X`. Cartan's formula `L_X dV = d (ι_X dV) + ι_X (d dV)` then gives the second
identity, since `d dV` has degree above the dimension.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 16, "The Divergence Theorem" (the divergence defined by `d (ι_X dV) = (div X) dV`).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence as the trace of the total covariant derivative).
-/

public section

noncomputable section

open Bundle Module Riemannian.Tensor TauCeti.Manifold VectorField
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {m : ℕ} {X : (x : M) → TangentSpace I x}

/-- **The divergence measures the change of volume.** At a point where the vector field `X` is
differentiable, the Lie derivative of the Riemannian volume form along `X` is the divergence of
`X` times the volume form. -/
theorem mlieDerivForm_riemannianVolumeForm_apply (o : Manifold.Orientation I M (Fin m)) {x : M}
    (hX : MDiffAt (T% X) x) :
    mlieDerivForm X (riemannianVolumeForm o) x = divergence I X x • riemannianVolumeForm o x := by
  -- We evaluate both sides on the chart frame `e` at `x`, computing the three terms of the bracket
  -- formula `L_X dV (e) = X (dV (e)) - ∑ᵢ dV (e₁, …, [X, eᵢ], …, eₙ)` separately.
  classical
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  set e := trivializationAt E (TangentSpace I) x
  set b := Module.finBasis ℝ E
  set cov := CovariantDerivative.leviCivitaConnection I M
  have ht : cov.IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero _).2
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).torsion
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  let σ : Fin (finrank ℝ E) ≃ Fin m := finCongr hm
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hx
  -- The chart frame at `x`, indexed by `Fin m`, and the tangent basis it gives at `x`.
  let F : Fin m → (y : M) → TangentSpace I y := fun i ↦ chartLocalFrame (I := I) x (σ.symm i)
  let B : Basis (Fin m) ℝ (TangentSpace I x) := (e.basisAt b hx).reindex σ
  have hB : ⇑B = (F · x) := by
    funext i
    rw [Module.Basis.reindex_apply]
    simp only [F, chartLocalFrame_def]
    exact (e.localFrame_apply_of_mem_baseSet b (i := σ.symm i) hx).symm
  have hrepr (w : TangentSpace I x) (i : Fin m) :
      B.repr w i = e.localFrameCoeff I b (σ.symm i) x w := by
    rw [Module.Basis.repr_reindex_apply, e.localFrameCoeff_apply_of_mem_baseSet b hx (fun _ ↦ w)]
  have hF (i : Fin m) : MDiffAt (T% (F i)) x :=
    ((contMDiffOn_chartLocalFrame (n := 1) x (σ.symm i)).contMDiffAt hbase).mdifferentiableAt
      one_ne_zero
  have hφ := ((isSmoothForm_riemannianVolumeForm (n := 1) o).contMDiff x).mdifferentiableAt
    one_ne_zero
  -- Near `x` the volume of the chart frame is `c ρ` for a constant `c`.
  obtain ⟨c, -, hc⟩ := exists_eventually_riemannianVolumeForm_chartLocalFrame_eq o σ x
  have hc' : (fun y ↦ riemannianVolumeForm o y (F · y)) =ᶠ[𝓝 x]
      fun y ↦ c * chartVolumeDensity (I := I) x y := hc
  have hρ : MDiffAt (chartVolumeDensity (I := I) x) x :=
    ((contMDiffOn_chartVolumeDensity (n := 1) x).contMDiffAt hbase).mdifferentiableAt one_ne_zero
  have hφB : riemannianVolumeForm o x B = c * chartVolumeDensity (I := I) x x := by
    rw [hB]
    exact hc.self_of_nhds
  -- `X (dV (e)) = dV (e) ∑ᵢ (∇_X eᵢ)ⁱ`.
  have hderiv : mvfderiv I (fun y ↦ riemannianVolumeForm o y (F · y)) x (X x) =
      riemannianVolumeForm o x B * ∑ i, B.repr (cov (F i) x (X x)) i := by
    rw [hc'.mvfderiv_eq, mvfderiv_fun_mul mdifferentiableAt_const hρ, mvfderiv_const, smul_zero,
      add_zero, smul_apply, mvfderiv_chartVolumeDensity
        (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).isMetricCompatible
        x hx (X x), hφB, smul_eq_mul, mul_assoc]
    congr 2
    simp only [hrepr]
    exact (Equiv.sum_comp σ.symm fun k ↦
      e.localFrameCoeff I b k x (cov (chartLocalFrame (I := I) x k) x (X x))).symm
  -- `dV (e₁, …, [X, eᵢ], …, eₙ) = ([X, eᵢ])ⁱ dV (e)`, with `[X, eᵢ] = ∇_X eᵢ - ∇_{eᵢ} X`.
  have hbracket (i : Fin m) :
      riemannianVolumeForm o x (Function.update B i (mlieBracket I X (F i) x)) =
        (B.repr (cov (F i) x (X x)) i - B.repr (cov X x (B i)) i) *
          riemannianVolumeForm o x B := by
    rw [← (cov.isTorsionFree_iff.1 ht) hX (hF i), ← congrFun hB i, ← Finsupp.sub_apply,
      ← map_sub, ← smul_eq_mul]
    exact (riemannianVolumeForm o x).toAlternatingMap.map_update_basis B i _
  -- `∑ᵢ (∇_{eᵢ} X)ⁱ = div X`.
  have hdiv : divergence I X x = ∑ i, B.repr (cov X x (B i)) i := by
    rw [divergence_def, LinearMap.trace_eq_matrix_trace ℝ B]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
    rfl
  -- Both sides are top-degree forms, so they agree once they agree on the basis `B`.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [(mlieDerivForm X (riemannianVolumeForm o) x).toAlternatingMap.eq_smul_basis_det B,
    (divergence I X x • riemannianVolumeForm o x).toAlternatingMap.eq_smul_basis_det B]
  congr 1
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [ContinuousAlternatingMap.smul_apply, hB, mlieDerivForm_apply_vectorField hφ hF, ← hB,
    hderiv, Finset.sum_congr rfl fun i _ ↦ hbracket i, ← Finset.sum_mul, Finset.sum_sub_distrib,
    hdiv, smul_eq_mul]
  ring

/-- **The divergence measures the change of volume.** For a differentiable vector field `X`, the
Lie derivative of the Riemannian volume form along `X` is the divergence of `X` times the volume
form. -/
theorem mlieDerivForm_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (hX : MDiff (T% X)) :
    mlieDerivForm X (riemannianVolumeForm o) = divergence I X • riemannianVolumeForm o :=
  funext fun x ↦ mlieDerivForm_riemannianVolumeForm_apply o (hX x)

/-- **The divergence through the volume form**, `d (ι_X dV) = (div X) dV`: at a point where the
vector field `X` is differentiable, the exterior derivative of the contraction of the Riemannian
volume form with `X` is the divergence of `X` times the volume form. -/
theorem mextDeriv_interior_riemannianVolumeForm_apply {k : ℕ}
    (o : Manifold.Orientation I M (Fin (k + 1))) {x : M} (hX : MDiffAt (T% X) x) :
    mextDeriv ((riemannianVolumeForm o).interior X) x =
      divergence I X x • riemannianVolumeForm o x := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hφ := ((isSmoothForm_riemannianVolumeForm (n := 1) o).contMDiff x).mdifferentiableAt
    one_ne_zero
  have hm : finrank ℝ E ≤ k + 1 := by simp [← o.card_eq]
  rw [← mlieDerivForm_eq_mextDeriv_interior_apply hφ hX
      (congrFun (mextDeriv_eq_zero_of_finrank_le hm _) x),
    mlieDerivForm_riemannianVolumeForm_apply o hX]

/-- **The divergence through the volume form**, `d (ι_X dV) = (div X) dV`: for a differentiable
vector field `X`, the exterior derivative of the contraction of the Riemannian volume form with
`X` is the divergence of `X` times the volume form. -/
theorem mextDeriv_interior_riemannianVolumeForm {k : ℕ}
    (o : Manifold.Orientation I M (Fin (k + 1))) (hX : MDiff (T% X)) :
    mextDeriv ((riemannianVolumeForm o).interior X) =
      divergence I X • riemannianVolumeForm o :=
  funext fun x ↦ mextDeriv_interior_riemannianVolumeForm_apply o (hX x)

end TauCeti
