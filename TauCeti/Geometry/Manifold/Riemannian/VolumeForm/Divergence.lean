/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-!
# The divergence and the Riemannian volume form

On an oriented Riemannian manifold with volume form `dV`, the divergence of a vector field `X`,
defined as the trace of its Levi-Civita covariant derivative, is characterized by

`d (ι_X dV) = (div X) dV`.

This is the form-level description of the divergence: `ι_X dV` is the flux form of `X`, and the
identity is what turns Stokes' theorem for `ι_X dV` into the divergence theorem. The divergence
itself is defined without reference to an orientation; reversing the orientation changes the sign
of both `dV` and `ι_X dV`.

The proof is a computation in the coordinate frame `e₁, …, eₙ` of a chart. There
`dV(e₁, …, eₙ) = ±ρ` with `ρ = √det (gᵢⱼ)` and a locally constant sign, and contracting `X` into
`dV` and evaluating on the frame with `eᵢ` removed gives `±(-1)^(i-1) ρ Xⁱ`. Since coordinate
vector fields commute, the invariant formula for the exterior derivative reduces to
`d (ι_X dV)(e₁, …, eₙ) = ± ∑ᵢ ∂ᵢ (ρ Xⁱ)`, which is `± ρ div X` by the coordinate formula for the
divergence. The identity holds at every point where `X` is differentiable, including boundary and
corner points.

## Main results

* `TauCeti.mextDeriv_interior_riemannianVolumeForm_apply`: `d (ι_X dV) = (div X) dV` at a point
  where `X` is differentiable.
* `TauCeti.mextDeriv_interior_riemannianVolumeForm`: the same identity for a differentiable
  vector field, as an equality of forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 16, the divergence of a vector field on an oriented Riemannian manifold.
* John M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5, the divergence as the trace of the covariant derivative.
-/

public section

noncomputable section

open Bundle Filter Module Riemannian.Tensor
open scoped Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] {m : ℕ}

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Near `x`, contracting `X` into the volume form and evaluating on the coordinate frame with its
`i`-th vector removed gives `(-1)^i c ρ Xⁱ`, where `Xⁱ` is the `i`-th coordinate of `X` and
`c ρ` is the volume of the frame. -/
private theorem eventually_interior_riemannianVolumeForm_removeNth
    (o : Manifold.Orientation I M (Fin (m + 1))) (σ : Fin (finrank ℝ E) ≃ Fin (m + 1))
    (X : (x : M) → TangentSpace I x) {x : M} {c : ℝ}
    (hc : ∀ᶠ y in 𝓝 x, riemannianVolumeForm o y (fun i ↦ chartLocalFrame (I := I) x (σ.symm i) y) =
      c * chartVolumeDensity (I := I) x y) :
    ∀ᶠ y in 𝓝 x, ∀ i : Fin (m + 1),
      (riemannianVolumeForm o).interior X y (i.removeNth fun j ↦ chartLocalFrame x (σ.symm j) y) =
        (-1) ^ (i : ℕ) * c * (chartVolumeDensity (I := I) x y *
          (trivializationAt E (TangentSpace I) x).localFrameCoeff I (Module.finBasis ℝ E)
            (σ.symm i) y (X y)) := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  let _ : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set e := trivializationAt E (TangentSpace I) x
  filter_upwards [hc, e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)]
    with y hcy hy i
  have h := (riemannianVolumeForm o y).toAlternatingMap.map_vecCons_removeNth_basis
    ((e.basisAt (Module.finBasis ℝ E) hy).reindex σ) (X y) i
  rw [coe_basisAt_reindex_eq_chartLocalFrame σ x hy] at h
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, hcy, Module.Basis.repr_reindex_apply,
    ← e.localFrameCoeff_apply_of_mem_baseSet (I := I) _ hy X, smul_eq_mul] at h
  rw [RoughForm.interior_apply]
  linear_combination h

/-- The directional derivative of `(ι_X dV)(e₁, …, êᵢ, …, eₙ)` along `eᵢ` at `x` is
`(-1)^i c ∂ᵢ (ρ Xⁱ)`. -/
private theorem mvfderiv_interior_riemannianVolumeForm_removeNth
    (o : Manifold.Orientation I M (Fin (m + 1))) (σ : Fin (finrank ℝ E) ≃ Fin (m + 1))
    {X : (x : M) → TangentSpace I x} {x : M} {c : ℝ}
    (hc : ∀ᶠ y in 𝓝 x, riemannianVolumeForm o y (fun i ↦ chartLocalFrame (I := I) x (σ.symm i) y) =
      c * chartVolumeDensity (I := I) x y)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (i : Fin (m + 1)) :
    mvfderiv I (fun y ↦ (riemannianVolumeForm o).interior X y
        (i.removeNth fun j ↦ chartLocalFrame x (σ.symm j) y)) x (chartLocalFrame x (σ.symm i) x) =
      (-1) ^ (i : ℕ) * c * mvfderiv I (fun y ↦ chartVolumeDensity (I := I) x y *
          (trivializationAt E (TangentSpace I) x).localFrameCoeff I (Module.finBasis ℝ E)
            (σ.symm i) y (X y)) x (chartLocalFrame x (σ.symm i) x) := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  let _ : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hx := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) x
  have hρ : MDifferentiableAt I 𝓘(ℝ) (chartVolumeDensity (I := I) x) x :=
    ((contMDiffOn_chartVolumeDensity (n := 1) x).contMDiffAt
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx)).mdifferentiableAt
        one_ne_zero
  have hf := hρ.mul (mdifferentiableAt_localFrameCoeff (Module.finBasis ℝ E) hx hX (σ.symm i))
  -- The function is a constant multiple of `ρ Xⁱ` near `x`, and constants factor out of `d`.
  have h := mvfderiv_mul (mdifferentiableAt_const (c := (-1) ^ (i : ℕ) * c)) hf
  rw [mvfderiv_const, smul_zero, add_zero] at h
  rw [Filter.EventuallyEq.mvfderiv_eq
    ((eventually_interior_riemannianVolumeForm_removeNth o σ X hc).mono fun y hy ↦ hy i)]
  exact congrArg (fun L ↦ L (chartLocalFrame x (σ.symm i) x)) h

/-- **The divergence through the volume form.** At a point where the vector field `X` is
differentiable, the exterior derivative of the contraction of `X` into the Riemannian volume form
is the divergence of `X` times the volume form: `d (ι_X dV) = (div X) dV`. -/
theorem mextDeriv_interior_riemannianVolumeForm_apply
    (o : Manifold.Orientation I M (Fin (m + 1))) {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) :
    mextDeriv ((riemannianVolumeForm o).interior X) x =
      Manifold.divergence I X x • riemannianVolumeForm o x := by
  classical
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hm : finrank ℝ E = m + 1 := by simpa using o.card_eq.symm
  let σ : Fin (finrank ℝ E) ≃ Fin (m + 1) := finCongr hm
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  obtain ⟨c, -, hc⟩ := exists_eventually_riemannianVolumeForm_chartLocalFrame_eq o σ x
  -- The inputs of the invariant formula are differentiable at `x`, and the frame commutes.
  have hφ := RoughForm.mdifferentiableAt_interior hX
    (((isSmoothForm_riemannianVolumeForm (n := 1) o).contMDiff x).mdifferentiableAt one_ne_zero)
  have hV (i : Fin (m + 1)) : MDifferentiableAt I I.tangent
      (fun y ↦ (chartLocalFrame (I := I) x (σ.symm i) y : TangentBundle I M)) x :=
    ((contMDiffOn_chartLocalFrame (n := 1) x (σ.symm i)).contMDiffAt
      (e.open_baseSet.mem_nhds hx)).mdifferentiableAt one_ne_zero
  have hVV (i j : Fin (m + 1)) : VectorField.mlieBracket I (chartLocalFrame (I := I) x (σ.symm i))
      (chartLocalFrame x (σ.symm j)) x = 0 := by
    simpa only [chartLocalFrame_def] using Manifold.mlieBracket_localFrame_trivializationAt
      (Module.finBasis ℝ E) x (mem_extChartAt_source x) (σ.symm i) (σ.symm j)
  -- Compare the two top forms on the coordinate frame at `x`.
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul _ ((e.basisAt (Module.finBasis ℝ E) hx).reindex σ),
    ContinuousAlternatingMap.apply_eq_det_mul (Manifold.divergence I X x • riemannianVolumeForm o x)
      ((e.basisAt (Module.finBasis ℝ E) hx).reindex σ),
    coe_basisAt_reindex_eq_chartLocalFrame σ x hx,
    mextDeriv_apply_vectorField_of_mlieBracket_eq_zero hφ hV hVV]
  congr 1
  -- The signs `(-1)^i` cancel, leaving `c ∑ᵢ ∂ᵢ (ρ Xⁱ) = c ρ div X`.
  trans c * ∑ i, mvfderiv I (fun y ↦ chartVolumeDensity (I := I) x y *
      e.localFrameCoeff I (Module.finBasis ℝ E) (σ.symm i) y (X y)) x
        (chartLocalFrame (I := I) x (σ.symm i) x)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mvfderiv_interior_riemannianVolumeForm_removeNth o σ hc hX, zsmul_eq_mul]
    push_cast
    rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;> rw [h] <;> ring
  rw [Equiv.sum_comp σ.symm (fun k ↦ mvfderiv I (fun y ↦ chartVolumeDensity (I := I) x y *
      e.localFrameCoeff I (Module.finBasis ℝ E) k y (X y)) x (chartLocalFrame (I := I) x k x)),
    ← chartVolumeDensity_mul_divergence x hx hX, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    hc.self_of_nhds]
  ring

/-- **The divergence through the volume form.** For a differentiable vector field `X`, the
exterior derivative of the contraction of `X` into the Riemannian volume form is the divergence of
`X` times the volume form: `d (ι_X dV) = (div X) dV`. -/
theorem mextDeriv_interior_riemannianVolumeForm (o : Manifold.Orientation I M (Fin (m + 1)))
    {X : (x : M) → TangentSpace I x}
    (hX : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) :
    mextDeriv ((riemannianVolumeForm o).interior X) =
      fun x ↦ Manifold.divergence I X x • riemannianVolumeForm o x :=
  funext fun x ↦ mextDeriv_interior_riemannianVolumeForm_apply o (hX x)

end TauCeti
