/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Symplectic.StandardCompatible
import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# The canonical Liouville one-form on `V × V`

For any real inner product space `V`, the doubled space `V × V` with coordinates `(q, p)` carries
the canonical Liouville one-form `TauCeti.innerProductLiouvilleForm` (`⟪p, dq⟫`), whose exterior
derivative is `-TauCeti.stdSymplecticForm` (`TauCeti.mextDeriv_innerProductLiouvilleForm_apply`).

## Main definitions

* `TauCeti.innerProductLiouvilleForm`: the Liouville one-form `⟪p, dq⟫` on `V × V`.

## Main results

* `TauCeti.innerProductLiouvilleForm_apply`: evaluation of `⟪p, dq⟫`.
* `TauCeti.mextDeriv_innerProductLiouvilleForm_apply`: `d⟪p, dq⟫ = -stdSymplecticForm`.
-/

public section

noncomputable section

open scoped Manifold InnerProductSpace

namespace TauCeti

/-- The canonical Liouville one-form `⟪p, dq⟫` on `V × V`, built via
`ContinuousLinearMap.liouvilleFormCLM` from `2 • ((q, p), (u, v)) ↦ ⟪p, u⟫`. Its exterior
derivative is `-TauCeti.stdSymplecticForm`
(`TauCeti.mextDeriv_innerProductLiouvilleForm_apply`). -/
def innerProductLiouvilleForm (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    SmoothForm 𝓘(ℝ, V × V) (V × V) ℝ 1 :=
  ⟨(ContinuousLinearMap.liouvilleFormCLM
      ((2 : ℝ) • ((innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ V V)
        (ContinuousLinearMap.fst ℝ V V))) : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ),
    (isSmoothForm_modelSpace_iff.2
      (ContinuousLinearMap.liouvilleFormCLM _).contDiff).mem_smoothBundleForms⟩

/-- Unfolding lemma for the underlying rough form of `innerProductLiouvilleForm V`. -/
private theorem innerProductLiouvilleForm_toRoughForm (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] :
    (innerProductLiouvilleForm V).val =
      (ContinuousLinearMap.liouvilleFormCLM
        ((2 : ℝ) • ((innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ V V)
          (ContinuousLinearMap.fst ℝ V V))) : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ) :=
  rfl

/-- `innerProductLiouvilleForm V` evaluates a tangent vector `v` at `(q, p)` as `⟪p, v.fst⟫`. -/
@[simp]
theorem innerProductLiouvilleForm_apply {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x : V × V) (v : TangentSpace 𝓘(ℝ, V × V) x) :
    (innerProductLiouvilleForm V).val x ![v] =
      ⟪x.snd, (NormedSpace.fromTangentSpace x v).fst⟫_ℝ := by
  rw [innerProductLiouvilleForm_toRoughForm]
  -- `TangentSpace 𝓘(ℝ, V × V) x` is definitionally `V × V`, and `NormedSpace.fromTangentSpace x`
  -- is the definitional identity on that carrier.
  refine (ContinuousLinearMap.liouvilleFormCLM_apply _ x
    ![NormedSpace.fromTangentSpace x v]).trans ?_
  simp only [smul_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', innerSL_apply_apply,
    Matrix.cons_val_zero, smul_eq_mul]
  ring

/-- The exterior derivative of `innerProductLiouvilleForm V` is `-stdSymplecticForm`. -/
theorem mextDeriv_innerProductLiouvilleForm_apply {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (y : V × V) (u w : TangentSpace 𝓘(ℝ, V × V) y) :
    mextDeriv (innerProductLiouvilleForm V).val y ![u, w] =
      -stdSymplecticForm (NormedSpace.fromTangentSpace y u)
        (NormedSpace.fromTangentSpace y w) := by
  -- On the model space `V × V`, `mextDeriv` coincides with `extDeriv`, `TangentSpace 𝓘(ℝ, V × V) y`
  -- is definitionally `V × V` with `NormedSpace.fromTangentSpace y` as the identity, and the
  -- trivial fibre `Bundle.Trivial (V × V) ℝ y` is definitionally `ℝ`.
  refine (congrArg (fun (A : (V × V) [⋀^Fin 2]→L[ℝ] ℝ) ↦
      A ![NormedSpace.fromTangentSpace y u, NormedSpace.fromTangentSpace y w])
    (mextDeriv_eq_extDeriv (innerProductLiouvilleForm V).val y)).trans ?_
  rw [innerProductLiouvilleForm_toRoughForm, ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply]
  simp only [smul_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', innerSL_apply_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul,
    stdSymplecticForm_apply]
  rw [real_inner_comm (NormedSpace.fromTangentSpace y w).snd]
  ring

end TauCeti
