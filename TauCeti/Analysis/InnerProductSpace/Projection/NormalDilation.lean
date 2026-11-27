/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Analysis.InnerProductSpace.ProdL2

/-!
# The normal dilation along a subspace

Let `E` be a real inner product space and `V` a subspace of `E` with an orthogonal projection.
The normal dilation `Submodule.normalDilation V t = P_{Vᗮ} + t P_V` fixes the orthogonal
complement `Vᗮ` and multiplies `V` by `t`. Near a submanifold, after choosing a tube, `V` plays the
role of the normal directions, and composing a field with the normal dilation reads it in the
normal coordinate rescaled by `t`.

## Main definitions

* `Submodule.normalDilation V t`: the linear map `P_{Vᗮ} + t P_V`.
* `Submodule.normalDilationEquiv V ht`: the normal dilation by `t ≠ 0` as an automorphism, with
  inverse the normal dilation by `t⁻¹` (`Submodule.normalDilationEquiv_symm`).

## Main results

* `Submodule.normalDilation_mul`: normal dilations compose by multiplying their factors.
* `Submodule.det_normalDilation`: `det (normalDilation V t) = t ^ dim V`.
* `Submodule.normalDilation_comap_prod`: along a product subspace `p × q` of
  `WithLp 2 (E₁ × E₂)`, the normal dilation dilates each component along its factor.
-/

public section

noncomputable section

open Module

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : Submodule ℝ E)
  [V.HasOrthogonalProjection]

/-- The **normal dilation** by `t` along the subspace `V`: the linear map `P_{Vᗮ} + t P_V`, which
fixes the orthogonal complement `Vᗮ` and multiplies `V` by `t`. Composing a field with it reads
the field in the normal coordinate rescaled by `t`. -/
def normalDilation (t : ℝ) : E →L[ℝ] E :=
  Vᗮ.starProjection + t • V.starProjection

@[simp]
theorem normalDilation_apply (t : ℝ) (x : E) :
    V.normalDilation t x = Vᗮ.starProjection x + t • V.starProjection x :=
  (rfl)

/-- The normal dilation fixes the horizontal part of every vector. -/
theorem normalDilation_starProjection_orthogonal (t : ℝ) (x : E) :
    V.normalDilation t (Vᗮ.starProjection x) = Vᗮ.starProjection x := by
  rw [normalDilation_apply, starProjection_eq_self_iff.2 (Vᗮ.starProjection_apply_mem x),
    (V.starProjection_apply_eq_zero_iff).2 (Vᗮ.starProjection_apply_mem x), smul_zero, add_zero]

/-- The normal dilation by `t` multiplies the normal part of every vector by `t`. -/
theorem normalDilation_starProjection (t : ℝ) (x : E) :
    V.normalDilation t (V.starProjection x) = t • V.starProjection x := by
  rw [normalDilation_apply, starProjection_eq_self_iff.2 (V.starProjection_apply_mem x),
    (Vᗮ.starProjection_apply_eq_zero_iff).2
      (le_orthogonal_orthogonal V (V.starProjection_apply_mem x)), zero_add]

@[simp]
theorem normalDilation_one : V.normalDilation 1 = ContinuousLinearMap.id ℝ E := by
  ext x
  rw [ContinuousLinearMap.id_apply, normalDilation_apply, one_smul, add_comm,
    starProjection_add_starProjection_orthogonal]

/-- Normal dilations compose by multiplying their factors. -/
theorem normalDilation_mul (s t : ℝ) :
    V.normalDilation (s * t) = (V.normalDilation s).comp (V.normalDilation t) := by
  ext x
  rw [ContinuousLinearMap.comp_apply, normalDilation_apply V t, map_add, map_smul,
    normalDilation_starProjection_orthogonal, normalDilation_starProjection, smul_smul,
    normalDilation_apply, mul_comm]

/-- The normal dilation by `t ≠ 0` undoes the normal dilation by `t⁻¹`. -/
theorem normalDilation_normalDilation_inv {t : ℝ} (ht : t ≠ 0) (x : E) :
    V.normalDilation t (V.normalDilation t⁻¹ x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← normalDilation_mul, mul_inv_cancel₀ ht,
    normalDilation_one, ContinuousLinearMap.id_apply]

/-- For `t ≠ 0` the normal dilation by `t` is a linear automorphism, with inverse the normal
dilation by `t⁻¹`. -/
def normalDilationEquiv {t : ℝ} (ht : t ≠ 0) : E ≃L[ℝ] E :=
  .ofContinuousLinearMap (V.normalDilation t) (V.normalDilation t⁻¹)
    (by rw [← normalDilation_mul, mul_inv_cancel₀ ht, normalDilation_one])
    (by rw [← normalDilation_mul, inv_mul_cancel₀ ht, normalDilation_one])

@[simp]
theorem coe_normalDilationEquiv {t : ℝ} (ht : t ≠ 0) :
    (V.normalDilationEquiv ht : E →L[ℝ] E) = V.normalDilation t :=
  (rfl)

@[simp]
theorem coeFn_normalDilationEquiv {t : ℝ} (ht : t ≠ 0) :
    ⇑(V.normalDilationEquiv ht) = V.normalDilation t :=
  (rfl)

theorem normalDilationEquiv_apply {t : ℝ} (ht : t ≠ 0) (x : E) :
    V.normalDilationEquiv ht x = V.normalDilation t x :=
  (rfl)

/-- The inverse of the normal dilation by `t ≠ 0` is the normal dilation by `t⁻¹`. -/
@[simp]
theorem normalDilationEquiv_symm {t : ℝ} (ht : t ≠ 0) :
    (V.normalDilationEquiv ht).symm = V.normalDilationEquiv (inv_ne_zero ht) := by
  ext x
  rw [ContinuousLinearEquiv.symm_apply_eq, normalDilationEquiv_apply, normalDilationEquiv_apply,
    normalDilation_normalDilation_inv V ht]

/-- **The determinant of the normal dilation** by `t` is `t ^ dim V`. -/
theorem det_normalDilation [FiniteDimensional ℝ E] (t : ℝ) :
    LinearMap.det (V.normalDilation t : E →ₗ[ℝ] E) = t ^ finrank ℝ V := by
  -- Read through the splitting `E ≃ V × Vᗮ`, the dilation is `t • id ⊕ id`.
  set e := prodEquivOfIsCompl V Vᗮ V.isCompl_orthogonal
  have hconj : (V.normalDilation t : E →ₗ[ℝ] E) =
      (e : V × Vᗮ →ₗ[ℝ] E) ∘ₗ (LinearMap.prodMap (t • LinearMap.id) LinearMap.id) ∘ₗ
        (e.symm : E →ₗ[ℝ] V × Vᗮ) := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨v, w⟩ := y
    have hw : V.starProjection (w : E) = 0 := (V.starProjection_apply_eq_zero_iff).2 w.property
    simp [e, hw, starProjection_eq_self_iff.2 v.property, add_comm]
  rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id,
    LinearMap.det_id, mul_one, mul_one]

section Prod

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] (p : Submodule ℝ E₁) (q : Submodule ℝ E₂) [p.HasOrthogonalProjection]
  [q.HasOrthogonalProjection]

/-- **The normal dilation along a product subspace** dilates each component along its factor:
along `p × q ⊆ WithLp 2 (E₁ × E₂)`, the normal dilation by `t` is
`(x, y) ↦ (normalDilation p t x, normalDilation q t y)`. -/
theorem normalDilation_comap_prod (t : ℝ) (x : WithLp 2 (E₁ × E₂)) :
    ((p.prod q).comap (WithLp.linearEquiv 2 ℝ (E₁ × E₂)).toLinearMap).normalDilation t x =
      WithLp.toLp 2 (p.normalDilation t x.fst, q.normalDilation t x.snd) := by
  simp only [normalDilation_apply, starProjection_orthogonal_val,
    WithLp.starProjection_comap_prod]
  exact WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp))

end Prod

end Submodule
