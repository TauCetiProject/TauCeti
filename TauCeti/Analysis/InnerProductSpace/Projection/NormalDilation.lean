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

On `ℝ × E`, with the Euclidean norm of `WithLp 2 (ℝ × E)`, a subspace `V` of `E` gives two
subspaces: `V.map (WithLp.inrL2 ℝ ℝ E).toLinearMap`, the vectors `(0, v)` with `v ∈ V`, for which
the extra coordinate is a tangent direction, and `V.comap (WithLp.sndₗ 2 ℝ ℝ E)`, the vectors
`(s, v)` with `v ∈ V`, for which it is a normal direction. The normal dilations along them act on
the second factor as the normal dilation along `V`, and on the first factor as the identity and as
the multiplication by `t` respectively (`Submodule.normalDilation_map_inrL2_toLp`,
`Submodule.normalDilation_comap_sndₗ_toLp`).

## Main definitions

* `Submodule.normalDilation V t`: the linear map `P_{Vᗮ} + t P_V`.
* `Submodule.normalDilationEquiv V ht`: the normal dilation by `t ≠ 0` as an automorphism, with
  inverse the normal dilation by `t⁻¹` (`Submodule.normalDilationEquiv_symm`).

## Main results

* `Submodule.normalDilation_add_of_mem_orthogonal`: the normal dilation sends `p + q`, with
  `p ∈ Vᗮ` and `q ∈ V`, to `p + t q`.
* `Submodule.normalDilation_mul`: normal dilations compose by multiplying their factors.
* `Submodule.det_normalDilation`: `det (normalDilation V t) = t ^ dim V`.
* `Submodule.normalDilation_map_inrL2_toLp`, `Submodule.normalDilation_comap_sndₗ_toLp`: the
  normal dilations of `ℝ × E` along `V` with the first coordinate tangent or normal.
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

/-- The normal dilation by `t` sends `p + q`, with `p ∈ Vᗮ` and `q ∈ V`, to `p + t q`. -/
theorem normalDilation_add_of_mem_orthogonal {p q : E} (hp : p ∈ Vᗮ) (hq : q ∈ V) (t : ℝ) :
    V.normalDilation t (p + q) = p + t • q := by
  rw [map_add, ← (Vᗮ.starProjection_eq_self_iff).2 hp, ← (V.starProjection_eq_self_iff).2 hq,
    normalDilation_starProjection_orthogonal, normalDilation_starProjection]

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
    ← ContinuousLinearMap.comp_apply, ← normalDilation_mul, mul_inv_cancel₀ ht, normalDilation_one,
    ContinuousLinearMap.id_apply]

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

/-! ### Normal dilations of `ℝ × E` -/

/-- **A tangent coordinate.** Along the subspace of vectors `(0, v)`, `v ∈ V`, of `ℝ × E`, the
normal dilation by `t` fixes the first coordinate and acts on the second as the normal dilation
along `V`: `(s, y) ↦ (s, normalDilation V t y)`. -/
theorem normalDilation_map_inrL2_toLp
    [(V.map (WithLp.inrL2 ℝ ℝ E).toLinearMap).HasOrthogonalProjection] (t s : ℝ) (y : E) :
    (V.map (WithLp.inrL2 ℝ ℝ E).toLinearMap).normalDilation t (WithLp.toLp 2 (s, y)) =
      WithLp.toLp 2 (s, V.normalDilation t y) := by
  have hdec : WithLp.toLp 2 (s, y) =
      WithLp.toLp 2 (s, Vᗮ.starProjection y) + WithLp.toLp 2 (0, V.starProjection y) := by
    apply WithLp.ofLp_injective 2
    ext <;> simp [add_comm]
  have hp :
      WithLp.toLp 2 (s, Vᗮ.starProjection y) ∈ (V.map (WithLp.inrL2 ℝ ℝ E).toLinearMap)ᗮ := by
    rw [mem_orthogonal]
    rintro _ ⟨q, hq, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, WithLp.inrL2_apply, WithLp.prod_inner_apply,
      inner_zero_left, zero_add]
    exact inner_right_of_mem_orthogonal hq (Vᗮ.starProjection_apply_mem y)
  have hq : WithLp.toLp 2 (0, V.starProjection y) ∈ V.map (WithLp.inrL2 ℝ ℝ E).toLinearMap :=
    ⟨_, V.starProjection_apply_mem y, (WithLp.inrL2_apply ℝ ℝ E _)⟩
  rw [hdec, normalDilation_add_of_mem_orthogonal _ hp hq]
  apply WithLp.ofLp_injective 2
  ext <;> simp [normalDilation_apply]

/-- **A normal coordinate.** Along the subspace of vectors `(s, v)`, `v ∈ V`, of `ℝ × E`, the
normal dilation by `t` multiplies the first coordinate by `t` and acts on the second as the
normal dilation along `V`: `(s, y) ↦ (t s, normalDilation V t y)`. -/
theorem normalDilation_comap_sndₗ_toLp [(V.comap (WithLp.sndₗ 2 ℝ ℝ E)).HasOrthogonalProjection]
    (t s : ℝ) (y : E) :
    (V.comap (WithLp.sndₗ 2 ℝ ℝ E)).normalDilation t (WithLp.toLp 2 (s, y)) =
      WithLp.toLp 2 (t * s, V.normalDilation t y) := by
  have hdec : WithLp.toLp 2 (s, y) =
      WithLp.toLp 2 (0, Vᗮ.starProjection y) + WithLp.toLp 2 (s, V.starProjection y) := by
    apply WithLp.ofLp_injective 2
    ext <;> simp [add_comm]
  have hp : WithLp.toLp 2 (0, Vᗮ.starProjection y) ∈ (V.comap (WithLp.sndₗ 2 ℝ ℝ E))ᗮ := by
    rw [mem_orthogonal]
    intro w hw
    rw [mem_comap, WithLp.sndₗ_apply] at hw
    simp only [WithLp.prod_inner_apply, inner_zero_right, zero_add]
    exact inner_right_of_mem_orthogonal hw (Vᗮ.starProjection_apply_mem y)
  have hq : WithLp.toLp 2 (s, V.starProjection y) ∈ V.comap (WithLp.sndₗ 2 ℝ ℝ E) :=
    mem_comap.2 (by simp [V.starProjection_apply_mem y])
  rw [hdec, normalDilation_add_of_mem_orthogonal _ hp hq]
  apply WithLp.ofLp_injective 2
  ext <;> simp [normalDilation_apply]

end Submodule
