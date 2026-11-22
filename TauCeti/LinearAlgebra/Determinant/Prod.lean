/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of endomorphisms of `R × R` and of `K × V`

An endomorphism `A` of `R × R` is determined by the images `A (1, 0)` and `A (0, 1)` of the
standard basis vectors, and its determinant is the `2 × 2` determinant of these two columns. This
is `Matrix.det_fin_two` read through the basis `Module.Basis.finTwoProd R`. It is the Jacobian
determinant in the change of variables formula for maps of the plane `ℝ × ℝ`.

Consequently `A` multiplies the wedge product of two linear forms `κ` and `α` on `R × R` by its
determinant: `κ (A e₁) α (A e₂) - κ (A e₂) α (A e₁) = det A (κ e₁ α e₂ - κ e₂ α e₁)`. This is the
transformation rule of a two-form on the plane under pullback. Likewise every alternating form `ω`
of degree two on `R × R` is its value on the standard basis times the `2 × 2` determinant:
`ω (v, w) = (v₁ w₂ - v₂ w₁) ω ((1, 0), (0, 1))`.

Over a field `K`, an endomorphism `B` of `K × V` that fixes the second component of every vector is
block triangular, with diagonal blocks the scalar `(B (1, 0)).1` on the axis `K × 0` and the
identity on the quotient `V`, so its determinant is `(B (1, 0)).1`.

## Main results

* `LinearMap.det_finTwoProd`: the determinant of an endomorphism of `R × R`.
* `LinearMap.det_mul_wedge_finTwoProd`: an endomorphism of `R × R` multiplies the wedge product
  of two linear forms by its determinant.
* `LinearMap.det_eq_fst_of_snd_eq`: the determinant of an endomorphism of `K × V` fixing the
  second component.
* `AlternatingMap.apply_eq_mul_apply_finTwoProd`: an alternating form of degree two on `R × R` is
  its value on the standard basis times the determinant.
-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R]

/-- The determinant of an endomorphism of `R × R` in terms of the images `A (1, 0)` and
`A (0, 1)` of the standard basis vectors. -/
theorem det_finTwoProd (A : (R × R) →ₗ[R] R × R) :
    LinearMap.det A = (A (1, 0)).1 * (A (0, 1)).2 - (A (1, 0)).2 * (A (0, 1)).1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd R), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one]
  ring

/-- An endomorphism `A` of `R × R` multiplies the wedge product `κ ∧ α` of two linear forms on
`R × R`, evaluated on the standard basis vectors `(1, 0)` and `(0, 1)`, by its determinant. -/
theorem det_mul_wedge_finTwoProd (A : (R × R) →ₗ[R] R × R) (κ α : (R × R) →ₗ[R] R) :
    LinearMap.det A * (κ (1, 0) * α (0, 1) - κ (0, 1) * α (1, 0)) =
      κ (A (1, 0)) * α (A (0, 1)) - κ (A (0, 1)) * α (A (1, 0)) := by
  have h (φ : (R × R) →ₗ[R] R) (e : R × R) : φ e = e.1 * φ (1, 0) + e.2 * φ (0, 1) := by
    have he : e = e.1 • ((1, 0) : R × R) + e.2 • ((0, 1) : R × R) := by ext <;> simp
    conv_lhs => rw [he]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [det_finTwoProd, h κ (A (1, 0)), h κ (A (0, 1)), h α (A (1, 0)), h α (A (0, 1))]
  ring

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An endomorphism `B` of `K × V` that fixes the second component of every vector has determinant
`(B (1, 0)).1`: it is block triangular, with diagonal blocks multiplication by `(B (1, 0)).1` on the
axis `K × 0` and the identity on the quotient. -/
theorem det_eq_fst_of_snd_eq (B : K × V →ₗ[K] K × V) (hB : ∀ v, (B v).2 = v.2) :
    LinearMap.det B = (B (1, 0)).1 := by
  set W := LinearMap.ker (LinearMap.snd K K V)
  have hW : W ≤ W.comap B := fun v hv ↦ by
    simp only [W, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.snd_apply, hB] at hv ⊢
    exact hv
  -- On the axis `W = K × 0`, `B` is multiplication by `(B (1, 0)).1`.
  have hR : B.restrict (p := W) (q := W) hW = (B (1, 0)).1 • LinearMap.id := by
    refine LinearMap.ext fun ⟨w, hw⟩ ↦ Subtype.ext ?_
    have hw2 : w.2 = 0 := by simpa only [W, LinearMap.mem_ker, LinearMap.snd_apply] using hw
    have hw' : w = w.1 • ((1 : K), (0 : V)) := Prod.ext (by simp) (by simp [hw2])
    have hB1 : B (1, 0) = ((B (1, 0)).1, 0) := Prod.ext rfl (hB _)
    rw [LinearMap.coe_restrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
      Submodule.coe_mk]
    conv_lhs => rw [hw']
    rw [map_smul, hB1]
    exact Prod.ext (by simp [mul_comm]) (by simp [hw2])
  -- On the quotient by `W`, `B` is the identity.
  have hQ : W.mapQ W B hW = LinearMap.id := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply, Submodule.Quotient.eq]
    simp [W, hB]
  have hWr : Module.finrank K W = 1 := by
    rw [show W = LinearMap.range (LinearMap.inl K K V) from (LinearMap.range_inl K K V).symm,
      LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_self]
  rw [LinearMap.det_eq_det_mul_det (W := W) B hW, hR, hQ, LinearMap.det_id, mul_one,
    LinearMap.det_smul, LinearMap.det_id, mul_one, hWr, pow_one]

end Field

end LinearMap

namespace AlternatingMap

variable {R : Type*} [CommRing R]

/-- An alternating form `ω` of degree two on `R × R` is its value on the standard basis
`((1, 0), (0, 1))` times the `2 × 2` determinant:
`ω (v, w) = (v₁ w₂ - v₂ w₁) ω ((1, 0), (0, 1))`. -/
theorem apply_eq_mul_apply_finTwoProd (ω : (R × R) [⋀^Fin 2]→ₗ[R] R) (v w : R × R) :
    ω ![v, w] = (v.1 * w.2 - v.2 * w.1) * ω ![(1, 0), (0, 1)] := by
  have h := congrArg (· ![v, w]) (ω.eq_smul_basis_det (Module.Basis.finTwoProd R))
  have hb : ⇑(Module.Basis.finTwoProd R) = ![((1 : R), (0 : R)), (0, 1)] := by
    ext i : 1
    fin_cases i <;> simp
  simp only [_root_.smul_apply, Module.Basis.det_apply, Matrix.det_fin_two,
    Module.Basis.toMatrix_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Module.Basis.coe_finTwoProd_repr, hb] at h
  rw [h]
  ring

end AlternatingMap
