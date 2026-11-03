/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Unitary transvection matrices

Let `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` be the `σ`-sesquilinear form of a Gram matrix `Q` over a
commutative ring, for a ring endomorphism `σ`. For a vector `v` and a scalar `a` the *unitary
transvection*

```text
τ_{v,a} : x ↦ x + a h(v, x) v,         matrix  1 + a v (vᵀ ^ σ Q),
```

is `Matrix.unitaryTransvection Q σ v a`. When `v` is isotropic, `h(v, v) = 0`, it has determinant
one and `τ_{v,a} τ_{v,b} = τ_{v,a+b}`. If moreover `σ` is an involution and `Q` is
`ε`-Hermitian, `(Q ^ σ)ᵀ = ε • Q`, then

```text
(τ_{v,a} ^ σ)ᵀ Q τ_{v,a} = Q + (a + ε σ(a)) (Q v) (vᵀ ^ σ Q),
```

so `τ_{v,a}` preserves the form when `a + ε σ(a) = 0`. A form-preserving matrix `M` conjugates
`τ_{v,a}` to `τ_{M v,a}`, and rescaling `v` by `c` rescales the parameter by `c σ(c)`.

This file only concerns the matrices themselves. Their membership in the special isometry group
`Matrix.specialIsometryGroup Q σ` and the transvection groups of isotropic points are in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Transvection`.

For `σ = id` and the standard alternating Gram matrix `TauCeti.JFin`, `τ_{v,a}` is the symplectic
transvection `TauCeti.GLSymplecticFin.symplecticTransvection`
(`TauCeti.GLSymplecticFin.coe_symplecticTransvection_eq_unitaryTransvection`). That construction in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transvection` served as the model for
this file; the basic laws of symplectic transvections are derived from the general ones proved
here.

## Main definitions

* `Matrix.unitaryTransvection Q σ v a`: the matrix `1 + a v (vᵀ ^ σ Q)` of `τ_{v,a}`.

## Main results

* `Matrix.unitaryTransvection_mulVec`: `τ_{v,a} x = x + a h(v, x) v`, and
  `Matrix.toLin'_unitaryTransvection`: as a linear map it is Mathlib's `LinearMap.transvection`.
* `Matrix.det_unitaryTransvection`, `Matrix.unitaryTransvection_mul_unitaryTransvection`: an
  isotropic vector gives transvections of determinant one, additive in the parameter.
* `Matrix.transpose_map_unitaryTransvection_mul_mul`: the defect of `τ_{v,a}` from being an
  isometry of an `ε`-Hermitian form.
* `Matrix.mul_unitaryTransvection_mul_of_mul_eq_one`: a form-preserving `M` conjugates `τ_{v,a}`
  to `τ_{M v,a}`.
* `Matrix.exists_eq_unitaryTransvection_smul_iff`: over a field, the transvections along a nonzero
  multiple of `v` are those along `v`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing K] (Q : Matrix n n K) (σ : K →+* K)

/-- **The unitary transvection** `τ_{v,a} : x ↦ x + a h(v, x) v` along `v`, for the sesquilinear
form `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)`. Its matrix is `1 + a v (vᵀ ^ σ Q)`. It has determinant one
when `v` is isotropic (`Matrix.det_unitaryTransvection`). For an involution `σ` and an
`ε`-Hermitian `Q` it is then an isometry when `a + ε σ(a) = 0`
(`Matrix.exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection`), and, if moreover `K` is a
field, `Q` is nondegenerate and `v ≠ 0`, only then (`Matrix.exists_coe_eq_unitaryTransvection_iff`).
-/
def unitaryTransvection (v : n → K) (a : K) : Matrix n n K :=
  1 + a • vecMulVec v ((σ ∘ v) ᵥ* Q)

variable {Q σ}

/-- The matrix of the unitary transvection `τ_{v,a}` is `1 + a v (vᵀ ^ σ Q)`. -/
theorem unitaryTransvection_def (v : n → K) (a : K) :
    Q.unitaryTransvection σ v a = 1 + a • vecMulVec v ((σ ∘ v) ᵥ* Q) :=
  (rfl)

/-- The unitary transvection `τ_{v,a}` sends `x` to `x + a h(v, x) v`. -/
theorem unitaryTransvection_mulVec (v : n → K) (a : K) (x : n → K) :
    Q.unitaryTransvection σ v a *ᵥ x = x + (a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  rw [unitaryTransvection, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, ← dotProduct_mulVec, smul_smul]

/-- As a linear map, the unitary transvection `τ_{v,a}` is Mathlib's transvection
`x ↦ x + f x • v` for the linear form `f = a h(v, ·)`. -/
theorem toLin'_unitaryTransvection (v : n → K) (a : K) :
    toLin' (Q.unitaryTransvection σ v a) =
      LinearMap.transvection (dotProductEquiv K n (a • ((σ ∘ v) ᵥ* Q))) v := by
  refine LinearMap.ext fun x ↦ ?_
  rw [toLin'_apply, unitaryTransvection_mulVec, LinearMap.transvection.apply,
    dotProductEquiv_apply_apply, smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul]

/-- The unitary transvection with parameter `0` is the identity. -/
@[simp]
theorem unitaryTransvection_zero_right (v : n → K) : Q.unitaryTransvection σ v 0 = 1 := by
  simp [unitaryTransvection]

/-- The unitary transvection along the zero vector is the identity. -/
@[simp]
theorem unitaryTransvection_zero_left (a : K) : Q.unitaryTransvection σ 0 a = 1 := by
  simp [unitaryTransvection]

/-- Rescaling the vector by `c` rescales the parameter by `c σ(c)`: `τ_{c v,a} = τ_{v,a c σ(c)}`. -/
theorem unitaryTransvection_smul (c : K) (v : n → K) (a : K) :
    Q.unitaryTransvection σ (c • v) a = Q.unitaryTransvection σ v (a * c * σ c) := by
  rw [unitaryTransvection, unitaryTransvection, RingHom.comp_smul, smul_vecMul, vecMulVec_smul,
    smul_vecMulVec, smul_smul, smul_smul, mul_right_comm a (σ c) c]

/-- **Unitary transvections along an isotropic vector are additive in the parameter**:
`τ_{v,a} τ_{v,b} = τ_{v,a+b}`. -/
theorem unitaryTransvection_mul_unitaryTransvection {v : n → K}
    (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a b : K) :
    Q.unitaryTransvection σ v a * Q.unitaryTransvection σ v b =
      Q.unitaryTransvection σ v (a + b) := by
  -- The rank-one part `v (vᵀ ^ σ Q)` squares to zero, as its row pairs to zero with `v`.
  have hv' : (σ ∘ v) ᵥ* Q ⬝ᵥ v = 0 := (dotProduct_mulVec _ _ _).symm.trans hv
  simp only [unitaryTransvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec_eq_zero hv', smul_zero, add_zero, add_smul]
  abel

/-- **A transvection along an isotropic vector has determinant one.** -/
@[simp]
theorem det_unitaryTransvection {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a : K) :
    (Q.unitaryTransvection σ v a).det = 1 := by
  rw [unitaryTransvection, ← smul_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← dotProduct_mulVec, hv,
    smul_zero, add_zero]

/-- **A form-preserving matrix conjugates `τ_{v,a}` to `τ_{M v,a}`**: if `(M ^ σ)ᵀ Q M = Q` and
`M M' = 1`, then `M τ_{v,a} M' = τ_{M v,a}`. -/
theorem mul_unitaryTransvection_mul_of_mul_eq_one {M M' : Matrix n n K} (hMM' : M * M' = 1)
    (hM : (M.map σ)ᵀ * Q * M = Q) (v : n → K) (a : K) :
    M * Q.unitaryTransvection σ v a * M' = Q.unitaryTransvection σ (M *ᵥ v) a := by
  -- The isometry equation `(M ^ σ)ᵀ Q M = Q` gives `(M ^ σ)ᵀ Q = Q M'`.
  have hQM : (M.map σ)ᵀ * Q = Q * M' := by
    calc (M.map σ)ᵀ * Q = (M.map σ)ᵀ * Q * (M * M') := by rw [hMM', Matrix.mul_one]
      _ = (M.map σ)ᵀ * Q * M * M' := by simp only [Matrix.mul_assoc]
      _ = Q * M' := by rw [hM]
  have hrow : (σ ∘ (M *ᵥ v)) ᵥ* Q = ((σ ∘ v) ᵥ* Q) ᵥ* M' := by
    rw [comp_mulVec_eq_vecMul_transpose_map, vecMul_vecMul, hQM, vecMul_vecMul]
  rw [unitaryTransvection, unitaryTransvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    hMM', Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, hrow]

/-- **The isometry defect of a unitary transvection.** If `σ` is an involution, `Q` is
`ε`-Hermitian and `v` is isotropic, then
`(τ_{v,a} ^ σ)ᵀ Q τ_{v,a} = Q + (a + ε σ(a)) (Q v) (vᵀ ^ σ Q)`. In particular `τ_{v,a}` preserves
the form when `a + ε σ(a) = 0`. -/
theorem transpose_map_unitaryTransvection_mul_mul (hσ : Function.Involutive σ) {ε : K}
    (hQ : (Q.map σ)ᵀ = ε • Q) {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a : K) :
    ((Q.unitaryTransvection σ v a).map σ)ᵀ * Q * Q.unitaryTransvection σ v a =
      Q + (a + ε * σ a) • vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) := by
  -- Applying `σ` to the row `vᵀ ^ σ Q` gives `vᵀ (Q ^ σ) = ε (Q v)ᵀ`, as `σ` is an involution.
  have hw : σ ∘ ((σ ∘ v) ᵥ* Q) = ε • (Q *ᵥ v) := by
    ext i
    have hσv : σ ∘ (σ ∘ v) = v := funext fun j ↦ hσ (v j)
    rw [Function.comp_apply, RingHom.map_vecMul, hσv, ← mulVec_transpose, hQ, smul_mulVec]
  have hT : ((Q.unitaryTransvection σ v a).map σ)ᵀ =
      1 + (σ a * ε) • vecMulVec (Q *ᵥ v) (σ ∘ v) := by
    have hmap : (Q.unitaryTransvection σ v a).map σ =
        1 + σ a • vecMulVec (σ ∘ v) (σ ∘ ((σ ∘ v) ᵥ* Q)) := by
      ext i j
      simp [unitaryTransvection, Matrix.one_apply, vecMulVec_apply, apply_ite σ]
    rw [hmap, hw, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec,
      smul_vecMulVec, smul_smul]
  have h₁ : vecMulVec (Q *ᵥ v) (σ ∘ v) * Q = vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) :=
    vecMulVec_mul _ _ _
  have h₂ : Q * vecMulVec v ((σ ∘ v) ᵥ* Q) = vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) :=
    mul_vecMulVec _ _ _
  have hv' : (σ ∘ v) ᵥ* Q ⬝ᵥ v = 0 := (dotProduct_mulVec _ _ _).symm.trans hv
  rw [hT, unitaryTransvection]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h₁, h₂, vecMulVec_mul_vecMulVec_eq_zero hv', smul_zero, add_zero]
  module

end CommRing

section Field

variable [Field K] {Q : Matrix n n K} {σ : K →+* K}

/-- Along a nonzero multiple `c v` of `v`, the unitary transvections are those along `v`. -/
theorem exists_eq_unitaryTransvection_smul_iff {c : K} (hc : c ≠ 0) (v : n → K)
    (M : Matrix n n K) :
    (∃ a, M = Q.unitaryTransvection σ (c • v) a) ↔ ∃ a, M = Q.unitaryTransvection σ v a := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  simp_rw [unitaryTransvection_smul]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨_, ha⟩, fun ⟨a, ha⟩ ↦ ⟨a / (c * σ c), ?_⟩⟩
  rw [ha]
  congr 1
  field_simp

end Field

end Matrix
