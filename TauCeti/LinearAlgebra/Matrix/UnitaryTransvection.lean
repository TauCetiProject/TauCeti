/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# Unitary transvections

Let `σ` be a ring endomorphism of a commutative semiring `R` and `Q` a square matrix over `R`, and
write `B(x, y) = σ(x)ᵀ Q y` for the `σ`-sesquilinear form with Gram matrix `Q`, semilinear in its
first argument. A matrix `g` preserves `B` exactly when `σ(g)ᵀ Q g = Q`. For a vector `v` and a
scalar `a`, the **unitary transvection**

```text
τ_{v,a} : x ↦ x + a B(v, x) v,        τ_{v,a} = 1 + a v (σ(v)ᵀ Q)
```

is `Matrix.unitaryTransvection Q σ v a`. When `v` is isotropic, `B(v, v) = 0`, the map
`a ↦ τ_{v,a}` turns addition into multiplication, and over a commutative ring `τ_{v,a}` has
determinant one. When moreover `σ` is an involution, the Gram matrix satisfies `σ(Q)ᵀ = ε Q`, so
that `B` is `ε`-Hermitian, and `a + ε σ(a) = 0`, the transvection preserves `B`. A matrix `g`
preserving `B` conjugates `τ_{v,a}` to `τ_{g v,a}`. That such a `g` preserves the values of `B`,
and that `B` is then `ε`-Hermitian, are `Matrix.comp_mulVec_dotProduct_mulVec_mulVec` and
`Matrix.apply_comp_dotProduct_mulVec` in `TauCeti/LinearAlgebra/Matrix/SesquilinearForm.lean`.

For `σ` the involution `x ↦ x ^ q` of the field with `q²` elements and `B` Hermitian, these are
the transvections of the finite special unitary group `SU_n(q)`. The transvections along a fixed
isotropic vector form an abelian subgroup, and the conjugation law permutes these subgroups like
the isotropic vectors, which is the shape of an Iwasawa structure for the action of the unitary
group on the isotropic points of projective space.

## Main definitions

* `Matrix.unitaryTransvection`: the matrix `1 + a v (σ(v)ᵀ Q)`.

## Main results

* `Matrix.unitaryTransvection_mulVec`: the action `x ↦ x + a B(v, x) v`; as a linear map
  `τ_{v,a}` is Mathlib's `LinearMap.transvection` (`Matrix.toLin'_unitaryTransvection`).
* `Matrix.unitaryTransvection_mul_unitaryTransvection`: `τ_{v,a} τ_{v,b} = τ_{v,a+b}` for
  isotropic `v`.
* `Matrix.det_unitaryTransvection`: an isotropic transvection has determinant one.
* `Matrix.unitaryTransvection_smul`: rescaling the vector, `τ_{c v,a} = τ_{v, a c σ(c)}`.
* `Matrix.mul_unitaryTransvection`: the conjugation law `g τ_{v,a} = τ_{g v,a} g` for `g`
  preserving `B`.
* `Matrix.transpose_map_unitaryTransvection_mul_mul_self`: an isotropic transvection with
  `a + ε σ(a) = 0` preserves the `ε`-Hermitian form `B`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), the chapter on unitary groups.
* L. C. Grove, *Classical Groups and Geometric Algebra*, Graduate Studies in Mathematics 39
  (2002), the chapters on unitary groups.
-/

public section

namespace Matrix

variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]

/-- **The unitary transvection** `τ_{v,a} = 1 + a v (σ(v)ᵀ Q)` along the vector `v`, for the
`σ`-sesquilinear form `B(x, y) = σ(x)ᵀ Q y`. It acts by `x ↦ x + a B(v, x) v`
(`Matrix.unitaryTransvection_mulVec`). -/
def unitaryTransvection (Q : Matrix n n R) (σ : R →+* R) (v : n → R) (a : R) : Matrix n n R :=
  1 + a • vecMulVec v ((σ ∘ v) ᵥ* Q)

variable {Q : Matrix n n R} {σ : R →+* R} {v : n → R}

theorem unitaryTransvection_def (Q : Matrix n n R) (σ : R →+* R) (v : n → R) (a : R) :
    Q.unitaryTransvection σ v a = 1 + a • vecMulVec v ((σ ∘ v) ᵥ* Q) :=
  (rfl)

@[simp]
theorem unitaryTransvection_zero : Q.unitaryTransvection σ v 0 = 1 := by
  rw [unitaryTransvection_def, zero_smul, add_zero]

/-- The unitary transvection `τ_{v,a}` sends `x` to `x + a B(v, x) v`. -/
theorem unitaryTransvection_mulVec (a : R) (x : n → R) :
    Q.unitaryTransvection σ v a *ᵥ x = x + (a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  rw [unitaryTransvection_def, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, ← dotProduct_mulVec, smul_smul]

/-- As a linear map, the unitary transvection `τ_{v,a}` is Mathlib's transvection
`x ↦ x + f x • v` for the linear form `f = a B(v, ·)`. -/
theorem toLin'_unitaryTransvection (a : R) :
    toLin' (Q.unitaryTransvection σ v a) = LinearMap.transvection (a • toBilin' Q (σ ∘ v)) v := by
  refine LinearMap.ext fun x ↦ ?_
  rw [toLin'_apply, unitaryTransvection_mulVec, LinearMap.transvection.apply,
    LinearMap.smul_apply, toBilin'_apply', smul_eq_mul]

/-- **The parameter of a transvection along an isotropic vector is additive.** If `B(v, v) = 0`,
then `τ_{v,a} τ_{v,b} = τ_{v,a+b}`, so `a ↦ τ_{v,a}` turns addition into multiplication. Over a
commutative ring, where `τ_{v,-a}` inverts `τ_{v,a}`, these transvections form a one-parameter
group. -/
theorem unitaryTransvection_mul_unitaryTransvection (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a b : R) :
    Q.unitaryTransvection σ v a * Q.unitaryTransvection σ v b =
      Q.unitaryTransvection σ v (a + b) := by
  refine toLin'.injective ?_
  rw [toLin'_mul, toLin'_unitaryTransvection, toLin'_unitaryTransvection,
    LinearMap.transvection.comp_of_right_eq (by
      rw [LinearMap.smul_apply, toBilin'_apply', hv, smul_zero]),
    ← add_smul, toLin'_unitaryTransvection]

/-- Rescaling the vector of a unitary transvection rescales its parameter by the norm of the
scalar: `τ_{c v,a} = τ_{v, a c σ(c)}`. -/
theorem unitaryTransvection_smul (c a : R) :
    Q.unitaryTransvection σ (c • v) a = Q.unitaryTransvection σ v (a * c * σ c) := by
  have hσv : σ ∘ (c • v) = σ c • (σ ∘ v) := funext fun i ↦ by simp
  rw [unitaryTransvection_def, unitaryTransvection_def, hσv, smul_vecMul, smul_vecMulVec,
    vecMulVec_smul, smul_smul, smul_smul, mul_assoc]

/-- **The conjugation law.** A matrix `g` preserving the form, `σ(g)ᵀ Q g = Q`, carries the
transvection `τ_{v,a}` to `τ_{g v,a}`: `g τ_{v,a} = τ_{g v,a} g`. -/
theorem mul_unitaryTransvection {g : Matrix n n R} (hg : (g.map σ)ᵀ * Q * g = Q) (a : R) :
    g * Q.unitaryTransvection σ v a = Q.unitaryTransvection σ (g *ᵥ v) a * g := by
  have hw : (σ ∘ (g *ᵥ v)) ᵥ* Q ᵥ* g = (σ ∘ v) ᵥ* Q := by
    rw [(funext (σ.map_mulVec g v) : σ ∘ (g *ᵥ v) = _), ← vecMul_transpose, vecMul_vecMul,
      vecMul_vecMul, ← Matrix.mul_assoc, hg]
  rw [unitaryTransvection_def, unitaryTransvection_def, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, mul_smul_comm, smul_mul_assoc, mul_vecMulVec, vecMulVec_mul,
    hw]

/-- **Unitary transvections are isometries.** Let `σ` be an involution, let the Gram matrix
satisfy `σ(Q)ᵀ = ε Q`, so that `σ(B(x, y)) = ε B(y, x)`, and let `v` be isotropic. If
`a + ε σ(a) = 0`, then `τ_{v,a}` preserves the form: `σ(τ_{v,a})ᵀ Q τ_{v,a} = Q`. -/
theorem transpose_map_unitaryTransvection_mul_mul_self (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : R} (ha : a + ε * σ a = 0) :
    ((Q.unitaryTransvection σ v a).map σ)ᵀ * Q * Q.unitaryTransvection σ v a = Q := by
  set w := (σ ∘ v) ᵥ* Q with hw
  -- The transposed conjugate of the rank-one part `v wᵀ` is `ε (Q v) σ(v)ᵀ`.
  have hmap : ((vecMulVec v w).map σ)ᵀ = ε • vecMulVec (Q *ᵥ v) (σ ∘ v) := by
    have hσw : σ ∘ w = v ᵥ* Q.map σ := funext fun i ↦ by
      rw [Function.comp_apply, hw, RingHom.map_vecMul, ← Function.comp_assoc, hσ.comp_self,
        Function.id_comp]
    have hmap' : (vecMulVec v w).map σ = vecMulVec (σ ∘ v) (σ ∘ w) := by
      ext i j
      simp [vecMulVec_apply]
    rw [hmap', transpose_vecMulVec, hσw, ← mulVec_transpose, hQ, smul_mulVec, smul_vecMulVec]
  have hτ : (Q.unitaryTransvection σ v a).map σ = 1 + σ a • (vecMulVec v w).map σ := by
    ext i j
    by_cases hij : i = j <;> simp [unitaryTransvection_def, hw, hij]
  have h₁ : vecMulVec (Q *ᵥ v) (σ ∘ v) * Q = vecMulVec (Q *ᵥ v) w := vecMulVec_mul _ _ _
  have h₂ : Q * vecMulVec v w = vecMulVec (Q *ᵥ v) w := mul_vecMulVec _ _ _
  have h₃ : vecMulVec (Q *ᵥ v) w * vecMulVec v w = 0 := by
    rw [vecMulVec_mul_vecMulVec, hw, ← dotProduct_mulVec, hv, zero_smul, vecMulVec_zero]
  rw [hτ, transpose_add, transpose_one, transpose_smul, hmap, unitaryTransvection_def, ← hw]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
    mul_smul_comm, h₁, h₂, h₃, smul_zero, add_zero, smul_smul]
  rw [add_assoc, ← add_smul, mul_comm (σ a), add_comm (ε * σ a), ha, zero_smul, add_zero]

section CommRing

variable {R : Type*} [CommRing R] {Q : Matrix n n R} {σ : R →+* R} {v : n → R}

/-- **An isotropic transvection has determinant one.** -/
theorem det_unitaryTransvection (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a : R) :
    (Q.unitaryTransvection σ v a).det = 1 := by
  rw [unitaryTransvection_def, ← sub_neg_eq_add, ← neg_smul, ← smul_vecMulVec,
    TauCeti.det_one_sub_vecMulVec, dotProduct_smul, ← dotProduct_mulVec, hv, smul_zero,
    sub_zero]

end CommRing

end Matrix

end
