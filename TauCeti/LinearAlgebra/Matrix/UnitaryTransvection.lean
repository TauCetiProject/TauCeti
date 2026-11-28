/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Star.Pi
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

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
The special isometry group of `B` and these transvection groups, indexed by the isotropic points,
are in `TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup/Isometry/Transvection.lean`.

## Main definitions

* `Matrix.unitaryTransvection`: the matrix `1 + a v (σ(v)ᵀ Q)`.

## Main results

* `Matrix.unitaryTransvection_mulVec`: the action `x ↦ x + a B(v, x) v`; as a linear map
  `τ_{v,a}` is Mathlib's `LinearMap.transvection` (`Matrix.toLin'_unitaryTransvection`).
* `Matrix.unitaryTransvection_mul_unitaryTransvection_eq`: the product formula
  `τ_{v,a} τ_{v,b} = τ_{v, a + b + a b B(v, v)}`, which for isotropic `v` is
  `τ_{v,a} τ_{v,b} = τ_{v,a+b}` (`Matrix.unitaryTransvection_mul_unitaryTransvection`).
* `Matrix.det_unitaryTransvection_eq` and `Matrix.det_unitaryTransvection`: the determinant
  `1 + a B(v, v)`, which is `1` when `v` is isotropic.
* `Matrix.unitaryTransvection_smul`: rescaling the vector, `τ_{c v,a} = τ_{v, a c σ(c)}`.
* `Matrix.mul_unitaryTransvection`: the conjugation law `g τ_{v,a} = τ_{g v,a} g` for `g`
  preserving `B`.
* `Matrix.transpose_map_unitaryTransvection_mul_mul`: the isometry defect
  `σ(τ_{v,a})ᵀ Q τ_{v,a} - Q = (a + ε σ(a) + ε a σ(a) B(v, v)) (Q v) (σ(v)ᵀ Q)` for the
  `ε`-Hermitian form `B`, giving isometries when the coefficient vanishes
  (`Matrix.transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero`,
  `Matrix.transpose_map_unitaryTransvection_mul_mul_self`).
* `Matrix.star_unitaryTransvection_mul_mul_self_of_eq_zero` and
  `Matrix.unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero`: for
  `σ = starRingEnd R` and a Hermitian Gram matrix `A`, `τ_{v,a}` preserves the form and is inverted
  by `τ_{v,star a}` when `a + star a + a star a B(v, v) = 0`.
* `Matrix.unitaryTransvection_mulVec_of_dotProduct_eq_zero` and
  `Matrix.unitaryTransvection_sub_mulVec_eq`: `τ_{v,a}` fixes every `x` with `B(v, x) = 0`, and
  if `a B(x - y, y) = 1`, then `τ_{x - y,a}` sends `y` to `x`.
* `Matrix.exists_eq_unitaryTransvection_smul_iff`: over a field, the transvections along a nonzero
  multiple of `v` are those along `v`.

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

/-- Along the zero vector `v = 0`, every unitary transvection is the identity matrix. -/
@[simp]
theorem unitaryTransvection_zero_left (a : R) : Q.unitaryTransvection σ 0 a = 1 := by
  rw [unitaryTransvection_def, zero_vecMulVec, smul_zero, add_zero]

/-- The unitary transvection `τ_{v,a}` sends `x` to `x + a B(v, x) v`. -/
theorem unitaryTransvection_mulVec (a : R) (x : n → R) :
    Q.unitaryTransvection σ v a *ᵥ x = x + (a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  rw [unitaryTransvection_def, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, ← dotProduct_mulVec, smul_smul]

/-- A transvection fixes vectors orthogonal to its direction for the sesquilinear form. -/
theorem unitaryTransvection_mulVec_of_dotProduct_eq_zero (a : R) {x : n → R}
    (hx : (σ ∘ v) ⬝ᵥ Q *ᵥ x = 0) : Q.unitaryTransvection σ v a *ᵥ x = x := by
  simp [unitaryTransvection_mulVec, hx]

/-- As a linear map, the unitary transvection `τ_{v,a}` is Mathlib's transvection
`x ↦ x + f x • v` for the linear form `f = a B(v, ·)`. -/
theorem toLin'_unitaryTransvection (a : R) :
    toLin' (Q.unitaryTransvection σ v a) = LinearMap.transvection (a • toBilin' Q (σ ∘ v)) v := by
  refine LinearMap.ext fun x ↦ ?_
  rw [toLin'_apply, unitaryTransvection_mulVec, LinearMap.transvection.apply,
    LinearMap.smul_apply, toBilin'_apply', smul_eq_mul]

/-- **The product of two transvections or quasi-reflections along the same vector**:
`τ_{v,a} τ_{v,b} = τ_{v, a + b + a b B(v, v)}`. -/
theorem unitaryTransvection_mul_unitaryTransvection_eq (a b : R) :
    Q.unitaryTransvection σ v a * Q.unitaryTransvection σ v b =
      Q.unitaryTransvection σ v (a + b + a * b * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) := by
  apply toLin'.injective
  have h (r : R) : LinearMap.transvection (r • toBilin' Q (σ ∘ v)) v =
      LinearMap.transvection (toBilin' Q (σ ∘ v)) (r • v) := by
    ext x
    simp [LinearMap.transvection.apply, mul_smul, mul_comm, mul_assoc]
  have hc : a + b + b * toBilin' Q (σ ∘ v) v * a = a + b + a * b * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) := by
    rw [toBilin'_apply']
    ring
  simp only [toLin'_mul, toLin'_unitaryTransvection, h]
  rw [LinearMap.transvection.comp_smul_smul, hc]

/-- **The parameter of a transvection along an isotropic vector is additive.** If `B(v, v) = 0`,
then `τ_{v,a} τ_{v,b} = τ_{v,a+b}`, so `a ↦ τ_{v,a}` turns addition into multiplication. Over a
commutative ring, where `τ_{v,-a}` inverts `τ_{v,a}`, these transvections form a one-parameter
group. -/
theorem unitaryTransvection_mul_unitaryTransvection (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a b : R) :
    Q.unitaryTransvection σ v a * Q.unitaryTransvection σ v b =
      Q.unitaryTransvection σ v (a + b) := by
  rw [unitaryTransvection_mul_unitaryTransvection_eq, hv, mul_zero, add_zero]

/-- Rescaling the vector of a unitary transvection rescales its parameter by the norm of the
scalar: `τ_{c v,a} = τ_{v, a c σ(c)}`. -/
theorem unitaryTransvection_smul (c a : R) :
    Q.unitaryTransvection σ (c • v) a = Q.unitaryTransvection σ v (a * c * σ c) := by
  rw [unitaryTransvection_def, unitaryTransvection_def, TauCeti.map_comp_smul, smul_vecMul,
    smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul, mul_assoc]

/-- **The conjugation law.** A matrix `g` preserving the form, `σ(g)ᵀ Q g = Q`, carries the
transvection `τ_{v,a}` to `τ_{g v,a}`: `g τ_{v,a} = τ_{g v,a} g`. -/
theorem mul_unitaryTransvection {g : Matrix n n R} (hg : (g.map σ)ᵀ * Q * g = Q) (a : R) :
    g * Q.unitaryTransvection σ v a = Q.unitaryTransvection σ (g *ᵥ v) a * g := by
  rw [unitaryTransvection_def, unitaryTransvection_def, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, mul_smul_comm, smul_mul_assoc, mul_vecMulVec, vecMulVec_mul,
    comp_mulVec_vecMul_vecMul hg]

/-- **The isometry defect of a unitary transvection or quasi-reflection.** Let `σ` be an involution
and let the Gram matrix satisfy `σ(Q)ᵀ = ε Q`. Then
`σ(τ_{v,a})ᵀ Q τ_{v,a} = Q + (a + ε σ(a) + ε a σ(a) B(v, v)) (Q v) (σ(v)ᵀ Q)`. -/
theorem transpose_map_unitaryTransvection_mul_mul (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (a : R) :
    ((Q.unitaryTransvection σ v a).map σ)ᵀ * Q * Q.unitaryTransvection σ v a =
      Q + (a + ε * σ a + ε * a * σ a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) •
        vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) := by
  set w := (σ ∘ v) ᵥ* Q with hw
  have hτ : (Q.unitaryTransvection σ v a).map σ = 1 + σ a • (vecMulVec v w).map σ := by
    ext i j; by_cases hij : i = j <;> simp [unitaryTransvection_def, hw, hij]
  have h₁ : vecMulVec (Q *ᵥ v) (σ ∘ v) * Q = vecMulVec (Q *ᵥ v) w := vecMulVec_mul _ _ _
  have h₂ : Q * vecMulVec v w = vecMulVec (Q *ᵥ v) w := mul_vecMulVec _ _ _
  have h₃ : vecMulVec (Q *ᵥ v) w * vecMulVec v w = ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) • vecMulVec (Q *ᵥ v) w :=
    by rw [vecMulVec_mul_vecMulVec, hw, ← dotProduct_mulVec, vecMulVec_smul]
  rw [hτ, transpose_add, transpose_one, transpose_smul, transpose_map_vecMulVec_vecMul hσ hQ v v,
    unitaryTransvection_def, ← hw]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
    mul_smul_comm, h₁, h₂, h₃, smul_add, smul_smul]
  rw [add_assoc, ← add_smul, ← add_smul]; congr 2; ring

/-- **Unitary quasi-reflections are isometries.** If `σ` is an involution, `σ(Q)ᵀ = ε Q`, and
`a + ε σ(a) + ε a σ(a) B(v, v) = 0`, then `τ_{v,a}` preserves the form. -/
theorem transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero (hσ : Function.Involutive σ)
    {ε : R} (hQ : (Q.map σ)ᵀ = ε • Q) {a : R}
    (ha : a + ε * σ a + ε * a * σ a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0) :
    ((Q.unitaryTransvection σ v a).map σ)ᵀ * Q * Q.unitaryTransvection σ v a = Q := by
  rw [transpose_map_unitaryTransvection_mul_mul hσ hQ, ha, zero_smul, add_zero]

/-- **Unitary transvections are isometries.** Let `σ` be an involution, let the Gram matrix
satisfy `σ(Q)ᵀ = ε Q`, so that `σ(B(x, y)) = ε B(y, x)`, and let `v` be isotropic. If
`a + ε σ(a) = 0`, then `τ_{v,a}` preserves the form: `σ(τ_{v,a})ᵀ Q τ_{v,a} = Q`. -/
theorem transpose_map_unitaryTransvection_mul_mul_self (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : R} (ha : a + ε * σ a = 0) :
    ((Q.unitaryTransvection σ v a).map σ)ᵀ * Q * Q.unitaryTransvection σ v a = Q :=
  transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero hσ hQ (by simp [hv, ha])

section StarRing

variable [StarRing R] {A : Matrix n n R} {a : R}

/-- **Admissible unitary transvections preserve a Hermitian form.** For Hermitian `A`, the unitary
transvection `τ_{v,a} = 1 + a • v (star v ᵥ* A)` satisfies `star τ_{v,a} * A * τ_{v,a} = A` when
`a + star a + a * star a * ⟨v, v⟩ = 0`, where `⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y`. This is
`Matrix.transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero` for `σ = starRingEnd R` and
`ε = 1`. -/
theorem star_unitaryTransvection_mul_mul_self_of_eq_zero (hA : A.IsHermitian)
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) :
    star (A.unitaryTransvection (starRingEnd R) v a) * A *
      A.unitaryTransvection (starRingEnd R) v a = A := by
  have h := transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero (v := v) (a := a)
    starRingEnd_self_apply (by rw [one_smul, transpose_map_starRingEnd, hA.eq])
    (by rwa [one_mul, one_mul, TauCeti.starRingEnd_comp_eq_star, starRingEnd_apply])
  rwa [transpose_map_starRingEnd, ← star_eq_conjTranspose] at h

/-- For `a + star a + a * star a * ⟨v, v⟩ = 0`, the unitary transvection `τ_{v,star a}` is a right
inverse of `τ_{v,a}`. -/
theorem unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) :
    A.unitaryTransvection (starRingEnd R) v a * A.unitaryTransvection (starRingEnd R) v (star a) =
      1 := by
  rw [unitaryTransvection_mul_unitaryTransvection_eq, TauCeti.starRingEnd_comp_eq_star, ha,
    unitaryTransvection_zero]

end StarRing

section CommRing

variable {R : Type*} [CommRing R] {Q : Matrix n n R} {σ : R →+* R} {v : n → R}

/-- A transvection along `x - y` sends `y` to `x` when its action coefficient is one. -/
theorem unitaryTransvection_sub_mulVec_eq {x y : n → R} {a : R}
    (hxy : a * ((σ ∘ (x - y)) ⬝ᵥ Q *ᵥ y) = 1) :
    Q.unitaryTransvection σ (x - y) a *ᵥ y = x := by
  simp only [unitaryTransvection_mulVec, hxy, one_smul, add_sub_cancel]

/-- **Determinant of a unitary transvection or quasi-reflection**:
`det(τ_{v,a}) = 1 + a B(v, v)`. -/
theorem det_unitaryTransvection_eq (a : R) :
    (Q.unitaryTransvection σ v a).det = 1 + a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) := by
  rw [unitaryTransvection_def, TauCeti.det_one_add_smul_vecMulVec, ← dotProduct_mulVec]

/-- **An isotropic transvection has determinant one.** -/
theorem det_unitaryTransvection (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a : R) :
    (Q.unitaryTransvection σ v a).det = 1 := by
  rw [det_unitaryTransvection_eq, hv, mul_zero, add_zero]

end CommRing

section Field

variable {K : Type*} [Field K] {Q : Matrix n n K} {σ : K →+* K}

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

end
