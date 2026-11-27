/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form
public import TauCeti.LinearAlgebra.Matrix.UnitaryTransvection
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Eichler transformations of a hermitian form

Let `R` be a commutative ring with an involution `star`, `J` a square matrix over `R`, and
`h(v, w) = star v ⬝ᵥ J *ᵥ w` the sesquilinear form of Gram matrix `J`, conjugate-linear in the
first slot. For vectors `x`, `u` and a scalar `ς`, the **Eichler transformation**

```text
E_{x,u,ς} : v ↦ v + h(u, v) x - h(x, v) (u + ς x),
E_{x,u,ς} = 1 + x (star u J) - (u + ς x) (star x J)
```

is `Matrix.eichlerTransvection J x u ς`. When `J` is hermitian, `x` is isotropic (`h(x, x) = 0`),
`u` is orthogonal to `x` (`h(u, x) = 0`) and `ς + star ς = h(u, u)`, it preserves `h`: its
adjoint for `h` is `E_{x,-u,star ς}`, which is also its inverse. It is then an element of the
unitary group `Matrix.unitaryGroupOf J`, which is `Matrix.unitaryGroupOf.eichlerTransvection`.
Nothing is assumed of `R` beyond commutativity, and `J` need not be invertible; this is the
generality in which the Eichler transformations with integral data serve for Witt's theorem over
rings such as the integral finite adeles of a CM field.

For a fixed isotropic `x`, the transformations `E_{x,u,ς}` multiply like a Heisenberg group:
`E_{x,u,ς} E_{x,u',ς'} = E_{x,u+u',ς+ς'+h(u,u')}`. Those with `u = 0` are the unitary
transvections `τ_{x,-ς}` of `TauCeti.LinearAlgebra.Matrix.UnitaryTransvection`, and the
transformation depends on `u` only modulo `x`, up to a change of `ς`. A matrix preserving `h`
conjugates `E_{x,u,ς}` to `E_{g x,g u,ς}`.

## Main definitions

* `Matrix.eichlerTransvection J x u ς`: the matrix `1 + x (star u J) - (u + ς x) (star x J)`.
* `Matrix.unitaryGroupOf.eichlerTransvection`: for hermitian `J`, isotropic `x`, `u` orthogonal to
  `x` and `ς + star ς = h(u, u)`, the Eichler transformation as an element of `unitaryGroupOf J`.

## Main results

* `Matrix.eichlerTransvection_mulVec`: the action `v ↦ v + h(u, v) x - h(x, v) (u + ς x)`.
* `Matrix.eichlerTransvection_mul_eichlerTransvection`: the product law
  `E_{x,u,ς} E_{x,u',ς'} = E_{x,u+u',ς+ς'+h(u,u')}` for isotropic `x` with `h(u, x) = 0` and
  `h(x, u') = 0`.
* `Matrix.inv_eichlerTransvection`: for isotropic `x` with `h(u, x) = h(x, u) = 0` and
  `ς + star ς = h(u, u)`, the inverse `E_{x,u,ς}⁻¹ = E_{x,-u,star ς}`.
* `Matrix.star_eichlerTransvection_mul`: for hermitian `J`, the adjoint identity
  `star E_{x,u,ς} J = J E_{x,-u,star ς}`.
* `Matrix.star_eichlerTransvection_mul_mul_self`: **the Eichler transformation is an isometry**,
  `star E J E = J`.
* `Matrix.mul_eichlerTransvection`: the conjugation law `g E_{x,u,ς} = E_{g x,g u,ς} g` for `g`
  preserving the form.

## Attribution

The matrix `1 + x (star u J) - (u + ς x) (star x J)` and the proof that it is an isometry, through
the transformation `E_{x,-u,star ς}` which is both its inverse and its adjoint, are adapted from
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/WittTheorem.lean`: `New.eichlerMap`, `New.eichlerMap_mulVec` and
`New.exists_unitary_eq_eichlerMap`. The product law, the comparison with unitary transvections,
the dependence on `u` modulo `x`, rescaling and the conjugation law are added here.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Grundlehren der mathematischen
  Wissenschaften 63, Springer (1952).
* A. J. Hahn and O. T. O'Meara, *The Classical Groups and K-Theory*, Grundlehren der
  mathematischen Wissenschaften 291, Springer (1989).
-/

public section

namespace Matrix

variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

/-- **The Eichler transformation** `E_{x,u,ς} = 1 + x (star u J) - (u + ς x) (star x J)` of the
sesquilinear form `h(v, w) = star v ⬝ᵥ J *ᵥ w`. It acts by `v ↦ v + h(u, v) x - h(x, v) (u + ς x)`
(`Matrix.eichlerTransvection_mulVec`), and it preserves `h` when `J` is hermitian, `x` is
isotropic, `h(u, x) = 0` and `ς + star ς = h(u, u)`
(`Matrix.star_eichlerTransvection_mul_mul_self`). -/
def eichlerTransvection (J : Matrix n n R) (x u : n → R) (ς : R) : Matrix n n R :=
  1 + vecMulVec x (star u ᵥ* J) - vecMulVec (u + ς • x) (star x ᵥ* J)

variable {J : Matrix n n R} {x u u' : n → R} {ς ς' : R}

theorem eichlerTransvection_def (J : Matrix n n R) (x u : n → R) (ς : R) :
    J.eichlerTransvection x u ς =
      1 + vecMulVec x (star u ᵥ* J) - vecMulVec (u + ς • x) (star x ᵥ* J) :=
  (rfl)

/-- The Eichler transformation `E_{x,u,ς}` sends `v` to `v + h(u, v) x - h(x, v) (u + ς x)`. -/
theorem eichlerTransvection_mulVec (v : n → R) :
    J.eichlerTransvection x u ς *ᵥ v =
      v + (star u ⬝ᵥ J *ᵥ v) • x - (star x ⬝ᵥ J *ᵥ v) • (u + ς • x) := by
  simp only [eichlerTransvection_def, sub_mulVec, add_mulVec, one_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, dotProduct_mulVec]

/-- Along the zero vector `x = 0`, every Eichler transformation is the identity matrix. -/
@[simp]
theorem eichlerTransvection_zero_left (u : n → R) (ς : R) : J.eichlerTransvection 0 u ς = 1 := by
  rw [eichlerTransvection_def, star_zero, zero_vecMul, vecMulVec_zero, zero_vecMulVec, add_zero,
    sub_zero]

/-- **The Eichler transformations with `u = 0` are unitary transvections**: `E_{x,0,ς}` is the
transvection `τ_{x,-ς} : v ↦ v - ς h(x, v) x` of `Matrix.unitaryTransvection`, for the involution
`star`. -/
@[simp]
theorem eichlerTransvection_zero_eq_unitaryTransvection (x : n → R) (ς : R) :
    J.eichlerTransvection x 0 ς = J.unitaryTransvection (starRingEnd R) x (-ς) := by
  have hx : (starRingEnd R ∘ x) = star x := funext fun i ↦ starRingEnd_apply (x i)
  rw [eichlerTransvection_def, unitaryTransvection_def, hx, star_zero, zero_vecMul, vecMulVec_zero,
    zero_add, add_zero, smul_vecMulVec, neg_smul, sub_eq_add_neg]

/-- An Eichler transformation fixes its isotropic vector `x` when `h(u, x) = 0`. -/
theorem eichlerTransvection_mulVec_self (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hux : star u ⬝ᵥ J *ᵥ x = 0) : J.eichlerTransvection x u ς *ᵥ x = x := by
  rw [eichlerTransvection_mulVec, hux, hx, zero_smul, zero_smul, add_zero, sub_zero]

/-- An Eichler transformation `E_{x,u,ς}` fixes every vector `v` with `h(x, v) = h(u, v) = 0`. -/
theorem eichlerTransvection_mulVec_of_dotProduct_eq_zero {v : n → R}
    (hxv : star x ⬝ᵥ J *ᵥ v = 0) (huv : star u ⬝ᵥ J *ᵥ v = 0) :
    J.eichlerTransvection x u ς *ᵥ v = v := by
  rw [eichlerTransvection_mulVec, hxv, huv, zero_smul, zero_smul, add_zero, sub_zero]

/-- **The Eichler transformation depends on `u` only modulo `x`**, up to a change of the
scalar: `E_{x,u+c x,ς} = E_{x,u,ς+c-star c}`. -/
theorem eichlerTransvection_add_smul (c : R) :
    J.eichlerTransvection x (u + c • x) ς = J.eichlerTransvection x u (ς + c - star c) := by
  simp only [eichlerTransvection_def, star_add, star_smul, add_vecMul, smul_vecMul,
    vecMulVec_add, vecMulVec_smul, add_vecMulVec, sub_vecMulVec, smul_vecMulVec, sub_smul, add_smul]
  module

/-- Rescaling the isotropic vector of an Eichler transformation:
`E_{c x,u,ς} = E_{x,star c u,c star c ς}`. -/
theorem eichlerTransvection_smul (c : R) :
    J.eichlerTransvection (c • x) u ς = J.eichlerTransvection x (star c • u) (c * star c * ς) := by
  simp only [eichlerTransvection_def, star_smul, star_star, smul_vecMul, smul_vecMulVec,
    vecMulVec_smul, add_vecMulVec, smul_smul]
  module

/-- **The product law.** For isotropic `x` with `h(u, x) = 0` and `h(x, u') = 0`,
`E_{x,u,ς} E_{x,u',ς'} = E_{x,u+u',ς+ς'+h(u,u')}`: for fixed `x` the Eichler transformations
multiply like a Heisenberg group. -/
theorem eichlerTransvection_mul_eichlerTransvection (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hux : star u ⬝ᵥ J *ᵥ x = 0) (hxu' : star x ⬝ᵥ J *ᵥ u' = 0) (ς ς' : R) :
    J.eichlerTransvection x u ς * J.eichlerTransvection x u' ς' =
      J.eichlerTransvection x (u + u') (ς + ς' + star u ⬝ᵥ J *ᵥ u') := by
  refine ext_iff_mulVec.2 fun v ↦ ?_
  simp only [← mulVec_mulVec, eichlerTransvection_mulVec, mulVec_add, mulVec_sub, mulVec_smul,
    star_add, add_dotProduct, hx, hux, hxu']
  module

/-- **A left inverse of an Eichler transformation.** For isotropic `x` with `h(u, x) = 0`,
`h(x, u) = 0` and `ς + star ς = h(u, u)`, the Eichler transformation `E_{x,-u,star ς}` is a left
inverse of `E_{x,u,ς}`. -/
theorem eichlerTransvection_neg_mul_eichlerTransvection (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hux : star u ⬝ᵥ J *ᵥ x = 0) (hxu : star x ⬝ᵥ J *ᵥ u = 0)
    (hς : ς + star ς = star u ⬝ᵥ J *ᵥ u) :
    J.eichlerTransvection x (-u) (star ς) * J.eichlerTransvection x u ς = 1 := by
  have hux' : star (-u) ⬝ᵥ J *ᵥ x = 0 := by rw [star_neg, neg_dotProduct, hux, neg_zero]
  have hς' : star ς + ς + star (-u) ⬝ᵥ J *ᵥ u = 0 := by
    rw [star_neg, neg_dotProduct, add_comm (star ς), hς, add_neg_cancel]
  rw [eichlerTransvection_mul_eichlerTransvection hx hux' hxu, neg_add_cancel, hς']
  simp

/-- **The inverse matrix of an Eichler transformation.** For isotropic `x` with `h(u, x) = 0`,
`h(x, u) = 0` and `ς + star ς = h(u, u)`, the inverse of `E_{x,u,ς}` is `E_{x,-u,star ς}`. -/
theorem inv_eichlerTransvection (hx : star x ⬝ᵥ J *ᵥ x = 0) (hux : star u ⬝ᵥ J *ᵥ x = 0)
    (hxu : star x ⬝ᵥ J *ᵥ u = 0) (hς : ς + star ς = star u ⬝ᵥ J *ᵥ u) :
    (J.eichlerTransvection x u ς)⁻¹ = J.eichlerTransvection x (-u) (star ς) :=
  inv_eq_left_inv (eichlerTransvection_neg_mul_eichlerTransvection hx hux hxu hς)

/-- **The adjoint identity.** For hermitian `J`, `star E_{x,u,ς} J = J E_{x,-u,star ς}`: the
adjoint of `E_{x,u,ς}` for the form of `J` is `E_{x,-u,star ς}`. -/
theorem star_eichlerTransvection_mul (hJ : J.IsHermitian) (x u : n → R) (ς : R) :
    star (J.eichlerTransvection x u ς) * J = J * J.eichlerTransvection x (-u) (star ς) := by
  simp only [eichlerTransvection_def, star_add, star_sub, star_one, star_eq_conjTranspose,
    conjTranspose_vecMulVec, star_vecMul, star_star, hJ.eq, Matrix.add_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_neg, Matrix.mul_smul, mul_vecMulVec, star_neg, star_smul, neg_vecMul, vecMulVec_neg,
    add_vecMulVec, smul_vecMulVec, neg_vecMulVec]
  module

/-- **The Eichler transformation is an isometry.** For hermitian `J`, isotropic `x`,
`h(u, x) = 0` and `ς + star ς = h(u, u)`, the Eichler transformation `E_{x,u,ς}` preserves the
form of `J`: `star E J E = J`. -/
theorem star_eichlerTransvection_mul_mul_self (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hux : star u ⬝ᵥ J *ᵥ x = 0) (hς : ς + star ς = star u ⬝ᵥ J *ᵥ u) :
    star (J.eichlerTransvection x u ς) * J * J.eichlerTransvection x u ς = J := by
  have hxu : star x ⬝ᵥ J *ᵥ u = 0 := by
    rw [← hJ.star_dotProduct_mulVec_comm, hux, star_zero]
  rw [star_eichlerTransvection_mul hJ, Matrix.mul_assoc,
    eichlerTransvection_neg_mul_eichlerTransvection hx hux hxu hς, Matrix.mul_one]

/-- **The conjugation law.** A matrix `g` preserving the form of `J`, `star g J g = J`, carries
the Eichler transformation `E_{x,u,ς}` to `E_{g x,g u,ς}`: `g E_{x,u,ς} = E_{g x,g u,ς} g`. -/
theorem mul_eichlerTransvection {g : Matrix n n R} (hg : star g * J * g = J) (x u : n → R)
    (ς : R) :
    g * J.eichlerTransvection x u ς = J.eichlerTransvection (g *ᵥ x) (g *ᵥ u) ς * g := by
  refine ext_iff_mulVec.2 fun v ↦ ?_
  have hform (y : n → R) : star (g *ᵥ y) ⬝ᵥ J *ᵥ g *ᵥ v = star y ⬝ᵥ J *ᵥ v := by
    rw [← star_dotProduct_conjTranspose_mul_mul_mulVec, ← star_eq_conjTranspose, hg]
  simp only [← mulVec_mulVec, eichlerTransvection_mulVec, hform, mulVec_add, mulVec_sub,
    mulVec_smul]

namespace unitaryGroupOf

/-- **The Eichler transformation as an element of the unitary group.** For hermitian `J`, an
isotropic vector `x`, a vector `u` with `h(u, x) = 0` and `ς` with `ς + star ς = h(u, u)`, the
Eichler transformation `E_{x,u,ς} : v ↦ v + h(u, v) x - h(x, v) (u + ς x)` is an element of
`unitaryGroupOf J`, with inverse `E_{x,-u,star ς}`. -/
def eichlerTransvection (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hux : star u ⬝ᵥ J *ᵥ x = 0) (hς : ς + star ς = star u ⬝ᵥ J *ᵥ u) :
    unitaryGroupOf J :=
  have hxu : star x ⬝ᵥ J *ᵥ u = 0 := by
    rw [← hJ.star_dotProduct_mulVec_comm, hux, star_zero]
  have hinv : J.eichlerTransvection x (-u) (star ς) * J.eichlerTransvection x u ς = 1 :=
    eichlerTransvection_neg_mul_eichlerTransvection hx hux hxu hς
  ⟨⟨J.eichlerTransvection x u ς, J.eichlerTransvection x (-u) (star ς),
      mul_eq_one_comm.mp hinv, hinv⟩,
    mem_unitaryGroupOf_iff.2 (star_eichlerTransvection_mul_mul_self hJ hx hux hς)⟩

/-- The matrix of the Eichler transformation in the unitary group is `E_{x,u,ς}`. -/
@[simp]
theorem val_eichlerTransvection (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hux : star u ⬝ᵥ J *ᵥ x = 0) (hς : ς + star ς = star u ⬝ᵥ J *ᵥ u) :
    ((eichlerTransvection hJ hx hux hς : GL n R) : Matrix n n R) =
      J.eichlerTransvection x u ς :=
  (rfl)

end unitaryGroupOf

end Matrix
