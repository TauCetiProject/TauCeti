/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.UnitaryTransvection
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Unitary Siegel transformations

Let `σ` be a ring endomorphism of a commutative ring `R`, let `Q` be a square matrix over `R`, and
write `B(x, y) = σ(x)ᵀ Q y` for the `σ`-sesquilinear form `(σ ∘ x) ⬝ᵥ (Q *ᵥ y)` of Gram matrix
`Q`. A unitary transvection `τ_{u,c} = 1 + c u (σ(u)ᵀ Q)` (`Matrix.unitaryTransvection`) adds a
multiple of an isotropic vector `u` along `u^⊥`. To move `u^⊥ / R ∙ u` while fixing `u`, one uses
the **Siegel transformation** (also called an **Eichler transvection**): for vectors `u`, `w`, a
sign scalar `ε`, and a scalar `c`,

```text
S(u, w, c) : v ↦ v + B(u, v) (w + c u) - ε B(w, v) u,
S(u, w, c) = 1 + (w + c u) (σ(u)ᵀ Q) - ε u (σ(w)ᵀ Q).
```

This is `Matrix.siegelTransvection Q σ ε u w c`. For `w = 0` it reduces to the unitary transvection
`τ_{u,c}` (`Matrix.siegelTransvection_zero_eq_unitaryTransvection`). When `u` is isotropic
(`B(u, u) = 0`), the two rank-one perturbations in `S(u, w, c)` have orthogonal inner vectors and
factor as `(1 + (w + c u) (σ(u)ᵀ Q)) (1 - ε u (σ(w)ᵀ Q))` (`Matrix.siegelTransvection_eq_mul`);
when moreover `B(u, w) = 0` and `B(w, u) = 0`, each factor has determinant one, so `S(u, w, c)` has
determinant one (`Matrix.det_siegelTransvection`) and fixes `u`
(`Matrix.siegelTransvection_mulVec_self`).

For a fixed isotropic `u`, composition on vectors `w` orthogonal to `u` obeys the Heisenberg law

```text
S(u, w₁, c₁) S(u, w₂, c₂) = S(u, w₁ + w₂, c₁ + c₂ - ε B(w₁, w₂))
```

(`Matrix.siegelTransvection_mul_siegelTransvection`), and a matrix `g` preserving `B` conjugates
`S(u, w, c)` to `S(g u, g w, c)` (`Matrix.mul_siegelTransvection`). When `σ` is an involution and
`Q` is `ε`-Hermitian (`σ(Q)ᵀ = ε Q`), the isometry defect of `S(u, w, c)` is
`(c + ε σ(c) + ε B(w, w)) (Q u) (σ(u)ᵀ Q)` (`Matrix.transpose_map_siegelTransvection_mul_mul`), so
`S(u, w, c)` preserves `B` whenever `c + ε σ(c) + ε B(w, w) = 0`
(`Matrix.transpose_map_siegelTransvection_mul_mul_self`).

In a unitary space over a field, Siegel transformations along `u` act transitively on the isotropic
vectors sharing a given nonzero pairing with `u`, including in Witt index one where every vector of
`u^⊥` outside `K ∙ u` is anisotropic and no unitary transvection outside `K ∙ u` exists. That
point-stabilizer transitivity and the resulting primitivity of the special unitary group on its
isotropic points are proved in
`TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup/Isometry/Primitive.lean`.

## Main definitions

* `Matrix.siegelTransvection`: the matrix `1 + (w + c u) (σ(u)ᵀ Q) - ε u (σ(w)ᵀ Q)`.

## Main results

* `Matrix.siegelTransvection_zero_eq_unitaryTransvection`: `S(u, 0, c) = τ_{u,c}`.
* `Matrix.siegelTransvection_mulVec`: the action `v ↦ v + B(u, v) (w + c u) - ε B(w, v) u`.
* `Matrix.siegelTransvection_mulVec_self`: `S(u, w, c)` fixes `u` when `B(u, u) = B(w, u) = 0`.
* `Matrix.siegelTransvection_add_smul`: shifting `w` by `a u` shifts `c` to `c + a - ε σ(a)`.
* `Matrix.siegelTransvection_eq_mul` and `Matrix.det_siegelTransvection`: two-factor product for
  isotropic `u`, and determinant one when `B(u, w) = B(w, u) = 0`.
* `Matrix.siegelTransvection_mul_siegelTransvection` and `Matrix.siegelTransvection_mul_neg`: the
  Heisenberg multiplication law and explicit inverse `S(u, -w, -c - ε B(w, w))`.
* `Matrix.mul_siegelTransvection`: the conjugation law `g S(u, w, c) = S(g u, g w, c) g`.
* `Matrix.transpose_map_siegelTransvection_mul_mul` and
  `Matrix.transpose_map_siegelTransvection_mul_mul_self`: the isometry defect and the condition
  `c + ε σ(c) + ε B(w, w) = 0` for `S(u, w, c)` to preserve `B`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11, especially
  §10.4 and §11.4 on Siegel transformations.
* L. C. Grove, *Classical Groups and Geometric Algebra*, Graduate Studies in Mathematics 39
  (2002), Chapter 11.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **The unitary Siegel transformation** (or Eichler transvection)
`S(u, w, c) = 1 + (w + c u) (σ(u)ᵀ Q) - ε u (σ(w)ᵀ Q)` for the `σ`-sesquilinear form
`B(x, y) = σ(x)ᵀ Q y`. It acts by `v ↦ v + B(u, v) (w + c u) - ε B(w, v) u`
(`Matrix.siegelTransvection_mulVec`). -/
def siegelTransvection (Q : Matrix n n R) (σ : R →+* R) (ε : R) (u w : n → R) (c : R) :
    Matrix n n R :=
  1 + vecMulVec (w + c • u) ((σ ∘ u) ᵥ* Q) - ε • vecMulVec u ((σ ∘ w) ᵥ* Q)

variable {Q : Matrix n n R} {σ : R →+* R} {ε : R} {u : n → R}

theorem siegelTransvection_def (Q : Matrix n n R) (σ : R →+* R) (ε : R) (u w : n → R) (c : R) :
    Q.siegelTransvection σ ε u w c =
      1 + vecMulVec (w + c • u) ((σ ∘ u) ᵥ* Q) - ε • vecMulVec u ((σ ∘ w) ᵥ* Q) :=
  (rfl)

/-- For `w = 0`, the Siegel transformation `S(u, 0, c)` is the unitary transvection `τ_{u,c}`. -/
@[simp]
theorem siegelTransvection_zero_eq_unitaryTransvection (c : R) :
    Q.siegelTransvection σ ε u 0 c = Q.unitaryTransvection σ u c := by
  have h0 : σ ∘ (0 : n → R) = 0 := funext fun _ ↦ map_zero σ
  rw [siegelTransvection_def, zero_add, h0, zero_vecMul, vecMulVec_zero, smul_zero, sub_zero,
    smul_vecMulVec, unitaryTransvection_def]

/-- For `w = 0` and `c = 0`, the Siegel transformation is the identity matrix. -/
theorem siegelTransvection_zero_zero : Q.siegelTransvection σ ε u 0 0 = 1 := by
  rw [siegelTransvection_zero_eq_unitaryTransvection, unitaryTransvection_zero]

/-- Along the zero vector `u = 0`, every Siegel transformation is the identity matrix. -/
theorem siegelTransvection_zero_left (w : n → R) (c : R) :
    Q.siegelTransvection σ ε 0 w c = 1 := by
  have h0 : σ ∘ (0 : n → R) = 0 := funext fun _ ↦ map_zero σ
  rw [siegelTransvection_def, smul_zero, add_zero, h0, zero_vecMul, vecMulVec_zero, zero_vecMulVec,
    smul_zero, add_zero, sub_zero]

/-- The Siegel transformation `S(u, w, c)` sends `v` to
`v + B(u, v) (w + c u) - ε B(w, v) u`. -/
theorem siegelTransvection_mulVec (w : n → R) (c : R) (v : n → R) :
    Q.siegelTransvection σ ε u w c *ᵥ v =
      v + ((σ ∘ u) ⬝ᵥ (Q *ᵥ v)) • (w + c • u) - (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ v))) • u := by
  rw [siegelTransvection_def, sub_mulVec, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, ← dotProduct_mulVec, ← dotProduct_mulVec,
    smul_smul]

/-- When `B(u, u) = 0` and `B(w, u) = 0`, the Siegel transformation `S(u, w, c)` fixes `u`. -/
theorem siegelTransvection_mulVec_self (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) {w : n → R}
    (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) (c : R) :
    Q.siegelTransvection σ ε u w c *ᵥ u = u := by
  rw [siegelTransvection_mulVec, hu, hwu, zero_smul, mul_zero, zero_smul, add_zero, sub_zero]

/-- Shifting `w` by `a • u` shifts the scalar parameter `c` by `a - ε σ(a)`. -/
theorem siegelTransvection_add_smul (w : n → R) (a c : R) :
    Q.siegelTransvection σ ε u (w + a • u) c =
      Q.siegelTransvection σ ε u w (c + a - ε * σ a) := by
  refine mulVec_injective (funext fun v ↦ ?_)
  rw [siegelTransvection_mulVec, siegelTransvection_mulVec, comp_add_dotProduct_mulVec,
    comp_smul_dotProduct_mulVec]
  module

/-- **Two-factor product for an isotropic `u`.** When `B(u, u) = 0`, the two rank-one perturbations
in `S(u, w, c)` multiply to zero in the order `((w + c u) (σ(u)ᵀ Q)) (u (σ(w)ᵀ Q))`, so `S(u, w, c)`
factors as `(1 + (w + c u) (σ(u)ᵀ Q)) * (1 - ε u (σ(w)ᵀ Q))`. -/
theorem siegelTransvection_eq_mul (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (w : n → R) (c : R) :
    Q.siegelTransvection σ ε u w c =
      (1 + vecMulVec (w + c • u) ((σ ∘ u) ᵥ* Q)) *
        (1 - ε • vecMulVec u ((σ ∘ w) ᵥ* Q)) := by
  have hprod : vecMulVec (w + c • u) ((σ ∘ u) ᵥ* Q) * vecMulVec u ((σ ∘ w) ᵥ* Q) = 0 := by
    rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, hu, zero_smul, vecMulVec_zero]
  rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, mul_smul_comm, hprod, smul_zero, add_zero, siegelTransvection_def]

/-- **A Siegel transformation along an isotropic `u` orthogonal to `w` has determinant one.** -/
theorem det_siegelTransvection (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) {w : n → R}
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) (c : R) :
    (Q.siegelTransvection σ ε u w c).det = 1 := by
  have hd₁ : (1 + vecMulVec (w + c • u) ((σ ∘ u) ᵥ* Q)).det = 1 := by
    rw [← sub_neg_eq_add, ← neg_vecMulVec, TauCeti.det_one_sub_vecMulVec, dotProduct_neg,
      ← dotProduct_mulVec, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, huw, hu,
      smul_zero, add_zero, neg_zero, sub_zero]
  have hd₂ : (1 - ε • vecMulVec u ((σ ∘ w) ᵥ* Q)).det = 1 := by
    rw [← smul_vecMulVec, TauCeti.det_one_sub_vecMulVec, dotProduct_smul, ← dotProduct_mulVec,
      hwu, smul_zero, sub_zero]
  rw [siegelTransvection_eq_mul hu, det_mul, hd₁, hd₂, mul_one]

/-- **The Heisenberg multiplication law.** If `B(u, u) = 0`, `B(u, w₂) = 0`, and `B(w₁, u) = 0`,
then `S(u, w₁, c₁) * S(u, w₂, c₂) = S(u, w₁ + w₂, c₁ + c₂ - ε B(w₁, w₂))`. -/
theorem siegelTransvection_mul_siegelTransvection (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    {w₁ w₂ : n → R} (huw₂ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w₂) = 0) (hw₁u : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ u) = 0)
    (c₁ c₂ : R) :
    Q.siegelTransvection σ ε u w₁ c₁ * Q.siegelTransvection σ ε u w₂ c₂ =
      Q.siegelTransvection σ ε u (w₁ + w₂) (c₁ + c₂ - ε * ((σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂))) := by
  have huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ (w₂ + c₂ • u)) = 0 := by
    rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, huw₂, hu, smul_zero, add_zero]
  have hw₁z : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ (w₂ + c₂ • u)) = (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂) := by
    rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hw₁u, smul_zero, add_zero]
  refine mulVec_injective (funext fun v ↦ ?_)
  rw [← mulVec_mulVec, siegelTransvection_mulVec w₂ c₂, mulVec_sub, mulVec_add, mulVec_smul,
    mulVec_smul, siegelTransvection_mulVec_self hu hw₁u, siegelTransvection_mulVec,
    siegelTransvection_mulVec, siegelTransvection_mulVec, huz, hw₁z,
    comp_add_dotProduct_mulVec]
  module

/-- **Inverting a Siegel transformation.** If `B(u, u) = B(u, w) = B(w, u) = 0`, then
`S(u, -w, -c - ε B(w, w))` is the inverse of `S(u, w, c)`. -/
theorem siegelTransvection_mul_neg (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) {w : n → R}
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) (c : R) :
    Q.siegelTransvection σ ε u w c *
        Q.siegelTransvection σ ε u (-w) (-c - ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w))) = 1 := by
  have huw' : (σ ∘ u) ⬝ᵥ (Q *ᵥ (-w)) = 0 := by rw [mulVec_neg, dotProduct_neg, huw, neg_zero]
  rw [siegelTransvection_mul_siegelTransvection hu huw' hwu, add_neg_cancel, mulVec_neg,
    dotProduct_neg, mul_neg, sub_neg_eq_add, add_assoc, sub_add_cancel, add_neg_cancel,
    siegelTransvection_zero_zero]

/-- **The conjugation law.** A matrix `g` preserving the form, `σ(g)ᵀ Q g = Q`, conjugates
`S(u, w, c)` to `S(g u, g w, c)`: `g * S(u, w, c) = S(g u, g w, c) * g`. -/
theorem mul_siegelTransvection {g : Matrix n n R} (hg : (g.map σ)ᵀ * Q * g = Q) (w : n → R)
    (c : R) :
    g * Q.siegelTransvection σ ε u w c =
      Q.siegelTransvection σ ε (g *ᵥ u) (g *ᵥ w) c * g := by
  have hrow (v : n → R) : (σ ∘ (g *ᵥ v)) ᵥ* Q ᵥ* g = (σ ∘ v) ᵥ* Q := by
    rw [(funext (σ.map_mulVec g v) : σ ∘ (g *ᵥ v) = _), ← vecMul_transpose, vecMul_vecMul,
      vecMul_vecMul, ← Matrix.mul_assoc, hg]
  rw [siegelTransvection_def, siegelTransvection_def, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_smul_comm,
    smul_mul_assoc, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul, hrow u, hrow w,
    mulVec_add, mulVec_smul]

omit [DecidableEq n] in
/-- For an involutive `σ` and `σ(Q)ᵀ = ε Q`, the transposed conjugate of `x (σ(y)ᵀ Q)` is
`ε (Q y) σ(x)ᵀ`. -/
private theorem transpose_map_vecMulVec_vecMul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (x y : n → R) :
    ((vecMulVec x ((σ ∘ y) ᵥ* Q)).map σ)ᵀ = ε • vecMulVec (Q *ᵥ y) (σ ∘ x) := by
  have hσy : σ ∘ ((σ ∘ y) ᵥ* Q) = y ᵥ* Q.map σ := funext fun i ↦ by
    rw [Function.comp_apply, RingHom.map_vecMul, ← Function.comp_assoc, hσ.comp_self,
      Function.id_comp]
  have hmap : (vecMulVec x ((σ ∘ y) ᵥ* Q)).map σ = vecMulVec (σ ∘ x) (σ ∘ ((σ ∘ y) ᵥ* Q)) := by
    ext i j
    simp [vecMulVec_apply]
  rw [hmap, transpose_vecMulVec, hσy, ← mulVec_transpose, hQ, smul_mulVec, smul_vecMulVec]

/-- **The isometry defect of a Siegel transformation.** Let `σ` be an involution, let the Gram
matrix satisfy `σ(Q)ᵀ = ε Q`, and let `B(u, u) = B(u, w) = B(w, u) = 0`. Then
`σ(S(u, w, c))ᵀ Q S(u, w, c) = Q + (c + ε σ(c) + ε B(w, w)) (Q u) (σ(u)ᵀ Q)`. -/
theorem transpose_map_siegelTransvection_mul_mul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) {w : n → R}
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) (c : R) :
    ((Q.siegelTransvection σ ε u w c).map σ)ᵀ * Q * Q.siegelTransvection σ ε u w c =
      Q + (c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w))) • vecMulVec (Q *ᵥ u) ((σ ∘ u) ᵥ* Q) := by
  set z := w + c • u with hz
  -- Applying `σ(Q)ᵀ = ε Q` twice gives `(σ(ε) * ε) • Q = Q`.
  have hεQ : (σ ε * ε) • Q = Q := Matrix.ext fun i j ↦ by
    have h₁ : σ (Q i j) = ε * Q j i := congrFun (congrFun hQ j) i
    have h₂ : σ (Q j i) = ε * Q i j := congrFun (congrFun hQ i) j
    rw [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← h₂, ← map_mul, ← h₁, hσ]
  have hS : (Q.siegelTransvection σ ε u w c).map σ =
      1 + (vecMulVec z ((σ ∘ u) ᵥ* Q)).map σ - σ ε • (vecMulVec u ((σ ∘ w) ᵥ* Q)).map σ := by
    ext i j
    by_cases hij : i = j <;> simp [siegelTransvection_def, hz, hij]
  have hleft : ((Q.siegelTransvection σ ε u w c).map σ)ᵀ * Q =
      Q + ε • vecMulVec (Q *ᵥ u) ((σ ∘ z) ᵥ* Q) - vecMulVec (Q *ᵥ w) ((σ ∘ u) ᵥ* Q) := by
    rw [hS, transpose_sub, transpose_add, transpose_one, transpose_smul,
      transpose_map_vecMulVec_vecMul hσ hQ z u, transpose_map_vecMulVec_vecMul hσ hQ u w,
      Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, smul_mul_assoc, smul_mul_assoc,
      smul_mul_assoc, vecMulVec_mul, vecMulVec_mul, smul_smul, ← smul_vecMulVec (σ ε * ε),
      ← smul_mulVec, hεQ]
  -- Compare both sides on an arbitrary column vector `v`.
  refine mulVec_injective (funext fun v ↦ ?_)
  set Sv := Q.siegelTransvection σ ε u w c *ᵥ v with hSv
  have hSv_def : Sv = v + ((σ ∘ u) ⬝ᵥ (Q *ᵥ v)) • z - (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ v))) • u := by
    rw [hSv, siegelTransvection_mulVec, ← hz]
  have huSv : (σ ∘ u) ⬝ᵥ (Q *ᵥ Sv) = (σ ∘ u) ⬝ᵥ (Q *ᵥ v) := by
    rw [hSv_def, hz, mulVec_sub, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, mulVec_smul,
      dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_add, dotProduct_smul,
      dotProduct_smul, huw, hu]
    simp
  have hzSv : (σ ∘ z) ⬝ᵥ (Q *ᵥ Sv) =
      (σ ∘ w) ⬝ᵥ (Q *ᵥ v) + σ c * ((σ ∘ u) ⬝ᵥ (Q *ᵥ v)) +
        ((σ ∘ u) ⬝ᵥ (Q *ᵥ v)) * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) := by
    rw [hSv_def, hz, comp_add_dotProduct_mulVec, comp_smul_dotProduct_mulVec, mulVec_sub,
      mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, mulVec_smul]
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, huw, hwu, hu,
      mul_zero, add_zero, sub_zero]
    ring
  rw [← mulVec_mulVec, ← hSv, hleft, sub_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec,
    vecMulVec_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul,
    op_smul_eq_smul, ← dotProduct_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, huSv, hzSv,
    hSv_def, hz, mulVec_sub, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, mulVec_smul]
  module

/-- **Admissible Siegel transformations are isometries.** Let `σ` be an involution, let the Gram
matrix satisfy `σ(Q)ᵀ = ε Q`, and let `B(u, u) = B(u, w) = B(w, u) = 0`. If
`c + ε σ(c) + ε B(w, w) = 0`, then `S(u, w, c)` preserves the form:
`σ(S(u, w, c))ᵀ Q S(u, w, c) = Q`. -/
theorem transpose_map_siegelTransvection_mul_mul_self (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) {w : n → R}
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) {c : R}
    (hc : c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0) :
    ((Q.siegelTransvection σ ε u w c).map σ)ᵀ * Q * Q.siegelTransvection σ ε u w c = Q := by
  rw [transpose_map_siegelTransvection_mul_mul hσ hQ hu huw hwu, hc, zero_smul, add_zero]

end Matrix

end
