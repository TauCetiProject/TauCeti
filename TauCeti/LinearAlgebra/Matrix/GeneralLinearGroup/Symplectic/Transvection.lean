/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import TauCeti.Data.Matrix.Basis

/-!
# Symplectic transvections

Let `ω(x, y) = xᵀ J y` be the standard alternating form on `Fin (m + m) → R`, where `J` is the
transported form `TauCeti.JFin`. For a vector `v` and a scalar `c`, the **symplectic transvection**

```text
τ_{v,c} : x ↦ x + c ω(v, x) v,        τ_{v,c} = 1 + c v (vᵀ J)
```

preserves `ω`, because `ω(v, v) = 0`. This file constructs `τ_{v,c}` in the standard symplectic
group `TauCeti.GLSymplecticFin m R` over an arbitrary commutative ring and proves its basic laws:
`τ_{v,a} τ_{v,b} = τ_{v,a+b}`, `τ_{a v,c} = τ_{v,a²c}`, and `g τ_{v,c} g⁻¹ = τ_{g v,c}` for a
symplectic `g`.

The standard root elements are products of symplectic transvections. A long-root element is a
single transvection along a coordinate vector. For a short root, if `u` and `w` span a totally
isotropic plane then `τ_{u+w,c} τ_{u,-c} τ_{w,-c} = 1 + c (u (wᵀ J) + w (uᵀ J))`, and the three
short-root families are of this form for suitable coordinate vectors. Since the root subgroups
generate the symplectic group over a field (`TauCeti.GLSymplecticFin.eq_top_of_root_subgroups`),
so do the symplectic transvections. Together with the conjugation law, this is what makes the
symplectic transvections along the points of projective space an Iwasawa structure, the input of
Iwasawa's simplicity criterion for the projective symplectic groups.

## Main declarations

* `TauCeti.GLSymplecticFin.symplecticTransvection`: the transvection `τ_{v,c}`, with its matrix
  `TauCeti.GLSymplecticFin.coe_symplecticTransvection` and its action on vectors
  `TauCeti.GLSymplecticFin.coe_symplecticTransvection_mulVec`; as a linear map it is Mathlib's
  `LinearMap.transvection` (`TauCeti.GLSymplecticFin.toLin'_symplecticTransvection`).
* `TauCeti.GLSymplecticFin.symplecticTransvectionHom`: the one-parameter subgroup `c ↦ τ_{v,c}`.
* `TauCeti.GLSymplecticFin.symplecticTransvection_smul`: rescaling the vector.
* `TauCeti.GLSymplecticFin.mul_symplecticTransvection_mul_inv`: the conjugation law.
* `TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit_eq_symplecticTransvection`,
  `TauCeti.GLSymplecticFin.differenceShortRootUnit_eq_symplecticTransvection` and their siblings:
  every root element is a product of at most three symplectic transvections.
* `TauCeti.GLSymplecticFin.eq_top_of_symplecticTransvection_mem`: over a field, the symplectic
  transvections generate the symplectic group.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, §§4--5.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ}

/-- A rank-one matrix of the shape `a (bᵀ J)` kills another one `c (dᵀ J)` from the left when
`ω(b, c) = 0`. -/
private theorem vecMulVec_mul_vecMulVec_JFin {a b c d : Fin (m + m) → R}
    (h : b ⬝ᵥ (JFin m R *ᵥ c) = 0) :
    vecMulVec a (b ᵥ* JFin m R) * vecMulVec c (d ᵥ* JFin m R) = 0 := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, h, zero_smul, vecMulVec_zero]

/-- The self-pairing of the rank-one matrix `(-c) v (vᵀ J)` vanishes, so `1 - (-c) v (vᵀ J)` is
invertible (`TauCeti.oneSubVecMulVecGL` with the unit `-1`). -/
private theorem vecMul_JFin_dotProduct_neg_smul (v : Fin (m + m) → R) (c : R) :
    (v ᵥ* JFin m R) ⬝ᵥ ((-c) • v) = ((-1 : Rˣ) : R) + 1 := by
  rw [dotProduct_smul, ← dotProduct_mulVec, dotProduct_JFin_mulVec_self, smul_zero, Units.val_neg,
    Units.val_one, neg_add_cancel]

/-- The matrix `1 + c v (vᵀ J)` preserves the standard alternating form. -/
private theorem one_add_smul_vecMulVec_JFin_mem (v : Fin (m + m) → R) (c : R) :
    (1 + c • vecMulVec v (v ᵥ* JFin m R))ᵀ * JFin m R * (1 + c • vecMulVec v (v ᵥ* JFin m R)) =
      JFin m R := by
  have hJv : JFin m R *ᵥ v = -(v ᵥ* JFin m R) := by
    rw [← vecMul_transpose, JFin_transpose m R, vecMul_neg]
  have hzero : vecMulVec (v ᵥ* JFin m R) (v ᵥ* JFin m R) * vecMulVec v (v ᵥ* JFin m R) = 0 :=
    vecMulVec_mul_vecMulVec_JFin (dotProduct_JFin_mulVec_self v)
  have hNJ : vecMulVec (v ᵥ* JFin m R) v * JFin m R =
      vecMulVec (v ᵥ* JFin m R) (v ᵥ* JFin m R) := vecMulVec_mul _ _ _
  have hJN : JFin m R * vecMulVec v (v ᵥ* JFin m R) =
      -vecMulVec (v ᵥ* JFin m R) (v ᵥ* JFin m R) := by
    rw [mul_vecMulVec, hJv, neg_vecMulVec]
  rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
    mul_smul_comm, hNJ, hJN, hzero, smul_zero, add_zero, smul_neg]
  abel

/-- **The symplectic transvection** `τ_{v,c} : x ↦ x + c ω(v, x) v` along the vector `v`, where
`ω(x, y) = xᵀ J y` is the standard alternating form. Its matrix is `1 + c v (vᵀ J)`
(`TauCeti.GLSymplecticFin.coe_symplecticTransvection`), built as the rank-one perturbation
`TauCeti.oneSubVecMulVecGL` of the identity by `(-c) v (vᵀ J)`. -/
def symplecticTransvection (v : Fin (m + m) → R) (c : R) : GLSymplecticFin m R :=
  ⟨oneSubVecMulVecGL (-1) ((-c) • v) (v ᵥ* JFin m R) (vecMul_JFin_dotProduct_neg_smul v c),
    mem_iff'.mpr (by
      rw [coe_oneSubVecMulVecGL, smul_vecMulVec, neg_smul, sub_neg_eq_add]
      exact one_add_smul_vecMulVec_JFin_mem v c)⟩

/-- The matrix of `τ_{v,c}` in the form `1 - (-c) v (vᵀ J)` of `TauCeti.oneSubVecMulVecGL`. -/
private theorem coe_symplecticTransvection_eq_one_sub (v : Fin (m + m) → R) (c : R) :
    (((symplecticTransvection v c : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R) =
      1 - vecMulVec ((-c) • v) (v ᵥ* JFin m R) :=
  coe_oneSubVecMulVecGL _ _ _ _

/-- The matrix of the symplectic transvection `τ_{v,c}` is `1 + c v (vᵀ J)`. -/
@[simp]
theorem coe_symplecticTransvection (v : Fin (m + m) → R) (c : R) :
    (((symplecticTransvection v c : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R) =
      1 + c • vecMulVec v (v ᵥ* JFin m R) := by
  rw [coe_symplecticTransvection_eq_one_sub, smul_vecMulVec, neg_smul, sub_neg_eq_add]

/-- The symplectic transvection `τ_{v,c}` sends `x` to `x + c ω(v, x) v`. -/
theorem coe_symplecticTransvection_mulVec (v : Fin (m + m) → R) (c : R)
    (x : Fin (m + m) → R) :
    (((symplecticTransvection v c : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R) *ᵥ x =
      x + (c * (v ⬝ᵥ (JFin m R *ᵥ x))) • v := by
  rw [coe_symplecticTransvection, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, ← dotProduct_mulVec, smul_smul]

/-- As a linear map, the symplectic transvection `τ_{v,c}` is Mathlib's transvection
`x ↦ x + f x • v` for the linear form `f = c ω(v, ·)`. -/
theorem toLin'_symplecticTransvection (v : Fin (m + m) → R) (c : R) :
    toLin' (((symplecticTransvection v c : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R) =
      LinearMap.transvection (c • toBilin' (JFin m R) v) v := by
  refine LinearMap.ext fun x ↦ ?_
  rw [toLin'_apply, coe_symplecticTransvection_mulVec, LinearMap.transvection.apply,
    LinearMap.smul_apply, toBilin'_apply', smul_eq_mul]

/-- The transvection with parameter zero is the identity. -/
@[simp]
theorem symplecticTransvection_zero_right (v : Fin (m + m) → R) :
    symplecticTransvection v (0 : R) = 1 :=
  Subtype.ext <| Units.ext <| by simp

/-- The transvection along the zero vector is the identity. -/
@[simp]
theorem symplecticTransvection_zero_left (c : R) :
    symplecticTransvection (0 : Fin (m + m) → R) c = 1 :=
  Subtype.ext <| Units.ext <| by simp

/-- Adding parameters multiplies transvections along the same vector. -/
@[simp]
theorem symplecticTransvection_add (v : Fin (m + m) → R) (a b : R) :
    symplecticTransvection v (a + b) = symplecticTransvection v a * symplecticTransvection v b :=
  Subtype.ext <| Units.ext <| by
    rw [Subgroup.coe_mul, Units.val_mul, coe_symplecticTransvection_eq_one_sub,
      coe_symplecticTransvection_eq_one_sub, coe_symplecticTransvection_eq_one_sub,
      one_sub_vecMulVec_mul_one_sub_vecMulVec, dotProduct_smul, ← dotProduct_mulVec,
      dotProduct_JFin_mulVec_self, smul_zero, zero_smul, add_zero, neg_add, add_smul,
      add_vecMulVec, sub_add_eq_sub_sub]

/-- Inverting a transvection negates its parameter. -/
@[simp]
theorem symplecticTransvection_inv (v : Fin (m + m) → R) (c : R) :
    (symplecticTransvection v c)⁻¹ = symplecticTransvection v (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← symplecticTransvection_add, add_neg_cancel,
    symplecticTransvection_zero_right]

/-- **Rescaling the vector of a transvection** multiplies the parameter by the square of the
scalar: `τ_{a v,c} = τ_{v,a²c}`. -/
theorem symplecticTransvection_smul (a : R) (v : Fin (m + m) → R) (c : R) :
    symplecticTransvection (a • v) c = symplecticTransvection v (a ^ 2 * c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_symplecticTransvection, coe_symplecticTransvection, smul_vecMul, smul_vecMulVec,
    vecMulVec_smul, smul_smul, smul_smul, sq, mul_comm (a * a) c, mul_assoc]

/-- The symplectic transvections along a vector form a one-parameter subgroup. -/
def symplecticTransvectionHom (v : Fin (m + m) → R) : Multiplicative R →* GLSymplecticFin m R where
  toFun c := symplecticTransvection v c.toAdd
  map_one' := symplecticTransvection_zero_right v
  map_mul' a b := symplecticTransvection_add v a.toAdd b.toAdd

/-- The one-parameter subgroup of transvections along `v` sends `c` to `τ_{v,c}`. -/
@[simp]
theorem symplecticTransvectionHom_apply (v : Fin (m + m) → R) (c : Multiplicative R) :
    symplecticTransvectionHom v c = symplecticTransvection v c.toAdd :=
  (rfl)

/-- Rescaling the vector by a nonzero scalar does not change the group of transvections along it. -/
theorem range_symplecticTransvectionHom_smul {K : Type u} [Field K] {a : K} (ha : a ≠ 0)
    (v : Fin (m + m) → K) :
    (symplecticTransvectionHom (a • v)).range = (symplecticTransvectionHom v).range := by
  ext g
  simp only [MonoidHom.mem_range, symplecticTransvectionHom_apply, symplecticTransvection_smul]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd (a ^ 2 * c.toAdd), rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd ((a ^ 2)⁻¹ * c.toAdd), ?_⟩
    rw [toAdd_ofAdd, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha), one_mul]

/-- **Conjugating a symplectic transvection** by a symplectic matrix `g` moves its vector by `g`:
`g τ_{v,c} g⁻¹ = τ_{g v,c}`. -/
theorem mul_symplecticTransvection_mul_inv (g : GLSymplecticFin m R) (v : Fin (m + m) → R)
    (c : R) :
    g * symplecticTransvection v c * g⁻¹ =
      symplecticTransvection (((g : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R) *ᵥ
        v) c := by
  obtain ⟨G, hg⟩ := g
  -- The symplectic condition `Gᵀ J G = J` rewrites `Gᵀ J` as `J G⁻¹`.
  have hG : (G : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ * JFin m R =
      JFin m R * ((G⁻¹ : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R) := by
    conv_rhs => rw [← mem_iff'.mp hg]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  have hrow : (v ᵥ* JFin m R) ᵥ* ((G⁻¹ : GL (Fin (m + m)) R) :
      Matrix (Fin (m + m)) (Fin (m + m)) R) =
      ((G : Matrix (Fin (m + m)) (Fin (m + m)) R) *ᵥ v) ᵥ* JFin m R := by
    rw [vecMul_vecMul, ← hG, ← vecMul_vecMul, vecMul_transpose]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_symplecticTransvection]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_smul_comm, smul_mul_assoc, mul_vecMulVec, vecMulVec_mul, hrow]

/-! ### Root elements as products of transvections -/

/-- The row of `J` at an upper coordinate. -/
private theorem single_inl_vecMul_JFin (i : Fin m) :
    Pi.single (finSumFinEquiv (Sum.inl i)) (1 : R) ᵥ* JFin m R =
      -Pi.single (finSumFinEquiv (Sum.inr i)) 1 := by
  ext b
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  rw [single_one_vecMul, row_apply, JFin_eq_submatrix m R, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Pi.neg_apply, Pi.single_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  cases b <;> simp [J, one_apply, eq_comm]

/-- The row of `J` at a lower coordinate. -/
private theorem single_inr_vecMul_JFin (i : Fin m) :
    Pi.single (finSumFinEquiv (Sum.inr i)) (1 : R) ᵥ* JFin m R =
      Pi.single (finSumFinEquiv (Sum.inl i)) 1 := by
  ext b
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  rw [single_one_vecMul, row_apply, JFin_eq_submatrix m R, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Pi.single_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  cases b <;> simp [J, one_apply, eq_comm]

/-- The positive long-root element `x_{2eᵢ}(c)` is the transvection along the `i`-th upper
coordinate vector with parameter `-c`. -/
theorem positiveLongRootTransvectionUnit_eq_symplecticTransvection (i : Fin m) (c : R) :
    positiveLongRootTransvectionUnit i c =
      symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inl i)) 1) (-c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_positiveLongRootTransvectionUnit, coe_transvectionUnit_eq_one_add_single,
    coe_symplecticTransvection, single_inl_vecMul_JFin, vecMulVec_neg, smul_neg, ← neg_smul,
    neg_neg, smul_vecMulVec_single_single]

/-- The negative long-root element `x_{-2eᵢ}(c)` is the transvection along the `i`-th lower
coordinate vector with parameter `c`. -/
theorem negativeLongRootTransvectionUnit_eq_symplecticTransvection (i : Fin m) (c : R) :
    negativeLongRootTransvectionUnit i c =
      symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inr i)) 1) c := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_negativeLongRootTransvectionUnit, coe_transvectionUnit_eq_one_add_single,
    coe_symplecticTransvection, single_inr_vecMul_JFin, smul_vecMulVec_single_single]

/-- **Three transvections along a totally isotropic plane.** If `ω(u, w) = 0`, then
`τ_{u+w,c} τ_{u,-c} τ_{w,-c} = 1 + c (u (wᵀ J) + w (uᵀ J))`. -/
theorem coe_symplecticTransvection_add_mul_mul {u w : Fin (m + m) → R}
    (huw : u ⬝ᵥ (JFin m R *ᵥ w) = 0) (c : R) :
    (((symplecticTransvection (u + w) c * symplecticTransvection u (-c) *
          symplecticTransvection w (-c) : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R) =
      1 + c • (vecMulVec u (w ᵥ* JFin m R) + vecMulVec w (u ᵥ* JFin m R)) := by
  have hwu : w ⬝ᵥ (JFin m R *ᵥ u) = 0 := by rw [dotProduct_JFin_mulVec_eq_neg, huw, neg_zero]
  have huu := dotProduct_JFin_mulVec_self u
  have hww := dotProduct_JFin_mulVec_self w
  set P := vecMulVec u (u ᵥ* JFin m R)
  set Q := vecMulVec w (w ᵥ* JFin m R)
  set X := vecMulVec u (w ᵥ* JFin m R)
  set Y := vecMulVec w (u ᵥ* JFin m R)
  -- All products of the four rank-one pieces vanish, because `u` and `w` span an isotropic plane.
  have hPP : P * P = 0 := vecMulVec_mul_vecMulVec_JFin huu
  have hQP : Q * P = 0 := vecMulVec_mul_vecMulVec_JFin hwu
  have hXP : X * P = 0 := vecMulVec_mul_vecMulVec_JFin hwu
  have hYP : Y * P = 0 := vecMulVec_mul_vecMulVec_JFin huu
  have hQQ : Q * Q = 0 := vecMulVec_mul_vecMulVec_JFin hww
  have hXQ : X * Q = 0 := vecMulVec_mul_vecMulVec_JFin hww
  have hYQ : Y * Q = 0 := vecMulVec_mul_vecMulVec_JFin huw
  have hsum : vecMulVec (u + w) ((u + w) ᵥ* JFin m R) = P + Q + X + Y := by
    rw [add_vecMul, add_vecMulVec, vecMulVec_add, vecMulVec_add]
    abel
  have h1 : (1 + c • (P + Q + X + Y)) * (1 + (-c) • P) = 1 + c • (Q + X + Y) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, smul_mul_smul_comm]
    simp only [Matrix.add_mul, hPP, hQP, hXP, hYP, add_zero, smul_zero]
    module
  have h2 : (1 + c • (Q + X + Y)) * (1 + (-c) • Q) = 1 + c • (X + Y) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, smul_mul_smul_comm]
    simp only [Matrix.add_mul, hQQ, hXQ, hYQ, add_zero, smul_zero]
    module
  simp only [Subgroup.coe_mul, Units.val_mul, coe_symplecticTransvection, hsum]
  exact (congrArg (· * (1 + (-c) • Q)) h1).trans h2

/-- The difference short-root element `x_{eᵢ-eⱼ}(c)` is a product of three transvections, along
the `i`-th upper and `j`-th lower coordinate vectors and their sum. -/
theorem differenceShortRootUnit_eq_symplecticTransvection {i j : Fin m} (hij : i ≠ j) (c : R) :
    differenceShortRootUnit hij c =
      symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inl i)) 1 +
          Pi.single (finSumFinEquiv (Sum.inr j)) 1) c *
        symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inl i)) 1) (-c) *
        symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inr j)) 1) (-c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_differenceShortRootUnit_eq_one_add_single_sub_single,
    coe_symplecticTransvection_add_mul_mul (by
      -- Keep the coordinates as `finSumFinEquiv` images, so that injectivity compares them.
      rw [dotProduct_mulVec, single_inl_vecMul_JFin]
      simp [-finSumFinEquiv_apply_right, hij.symm])]
  simp only [single_inl_vecMul_JFin, single_inr_vecMul_JFin, vecMulVec_neg, smul_add, smul_neg,
    smul_vecMulVec_single_single]
  abel

/-- The positive-sum short-root element `x_{eᵢ+eⱼ}(c)` is a product of three transvections, along
the `i`-th and `j`-th upper coordinate vectors and their sum. -/
theorem positiveSumShortRootUnit_eq_symplecticTransvection {i j : Fin m} (hij : i ≠ j) (c : R) :
    positiveSumShortRootUnit hij c =
      symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inl i)) 1 +
          Pi.single (finSumFinEquiv (Sum.inl j)) 1) (-c) *
        symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inl i)) 1) c *
        symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inl j)) 1) c := by
  refine Subtype.ext (Units.ext ?_)
  -- The isotropic-plane identity with parameter `-c`, whose doubly negated parameters simplify.
  have hprod := coe_symplecticTransvection_add_mul_mul (R := R) (m := m)
    (u := Pi.single (finSumFinEquiv (Sum.inl i)) 1) (w := Pi.single (finSumFinEquiv (Sum.inl j)) 1)
    (by
      rw [dotProduct_mulVec, single_inl_vecMul_JFin]
      simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]) (-c)
  rw [neg_neg] at hprod
  rw [coe_positiveSumShortRootUnit, Units.val_mul, coe_transvectionUnit_eq_one_add_single,
    coe_transvectionUnit_eq_one_add_single,
    one_add_single_mul_one_add_single_of_ne (finSumFinEquiv_inl_ne_inr j j).symm, hprod]
  simp only [single_inl_vecMul_JFin, vecMulVec_neg, smul_add, smul_neg, neg_smul, neg_neg,
    smul_vecMulVec_single_single]
  abel

/-- The negative-sum short-root element `x_{-eᵢ-eⱼ}(c)` is a product of three transvections, along
the `i`-th and `j`-th lower coordinate vectors and their sum. -/
theorem negativeSumShortRootUnit_eq_symplecticTransvection {i j : Fin m} (hij : i ≠ j) (c : R) :
    negativeSumShortRootUnit hij c =
      symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inr i)) 1 +
          Pi.single (finSumFinEquiv (Sum.inr j)) 1) c *
        symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inr i)) 1) (-c) *
        symplecticTransvection (Pi.single (finSumFinEquiv (Sum.inr j)) 1) (-c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_negativeSumShortRootUnit, Units.val_mul, coe_transvectionUnit_eq_one_add_single,
    coe_transvectionUnit_eq_one_add_single,
    one_add_single_mul_one_add_single_of_ne (finSumFinEquiv_inr_ne_inl j j).symm,
    coe_symplecticTransvection_add_mul_mul (by
      rw [dotProduct_mulVec, single_inr_vecMul_JFin]
      simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right])]
  simp only [single_inr_vecMul_JFin, smul_add, smul_vecMulVec_single_single]
  abel

/-- A subgroup containing every symplectic transvection contains every standard root element. -/
theorem RootSubgroupIndex.hom_apply_mem_of_symplecticTransvection_mem
    (H : Subgroup (GLSymplecticFin m R))
    (h : ∀ (v : Fin (m + m) → R) (c : R), symplecticTransvection v c ∈ H)
    (root : RootSubgroupIndex m) (c : Multiplicative R) : root.hom c ∈ H := by
  cases root with
  | positiveLong i =>
      rw [hom_positiveLong, positiveLongRootTransvectionHom_apply,
        positiveLongRootTransvectionUnit_eq_symplecticTransvection]
      exact h _ _
  | negativeLong i =>
      rw [hom_negativeLong, negativeLongRootTransvectionHom_apply,
        negativeLongRootTransvectionUnit_eq_symplecticTransvection]
      exact h _ _
  | difference i j hij =>
      rw [hom_difference, differenceShortRootHom_apply,
        differenceShortRootUnit_eq_symplecticTransvection]
      exact H.mul_mem (H.mul_mem (h _ _) (h _ _)) (h _ _)
  | positiveSum i j hij =>
      rw [hom_positiveSum, positiveSumShortRootHom_apply,
        positiveSumShortRootUnit_eq_symplecticTransvection]
      exact H.mul_mem (H.mul_mem (h _ _) (h _ _)) (h _ _)
  | negativeSum i j hij =>
      rw [hom_negativeSum, negativeSumShortRootHom_apply,
        negativeSumShortRootUnit_eq_symplecticTransvection]
      exact H.mul_mem (H.mul_mem (h _ _) (h _ _)) (h _ _)

/-- **The symplectic transvections generate the symplectic group over a field.** A subgroup of
`Sp_{2m}(K)` containing every symplectic transvection is the whole group. -/
theorem eq_top_of_symplecticTransvection_mem {K : Type u} [Field K]
    (H : Subgroup (GLSymplecticFin m K))
    (h : ∀ (v : Fin (m + m) → K) (c : K), symplecticTransvection v c ∈ H) : H = ⊤ :=
  eq_top_of_root_subgroups H (RootSubgroupIndex.hom_apply_mem_of_symplecticTransvection_mem H h)

end TauCeti.GLSymplecticFin
