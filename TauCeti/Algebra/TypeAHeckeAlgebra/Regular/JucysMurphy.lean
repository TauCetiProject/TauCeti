/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Matrix
public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.GroupAlgebra

/-!
# Continuous additive Jucys–Murphy matrices

The additive Jucys–Murphy operators on the regular type-A Hecke module are realized on
one fixed permutation-indexed carrier. With `G_i(s)` the matrix of `g_i = s T_i`, their
recursion is `A_0(s) = 0` and
`A_(i+1)(s) = s⁻² (G_i(s) A_i(s) G_i(s) + G_i(s))`.
At a unit parameter these are exactly the matrices of left multiplication by the additive
Jucys–Murphy elements in PBW coordinates. For nonzero real parameters these coordinates
are orthonormal for the canonical trace form.

These matrices are symmetric, commute pairwise, and commute with the right regular
action. Their entries depend continuously on `Q > 0` at `s = √Q`, including through
`Q = 1`. In particular no division by `Q - 1` is used. This supplies continuous commuting
self-adjoint operators for spectral projection constructions; it does not identify their
spectrum with tableau contents. At parameter `1`, the matrix entries are explicitly
identified with left multiplication by the ordinary sums of transpositions.

## References

* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Chapter 3.

The multiplication comparison uses `TauCeti.TypeAHeckeAlgebra.additiveJucysMurphy` and
`CoxeterSystem.heckeLeftMatrix_eq_leftMulMatrix`.
-/

public section

open Matrix

namespace CoxeterSystem

open TauCeti TypeAHeckeAlgebra

variable {R : Type*} [Field R] {W : Type*} [Group W] [Fintype W] {n : ℕ}
variable (cs : CoxeterSystem (CoxeterMatrix.A n) W)

/-- Fixed-carrier matrices of the additive Jucys–Murphy elements, defined recursively
without a denominator `s² - 1`. Strand indices start at zero. -/
noncomputable def additiveJucysMurphyMatrix (s : R) : Fin (n + 1) → Matrix W W R :=
  Fin.induction 0 fun i A =>
    (s⁻¹ ^ 2) • (heckeLeftMatrix cs s i * A * heckeLeftMatrix cs s i +
      heckeLeftMatrix cs s i)

/-- The first additive Jucys–Murphy matrix is zero. -/
@[simp]
theorem additiveJucysMurphyMatrix_zero (s : R) :
    additiveJucysMurphyMatrix cs s 0 = 0 := by
  simp [additiveJucysMurphyMatrix]

/-- The fixed-carrier additive recurrence in the `g_i = s T_i` convention. -/
theorem additiveJucysMurphyMatrix_succ (s : R) (i : Fin n) :
    additiveJucysMurphyMatrix cs s i.succ =
      (s⁻¹ ^ 2) • (heckeLeftMatrix cs s i *
        additiveJucysMurphyMatrix cs s i.castSucc * heckeLeftMatrix cs s i +
          heckeLeftMatrix cs s i) := by
  simp [additiveJucysMurphyMatrix]

/-- Every additive Jucys–Murphy matrix is symmetric. -/
@[simp]
theorem transpose_additiveJucysMurphyMatrix (s : R) (i : Fin (n + 1)) :
    (additiveJucysMurphyMatrix cs s i)ᵀ = additiveJucysMurphyMatrix cs s i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [additiveJucysMurphyMatrix_succ]
    simp only [transpose_smul, transpose_add, transpose_mul, transpose_heckeLeftMatrix, ih,
      Matrix.mul_assoc]

/-- At a unit parameter the recursive matrix is left multiplication by the actual finite
additive Jucys–Murphy element in PBW coordinates. -/
theorem additiveJucysMurphyMatrix_eq_leftMulMatrix [DecidableEq W] (q : Rˣ)
    (i : Fin (n + 1)) :
    additiveJucysMurphyMatrix cs (q : R) i =
      Algebra.leftMulMatrix (basisTw (n := n + 1) q cs) (additiveJucysMurphy q i) := by
  classical
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hrec : additiveJucysMurphy q i.succ =
        T (n := n + 1) q i * additiveJucysMurphy q i.castSucc * T (n := n + 1) q i +
          (↑q⁻¹ : R) • T (n := n + 1) q i :=
      additiveJucysMurphy_succ (n := n + 1) i.val (by omega)
    rw [additiveJucysMurphyMatrix_succ, ih, hrec]
    simp only [heckeLeftMatrix_eq_leftMulMatrix (n := n + 1), map_add, map_mul, map_smul,
      smul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [← pow_two, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 q.ne_zero), one_smul,
      Units.val_inv_eq_inv_val]
    congr 2
    field_simp

/-- The fixed-coordinate action agrees with left multiplication on every vector. -/
theorem additiveJucysMurphyMatrix_mulVec_repr (q : Rˣ) (i : Fin (n + 1))
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    additiveJucysMurphyMatrix cs (q : R) i *ᵥ (basisTw (n := n + 1) q cs).repr x =
      (basisTw (n := n + 1) q cs).repr (additiveJucysMurphy q i * x) := by
  classical
  rw [additiveJucysMurphyMatrix_eq_leftMulMatrix, Algebra.leftMulMatrix_mulVec_repr]

/-- The additive Jucys–Murphy matrices commute at every unit parameter. -/
theorem commute_additiveJucysMurphyMatrix (q : Rˣ) (i j : Fin (n + 1)) :
    Commute (additiveJucysMurphyMatrix cs (q : R) i)
      (additiveJucysMurphyMatrix cs (q : R) j) := by
  classical
  simpa only [additiveJucysMurphyMatrix_eq_leftMulMatrix] using
    (commute_additiveJucysMurphy (q := q) i j).map
      (Algebra.leftMulMatrix (basisTw (n := n + 1) q cs))

/-- Every additive Jucys–Murphy matrix commutes with right simple multiplication,
as required for simultaneous left/right regular spectral decompositions. -/
theorem commute_additiveJucysMurphyMatrix_heckeRightMatrix (s : R)
    (i : Fin (n + 1)) (j : Fin n) :
    Commute (additiveJucysMurphyMatrix cs s i) (heckeRightMatrix cs s j) := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [additiveJucysMurphyMatrix_succ]
    have h := commute_heckeLeftMatrix_heckeRightMatrix cs s i j
    exact (((h.mul_left ih).mul_left h).add_left h).smul_left _

section Real

/-- On nonzero real parameters the additive regular matrices vary continuously. In
particular both `s = 1` and `s = -1` are regular points of this family. -/
theorem continuousOn_additiveJucysMurphyMatrix (i : Fin (n + 1)) :
    ContinuousOn (fun s : ℝ => additiveJucysMurphyMatrix cs s i) {s | s ≠ 0} := by
  induction i using Fin.induction with
  | zero => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ =>
      (0 : Matrix W W ℝ)) {s | s ≠ 0})
  | succ i ih =>
    simp only [additiveJucysMurphyMatrix_succ]
    exact ((continuousOn_id.inv₀ fun _ h => h).pow 2).smul
      ((((continuous_heckeLeftMatrix cs i).continuousOn.mul ih).mul
        (continuous_heckeLeftMatrix cs i).continuousOn).add
          (continuous_heckeLeftMatrix cs i).continuousOn)

/-- The positive-real additive Jucys–Murphy matrices are continuous through `Q = 1`.
The domain is the entire positive half-line, not a punctured neighborhood of `1`. -/
theorem continuousOn_additiveJucysMurphyMatrix_sqrt (i : Fin (n + 1)) :
    ContinuousOn (fun Q : ℝ => additiveJucysMurphyMatrix cs (Real.sqrt Q) i)
      (Set.Ioi 0) := by
  exact (continuousOn_additiveJucysMurphyMatrix cs i).comp
    Real.continuous_sqrt.continuousOn fun Q hQ => (Real.sqrt_pos.2 hQ).ne'

end Real

end CoxeterSystem

namespace TauCeti.TypeAHeckeAlgebra

/-- At parameter `1`, the entries are those of ordinary left multiplication by the
sum of the transpositions `(j,k)` with `j < k`. Thus the continuous endpoint is the
ordinary symmetric-group Jucys–Murphy operator. -/
theorem additiveJucysMurphyMatrix_one_apply {R : Type*} [Field R] {n : ℕ}
    (k : Fin (n + 1)) (v w : Equiv.Perm (Fin (n + 1))) :
    (permCoxeterSystem (n + 1)).additiveJucysMurphyMatrix (1 : R) k v w =
      ∑ j : Fin k.val,
        if v = Equiv.swap (j.castLE (Nat.le_of_lt k.isLt)) k * w then 1 else 0 := by
  classical
  let cs := permCoxeterSystem (n + 1)
  let e := groupAlgebraEquiv (R := R) cs (q := 1) (by simp)
  have hcoords : (basisTw (1 : Rˣ) cs).repr.toLinearMap =
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp e.toLinearMap := by
    apply (basisTw (1 : Rˣ) cs).ext
    intro u
    have he : e ((basisTw (1 : Rˣ) cs) u) = MonoidAlgebra.single u 1 := by
      simp [e, coe_basisTw]
    simpa only [LinearEquiv.coe_coe, Module.Basis.repr_self, LinearMap.comp_apply,
      AlgEquiv.toLinearMap_apply, MonoidAlgebra.coeffLinearEquiv_apply,
      MonoidAlgebra.coeff_single] using (congrArg MonoidAlgebra.coeff he).symm
  have hc (x : TypeAHeckeAlgebra R 1 (n + 1)) :
      (basisTw (1 : Rˣ) cs).repr x = (e x).coeff := LinearMap.congr_fun hcoords x
  have hmatrix := CoxeterSystem.additiveJucysMurphyMatrix_eq_leftMulMatrix cs (1 : Rˣ) k
  simp only [Units.val_one] at hmatrix
  rw [hmatrix, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [coe_basisTw, hc, map_mul]
  simp only [e, cs, groupAlgebraEquiv_additiveJucysMurphy, groupAlgebraEquiv_Tw,
    Finset.sum_mul, MonoidAlgebra.single_mul_single, inv_one, Units.val_one, mul_one,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  exact Finset.sum_congr rfl fun j _ => by simp only [eq_comm]

end TauCeti.TypeAHeckeAlgebra
