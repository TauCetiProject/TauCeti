/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Algebra.Polynomial.DivX
public import TauCeti.LinearAlgebra.Matrix.Diagonal
public import TauCeti.LinearAlgebra.Matrix.LastRowTransvection
public import TauCeti.LinearAlgebra.Matrix.SuperdiagonalShift
import Mathlib.Topology.Algebra.Polynomial

/-!
# The companion pencil of a polynomial

Let `A` be a ring, not necessarily commutative, and let `p = ∑ₖ aₖ Xᵏ` be a polynomial over `A` of
degree at most `d`. Its companion pencil at `z : A` is the `(d + 1) × (d + 1)` matrix
`TauCeti.companionPencil d p z` whose first `d` rows are `(…, 1, -z, …)`, with `1` on the
diagonal and `-z` just above it, and whose last row is `(a_d, …, a_1, a_0)`. It is linear in `z`
(`TauCeti.companionPencil_eq_sub_smul`), and it linearizes `p`: there are elementary matrices,
polynomial in `z` and the coefficients, with

`companionPencil d p z = lastRowTransvection d c * diagonal (1, …, 1, p(z)) * (1 - z • N)`

(`TauCeti.companionPencil_eq_mul`). Here `N` is the nilpotent superdiagonal shift, so `1 - z • N`
is upper unitriangular, and `lastRowTransvection d c` adds `cₖ` times row `k` to the last row,
where `cₖ` is the value at `z` of the Horner quotient `divX^[d - k] p`. Evaluation is
`p(z) = ∑ₖ aₖ zᵏ`, with coefficients on the left. Consequently the pencil is invertible exactly
when `p(z)` is (`TauCeti.isUnit_companionPencil_iff`). Over a commutative ring its determinant is
`p(z)` (`TauCeti.det_companionPencil`).

Scaling the off-diagonal entries of both elementary factors by a parameter `t` gives the
elementary row and column homotopy `TauCeti.companionHomotopy` from `diagonal (1, …, 1, p(z))`
at `t = 0` to the companion pencil at `t = 1`. It is invertible for every `t` exactly when `p(z)`
is, it is jointly continuous in `t` and `z`, and like the pencil it is natural for algebra
homomorphisms of the coefficient ring.

In the elementary proof of complex Bott periodicity, `A` is a ring of continuous endomorphisms
of a vector bundle and `p` is a polynomial clutching function over the circle. The pencil
replaces `p` by a clutching function of degree one on the bundle `E^(d+1)`, and the homotopy
identifies it with `p ⊕ 1` without leaving invertible clutching functions.

## References

* M. F. Atiyah and R. Bott, *On the periodicity theorem for complex vector bundles*, Acta Math.
  112 (1964), 229–247, §3, for the linearization of polynomial clutching functions.
* I. Gohberg, P. Lancaster and L. Rodman, *Matrix polynomials*, §1.1, for companion
  linearizations of matrix polynomials.
-/

public section

open Matrix Polynomial

namespace TauCeti

variable {A B : Type*}

section Ring

variable [Ring A] {d : ℕ}

/-- The companion pencil of `p` in degree `d`, evaluated at `z`: the `(d + 1) × (d + 1)` matrix
whose first `d` rows are `(…, 0, 1, -z, 0, …)`, with `1` on the diagonal, and whose last row is
`(p.coeff d, …, p.coeff 1, p.coeff 0)`. -/
def companionPencil (d : ℕ) (p : A[X]) (z : A) : Matrix (Fin (d + 1)) (Fin (d + 1)) A :=
  updateRow (1 - z • superdiagonalShift (d + 1)) (Fin.last d) fun j ↦ p.coeff j.rev

/-- The last row of the companion pencil lists the coefficients of `p` from degree `d` down. -/
@[simp]
theorem companionPencil_last_apply (p : A[X]) (z : A) (j : Fin (d + 1)) :
    companionPencil d p z (Fin.last d) j = p.coeff j.rev := by
  simp [companionPencil]

/-- The first `d` rows of the companion pencil carry `1` on the diagonal and `-z` just above
it. -/
@[simp]
theorem companionPencil_castSucc_apply (p : A[X]) (z : A) (i : Fin d) (j : Fin (d + 1)) :
    companionPencil d p z i.castSucc j =
      (if i.castSucc = j then 1 else 0) - if j = i.succ then z else 0 := by
  rw [companionPencil, updateRow_ne (Fin.castSucc_ne_last i)]
  simp [superdiagonalShift_apply, one_apply, Fin.ext_iff]

/-- The companion pencil is a linear pencil in `z`: its value at `z` is its value at `0` minus
`z` times the superdiagonal shift. -/
theorem companionPencil_eq_sub_smul (p : A[X]) (z : A) :
    companionPencil d p z = companionPencil d p 0 - z • superdiagonalShift (d + 1) := by
  ext i j
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [companionPencil, updateRow_apply, Fin.castSucc_ne_last]

/-- The values at `z` of the Horner quotients `divX^[d - k] p`, the multipliers of the row
operations which bring the companion pencil to diagonal form. -/
private theorem snoc_eval_iterate_divX (p : A[X]) (z : A) :
    Fin.snoc (α := fun _ ↦ A) (fun k : Fin d ↦ (divX^[d - k] p).eval z) (p.eval z) =
      fun j ↦ (divX^[(j.rev : ℕ)] p).eval z := by
  ext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j =>
    rw [Fin.snoc_castSucc, Fin.val_rev, Fin.val_castSucc,
      show d + 1 - ((j : ℕ) + 1) = d - j by omega]

/-- **The elementary factorization of the companion pencil.** For a polynomial of degree at most
`d`, the companion pencil is `diagonal (1, …, 1, p(z))` multiplied on the left by the elementary
row operations with multipliers `(divX^[d - k] p)(z)` and on the right by the upper
unitriangular matrix `1 - z • N`. -/
theorem companionPencil_eq_mul {p : A[X]} (hp : p.natDegree ≤ d) (z : A) :
    companionPencil d p z =
      lastRowTransvection d (fun k ↦ (divX^[d - k] p).eval z) *
        diagonal (Fin.snoc (α := fun _ ↦ A) 1 (p.eval z)) *
        (1 - z • superdiagonalShift (d + 1)) := by
  rw [lastRowTransvection_mul_diagonal, updateRow_mul, one_mul, companionPencil,
    snoc_eval_iterate_divX]
  congr 1
  ext j
  rw [vecMul_sub, vecMul_one, Pi.sub_apply]
  induction j using Fin.cases with
  | zero =>
    rw [vecMul_smul_superdiagonalShift_zero, sub_zero, Fin.val_rev, Fin.val_zero,
      Nat.add_sub_cancel, iterate_divX_eq_C_of_natDegree_le hp, eval_C]
  | succ j =>
    have hrev : (j.castSucc.rev : ℕ) = (j.succ.rev : ℕ) + 1 := by
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [vecMul_smul_superdiagonalShift_succ, hrev,
      ← iterate_divX_succ_mul_X_add_C (j.succ.rev : ℕ) p, eval_add, eval_mul_X, eval_C,
      add_sub_cancel_left]

/-- **Invertibility of the companion pencil.** For a polynomial of degree at most `d`, the
companion pencil at `z` is invertible exactly when `p(z)` is. -/
theorem isUnit_companionPencil_iff {p : A[X]} (hp : p.natDegree ≤ d) (z : A) :
    IsUnit (companionPencil d p z) ↔ IsUnit (p.eval z) := by
  rw [companionPencil_eq_mul hp, (isUnit_one_sub_smul_superdiagonalShift _ _).mul_right_iff,
    (isUnit_lastRowTransvection _).mul_left_iff, isUnit_diagonal_snoc_one_iff]

/-- The companion pencil is natural for ring homomorphisms of the coefficients. -/
theorem companionPencil_map [Ring B] (f : A →+* B) (p : A[X]) (z : A) :
    (companionPencil d p z).map f = companionPencil d (p.map f) (f z) := by
  ext i j
  induction i using Fin.lastCases with
  | last => simp
  | cast i =>
    rw [map_apply, companionPencil_castSucc_apply, companionPencil_castSucc_apply]
    simp [apply_ite f]

section Homotopy

variable {R : Type*} [CommSemiring R] [Algebra R A]

/-- The elementary row and column homotopy from `diagonal (1, …, 1, p(z))` to the companion
pencil: the off-diagonal entries of both elementary factors of `TauCeti.companionPencil_eq_mul`
are multiplied by `t`. It is `diagonal (1, …, 1, p(z))` at `t = 0` for every `p`, and the
companion pencil at `t = 1` when `p.natDegree ≤ d` (`TauCeti.companionHomotopy_one`). -/
noncomputable def companionHomotopy (d : ℕ) (p : A[X]) (z : A) (t : R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) A :=
  lastRowTransvection d (fun k ↦ t • (divX^[d - k] p).eval z) *
    diagonal (Fin.snoc (α := fun _ ↦ A) 1 (p.eval z)) *
    (1 - (t • z) • superdiagonalShift (d + 1))

/-- The homotopy at an arbitrary parameter `t`, as a product of the scaled elementary factors. -/
theorem companionHomotopy_def (p : A[X]) (z : A) (t : R) :
    companionHomotopy d p z t =
      lastRowTransvection d (fun k ↦ t • (divX^[d - k] p).eval z) *
        diagonal (Fin.snoc (α := fun _ ↦ A) 1 (p.eval z)) *
        (1 - (t • z) • superdiagonalShift (d + 1)) := by
  rw [companionHomotopy]

/-- At `t = 0` the homotopy is `diagonal (1, …, 1, p(z))`. -/
@[simp]
theorem companionHomotopy_zero (p : A[X]) (z : A) :
    companionHomotopy d p z (0 : R) = diagonal (Fin.snoc (α := fun _ ↦ A) 1 (p.eval z)) := by
  simp [companionHomotopy, ← Pi.zero_def]

/-- At `t = 1` the homotopy is the companion pencil. -/
@[simp]
theorem companionHomotopy_one {p : A[X]} (hp : p.natDegree ≤ d) (z : A) :
    companionHomotopy d p z (1 : R) = companionPencil d p z := by
  simp only [companionHomotopy, one_smul]
  exact (companionPencil_eq_mul hp z).symm

/-- Every stage of the homotopy is invertible exactly when `p(z)` is. -/
theorem isUnit_companionHomotopy_iff (p : A[X]) (z : A) (t : R) :
    IsUnit (companionHomotopy d p z t) ↔ IsUnit (p.eval z) := by
  rw [companionHomotopy, (isUnit_one_sub_smul_superdiagonalShift _ _).mul_right_iff,
    (isUnit_lastRowTransvection _).mul_left_iff, isUnit_diagonal_snoc_one_iff]

/-- The homotopy is jointly continuous in the parameter `t` and the point `z`. -/
theorem continuous_companionHomotopy [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace R] [ContinuousSMul R A] (p : A[X]) :
    Continuous fun q : R × A ↦ companionHomotopy d p q.2 q.1 := by
  unfold companionHomotopy
  simp only [lastRowTransvection_def]
  refine ((continuous_const.matrix_updateRow (Fin.last d)
    ((continuous_pi fun k : Fin d ↦ continuous_fst.smul
      ((divX^[d - (k : ℕ)] p).continuous.comp continuous_snd)).finSnoc continuous_const)).mul
    (Continuous.matrix_diagonal (continuous_const.finSnoc
      (p.continuous.comp continuous_snd)))).mul ?_
  exact continuous_const.sub ((continuous_fst.smul continuous_snd).smul continuous_const)

/-- The homotopy is natural for algebra homomorphisms of the coefficients. -/
theorem companionHomotopy_map [Ring B] [Algebra R B] (f : A →ₐ[R] B) (p : A[X]) (z : A)
    (t : R) :
    (companionHomotopy d p z t).map f = companionHomotopy d (p.map (f : A →+* B)) (f z) t := by
  have hdivX (m : ℕ) : divX^[m] (p.map (f : A →+* B)) = (divX^[m] p).map (f : A →+* B) := by
    ext n
    simp
  have heval (q : A[X]) : (q.map (f : A →+* B)).eval (f z) = f (q.eval z) :=
    eval_map_apply (f : A →+* B) z
  simp only [companionHomotopy, Matrix.map_mul, hdivX, heval]
  congr 2
  · rw [lastRowTransvection_def, lastRowTransvection_def, map_updateRow,
      Matrix.map_one _ (map_zero f) (map_one f), Fin.comp_snoc, map_one]
    congr 2
    ext k
    simp
  · rw [diagonal_map (map_zero f), ← Function.comp_def, Fin.comp_snoc, Pi.comp_one, map_one,
      Function.const_one]
  · ext i j
    simp [superdiagonalShift_apply, one_apply, apply_ite f]

end Homotopy

end Ring

section CommRing

variable [CommRing A] {d : ℕ}

/-- Over a commutative ring, the determinant of the companion pencil of a polynomial of degree at
most `d` is the value of the polynomial. -/
theorem det_companionPencil {p : A[X]} (hp : p.natDegree ≤ d) (z : A) :
    (companionPencil d p z).det = p.eval z := by
  have hlow : (lastRowTransvection d fun k ↦ (divX^[d - k] p).eval z).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    rw [lastRowTransvection_apply]
    split_ifs with hi
    · exact absurd hij' (hi ▸ not_lt.2 (Fin.le_last j))
    · exact one_apply_ne hij'.ne
  rw [companionPencil_eq_mul hp, det_mul, det_mul,
    (isUpperUnitriangular_one_sub_smul_superdiagonalShift _ _).det_eq_one,
    det_of_isLowerTriangular _ hlow, det_diagonal, Fin.prod_univ_castSucc,
    Fin.prod_univ_castSucc]
  simp [lastRowTransvection_apply, Fin.castSucc_ne_last]

end CommRing

end TauCeti
