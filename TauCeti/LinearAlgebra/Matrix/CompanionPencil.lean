/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Algebra.Polynomial.DivX
public import TauCeti.LinearAlgebra.Matrix.Diagonal
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Algebra.Polynomial
public import TauCeti.LinearAlgebra.Matrix.Triangular

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

section Shift

variable [Zero A] [One A]

/-- The nilpotent shift matrix of size `n`, with ones on the superdiagonal and zeros elsewhere. -/
def superdiagonalShift (n : ℕ) : Matrix (Fin n) (Fin n) A :=
  of fun i j => if (j : ℕ) = i + 1 then 1 else 0

/-- The entries of the superdiagonal shift. -/
theorem superdiagonalShift_apply (n : ℕ) (i j : Fin n) :
    superdiagonalShift n i j = if (j : ℕ) = i + 1 then (1 : A) else 0 :=
  (rfl)

/-- The last row of the superdiagonal shift vanishes. -/
@[simp]
theorem superdiagonalShift_last_apply (d : ℕ) (j : Fin (d + 1)) :
    superdiagonalShift (d + 1) (Fin.last d) j = (0 : A) := by
  rw [superdiagonalShift_apply, ite_eq_right_iff]
  intro h
  have := j.isLt
  simp only [Fin.val_last] at h
  omega

end Shift

section Ring

variable [Ring A] {d : ℕ}

/-- Subtracting a multiple of the superdiagonal shift from the identity gives an upper
unitriangular matrix. -/
theorem isUpperUnitriangular_one_sub_smul_superdiagonalShift (n : ℕ) (s : A) :
    Matrix.IsUpperUnitriangular (1 - s • superdiagonalShift n : Matrix (Fin n) (Fin n) A) := by
  refine (isUpperUnitriangular_def _).2 ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · have hne : i ≠ j := fun h ↦ (lt_irrefl _ (h ▸ hij))
    have hij' : (j : ℕ) < i := hij
    simp [superdiagonalShift_apply, one_apply, hne, show (j : ℕ) ≠ i + 1 by omega]
  · simp [superdiagonalShift_apply]

/-- Subtracting a multiple of the superdiagonal shift from the identity gives a unit. -/
theorem isUnit_one_sub_smul_superdiagonalShift (n : ℕ) (s : A) :
    IsUnit (1 - s • superdiagonalShift n : Matrix (Fin n) (Fin n) A) := by
  have h := (isUpperUnitriangular_one_sub_smul_superdiagonalShift n s).isNilpotent_sub_one
  rw [← sub_add_cancel (1 - s • superdiagonalShift n) 1]
  exact h.isUnit_add_one

/-- Row multiplication by a multiple of the superdiagonal shift: the first entry vanishes. -/
private theorem vecMul_smul_superdiagonalShift_zero (v : Fin (d + 1) → A) (s : A) :
    (v ᵥ* (s • superdiagonalShift (d + 1))) 0 = 0 := by
  simp [vecMul, dotProduct, superdiagonalShift_apply]

/-- Row multiplication by a multiple of the superdiagonal shift moves each entry one place to
the right. -/
private theorem vecMul_smul_superdiagonalShift_succ (v : Fin (d + 1) → A) (s : A) (j : Fin d) :
    (v ᵥ* (s • superdiagonalShift (d + 1))) j.succ = v j.castSucc * s := by
  simp only [vecMul, dotProduct, Matrix.smul_apply, superdiagonalShift_apply, Fin.val_succ,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_eq_single j.castSucc fun k hk ↦ ite_eq_right_iff.2 fun h ↦ absurd ?_ hk]
  · simp
  · rw [Fin.ext_iff, Fin.val_castSucc]
    omega

/-- The lower unitriangular matrix of size `d + 1` which agrees with the identity except in its
last row, where it is `(b 0, …, b (d - 1), 1)`. Multiplying by it on the left adds `b k` times
row `k` to the last row, for every `k < d`. -/
def lastRowTransvection (d : ℕ) (b : Fin d → A) : Matrix (Fin (d + 1)) (Fin (d + 1)) A :=
  (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) A).updateRow (Fin.last d) (Fin.snoc b 1)

/-- The entries of `lastRowTransvection d b`. -/
theorem lastRowTransvection_apply (b : Fin d → A) (i j : Fin (d + 1)) :
    lastRowTransvection d b i j =
      if i = Fin.last d then Fin.snoc (α := fun _ ↦ A) b 1 j else (1 : Matrix _ _ A) i j := by
  simp [lastRowTransvection, updateRow_apply]

/-- With all multipliers zero, `lastRowTransvection` is the identity. -/
@[simp]
theorem lastRowTransvection_zero : lastRowTransvection d (0 : Fin d → A) = 1 := by
  ext i j
  rw [lastRowTransvection_apply]
  split_ifs with hi
  · subst hi
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [one_apply, (Fin.castSucc_lt_last j).ne']
  · rfl

/-- The row operations `lastRowTransvection` compose by adding their multipliers. -/
theorem lastRowTransvection_mul_lastRowTransvection (b b' : Fin d → A) :
    lastRowTransvection d b * lastRowTransvection d b' = lastRowTransvection d (b + b') := by
  rw [lastRowTransvection, updateRow_mul, one_mul]
  ext i j
  rw [updateRow_apply]
  split_ifs with hi
  · subst hi
    simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      one_mul, lastRowTransvection_apply, Fin.castSucc_ne_last, ↓reduceIte]
    induction j using Fin.lastCases with
    | last => simp [one_apply, Fin.castSucc_ne_last]
    | cast j => simp [one_apply]
  · simp [lastRowTransvection_apply, hi]

/-- The elementary matrices `lastRowTransvection d b` are units, with inverse
`lastRowTransvection d (-b)`. -/
theorem isUnit_lastRowTransvection (b : Fin d → A) : IsUnit (lastRowTransvection d b) :=
  isUnit_iff_exists.2 ⟨lastRowTransvection d (-b), by
    simp [lastRowTransvection_mul_lastRowTransvection]⟩

/-- Right multiplication by `diagonal (1, …, 1, x)` scales the last column by `x`. -/
private theorem lastRowTransvection_mul_diagonal (b : Fin d → A) (x : A) :
    lastRowTransvection d b * diagonal (Fin.snoc (α := fun _ ↦ A) 1 x) =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) A).updateRow (Fin.last d)
        (Fin.snoc (α := fun _ ↦ A) b x) := by
  rw [lastRowTransvection, updateRow_mul, one_mul]
  ext i j
  rw [updateRow_apply, updateRow_apply]
  split_ifs with hi
  · rw [vecMul_diagonal]
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  · induction i using Fin.lastCases with
    | last => exact absurd rfl hi
    | cast i => simp [diagonal_apply, one_apply]

/-- `diagonal (1, …, 1, x)` is a unit exactly when `x` is. -/
private theorem isUnit_diagonal_snoc_one_iff (x : A) :
    IsUnit (diagonal (Fin.snoc (α := fun _ ↦ A) (1 : Fin d → A) x)) ↔ IsUnit x := by
  simp [isUnit_diagonal_iff, Pi.isUnit_iff, Fin.forall_fin_succ']

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
are multiplied by `t`. -/
noncomputable def companionHomotopy (d : ℕ) (p : A[X]) (z : A) (t : R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) A :=
  lastRowTransvection d (fun k ↦ t • (divX^[d - k] p).eval z) *
    diagonal (Fin.snoc (α := fun _ ↦ A) 1 (p.eval z)) *
    (1 - (t • z) • superdiagonalShift (d + 1))

/-- At `t = 0` the homotopy is `diagonal (1, …, 1, p(z))`. -/
@[simp]
theorem companionHomotopy_zero (p : A[X]) (z : A) :
    companionHomotopy d p z (0 : R) = diagonal (Fin.snoc (α := fun _ ↦ A) 1 (p.eval z)) := by
  simp only [companionHomotopy, zero_smul]
  rw [show (fun _ : Fin d ↦ (0 : A)) = 0 from rfl, lastRowTransvection_zero]
  simp

/-- At `t = 1` the homotopy is the companion pencil. -/
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
  unfold companionHomotopy lastRowTransvection
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
  · ext i j
    rw [map_apply, lastRowTransvection_apply, lastRowTransvection_apply]
    split_ifs
    · induction j using Fin.lastCases with
      | last => simp
      | cast j => simp
    · simp [one_apply, apply_ite f]
  · ext i j
    rw [map_apply, diagonal_apply, diagonal_apply]
    split_ifs with h
    · subst h
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp
    · simp
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
