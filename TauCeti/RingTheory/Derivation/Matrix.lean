/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Derivations applied entrywise to matrices

A derivation `D` of a commutative algebra `A` acts on matrices over `A` entry by entry, through
`Matrix.map`. This entrywise action satisfies the Leibniz rule for matrix multiplication,
`(M * N).map D = M.map D * N + M * N.map D`, because each entry of a product is a sum of products of
entries.

Consequently, if rectangular matrices `M` and `N` satisfy the linear intertwining (Sylvester)
differential equations `M.map D = M * Q - S * M` and `N.map D = N * P - Q * N`, then their product
`M * N` satisfies `(M * N).map D = (M * N) * P - S * (M * N)`
(`Derivation.map_matrix_mul_of_map_eq_mul_sub_mul`), giving an `R`-submodule
`Derivation.sylvesterSubmodule` of intertwining matrices and an `R`-subalgebra
`Derivation.sylvesterEndSubalgebra` of horizontal endomorphisms. Specializing to `M = N` with
`P = Q = S = -B` shows that if `D` acts on a square matrix `M` as the commutator with `B`, then it
acts on every power `M ^ m` as the commutator with `B` and kills every trace `(M ^ m).trace`.

On the general linear group `GL n A` over a commutative semiring `A`, the Leibniz rule for matrix
products shows that the right logarithmic derivative `D.matrixRightLogDeriv g = g.map D * g⁻¹`
satisfies the nonabelian 1-cocycle law
`D.matrixRightLogDeriv (h * g) = D.matrixRightLogDeriv h + h * D.matrixRightLogDeriv g * h⁻¹`
(`Derivation.matrixRightLogDeriv_mul`). Over a commutative ring `A`, differentiating `g⁻¹ * g = 1`
expresses `(g⁻¹).map D` as `-g⁻¹ * g.map D * g⁻¹` (`Derivation.map_matrix_inv`), feeding
`Derivation.matrixRightLogDeriv_inv` and `Derivation.matrixGauge_inv`. Twisting conjugation by the
right logarithmic derivative defines the left gauge action
`D.matrixGauge g M = g * M * g⁻¹ - g.map D * g⁻¹` of `GL n A` on connection matrices `D + M`, with
stabilizer subgroup `Derivation.matrixGaugeStabilizer`, characterized by the linear differential
equation `g.map D = g * M - N * g` (`Derivation.matrixGauge_eq_iff`) and compatible with base change
along ring homomorphisms intertwining two derivations (`Derivation.map_matrixGauge`).

Finally, let `S` be an `A`-algebra with a basis `b`, and let `D'` be a derivation of `S` extending
`D`, in the sense that `D' (algebraMap A S a) = algebraMap A S (D a)`. Then `D'` acts on
coordinates in `b` as `D` plus the connection matrix `Γ` whose columns are the coordinates of the
`D' (b q)`, and `D` applied entrywise to the matrix of multiplication by `s` gives the matrix of
multiplication by `D' s` plus the commutator of the matrix of `s` with `Γ`.

## Main definitions

* `Derivation.matrixRightLogDeriv`: the right logarithmic derivative `g.map D * g⁻¹` for
  `g : GL n A`.
* `Derivation.sylvesterSubmodule`: the `R`-submodule of rectangular matrices `M : Matrix m n A`
  solving `M.map D = M * P - Q * M`.
* `Derivation.sylvesterEndSubalgebra`: the `R`-subalgebra of square matrices `M : Matrix n n A`
  solving `M.map D = M * P - P * M`.
* `Derivation.matrixGauge`: the left gauge action `g * M * g⁻¹ - g.map D * g⁻¹` of `GL n A` on
  connection matrices `Matrix n n A`.
* `Derivation.matrixGaugeStabilizer`: the stabilizer subgroup of `M` under `Derivation.matrixGauge`.

## Main results

* `Derivation.map_matrix_mul`: the Leibniz rule for the entrywise action on matrix products.
* `Derivation.map_matrix_mul_of_map_eq_mul_sub_mul`: composition of Sylvester-intertwining
  matrices.
* `Derivation.map_matrix_pow_of_map_eq_mul_sub_mul`: if `D` acts on `M` as the commutator with `B`,
  it acts on each power of `M` as the commutator with `B`.
* `Derivation.trace_pow_eq_zero_of_map_eq_mul_sub_mul`: under the same hypothesis, `D` kills the
  traces of the powers of `M`.
* `Derivation.map_matrix_inv`: entrywise derivative of the inverse of `g : GL n A`.
* `Derivation.matrixRightLogDeriv_mul`: the 1-cocycle law for the right logarithmic derivative.
* `Derivation.matrixGauge_one`, `Derivation.matrixGauge_mul`, `Derivation.matrixGauge_inv`,
  `Derivation.matrixGauge_eq_iff`, `Derivation.map_matrixGauge`: group action, frame dictionary,
  Sylvester differential equation characterization, and functoriality of `Derivation.matrixGauge`.
* `Derivation.basis_repr_apply`: the coordinates of `D' x` in a basis, for a derivation `D'`
  extending `D`.
* `Derivation.map_leftMulMatrix`: the entrywise derivative of the matrix of multiplication.
-/

public section

namespace Derivation

variable {R A : Type*} [CommSemiring R]

/-- A derivation applied entrywise to the identity matrix vanishes. -/
@[simp]
theorem map_matrix_one {M n : Type*} [CommSemiring A] [AddCommMonoid M] [Algebra R A]
    [Module A M] [Module R M] [DecidableEq n] (D : Derivation R A M) :
    (1 : Matrix n n A).map D = 0 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

section CommSemiring

variable [CommSemiring A] [Algebra R A] (D : Derivation R A A)

/-- **The Leibniz rule for matrices**: a derivation applied entrywise to a product of matrices is
`M.map D * N + M * N.map D`. -/
theorem map_matrix_mul {l m n : Type*} [Fintype m] (M : Matrix l m A) (N : Matrix m n A) :
    (M * N).map D = M.map D * N + M * N.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, leibniz, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

section RightLogDeriv

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Right logarithmic derivative** `(Dg) g⁻¹` of an invertible matrix `g : GL n A` along a
derivation `D` over a commutative semiring `A`. -/
def matrixRightLogDeriv (g : Matrix.GeneralLinearGroup n A) : Matrix n n A :=
  (g : Matrix n n A).map D * (↑g⁻¹ : Matrix n n A)

theorem matrixRightLogDeriv_def (g : Matrix.GeneralLinearGroup n A) :
    D.matrixRightLogDeriv g = (g : Matrix n n A).map D * (↑g⁻¹ : Matrix n n A) :=
  (rfl)

@[simp]
theorem matrixRightLogDeriv_mul_coe (g : Matrix.GeneralLinearGroup n A) :
    D.matrixRightLogDeriv g * (g : Matrix n n A) = (g : Matrix n n A).map D := by
  simp [matrixRightLogDeriv_def]

@[simp]
theorem matrixRightLogDeriv_one :
    D.matrixRightLogDeriv (1 : Matrix.GeneralLinearGroup n A) = 0 := by
  simp [matrixRightLogDeriv_def]

/-- **Nonabelian 1-cocycle law for the right logarithmic derivative**:
`(D(h g)) (h g)⁻¹ = (Dh) h⁻¹ + h ((Dg) g⁻¹) h⁻¹`. -/
theorem matrixRightLogDeriv_mul (h g : Matrix.GeneralLinearGroup n A) :
    D.matrixRightLogDeriv (h * g) =
      D.matrixRightLogDeriv h + (h : Matrix n n A) * D.matrixRightLogDeriv g *
        (↑h⁻¹ : Matrix n n A) := by
  simp [matrixRightLogDeriv_def, map_matrix_mul, add_mul, Matrix.mul_assoc]

@[simp]
theorem matrixRightLogDeriv_scalar (u : Aˣ) :
    D.matrixRightLogDeriv (Matrix.GeneralLinearGroup.scalar n u) =
      Matrix.scalar n (D u * ↑u⁻¹) := by
  rw [matrixRightLogDeriv_def, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar]
  have hsc : (Matrix.scalar n (u : A)).map D = Matrix.scalar n (D u) := by
    simp [Matrix.scalar_apply]
  rw [hsc, ← map_mul]

end RightLogDeriv

end CommSemiring

variable [CommRing A] [Algebra R A] (D : Derivation R A A)
  {n : Type*} [Fintype n] [DecidableEq n]

/-- If a derivation acts on a square matrix `M` as the commutator with `B`, then it acts on every
power of `M` as the commutator with `B`. -/
theorem map_matrix_pow_of_map_eq_mul_sub_mul {M B : Matrix n n A} (h : M.map D = B * M - M * B)
    (m : ℕ) : (M ^ m).map D = B * M ^ m - M ^ m * B := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, map_matrix_mul, ih, h]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel

/-- If a derivation acts on a square matrix `M` as the commutator with `B`, then it kills the
trace of every power of `M`. -/
theorem trace_pow_eq_zero_of_map_eq_mul_sub_mul {M B : Matrix n n A}
    (h : M.map D = B * M - M * B) (m : ℕ) : D (M ^ m).trace = 0 := by
  rw [AddMonoidHom.map_trace, map_matrix_pow_of_map_eq_mul_sub_mul D h, Matrix.trace_sub,
    Matrix.trace_mul_comm, sub_self]

section Gauge

/-- **Entrywise derivative of an invertible matrix.** Differentiating `g⁻¹ * g = 1` yields
`(g⁻¹).map D = -g⁻¹ * g.map D * g⁻¹`. -/
theorem map_matrix_inv (g : Matrix.GeneralLinearGroup n A) :
    (↑g⁻¹ : Matrix n n A).map D = -(↑g⁻¹ : Matrix n n A) * (g : Matrix n n A).map D *
      (↑g⁻¹ : Matrix n n A) := by
  have h : ((↑g⁻¹ : Matrix n n A) * (g : Matrix n n A)).map D = 0 := by simp
  rw [map_matrix_mul] at h
  calc
    (↑g⁻¹ : Matrix n n A).map D =
        (↑g⁻¹ : Matrix n n A).map D * (g : Matrix n n A) * (↑g⁻¹ : Matrix n n A) := by
      simp [Matrix.mul_assoc]
    _ = -((↑g⁻¹ : Matrix n n A) * (g : Matrix n n A).map D) * (↑g⁻¹ : Matrix n n A) := by
      rw [add_eq_zero_iff_eq_neg.mp h]
    _ = -(↑g⁻¹ : Matrix n n A) * (g : Matrix n n A).map D * (↑g⁻¹ : Matrix n n A) := by simp

theorem matrixRightLogDeriv_inv (g : Matrix.GeneralLinearGroup n A) :
    D.matrixRightLogDeriv g⁻¹ = -(↑g⁻¹ : Matrix n n A) * (g : Matrix n n A).map D := by
  rw [matrixRightLogDeriv_def, map_matrix_inv, inv_inv, Matrix.mul_assoc]
  simp

/-- **Left gauge action on connection matrices along a derivation.** For `g : GL n A` and a
connection matrix `M : Matrix n n A` representing the connection operator `D + M`, changing frame
by `g` produces `g * M * g⁻¹ - g.map D * g⁻¹`. -/
def matrixGauge (g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) : Matrix n n A :=
  (g : Matrix n n A) * M * (↑g⁻¹ : Matrix n n A) -
    (g : Matrix n n A).map D * (↑g⁻¹ : Matrix n n A)

theorem matrixGauge_def (g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) :
    D.matrixGauge g M =
      (g : Matrix n n A) * M * (↑g⁻¹ : Matrix n n A) -
        (g : Matrix n n A).map D * (↑g⁻¹ : Matrix n n A) :=
  (rfl)

theorem matrixGauge_eq_conj_sub_matrixRightLogDeriv (g : Matrix.GeneralLinearGroup n A)
    (M : Matrix n n A) :
    D.matrixGauge g M = (g : Matrix n n A) * M * (↑g⁻¹ : Matrix n n A) - D.matrixRightLogDeriv g :=
  (rfl)

@[simp]
theorem matrixGauge_zero (g : Matrix.GeneralLinearGroup n A) :
    D.matrixGauge g 0 = -D.matrixRightLogDeriv g := by
  simp [matrixGauge_eq_conj_sub_matrixRightLogDeriv]

/-- The identity matrix acts trivially under `Derivation.matrixGauge`. -/
@[simp]
theorem matrixGauge_one (M : Matrix n n A) :
    D.matrixGauge (1 : Matrix.GeneralLinearGroup n A) M = M := by
  simp [matrixGauge_def]

/-- **Left group action law for `Derivation.matrixGauge`**:
`D.matrixGauge (h * g) M = D.matrixGauge h (D.matrixGauge g M)`. -/
theorem matrixGauge_mul (h g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) :
    D.matrixGauge (h * g) M = D.matrixGauge h (D.matrixGauge g M) := by
  simp only [matrixGauge_eq_conj_sub_matrixRightLogDeriv, matrixRightLogDeriv_mul, Units.val_mul,
    mul_inv_rev, mul_sub, sub_mul, Matrix.mul_assoc]
  abel

@[simp]
theorem matrixGauge_inv_matrixGauge (g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) :
    D.matrixGauge g⁻¹ (D.matrixGauge g M) = M := by
  rw [← matrixGauge_mul, inv_mul_cancel, matrixGauge_one]

@[simp]
theorem matrixGauge_matrixGauge_inv (g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) :
    D.matrixGauge g (D.matrixGauge g⁻¹ M) = M := by
  rw [← matrixGauge_mul, mul_inv_cancel, matrixGauge_one]

/-- **Frame dictionary**: rewriting in terms of `g⁻¹` converts `g⁻¹ M g + g⁻¹ (Dg)` into the left
gauge action of `g⁻¹` on `M`. -/
theorem matrixGauge_inv (g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) :
    D.matrixGauge g⁻¹ M =
      (↑g⁻¹ : Matrix n n A) * M * (g : Matrix n n A) +
        (↑g⁻¹ : Matrix n n A) * (g : Matrix n n A).map D := by
  rw [matrixGauge_eq_conj_sub_matrixRightLogDeriv, inv_inv, matrixRightLogDeriv_inv, neg_mul,
    sub_neg_eq_add]

theorem matrixGauge_inv_eq_iff {g : Matrix.GeneralLinearGroup n A} {M N : Matrix n n A} :
    D.matrixGauge g⁻¹ N = M ↔ D.matrixGauge g M = N :=
  ⟨fun h ↦ by rw [← h, matrixGauge_matrixGauge_inv],
    fun h ↦ by rw [← h, matrixGauge_inv_matrixGauge]⟩

/-- **Linear differential equation characterization of a gauge transformation**: `g` gauges `M` to
`N` if and only if `g` satisfies the Sylvester differential equation `g.map D = g * M - N * g`. -/
theorem matrixGauge_eq_iff {g : Matrix.GeneralLinearGroup n A} {M N : Matrix n n A} :
    D.matrixGauge g M = N ↔
      (g : Matrix n n A).map D = (g : Matrix n n A) * M - N * (g : Matrix n n A) := by
  constructor
  · intro h
    have hmul := congrArg (· * (g : Matrix n n A)) h
    simp only [matrixGauge_def, sub_mul, Matrix.mul_assoc, Units.inv_mul, mul_one] at hmul
    rw [sub_eq_iff_eq_add] at hmul
    rw [hmul]
    abel
  · intro h
    rw [matrixGauge_def, h, sub_mul]
    simp [Matrix.mul_assoc]

/-- **Functoriality of `Derivation.matrixGauge`** along any ring homomorphism intertwining two
derivations. -/
theorem map_matrixGauge {R' B : Type*} [CommSemiring R'] [CommRing B] [Algebra R' B]
    (D' : Derivation R' B B) {φ : A →+* B} (hφ : ∀ a, φ (D a) = D' (φ a))
    (g : Matrix.GeneralLinearGroup n A) (M : Matrix n n A) :
    (D.matrixGauge g M).map φ = D'.matrixGauge (g.map φ) (M.map φ) := by
  have hmap : ((g : Matrix n n A).map D).map φ = ((g.map φ : Matrix.GeneralLinearGroup n B) :
      Matrix n n B).map D' := by
    ext i j
    simp [hφ]
  have hinv : (↑g⁻¹ : Matrix n n A).map φ = (↑(g.map φ)⁻¹ : Matrix n n B) := by
    rw [← (Matrix.GeneralLinearGroup.map φ).map_inv, Matrix.GeneralLinearGroup.val_map_apply]
  rw [matrixGauge_def, matrixGauge_def, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
    Matrix.map_mul, Matrix.map_mul, hmap, hinv, Matrix.GeneralLinearGroup.val_map_apply]

/-- **Stabilizer subgroup** of a connection matrix `M` under `Derivation.matrixGauge`. -/
def matrixGaugeStabilizer (M : Matrix n n A) : Subgroup (Matrix.GeneralLinearGroup n A) where
  carrier := {g | D.matrixGauge g M = M}
  mul_mem' {h g} hh hg := by rw [Set.mem_ofPred_eq, matrixGauge_mul, hg, hh]
  one_mem' := D.matrixGauge_one M
  inv_mem' {g} hg := D.matrixGauge_inv_eq_iff.mpr hg

@[simp]
theorem mem_matrixGaugeStabilizer_iff {M : Matrix n n A} {g : Matrix.GeneralLinearGroup n A} :
    g ∈ D.matrixGaugeStabilizer M ↔ D.matrixGauge g M = M :=
  Iff.rfl

end Gauge

section Basis

variable {R' S : Type*} [CommSemiring R'] [CommRing S] [Algebra A S] [Algebra R' S]
  (D' : Derivation R' S S) (hD : ∀ a, D' (algebraMap A S a) = algebraMap A S (D a))

include hD

/-- In a basis `b`, the coordinates of `D' x` are the derivatives of the coordinates of `x` plus
the connection term `∑ r, b.repr x r * b.repr (D' (b r)) p`. -/
theorem basis_repr_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι A S) (x : S) (p : ι) :
    b.repr (D' x) p = D (b.repr x p) + ∑ r, b.repr x r * b.repr (D' (b r)) p := by
  classical
  have hsmul (c : A) (y : S) : D' (c • y) = c • D' y + D c • y := by
    rw [Algebra.smul_def, leibniz, hD, smul_eq_mul, smul_eq_mul, mul_comm y, ← Algebra.smul_def,
      ← Algebra.smul_def]
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, map_sum, Finset.sum_apply']
  simp only [hsmul, map_add, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [add_comm]

/-- In a basis `b`, the entrywise derivative of the matrix of multiplication by `s` is the matrix
of multiplication by `D' s` plus the commutator of that matrix with the connection matrix of
`D'` in `b`. -/
theorem map_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A S) (s : S) :
    (Algebra.leftMulMatrix b s).map D = Algebra.leftMulMatrix b (D' s) +
      (Algebra.leftMulMatrix b s * (Matrix.of fun p q => b.repr (D' (b q)) p) -
        (Matrix.of fun p q => b.repr (D' (b q)) p) * Algebra.leftMulMatrix b s) := by
  ext p q
  have h := basis_repr_apply D D' hD b (s * b q) p
  rw [leibniz, smul_eq_mul, smul_eq_mul, mul_comm (b q), map_add, Finsupp.add_apply,
    ← Algebra.leftMulMatrix_mulVec_repr] at h
  simp only [← Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct] at h
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.of_apply]
  simp only [mul_comm (Algebra.leftMulMatrix b s _ q)] at h
  linear_combination -h

end Basis

end Derivation
