/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Standard
public import TauCeti.QuantumGroups.QuantumInteger.Laurent
public import TauCeti.QuantumGroups.UqSl2.LadderModule

import Mathlib.Tactic

/-!
# The classical specialization of the positive ladder modules of `U_q(sl₂)`

In the ladder basis `v₀, …, v_m`, the positive ladder module `L_m^+` of `UqSl2 q` has matrices
whose entries are Laurent polynomials with integer coefficients in `v`, evaluated at `v = q`:

* `ladderMatrixE m`, with `E v_j = [m - j + 1]_v v_(j - 1)`;
* `ladderMatrixF m`, with `F v_j = [j + 1]_v v_(j + 1)`;
* `ladderMatrixK m`, the diagonal matrix with entries `v^(m - 2j)`;
* `ladderMatrixH m`, the diagonal matrix with entries `[m - 2j]_v`, which at `v = q` is the
  matrix of `E F - F E = (K - K⁻¹) / (q - q⁻¹)`.

Here `[r]_v` is the Laurent quantum integer `TauCeti.laurentQuantumInteger r`. This integral form
describes the whole positive family at once, and it also makes sense at `v = 1`, where the quantum
integers become ordinary integers. There `E`, `F` and `H` become the integer matrices

`E v_j = (m - j + 1) v_(j - 1)`, `F v_j = (j + 1) v_(j + 1)`, `H v_j = (m - 2j) v_j`,

which satisfy the relations of the standard basis of `sl₂`. Over any commutative ring `K` they
therefore define an action of `LieAlgebra.SpecialLinear.sl (Fin 2) K` on `K^(m+1)`, the classical
specialization `ClassicalLadder K m` of `L_m^+`. This is a statement about the matrices of one
family of representations; substituting `q = 1` into the presentation of `UqSl2 q`, whose
commutator relation has the denominator `q - q⁻¹`, does not produce the enveloping algebra of
`sl₂`.

Over a field of characteristic zero the classical specialization is the standard
highest-weight module `V(m) = TauCeti.Sl2Std K m`. The ladder vector `v_j = F^j v₀ / j!` goes to
`(m choose j) w_j`, where `w_j` is the coordinate basis of `V(m)`, in which
`f · w_j = (m - j) w_(j + 1)`; the binomial factors record the two normalizations of the ladder
basis rather than identifying them.

## Main definitions

* `TauCeti.UqSl2.ladderMatrixE`, `ladderMatrixF`, `ladderMatrixK`, `ladderMatrixH`: the integral
  ladder matrices over `ℤ[v, v⁻¹]`.
* `TauCeti.UqSl2.ClassicalLadder K m`: the classical specialization of `L_m^+`, a module over
  `sl (Fin 2) K`.
* `TauCeti.UqSl2.ClassicalLadder.rep`: its action, sending the standard basis `(e, f, h)` of
  `sl (Fin 2) K` to the ladder matrices evaluated at `v = 1`.
* `TauCeti.UqSl2.ClassicalLadder.toSl2Std`: the module map to `V(m)` sending `v_j` to
  `(m choose j) w_j`, and `TauCeti.UqSl2.ClassicalLadder.equivSl2Std` the resulting isomorphism
  over a field of characteristic zero.

## Main results

* `TauCeti.UqSl2.LadderModule.toMatrix_rep_e`, `toMatrix_rep_f`, `toMatrix_rep_k`,
  `toMatrix_rep_e_mul_f_sub_f_mul_e`: the matrices of `E`, `F`, `K` and `E F - F E` on `L_m^+` are
  the integral ladder matrices evaluated at `v = q`.
* `TauCeti.UqSl2.map_laurentEval_one_ladderMatrixE` and its companions: the integral ladder
  matrices at `v = 1`.
* `TauCeti.UqSl2.ClassicalLadder.isSl2Triple`: for `m ≠ 0` in `K`, the specialized matrices
  `(H, E, F)` form an `sl₂` triple.
* `TauCeti.UqSl2.ClassicalLadder.toSl2Std_basis`: the module map sends `v_j` to
  `(m choose j) w_j`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.3, for the modules
  `V_(ε,n)`.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, Chapter 2, for
  the finite-dimensional modules of `U_q(sl₂)`.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 7.2, for the
  classical highest-weight modules.
-/

public section

open LaurentPolynomial LieAlgebra Module

namespace TauCeti

namespace UqSl2

/-! ### The integral ladder matrices -/

variable (m : ℕ)

/-- The matrix of `E` on the positive ladder module, over `ℤ[v, v⁻¹]`:
`E v_j = [m - j + 1]_v v_(j - 1)`, so the only nonzero entries are `[m - i]_v` at the positions
`(i, i + 1)`. -/
noncomputable def ladderMatrixE : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ[T;T⁻¹] :=
  Matrix.of fun i j => if (j : ℕ) = i + 1 then laurentQuantumInteger (m - i) else 0

/-- The matrix of `F` on the positive ladder module, over `ℤ[v, v⁻¹]`:
`F v_j = [j + 1]_v v_(j + 1)`, so the only nonzero entries are `[i]_v` at the positions
`(i, i - 1)`. -/
noncomputable def ladderMatrixF : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ[T;T⁻¹] :=
  Matrix.of fun i j => if (i : ℕ) = j + 1 then laurentQuantumInteger i else 0

/-- The matrix of `K` on the positive ladder module, over `ℤ[v, v⁻¹]`: the diagonal matrix with
entries `v^(m - 2j)`. -/
noncomputable def ladderMatrixK : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ[T;T⁻¹] :=
  Matrix.diagonal fun i => T ((m : ℤ) - 2 * i)

/-- The diagonal matrix with entries `[m - 2j]_v`. At `v = q` it is the matrix of
`E F - F E = (K - K⁻¹) / (q - q⁻¹)` on the positive ladder module, and at `v = 1` it is the matrix
of the Cartan element of `sl₂`. -/
noncomputable def ladderMatrixH : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ[T;T⁻¹] :=
  Matrix.diagonal fun i => laurentQuantumInteger ((m : ℤ) - 2 * i)

variable {m}

/-- The entries of `ladderMatrixE m`. -/
@[simp]
theorem ladderMatrixE_apply (i j : Fin (m + 1)) :
    ladderMatrixE m i j = if (j : ℕ) = i + 1 then laurentQuantumInteger (m - i) else 0 := by
  rw [ladderMatrixE, Matrix.of_apply]

/-- The entries of `ladderMatrixF m`. -/
@[simp]
theorem ladderMatrixF_apply (i j : Fin (m + 1)) :
    ladderMatrixF m i j = if (i : ℕ) = j + 1 then laurentQuantumInteger i else 0 := by
  rw [ladderMatrixF, Matrix.of_apply]

/-- The entries of `ladderMatrixK m`. -/
@[simp]
theorem ladderMatrixK_apply (i j : Fin (m + 1)) :
    ladderMatrixK m i j = if i = j then T ((m : ℤ) - 2 * i) else 0 :=
  Matrix.diagonal_apply ..

/-- The entries of `ladderMatrixH m`. -/
@[simp]
theorem ladderMatrixH_apply (i j : Fin (m + 1)) :
    ladderMatrixH m i j = if i = j then laurentQuantumInteger ((m : ℤ) - 2 * i) else 0 :=
  Matrix.diagonal_apply ..

/-! ### The matrices of the positive ladder modules -/

namespace LadderModule

variable {q : ℂ}

/-- The coordinates of an integer-indexed ladder vector in the ladder basis. -/
private theorem basis_repr_vec (j : ℤ) (i : Fin (m + 1)) :
    (basis q m 1).repr (vec q m 1 j) i = if (i : ℤ) = j then 1 else 0 := by
  by_cases hj : 0 ≤ j ∧ j ≤ m
  · obtain ⟨k, rfl⟩ : ∃ k : Fin (m + 1), (k : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
    rw [vec_coe, Basis.repr_self, Finsupp.single_apply]
    exact if_congr (by rw [eq_comm, Fin.ext_iff]; omega) rfl rfl
  · rw [vec_eq_zero_iff.mpr (by omega), map_zero, Finsupp.coe_zero, Pi.zero_apply,
      ite_eq_right (by omega)]

/-- The matrix of an operator acting on the ladder vectors as a weighted shift. -/
private theorem toMatrix_eq_of_vec {T : Module.End ℂ (LadderModule q m 1)} {c : ℤ → ℂ} {s : ℤ}
    (h : ∀ j : ℤ, T (vec q m 1 j) = c j • vec q m 1 (j + s)) (i j : Fin (m + 1)) :
    LinearMap.toMatrix (basis q m 1) (basis q m 1) T i j =
      if (i : ℤ) = j + s then c j else 0 := by
  rw [LinearMap.toMatrix_apply, ← vec_coe, h, map_smul, Finsupp.smul_apply, basis_repr_vec,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

variable [Fact (q ≠ 0)]

variable (m) in
/-- **The matrix of `E` on `L_m^+` is integral**: it is `ladderMatrixE m` evaluated at `v = q`. -/
theorem toMatrix_rep_e (hq : q - q⁻¹ ≠ 0) :
    LinearMap.toMatrix (basis q m 1) (basis q m 1) (rep q m 1 (e q)) =
      (ladderMatrixE m).map (laurentEval (Units.mk0 q Fact.out)) := by
  ext i j
  rw [toMatrix_eq_of_vec (s := -1) (fun j => by rw [← smul_def, e_smul_vec, ← sub_eq_add_neg])]
  rw [Matrix.map_apply, ladderMatrixE_apply, apply_ite (laurentEval _), map_zero,
    laurentEval_laurentQuantumInteger (by simpa using hq)]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_mk0]
  by_cases hij : (j : ℕ) = i + 1
  · rw [ite_eq_left (by omega), ite_eq_left hij]
    congr 1
    omega
  · rw [ite_eq_right (by omega), ite_eq_right hij]

variable (m) in
/-- **The matrix of `F` on `L_m^+` is integral**: it is `ladderMatrixF m` evaluated at `v = q`. -/
theorem toMatrix_rep_f (hq : q - q⁻¹ ≠ 0) :
    LinearMap.toMatrix (basis q m 1) (basis q m 1) (rep q m 1 (f q)) =
      (ladderMatrixF m).map (laurentEval (Units.mk0 q Fact.out)) := by
  ext i j
  rw [toMatrix_eq_of_vec (s := 1) (fun j => by rw [← smul_def, f_smul_vec])]
  rw [Matrix.map_apply, ladderMatrixF_apply, apply_ite (laurentEval _), map_zero,
    laurentEval_laurentQuantumInteger (by simpa using hq), Units.val_mk0]
  by_cases hij : (i : ℕ) = j + 1
  · rw [ite_eq_left (by omega), ite_eq_left hij]
    congr 1
    omega
  · rw [ite_eq_right (by omega), ite_eq_right hij]

variable (m) in
/-- **The matrix of `K` on `L_m^+` is integral**: it is `ladderMatrixK m` evaluated at `v = q`. -/
theorem toMatrix_rep_k :
    LinearMap.toMatrix (basis q m 1) (basis q m 1) (rep q m 1 (k q)) =
      (ladderMatrixK m).map (laurentEval (Units.mk0 q Fact.out)) := by
  ext i j
  rw [toMatrix_eq_of_vec (s := 0) (fun j => by rw [← smul_def, k_smul_vec, add_zero])]
  rw [Matrix.map_apply, ladderMatrixK_apply, apply_ite (laurentEval _), map_zero, laurentEval_T,
    Units.val_zpow_eq_zpow_val, Units.val_mk0]
  simp only [Units.val_one, Int.cast_one, one_mul, add_zero]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Fin.val_inj]

variable (m) in
/-- **The matrix of `E F - F E` on `L_m^+` is integral**: it is `ladderMatrixH m` evaluated at
`v = q`. Since `E F - F E = (K - K⁻¹) / (q - q⁻¹)`, its entries are the quantum integers
`[m - 2j]_q`. -/
theorem toMatrix_rep_e_mul_f_sub_f_mul_e (hq : q - q⁻¹ ≠ 0) :
    LinearMap.toMatrix (basis q m 1) (basis q m 1) (rep q m 1 (e q * f q - f q * e q)) =
      (ladderMatrixH m).map (laurentEval (Units.mk0 q Fact.out)) := by
  have hv : ∀ j : ℤ, rep q m 1 (e q * f q - f q * e q) (vec q m 1 j) =
      quantumInteger q ((m : ℤ) - 2 * j) • vec q m 1 (j + 0) := by
    intro j
    rw [← smul_def, e_mul_f_sub_f_mul_e, smul_assoc, sub_smul, k_smul_vec, kInv_smul_vec,
      ← sub_smul, smul_smul, add_zero, quantumInteger_def]
    congr 1
    simp only [Units.val_one, Int.cast_one, one_mul, neg_sub]
    ring
  ext i j
  rw [toMatrix_eq_of_vec hv, Matrix.map_apply, ladderMatrixH_apply, apply_ite (laurentEval _),
    map_zero, laurentEval_laurentQuantumInteger (by simpa using hq), Units.val_mk0, add_zero]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Fin.val_inj]

end LadderModule

/-! ### The specialization at `v = 1` -/

section Specialization

variable (K : Type*) [CommRing K]

/-- At `v = 1` the matrix of `E` has the integer entries `m - i` at the positions `(i, i + 1)`. -/
theorem map_laurentEval_one_ladderMatrixE :
    (ladderMatrixE m).map (laurentEval (1 : Kˣ)) =
      Matrix.of fun i j : Fin (m + 1) => if (j : ℕ) = i + 1 then (m : K) - (i : ℕ) else 0 := by
  ext i j
  simp [apply_ite (laurentEval (1 : Kˣ))]

/-- At `v = 1` the matrix of `F` has the integer entries `i` at the positions `(i, i - 1)`. -/
theorem map_laurentEval_one_ladderMatrixF :
    (ladderMatrixF m).map (laurentEval (1 : Kˣ)) =
      Matrix.of fun i j : Fin (m + 1) => if (i : ℕ) = j + 1 then ((i : ℕ) : K) else 0 := by
  ext i j
  simp [apply_ite (laurentEval (1 : Kˣ))]

/-- At `v = 1` the matrix of `K` is the identity. -/
theorem map_laurentEval_one_ladderMatrixK :
    (ladderMatrixK m).map (laurentEval (1 : Kˣ)) = 1 := by
  ext i j
  simp [apply_ite (laurentEval (1 : Kˣ)), Matrix.one_apply]

/-- At `v = 1` the matrix `ladderMatrixH m` is the diagonal matrix with entries `m - 2i`. -/
theorem map_laurentEval_one_ladderMatrixH :
    (ladderMatrixH m).map (laurentEval (1 : Kˣ)) =
      Matrix.diagonal fun i : Fin (m + 1) => (m : K) - 2 * (i : ℕ) := by
  ext i j
  simp [apply_ite (laurentEval (1 : Kˣ)), Matrix.diagonal_apply]

end Specialization

/-! ### The classical specialization as an `sl₂`-module -/

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [CommRing K] (m : ℕ)

/-- **The classical specialization of the positive ladder module `L_m^+`**: the coordinate space
`K^(m+1)`, with basis `v₀, …, v_m`, on which the standard basis `(e, f, h)` of
`LieAlgebra.SpecialLinear.sl (Fin 2) K` acts by the integral ladder matrices `ladderMatrixE m`,
`ladderMatrixF m` and `ladderMatrixH m` evaluated at `v = 1`. Its action is
`TauCeti.UqSl2.ClassicalLadder.rep`. -/
@[expose] def ClassicalLadder : Type _ := Fin (m + 1) → K

namespace ClassicalLadder

instance : AddCommGroup (ClassicalLadder K m) := inferInstanceAs (AddCommGroup (Fin (m + 1) → K))
instance : Module K (ClassicalLadder K m) := inferInstanceAs (Module K (Fin (m + 1) → K))

/-- The ladder basis `v₀, …, v_m` of the classical specialization. -/
noncomputable def basis : Basis (Fin (m + 1)) K (ClassicalLadder K m) :=
  Pi.basisFun K (Fin (m + 1))

/-- The raising operator: `ladderMatrixE m` evaluated at `v = 1`, so that
`E v_j = (m - j + 1) v_(j - 1)`. -/
noncomputable def raise : Module.End K (ClassicalLadder K m) :=
  Matrix.toLin (basis K m) (basis K m) ((ladderMatrixE m).map (laurentEval (1 : Kˣ)))

/-- The lowering operator: `ladderMatrixF m` evaluated at `v = 1`, so that
`F v_j = (j + 1) v_(j + 1)`. -/
noncomputable def lower : Module.End K (ClassicalLadder K m) :=
  Matrix.toLin (basis K m) (basis K m) ((ladderMatrixF m).map (laurentEval (1 : Kˣ)))

/-- The Cartan operator: `ladderMatrixH m` evaluated at `v = 1`, so that `H v_j = (m - 2j) v_j`. -/
noncomputable def cartan : Module.End K (ClassicalLadder K m) :=
  Matrix.toLin (basis K m) (basis K m) ((ladderMatrixH m).map (laurentEval (1 : Kˣ)))

variable {K m}

/-- The ladder basis vectors are the coordinate vectors. -/
@[simp]
theorem basis_apply (i j : Fin (m + 1)) : basis K m i j = if j = i then 1 else 0 :=
  (congrFun (Pi.basisFun_apply K (Fin (m + 1)) i) j).trans (Pi.single_apply i 1 j)

/-- The coordinates of a vector in the ladder basis are its values. -/
@[simp]
theorem basis_repr_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    (basis K m).repr v i = v i :=
  Pi.basisFun_repr K (Fin (m + 1)) (v : Fin (m + 1) → K) i

/-! The type synonym hides `Fin (m + 1) → K` from the `Pi` lemmas, so the pointwise operations
used below are restated. -/

/-- Subtraction on the classical specialization is coordinatewise. -/
@[simp] theorem sub_apply (v w : ClassicalLadder K m) (i : Fin (m + 1)) :
    (v - w) i = v i - w i := rfl

/-- Negation on the classical specialization is coordinatewise. -/
@[simp] theorem neg_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) : (-v) i = -v i := rfl

/-- Scalar multiplication on the classical specialization is coordinatewise. -/
@[simp] theorem smul_apply (c : K) (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    (c • v) i = c * v i := rfl

/-- The zero vector of the classical specialization has zero coordinates. -/
@[simp] theorem zero_apply (i : Fin (m + 1)) : (0 : ClassicalLadder K m) i = 0 := rfl

/-- The matrix of the raising operator in the ladder basis is `ladderMatrixE m` at `v = 1`. -/
theorem toMatrix_raise :
    LinearMap.toMatrix (basis K m) (basis K m) (raise K m) =
      (ladderMatrixE m).map (laurentEval (1 : Kˣ)) :=
  LinearMap.toMatrix_toLin ..

/-- The matrix of the lowering operator in the ladder basis is `ladderMatrixF m` at `v = 1`. -/
theorem toMatrix_lower :
    LinearMap.toMatrix (basis K m) (basis K m) (lower K m) =
      (ladderMatrixF m).map (laurentEval (1 : Kˣ)) :=
  LinearMap.toMatrix_toLin ..

/-- The matrix of the Cartan operator in the ladder basis is `ladderMatrixH m` at `v = 1`. -/
theorem toMatrix_cartan :
    LinearMap.toMatrix (basis K m) (basis K m) (cartan K m) =
      (ladderMatrixH m).map (laurentEval (1 : Kˣ)) :=
  LinearMap.toMatrix_toLin ..

/-- An operator given by a matrix in the ladder basis acts on coordinates by `Matrix.mulVec`. -/
private theorem toLin_apply_apply (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    Matrix.toLin (basis K m) (basis K m) M v i = M.mulVec (fun j => v j) i := by
  have hv : ⇑((basis K m).repr v) = fun j => v j := funext (basis_repr_apply v)
  rw [← basis_repr_apply (Matrix.toLin (basis K m) (basis K m) M v) i,
    ← LinearMap.toMatrix_mulVec_repr (basis K m) (basis K m), LinearMap.toMatrix_toLin, hv]

/-- The raising operator in coordinates: `(E v)_i = (m - i) v_(i + 1)`, and `0` at the last
index. -/
theorem raise_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    raise K m v i =
      if h : (i : ℕ) < m then ((m : K) - (i : ℕ)) * v ⟨(i : ℕ) + 1, by omega⟩ else 0 := by
  rw [raise, toLin_apply_apply, map_laurentEval_one_ladderMatrixE, Matrix.mulVec,
    dotProduct]
  simp only [Matrix.of_apply, ite_mul, zero_mul]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(i : ℕ) + 1, by omega⟩ fun j hj => ite_eq_right
      fun hc => hj (Fin.ext hc), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)

/-- The lowering operator in coordinates: `(F v)_i = i v_(i - 1)`, and `0` at index `0`. -/
theorem lower_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    lower K m v i =
      if h : 0 < (i : ℕ) then ((i : ℕ) : K) * v ⟨(i : ℕ) - 1, by omega⟩ else 0 := by
  rw [lower, toLin_apply_apply, map_laurentEval_one_ladderMatrixF, Matrix.mulVec,
    dotProduct]
  simp only [Matrix.of_apply, ite_mul, zero_mul]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(i : ℕ) - 1, by omega⟩ fun j hj => ite_eq_right
      fun hc => hj (Fin.ext (by simp; omega)), ite_eq_left (by simp; omega)]
  · exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)

/-- The Cartan operator in coordinates: `(H v)_i = (m - 2i) v_i`. -/
theorem cartan_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    cartan K m v i = ((m : K) - 2 * (i : ℕ)) * v i := by
  rw [cartan, toLin_apply_apply, map_laurentEval_one_ladderMatrixH, Matrix.mulVec_diagonal]

/-- Raising after lowering is diagonal, with eigenvalue `(m - i)(i + 1)` at index `i`. -/
private theorem raise_lower_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    raise K m (lower K m v) i = ((m : K) - (i : ℕ)) * ((i : ℕ) + 1) * v i := by
  rw [raise_apply]
  split_ifs with h
  · rw [lower_apply, dite_eq_left (by simp)]
    simp only [Nat.add_sub_cancel, Fin.eta]
    push_cast
    ring
  · rw [show (i : ℕ) = m by omega]
    ring

/-- Lowering after raising is diagonal, with eigenvalue `i (m - i + 1)` at index `i`. -/
private theorem lower_raise_apply (v : ClassicalLadder K m) (i : Fin (m + 1)) :
    lower K m (raise K m v) i = ((i : ℕ) : K) * ((m : K) - (i : ℕ) + 1) * v i := by
  rw [lower_apply]
  split_ifs with h
  · rw [raise_apply, dite_eq_left (by simp; omega)]
    simp only [Nat.sub_add_cancel h, Fin.eta]
    push_cast [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
    ring
  · rw [show (i : ℕ) = 0 by omega]
    ring

/-- The relation `⁅E, F⁆ = H` of the specialized matrices. -/
theorem lie_raise_lower : ⁅raise K m, lower K m⁆ = cartan K m := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_apply,
    raise_lower_apply, lower_raise_apply, cartan_apply]
  ring

/-- The relation `⁅H, E⁆ = 2 E` of the specialized matrices. -/
theorem lie_cartan_raise : ⁅cartan K m, raise K m⁆ = (2 : K) • raise K m := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.smul_apply, sub_apply, smul_apply, cartan_apply, raise_apply, raise_apply]
  split_ifs with h
  · rw [cartan_apply]
    push_cast
    ring
  · ring

/-- The relation `⁅H, F⁆ = -2 F` of the specialized matrices. -/
theorem lie_cartan_lower : ⁅cartan K m, lower K m⁆ = -((2 : K) • lower K m) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, sub_apply, neg_apply, smul_apply,
    cartan_apply, lower_apply, lower_apply]
  split_ifs with h
  · rw [cartan_apply]
    push_cast [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
    ring
  · ring

/-- For `m ≠ 0` in `K`, the specialized matrices `(H, E, F)` form an `sl₂` triple. -/
theorem isSl2Triple (hm : (m : K) ≠ 0) : IsSl2Triple (cartan K m) (raise K m) (lower K m) where
  h_ne_zero hc := by
    have h0 : cartan K m (basis K m 0) 0 = 0 := by rw [hc, LinearMap.zero_apply, zero_apply]
    rw [cartan_apply, basis_apply] at h0
    exact hm (by simpa using h0)
  lie_e_f := lie_raise_lower
  lie_h_e_nsmul := by rw [lie_cartan_raise, two_smul, two_nsmul]
  lie_h_f_nsmul := by rw [lie_cartan_lower, two_smul, two_nsmul]

variable (K m)

/-- **The classical specialization of `L_m^+` as a representation of `sl₂`**, sending the
standard basis `(e, f, h)` of `sl (Fin 2) K` to the ladder matrices evaluated at `v = 1`, which
obey the same relations. -/
noncomputable def rep : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ Module.End K (ClassicalLadder K m) :=
  lieHomOfSl2Basis (slFinTwoBasis K) (lie_slFinTwoBasis_zero_one K)
    (lie_slFinTwoBasis_two_zero K) (lie_slFinTwoBasis_two_one K) (raise K m) (lower K m)
    (cartan K m) lie_raise_lower lie_cartan_raise lie_cartan_lower

/-- The classical specialization is a Lie ring module over `sl (Fin 2) K`, by transport along
`TauCeti.UqSl2.ClassicalLadder.rep`. -/
noncomputable instance instLieRingModule :
    LieRingModule (SpecialLinear.sl (Fin 2) K) (ClassicalLadder K m) :=
  LieRingModule.compLieHom (ClassicalLadder K m) (rep K m)

/-- The classical specialization is a Lie module over `sl (Fin 2) K`. -/
instance instLieModule : LieModule K (SpecialLinear.sl (Fin 2) K) (ClassicalLadder K m) :=
  LieModule.compLieHom (ClassicalLadder K m) (rep K m)

variable {K m}

/-- The action of `sl (Fin 2) K` on the classical specialization is the one given by
`TauCeti.UqSl2.ClassicalLadder.rep`. -/
theorem lie_eq_rep_apply (x : SpecialLinear.sl (Fin 2) K) (v : ClassicalLadder K m) :
    ⁅x, v⁆ = rep K m x v :=
  LieRingModule.compLieHom_apply (ClassicalLadder K m) (rep K m) x v

/-- The representation sends the standard basis of `sl (Fin 2) K` to the specialized ladder
matrices. -/
theorem rep_apply_basis (i : Fin 3) :
    rep K m (slFinTwoBasis K i) = ![raise K m, lower K m, cartan K m] i :=
  lieHomOfSl2Basis_apply ..

/-! ### Comparison with the standard module `V(m)` -/

/-- The coordinatewise rescaling `v ↦ ((m choose j) v_j)_j`, which turns the ladder normalization
of the classical specialization into that of `V(m)`. -/
private def scale : ClassicalLadder K m →ₗ[K] Sl2Std K m where
  toFun v := fun j => ((m.choose j : ℕ) : K) * v j
  map_add' v w := funext fun j => mul_add _ (v j) (w j)
  map_smul' c v := funext fun j => by simp only [RingHom.id_apply]; exact mul_left_comm _ c (v j)

private theorem scale_apply (v : ClassicalLadder K m) (j : Fin (m + 1)) :
    scale v j = ((m.choose j : ℕ) : K) * v j :=
  rfl

/-- The binomial identity `(m choose i) (m - i) = (i + 1) (m choose (i + 1))` in `K`, for
`i ≤ m`. -/
private theorem choose_mul_sub {i : ℕ} (hi : i ≤ m) :
    ((m.choose i : ℕ) : K) * ((m : K) - i) = ((i : K) + 1) * ((m.choose (i + 1) : ℕ) : K) := by
  have hc := congrArg (Nat.cast : ℕ → K) (Nat.choose_succ_right_eq m i)
  push_cast [Nat.cast_sub hi] at hc
  linear_combination -hc

private theorem scale_raise (v : ClassicalLadder K m) :
    scale (raise K m v) = Sl2Std.raise K m (scale v) := by
  funext i
  rw [scale_apply, raise_apply, Sl2Std.raise_apply]
  split_ifs with h
  · rw [scale_apply, ← mul_assoc, ← mul_assoc, choose_mul_sub h.le]
  · rw [mul_zero]

private theorem scale_lower (v : ClassicalLadder K m) :
    scale (lower K m v) = Sl2Std.lower K m (scale v) := by
  funext i
  rw [scale_apply, lower_apply, Sl2Std.lower_apply]
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [scale_apply, ← mul_assoc, ← mul_assoc]
    simp only [hk, Nat.add_sub_cancel]
    rw [mul_comm _ ((k + 1 : ℕ) : K), Nat.cast_succ, ← choose_mul_sub (by omega)]
    ring
  · rw [mul_zero]

private theorem scale_cartan (v : ClassicalLadder K m) :
    scale (cartan K m v) = Sl2Std.diag K m (scale v) := by
  funext i
  rw [scale_apply, cartan_apply, Sl2Std.diag_apply, scale_apply]
  ring

variable (K m) in
/-- **The classical specialization of `L_m^+` maps to `V(m)`**: the module map sending the
ladder vector `v_j` to `(m choose j) w_j`, where `w_j` is the coordinate basis of
`TauCeti.Sl2Std K m`. Over a field of characteristic zero it is an isomorphism,
`TauCeti.UqSl2.ClassicalLadder.equivSl2Std`. -/
noncomputable def toSl2Std :
    ClassicalLadder K m →ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆ Sl2Std K m where
  __ := scale
  map_lie' {x v} := by
    have key : ∀ i : Fin 3, scale (rep K m (slFinTwoBasis K i) v) =
        Sl2Std.rep K m (slFinTwoBasis K i) (scale v) := by
      intro i
      rw [rep_apply_basis, Sl2Std.rep_apply_basis]
      fin_cases i
      · exact scale_raise v
      · exact scale_lower v
      · exact scale_cartan v
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lie_eq_rep_apply,
      Sl2Std.lie_eq_rep_apply]
    rw [← (slFinTwoBasis K).sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, key]

/-- The module map to `V(m)` in coordinates. -/
theorem toSl2Std_apply (v : ClassicalLadder K m) (j : Fin (m + 1)) :
    toSl2Std K m v j = ((m.choose j : ℕ) : K) * v j :=
  (rfl)

/-- **The module map to `V(m)` retains the basis normalization**: it sends the ladder vector `v_j`
to `(m choose j) w_j`. -/
theorem toSl2Std_basis (j : Fin (m + 1)) :
    toSl2Std K m (basis K m j) = ((m.choose j : ℕ) : K) • Sl2Std.basis K m j := by
  funext i
  rw [toSl2Std_apply, basis_apply, Sl2Std.smul_apply, Sl2Std.basis_apply]
  rcases eq_or_ne i j with rfl | h
  · rfl
  · simp [h]

end ClassicalLadder

section Field

variable (K : Type*) [Field K] [CharZero K] (m : ℕ)

namespace ClassicalLadder

/-- **The classical specialization of `L_m^+` is the standard module `V(m)`**: over a field of
characteristic zero, the module map `TauCeti.UqSl2.ClassicalLadder.toSl2Std`, sending `v_j` to
`(m choose j) w_j`, is an isomorphism of `sl (Fin 2) K`-modules. -/
noncomputable def equivSl2Std :
    ClassicalLadder K m ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆ Sl2Std K m where
  __ := toSl2Std K m
  invFun w := fun j => w j / ((m.choose j : ℕ) : K)
  left_inv v := funext fun j =>
    mul_div_cancel_left₀ (v j) (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
  right_inv w := funext fun j =>
    mul_div_cancel₀ (w j) (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')

/-- The isomorphism with `V(m)` sends the ladder vector `v_j` to `(m choose j) w_j`. -/
theorem equivSl2Std_basis (j : Fin (m + 1)) :
    equivSl2Std K m (basis K m j) = ((m.choose j : ℕ) : K) • Sl2Std.basis K m j :=
  toSl2Std_basis j

end ClassicalLadder

end Field

end UqSl2

end TauCeti
