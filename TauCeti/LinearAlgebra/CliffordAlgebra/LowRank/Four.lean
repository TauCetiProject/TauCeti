/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.Algebra.Quaternion.Basis
import TauCeti.Algebra.TensorProduct.Mul
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.NoncommRing

/-!
# The Clifford algebra of a four-dimensional diagonal form

For units `a` and `b` and scalars `c` and `d` in a field `K` in which `2` is invertible,
the Clifford algebra of
`<a, b, c, d>` is the tensor product

```text
  (a, b) tensor (-c / (ab), -d / (ab)).
```

The first two Clifford generators become the standard generators of the first quaternion
factor. The last two become the corresponding generators of the second factor multiplied by
the volume element `ij` of the first. Since `(ij)^2 = -ab`, this precisely compensates for the
two rescaled coefficients in the second factor. This explicit model computes the first
even-dimensional Clifford invariant beyond binary forms.

## Main results

* `CliffordAlgebra.weightedSumSquaresFourEquivTensorQuaternion`: the algebra equivalence above.
* `CliffordAlgebra.weightedSumSquaresFourEquivTensorQuaternion_symm_tmul_one` and
  `CliffordAlgebra.weightedSumSquaresFourEquivTensorQuaternion_symm_one_tmul`: its inverse on
  each quaternion factor, in terms of Clifford generators.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, Section 2.
-/

public section

open scoped Quaternion TensorProduct

namespace CliffordAlgebra

universe u

variable {K : Type u} [Field K]

private abbrev firstQuaternion (a b : Kˣ) := ℍ[K,(a : K),(b : K)]

private abbrev secondQuaternion (a b : Kˣ) (c d : K) :=
  ℍ[K,-((((a * b)⁻¹ : Kˣ) : K) * c),-((((a * b)⁻¹ : Kˣ) : K) * d)]

private abbrev fourQuaternionTensor (a b : Kˣ) (c d : K) :=
  firstQuaternion a b ⊗[K] secondQuaternion a b c d

private abbrev generatorZero (a b : Kˣ) (c d : K) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).i ⊗ₜ 1

private abbrev generatorOne (a b : Kˣ) (c d : K) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).j ⊗ₜ 1

private abbrev generatorTwo (a b : Kˣ) (c d : K) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ
    (_root_.QuaternionAlgebra.Basis.self K).i

private abbrev generatorThree (a b : Kˣ) (c d : K) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ
    (_root_.QuaternionAlgebra.Basis.self K).j

private def fourGenerator (a b : Kˣ) (c d : K) :
    (Fin 4 → K) →ₗ[K] fourQuaternionTensor a b c d where
  toFun x :=
    x 0 • generatorZero a b c d + x 1 • generatorOne a b c d +
      x 2 • generatorTwo a b c d + x 3 • generatorThree a b c d
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r x := by
    simp [smul_add, smul_smul]

private theorem generatorZero_sq (a b : Kˣ) (c d : K) :
    generatorZero a b c d * generatorZero a b c d = (a : K) • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.i_mul_i]
  simp only [zero_smul, add_zero, one_mul]
  rw [← TensorProduct.smul_tmul']
  rfl

private theorem generatorOne_sq (a b : Kˣ) (c d : K) :
    generatorOne a b c d * generatorOne a b c d = (b : K) • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.j_mul_j]
  simp only [one_mul]
  rw [← TensorProduct.smul_tmul']
  rfl

private theorem generatorTwo_sq (a b : Kˣ) (c d : K) :
    generatorTwo a b c d * generatorTwo a b c d = c • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.k_mul_k, _root_.QuaternionAlgebra.Basis.i_mul_i]
  simp only [zero_smul, add_zero]
  rw [← neg_smul]
  -- The quaternion square laws leave a tensor of scalar multiples; exposing that
  -- definitional shape is what allows the tensor-product scalar rule to apply.
  change (((-((a : K) * (b : K))) • (1 : firstQuaternion a b)) ⊗ₜ[K]
      ((-((((a * b)⁻¹ : Kˣ) : K) * c)) • (1 : secondQuaternion a b c d))) =
    c • (1 : fourQuaternionTensor a b c d)
  rw [TensorProduct.smul_tmul_smul]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp

private theorem generatorThree_sq (a b : Kˣ) (c d : K) :
    generatorThree a b c d * generatorThree a b c d = d • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.k_mul_k, _root_.QuaternionAlgebra.Basis.j_mul_j]
  rw [← neg_smul]
  -- As above, expose the scalar-tensor shape produced by the quaternion square laws.
  change (((-((a : K) * (b : K))) • (1 : firstQuaternion a b)) ⊗ₜ[K]
      ((-((((a * b)⁻¹ : Kˣ) : K) * d)) • (1 : secondQuaternion a b c d))) =
    d • (1 : fourQuaternionTensor a b c d)
  rw [TensorProduct.smul_tmul_smul]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp

private theorem generator_pair_anticommute (a b : Kˣ) (c d : K) :
    generatorZero a b c d * generatorOne a b c d +
        generatorOne a b c d * generatorZero a b c d = 0 ∧
      generatorZero a b c d * generatorTwo a b c d +
        generatorTwo a b c d * generatorZero a b c d = 0 ∧
      generatorZero a b c d * generatorThree a b c d +
        generatorThree a b c d * generatorZero a b c d = 0 ∧
      generatorOne a b c d * generatorTwo a b c d +
        generatorTwo a b c d * generatorOne a b c d = 0 ∧
      generatorOne a b c d * generatorThree a b c d +
        generatorThree a b c d * generatorOne a b c d = 0 ∧
      generatorTwo a b c d * generatorThree a b c d +
        generatorThree a b c d * generatorTwo a b c d = 0 := by
  -- Both quaternion factors have `c₂ = 0`, so their generators anticommute.
  let q := (_root_.QuaternionAlgebra.Basis.self K : _root_.QuaternionAlgebra.Basis
    (firstQuaternion a b) _ _ _)
  let q' := (_root_.QuaternionAlgebra.Basis.self K : _root_.QuaternionAlgebra.Basis
    (secondQuaternion a b c d) _ _ _)
  have hij := q.i_mul_j_add_j_mul_i.trans (zero_smul K _)
  have hik := q.i_mul_k_add_k_mul_i.trans (zero_smul K _)
  have hjk := q.j_mul_k_add_k_mul_j.trans (by rw [zero_mul, zero_smul])
  have hij' := q'.i_mul_j_add_j_mul_i.trans (zero_smul K _)
  open Algebra.TensorProduct in
  exact ⟨tmul_anticommute_of_left hij (Commute.refl _),
    tmul_anticommute_of_left hik (Commute.one_left _),
    tmul_anticommute_of_left hik (Commute.one_left _),
    tmul_anticommute_of_left hjk (Commute.one_left _),
    tmul_anticommute_of_left hjk (Commute.one_left _),
    tmul_anticommute_of_right (Commute.refl _) hij'⟩

private theorem fourGenerator_sq (a b : Kˣ) (c d : K) (x : Fin 4 → K) :
    fourGenerator a b c d x * fourGenerator a b c d x =
      algebraMap K _ (QuadraticMap.weightedSumSquares K
        ![(a : K), (b : K), (c : K), (d : K)] x) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := generator_pair_anticommute a b c d
  simp only [fourGenerator]
  have hq : QuadraticMap.weightedSumSquares K
      ![(a : K), (b : K), (c : K), (d : K)] x =
      (a : K) * (x 0 * x 0) +
        ((b : K) * (x 1 * x 1) + ((c : K) * (x 2 * x 2) + (d : K) * (x 3 * x 3))) := by
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]
  rw [hq]
  rw [Algebra.algebraMap_eq_smul_one]
  -- Distribute the scalar quadratic value into its four diagonal summands before
  -- replacing each summand by the corresponding generator square.
  rw [show
      ((a : K) * (x 0 * x 0) +
        ((b : K) * (x 1 * x 1) + ((c : K) * (x 2 * x 2) + (d : K) * (x 3 * x 3)))) •
          (1 : fourQuaternionTensor a b c d) =
      (x 0 * x 0) • ((a : K) • 1) + (x 1 * x 1) • ((b : K) • 1) +
        (x 2 * x 2) • ((c : K) • 1) + (x 3 * x 3) • ((d : K) • 1) by
    module]
  rw [← generatorZero_sq a b c d, ← generatorOne_sq a b c d,
    ← generatorTwo_sq a b c d, ← generatorThree_sq a b c d]
  -- Unfold the linear generator map so `noncomm_ring` sees the four summands.
  change (x 0 • generatorZero a b c d + x 1 • generatorOne a b c d +
      x 2 • generatorTwo a b c d + x 3 • generatorThree a b c d) *
      (x 0 • generatorZero a b c d + x 1 • generatorOne a b c d +
        x 2 • generatorTwo a b c d + x 3 • generatorThree a b c d) = _
  have h10 : generatorOne a b c d * generatorZero a b c d =
      -(generatorZero a b c d * generatorOne a b c d) := by
    exact eq_neg_of_add_eq_zero_right h01
  have h20 : generatorTwo a b c d * generatorZero a b c d =
      -(generatorZero a b c d * generatorTwo a b c d) := by
    exact eq_neg_of_add_eq_zero_right h02
  have h30 : generatorThree a b c d * generatorZero a b c d =
      -(generatorZero a b c d * generatorThree a b c d) := by
    exact eq_neg_of_add_eq_zero_right h03
  have h21 : generatorTwo a b c d * generatorOne a b c d =
      -(generatorOne a b c d * generatorTwo a b c d) := by
    exact eq_neg_of_add_eq_zero_right h12
  have h31 : generatorThree a b c d * generatorOne a b c d =
      -(generatorOne a b c d * generatorThree a b c d) := by
    exact eq_neg_of_add_eq_zero_right h13
  have h32 : generatorThree a b c d * generatorTwo a b c d =
      -(generatorTwo a b c d * generatorThree a b c d) := by
    exact eq_neg_of_add_eq_zero_right h23
  noncomm_ring [h10, h20, h30, h21, h31, h32]
  all_goals module

@[simp]
private theorem fourGenerator_single_zero (a b : Kˣ) (c d : K) :
    fourGenerator a b c d (Pi.single 0 1) = generatorZero a b c d := by
  simp [fourGenerator]

@[simp]
private theorem fourGenerator_single_one (a b : Kˣ) (c d : K) :
    fourGenerator a b c d (Pi.single 1 1) = generatorOne a b c d := by
  simp [fourGenerator]

@[simp]
private theorem fourGenerator_single_two (a b : Kˣ) (c d : K) :
    fourGenerator a b c d (Pi.single 2 1) = generatorTwo a b c d := by
  simp [fourGenerator]

@[simp]
private theorem fourGenerator_single_three (a b : Kˣ) (c d : K) :
    fourGenerator a b c d (Pi.single 3 1) = generatorThree a b c d := by
  simp [fourGenerator]

private def fourToTensor (a b : Kˣ) (c d : K) :
    _root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) →ₐ[K]
      fourQuaternionTensor a b c d :=
  _root_.CliffordAlgebra.lift _ ⟨fourGenerator a b c d, fourGenerator_sq a b c d⟩

@[simp]
private theorem fourToTensor_ue (a b : Kˣ) (c d : K) (i : Fin 4) :
    fourToTensor a b c d (_root_.CliffordAlgebra.ι _ (Pi.single i 1)) =
      fourGenerator a b c d (Pi.single i 1) := by
  rw [fourToTensor, _root_.CliffordAlgebra.lift_ι_apply]

private def firstPreimageBasis (a b : Kˣ) (c d : K) :
    _root_.QuaternionAlgebra.Basis
      (_root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]))
      (a : K) 0 (b : K) where
  i := _root_.CliffordAlgebra.ι _ (Pi.single 0 1)
  j := _root_.CliffordAlgebra.ι _ (Pi.single 1 1)
  k := _root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
    _root_.CliffordAlgebra.ι _ (Pi.single 1 1)
  i_mul_i := by
    rw [_root_.CliffordAlgebra.ι_sq_scalar]
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ,
      Algebra.algebraMap_eq_smul_one]
  j_mul_j := by
    rw [_root_.CliffordAlgebra.ι_sq_scalar]
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ,
      Algebra.algebraMap_eq_smul_one]
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul, zero_sub, eq_neg_iff_add_eq_zero,
      _root_.CliffordAlgebra.ι_mul_ι_add_swap]
    simp [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]

private def firstPreimage (a b : Kˣ) (c d : K) :
    firstQuaternion a b →ₐ[K]
      _root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]) :=
  (firstPreimageBasis a b c d).liftHom

private theorem fourToTensor_firstPreimage (a b : Kˣ) (c d : K) (x : firstQuaternion a b) :
    fourToTensor a b c d (firstPreimage a b c d x) = x ⊗ₜ (1 : secondQuaternion a b c d) := by
  have hhom : (fourToTensor a b c d).comp (firstPreimage a b c d) =
      (Algebra.TensorProduct.includeLeft :
        firstQuaternion a b →ₐ[K] fourQuaternionTensor a b c d) := by
    apply _root_.QuaternionAlgebra.hom_ext
    · simp [firstPreimage, _root_.QuaternionAlgebra.Basis.lift,
        firstPreimageBasis, fourToTensor_ue,
        Algebra.TensorProduct.includeLeft_apply]
      rfl
    · simp [firstPreimage, _root_.QuaternionAlgebra.Basis.lift,
        firstPreimageBasis, fourToTensor_ue,
        Algebra.TensorProduct.includeLeft_apply]
      rfl
  rw [← AlgHom.comp_apply, hhom, Algebra.TensorProduct.includeLeft_apply]

private def secondGeneratorPreimage (a b : Kˣ) (c d : K) (i : Fin 4) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  (-((a * b)⁻¹ : Kˣ) : K) •
    (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single 1 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single i 1))

private abbrev secondIpreimage (a b : Kˣ) (c d : K) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  secondGeneratorPreimage a b c d 2

private abbrev secondJpreimage (a b : Kˣ) (c d : K) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  secondGeneratorPreimage a b c d 3

private theorem secondGeneratorPreimage_sq (a b : Kˣ) (c d : K) (i : Fin 4) (e : K)
    (hpair : [Pi.single 0 1, Pi.single 1 1, Pi.single i 1].Pairwise
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]).IsOrtho)
    (he : QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]
      (Pi.single i 1) = e) :
    secondGeneratorPreimage a b c d i * secondGeneratorPreimage a b c d i =
      (-((((a * b)⁻¹ : Kˣ) : K) * e)) • 1 := by
  let Q := QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]
  let e0 : Fin 4 → K := Pi.single 0 1
  let e1 : Fin 4 → K := Pi.single 1 1
  let ei : Fin 4 → K := Pi.single i 1
  have hQ0 : Q e0 = (a : K) := by
    simp [Q, e0, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]
  have hQ1 : Q e1 = (b : K) := by
    simp [Q, e1, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]
  have hQi : Q ei = e := by simpa [Q, ei] using he
  have hpair' : [e0, e1, ei].Pairwise Q.IsOrtho := by simpa [Q, e0, e1, ei] using hpair
  have hs := _root_.CliffordAlgebra.prod_map_ι_sq_scalar (Q := Q) hpair'
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil, Nat.choose, pow_succ, pow_zero, one_mul] at hs
  simp only [hQ0, hQ1, hQi, Nat.succ_eq_add_one, Nat.reduceAdd, neg_mul,
    mul_assoc] at hs
  dsimp [Q, e0, e1, ei] at hs
  rw [secondGeneratorPreimage, smul_mul_smul_comm]
  simp only [mul_assoc]
  rw [hs]
  simp only [Algebra.smul_def, ← map_mul, mul_one]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp

private theorem secondIpreimage_sq (a b : Kˣ) (c d : K) :
    secondIpreimage a b c d * secondIpreimage a b c d =
      (-((((a * b)⁻¹ : Kˣ) : K) * c)) • 1 := by
  apply secondGeneratorPreimage_sq a b c d 2 c
  · simp [QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ]
  · simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]

private theorem secondJpreimage_sq (a b : Kˣ) (c d : K) :
    secondJpreimage a b c d * secondJpreimage a b c d =
      (-((((a * b)⁻¹ : Kˣ) : K) * d)) • 1 := by
  apply secondGeneratorPreimage_sq a b c d 3 d
  · simp [QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ]
  · simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]

private theorem secondPreimages_anticommute (a b : Kˣ) (c d : K) :
    secondIpreimage a b c d * secondJpreimage a b c d +
      secondJpreimage a b c d * secondIpreimage a b c d = 0 := by
  let Q := QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]
  let g (i : Fin 4) := _root_.CliffordAlgebra.ι Q (Pi.single i 1)
  have h20 : g 2 * g 0 = -(g 0 * g 2) := by
    apply _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    simp [Q, QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, add_comm]
  have h21 : g 2 * g 1 = -(g 1 * g 2) := by
    apply _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    simp [Q, QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, add_comm]
  have h30 : g 3 * g 0 = -(g 0 * g 3) := by
    apply _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    simp [Q, QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, add_comm]
  have h31 : g 3 * g 1 = -(g 1 * g 3) := by
    apply _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    simp [Q, QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, add_comm]
  have h32 : g 3 * g 2 = -(g 2 * g 3) := by
    apply _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    simp [Q, QuadraticMap.isOrtho_def, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, add_comm]
  -- The last two generators commute with the volume element `g 0 * g 1` of the first two.
  have h2u : Commute (g 2) (g 0 * g 1) := by
    calc
      g 2 * (g 0 * g 1) = (g 2 * g 0) * g 1 := (mul_assoc _ _ _).symm
      _ = (-(g 0 * g 2)) * g 1 := by rw [h20]
      _ = -(g 0 * (g 2 * g 1)) := by simp only [neg_mul, mul_assoc]
      _ = (g 0 * g 1) * g 2 := by rw [h21]; noncomm_ring
  have h3u : Commute (g 3) (g 0 * g 1) := by
    calc
      g 3 * (g 0 * g 1) = (g 3 * g 0) * g 1 := (mul_assoc _ _ _).symm
      _ = (-(g 0 * g 3)) * g 1 := by rw [h30]
      _ = -(g 0 * (g 3 * g 1)) := by simp only [neg_mul, mul_assoc]
      _ = (g 0 * g 1) * g 3 := by rw [h31]; noncomm_ring
  have hproducts :
      (g 0 * g 1 * g 2) * (g 0 * g 1 * g 3) +
        (g 0 * g 1 * g 3) * (g 0 * g 1 * g 2) = 0 := by
    rw [h2u.mul_mul_mul_comm, h3u.mul_mul_mul_comm, ← mul_add, h32, add_neg_cancel, mul_zero]
  rw [secondIpreimage, secondJpreimage, secondGeneratorPreimage,
    secondGeneratorPreimage, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add]
  exact smul_eq_zero_of_right _ hproducts

private theorem fourToTensor_secondGeneratorPreimage (a b : Kˣ) (c d : K) (i : Fin 4)
    (q : secondQuaternion a b c d)
    (hq : fourGenerator a b c d (Pi.single i 1) =
      (_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ q) :
    fourToTensor a b c d (secondGeneratorPreimage a b c d i) =
      (1 : firstQuaternion a b) ⊗ₜ q := by
  rw [secondGeneratorPreimage, map_smul, map_mul, map_mul,
    fourToTensor_ue, fourToTensor_ue, fourToTensor_ue,
    fourGenerator_single_zero, fourGenerator_single_one, hq,
    Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.i_mul_j,
    Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.k_mul_k]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, one_mul]
  rw [← neg_smul, TensorProduct.smul_tmul']
  congr 1
  ext <;> simp [mul_assoc]

private theorem fourToTensor_secondIpreimage (a b : Kˣ) (c d : K) :
    fourToTensor a b c d (secondIpreimage a b c d) =
      (1 : firstQuaternion a b) ⊗ₜ (_root_.QuaternionAlgebra.Basis.self K).i := by
  exact fourToTensor_secondGeneratorPreimage a b c d 2 _
    (fourGenerator_single_two a b c d)

private theorem fourToTensor_secondJpreimage (a b : Kˣ) (c d : K) :
    fourToTensor a b c d (secondJpreimage a b c d) =
      (1 : firstQuaternion a b) ⊗ₜ (_root_.QuaternionAlgebra.Basis.self K).j := by
  exact fourToTensor_secondGeneratorPreimage a b c d 3 _
    (fourGenerator_single_three a b c d)

private def secondPreimageBasis (a b : Kˣ) (c d : K) :
    _root_.QuaternionAlgebra.Basis
      (_root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]))
      (-((((a * b)⁻¹ : Kˣ) : K) * c)) 0 (-((((a * b)⁻¹ : Kˣ) : K) * d)) where
  i := secondIpreimage a b c d
  j := secondJpreimage a b c d
  k := secondIpreimage a b c d * secondJpreimage a b c d
  i_mul_i := by simpa using secondIpreimage_sq a b c d
  j_mul_j := secondJpreimage_sq a b c d
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul, zero_sub]
    exact eq_neg_of_add_eq_zero_right (secondPreimages_anticommute a b c d)

private def secondPreimage (a b : Kˣ) (c d : K) :
    secondQuaternion a b c d →ₐ[K]
      _root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), c, d]) :=
  (secondPreimageBasis a b c d).liftHom

private theorem fourToTensor_secondPreimage (a b : Kˣ) (c d : K) (x : secondQuaternion a b c d) :
    fourToTensor a b c d (secondPreimage a b c d x) = (1 : firstQuaternion a b) ⊗ₜ x := by
  have hhom : (fourToTensor a b c d).comp (secondPreimage a b c d) =
      (Algebra.TensorProduct.includeRight :
        secondQuaternion a b c d →ₐ[K] fourQuaternionTensor a b c d) := by
    apply _root_.QuaternionAlgebra.hom_ext
    · simpa [secondPreimage, _root_.QuaternionAlgebra.Basis.lift,
        secondPreimageBasis, Algebra.TensorProduct.includeRight_apply] using
          fourToTensor_secondIpreimage a b c d
    · simpa [secondPreimage, _root_.QuaternionAlgebra.Basis.lift,
        secondPreimageBasis, Algebra.TensorProduct.includeRight_apply] using
          fourToTensor_secondJpreimage a b c d
  rw [← AlgHom.comp_apply, hhom, Algebra.TensorProduct.includeRight_apply]

private theorem fourToTensor_surjective (a b : Kˣ) (c d : K) :
    Function.Surjective (fourToTensor a b c d) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      refine ⟨firstPreimage a b c d x * secondPreimage a b c d y, ?_⟩
      rw [map_mul, fourToTensor_firstPreimage, fourToTensor_secondPreimage,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add (fourToTensor a b c d) u v⟩

private theorem fourToTensor_bijective [Invertible (2 : K)] (a b : Kˣ) (c d : K) :
    Function.Bijective (fourToTensor a b c d) := by
  have hdim : Module.finrank K
      (_root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)])) =
      Module.finrank K (fourQuaternionTensor a b c d) := by
    simp [Module.finrank_tensorProduct, _root_.QuaternionAlgebra.finrank_eq_four,
      CliffordAlgebra.finrank_eq_two_pow]
  have hsurj := fourToTensor_surjective a b c d
  have hinj : Function.Injective (fourToTensor a b c d) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fourToTensor a b c d).toLinearMap) hdim).2 hsurj
  exact ⟨hinj, hsurj⟩

private theorem secondIpreimage_mul_secondJpreimage [Invertible (2 : K)] (a b : Kˣ) (c d : K) :
    secondIpreimage a b c d * secondJpreimage a b c d =
      (-((((a * b)⁻¹ : Kˣ) : K))) •
        (_root_.CliffordAlgebra.ι _ (Pi.single 2 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 3 1)) := by
  apply (fourToTensor_bijective a b c d).injective
  rw [map_mul, fourToTensor_secondIpreimage, fourToTensor_secondJpreimage, map_smul, map_mul,
    fourToTensor_ue, fourToTensor_ue, fourGenerator_single_two, fourGenerator_single_three,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    _root_.QuaternionAlgebra.Basis.k_mul_k, _root_.QuaternionAlgebra.Basis.i_mul_j,
    TensorProduct.neg_tmul, ← TensorProduct.smul_tmul', smul_neg, smul_smul]
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  rw [neg_mul, inv_mul_cancel₀ (mul_ne_zero a.ne_zero b.ne_zero), neg_one_smul, neg_neg]

/-- **The Clifford algebra of a four-dimensional diagonal form** as a tensor product of two
quaternion algebras:
`Cl<a,b,c,d> ≃ (a,b) ⊗ (-c/(ab),-d/(ab))`. -/
noncomputable def weightedSumSquaresFourEquivTensorQuaternion [Invertible (2 : K)]
    (a b : Kˣ) (c d : K) :
    _root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) ≃ₐ[K]
      (ℍ[K,(a : K),(b : K)] ⊗[K]
        ℍ[K,-((((a * b)⁻¹ : Kˣ) : K) * c),-((((a * b)⁻¹ : Kˣ) : K) * d)]) :=
  AlgEquiv.ofBijective (fourToTensor a b c d) (fourToTensor_bijective a b c d)

private theorem weightedSumSquaresFourEquivTensorQuaternion_apply [Invertible (2 : K)]
    (a b : Kˣ) (c d : K)
    (z : _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)])) :
    weightedSumSquaresFourEquivTensorQuaternion a b c d z = fourToTensor a b c d z :=
  rfl

/-- The explicit tensor-quaternion coordinates of the four-dimensional Clifford generators. -/
@[simp]
theorem weightedSumSquaresFourEquivTensorQuaternion_ι [Invertible (2 : K)]
    (a b : Kˣ) (c d : K) (x : Fin 4 → K) :
    weightedSumSquaresFourEquivTensorQuaternion a b c d
        (_root_.CliffordAlgebra.ι _ x) =
      x 0 • ((_root_.QuaternionAlgebra.Basis.self K).i ⊗ₜ
        (1 : ℍ[K,-((((a * b)⁻¹ : Kˣ) : K) * c),-((((a * b)⁻¹ : Kˣ) : K) * d)])) +
      x 1 • ((_root_.QuaternionAlgebra.Basis.self K).j ⊗ₜ
        (1 : ℍ[K,-((((a * b)⁻¹ : Kˣ) : K) * c),-((((a * b)⁻¹ : Kˣ) : K) * d)])) +
      x 2 • ((_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ
        (_root_.QuaternionAlgebra.Basis.self K).i) +
      x 3 • ((_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ
        (_root_.QuaternionAlgebra.Basis.self K).j) := by
  -- Expose the underlying Clifford lift; its universal-property equation then
  -- computes the equivalence on an arbitrary generator.
  change fourToTensor a b c d (_root_.CliffordAlgebra.ι _ x) = _
  rw [fourToTensor, _root_.CliffordAlgebra.lift_ι_apply]
  rfl

/-- The inverse of the four-dimensional model on the first quaternion factor: its standard
generators `i` and `j` come from the first two Clifford generators. -/
@[simp]
theorem weightedSumSquaresFourEquivTensorQuaternion_symm_tmul_one [Invertible (2 : K)]
    (a b : Kˣ) (c d : K) (x : ℍ[K,(a : K),(b : K)]) :
    (weightedSumSquaresFourEquivTensorQuaternion a b c d).symm
        (x ⊗ₜ (1 : ℍ[K,-((((a * b)⁻¹ : Kˣ) : K) * c),-((((a * b)⁻¹ : Kˣ) : K) * d)])) =
      algebraMap K _ x.re + x.imI • _root_.CliffordAlgebra.ι _ (Pi.single 0 1) +
        x.imJ • _root_.CliffordAlgebra.ι _ (Pi.single 1 1) +
        x.imK • (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 1 1)) := by
  rw [AlgEquiv.symm_apply_eq]
  exact (fourToTensor_firstPreimage a b c d x).symm

/-- The inverse of the four-dimensional model on the second quaternion factor: its standard
generators `i` and `j` come from the last two Clifford generators multiplied by the volume
element of the first two and rescaled by `-(ab)⁻¹`. -/
@[simp]
theorem weightedSumSquaresFourEquivTensorQuaternion_symm_one_tmul [Invertible (2 : K)]
    (a b : Kˣ) (c d : K)
    (y : ℍ[K,-((((a * b)⁻¹ : Kˣ) : K) * c),-((((a * b)⁻¹ : Kˣ) : K) * d)]) :
    (weightedSumSquaresFourEquivTensorQuaternion a b c d).symm
        ((1 : ℍ[K,(a : K),(b : K)]) ⊗ₜ y) =
      algebraMap K _ y.re +
        (-((((a * b)⁻¹ : Kˣ) : K)) * y.imI) • (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 1 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 2 1)) +
        (-((((a * b)⁻¹ : Kˣ) : K)) * y.imJ) • (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 1 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 3 1)) +
        (-((((a * b)⁻¹ : Kˣ) : K)) * y.imK) • (_root_.CliffordAlgebra.ι _ (Pi.single 2 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 3 1)) := by
  rw [AlgEquiv.symm_apply_eq, weightedSumSquaresFourEquivTensorQuaternion_apply,
    ← fourToTensor_secondPreimage a b c d y]
  congr 1
  rw [secondPreimage, _root_.QuaternionAlgebra.Basis.liftHom_apply,
    _root_.QuaternionAlgebra.Basis.lift]
  dsimp only [secondPreimageBasis]
  rw [secondIpreimage_mul_secondJpreimage]
  simp only [secondGeneratorPreimage, smul_smul]
  rw [mul_comm y.imI, mul_comm y.imJ, mul_comm y.imK]

end CliffordAlgebra
