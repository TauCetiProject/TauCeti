/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.NoncommRing

/-!
# The Clifford algebra of a four-dimensional diagonal form

For units `a`, `b`, `c`, and `d` in a field `K`, the Clifford algebra of
`<a, b, c, d>` is the tensor product

```text
  (a, b) tensor (-c / (ab), -d / (ab)).
```

The first two Clifford generators become the standard generators of the first quaternion
factor. The last two become the corresponding generators of the second factor multiplied by
the volume element `ij` of the first. Since `(ij)^2 = -ab`, this precisely compensates for the
two rescaled coefficients in the second factor. This explicit model computes the first
even-dimensional Clifford invariant beyond binary forms.

## Main result

* `CliffordAlgebra.weightedSumSquaresFourEquivTensorQuaternion`: the algebra equivalence above.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, Section 2.
-/

public section

open scoped Quaternion TensorProduct

namespace CliffordAlgebra

universe u

variable {K : Type u} [Field K]

private abbrev firstQuaternion (a b : Kˣ) := ℍ[K,(a : K),(b : K)]

private abbrev secondQuaternion (a b c d : Kˣ) :=
  ℍ[K,(-((a * b)⁻¹ * c) : Kˣ),(-((a * b)⁻¹ * d) : Kˣ)]

private abbrev fourQuaternionTensor (a b c d : Kˣ) :=
  firstQuaternion a b ⊗[K] secondQuaternion a b c d

private abbrev generatorZero (a b c d : Kˣ) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).i ⊗ₜ 1

private abbrev generatorOne (a b c d : Kˣ) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).j ⊗ₜ 1

private abbrev generatorTwo (a b c d : Kˣ) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ
    (_root_.QuaternionAlgebra.Basis.self K).i

private abbrev generatorThree (a b c d : Kˣ) : fourQuaternionTensor a b c d :=
  (_root_.QuaternionAlgebra.Basis.self K).k ⊗ₜ
    (_root_.QuaternionAlgebra.Basis.self K).j

private def fourGenerator (a b c d : Kˣ) :
    (Fin 4 → K) →ₗ[K] fourQuaternionTensor a b c d where
  toFun x :=
    x 0 • generatorZero a b c d + x 1 • generatorOne a b c d +
      x 2 • generatorTwo a b c d + x 3 • generatorThree a b c d
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r x := by
    simp [smul_add, smul_smul]

private theorem generatorZero_sq (a b c d : Kˣ) :
    generatorZero a b c d * generatorZero a b c d = (a : K) • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.i_mul_i]
  simp only [zero_smul, add_zero, one_mul]
  rw [← TensorProduct.smul_tmul']
  rfl

private theorem generatorOne_sq (a b c d : Kˣ) :
    generatorOne a b c d * generatorOne a b c d = (b : K) • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.j_mul_j]
  simp only [one_mul]
  rw [← TensorProduct.smul_tmul']
  rfl

private theorem generatorTwo_sq (a b c d : Kˣ) :
    generatorTwo a b c d * generatorTwo a b c d = (c : K) • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.k_mul_k, _root_.QuaternionAlgebra.Basis.i_mul_i]
  simp only [zero_smul, add_zero]
  rw [← neg_smul]
  change (((-((a : K) * (b : K))) • (1 : firstQuaternion a b)) ⊗ₜ[K]
      (((-((a * b)⁻¹ * c) : Kˣ) : K) • (1 : secondQuaternion a b c d))) =
    (c : K) • (1 : fourQuaternionTensor a b c d)
  rw [TensorProduct.smul_tmul_smul]
  congr 1
  simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

private theorem generatorThree_sq (a b c d : Kˣ) :
    generatorThree a b c d * generatorThree a b c d = (d : K) • 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    _root_.QuaternionAlgebra.Basis.k_mul_k, _root_.QuaternionAlgebra.Basis.j_mul_j]
  rw [← neg_smul]
  change (((-((a : K) * (b : K))) • (1 : firstQuaternion a b)) ⊗ₜ[K]
      (((-((a * b)⁻¹ * d) : Kˣ) : K) • (1 : secondQuaternion a b c d))) =
    (d : K) • (1 : fourQuaternionTensor a b c d)
  rw [TensorProduct.smul_tmul_smul]
  congr 1
  simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

private theorem generator_pair_anticommute (a b c d : Kˣ) :
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
  constructor
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.QuaternionAlgebra.Basis.i_mul_j, _root_.QuaternionAlgebra.Basis.j_mul_i]
    simp only [zero_smul, zero_sub, one_mul]
    rw [TensorProduct.neg_tmul]
    abel
  constructor
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.QuaternionAlgebra.Basis.i_mul_k, _root_.QuaternionAlgebra.Basis.k_mul_i]
    simp only [zero_smul, add_zero, one_mul, mul_one]
    rw [← TensorProduct.add_tmul]
    rw [neg_smul, add_neg_cancel, TensorProduct.zero_tmul]
  constructor
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.QuaternionAlgebra.Basis.i_mul_k, _root_.QuaternionAlgebra.Basis.k_mul_i]
    simp only [zero_smul, add_zero, one_mul, mul_one]
    rw [← TensorProduct.add_tmul]
    rw [neg_smul, add_neg_cancel, TensorProduct.zero_tmul]
  constructor
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.QuaternionAlgebra.Basis.j_mul_k, _root_.QuaternionAlgebra.Basis.k_mul_j]
    simp only [zero_mul, zero_smul, one_mul, mul_one]
    rw [← TensorProduct.add_tmul]
    rw [zero_sub, neg_add_cancel, TensorProduct.zero_tmul]
  constructor
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.QuaternionAlgebra.Basis.j_mul_k, _root_.QuaternionAlgebra.Basis.k_mul_j]
    simp only [zero_mul, zero_smul, one_mul, mul_one]
    rw [← TensorProduct.add_tmul]
    rw [zero_sub, neg_add_cancel, TensorProduct.zero_tmul]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.QuaternionAlgebra.Basis.k_mul_k, _root_.QuaternionAlgebra.Basis.i_mul_j,
      _root_.QuaternionAlgebra.Basis.j_mul_i]
    simp only [zero_smul, zero_sub]
    rw [← TensorProduct.tmul_add]
    rw [add_neg_cancel, TensorProduct.tmul_zero]

private theorem fourGenerator_sq (a b c d : Kˣ) (x : Fin 4 → K) :
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
  rw [show
      ((a : K) * (x 0 * x 0) +
        ((b : K) * (x 1 * x 1) + ((c : K) * (x 2 * x 2) + (d : K) * (x 3 * x 3)))) •
          (1 : fourQuaternionTensor a b c d) =
      (x 0 * x 0) • ((a : K) • 1) + (x 1 * x 1) • ((b : K) • 1) +
        (x 2 * x 2) • ((c : K) • 1) + (x 3 * x 3) • ((d : K) • 1) by
    module]
  rw [← generatorZero_sq a b c d, ← generatorOne_sq a b c d,
    ← generatorTwo_sq a b c d, ← generatorThree_sq a b c d]
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
private theorem fourGenerator_single_zero (a b c d : Kˣ) :
    fourGenerator a b c d (Pi.single 0 1) = generatorZero a b c d := by
  simp [fourGenerator]

@[simp]
private theorem fourGenerator_single_one (a b c d : Kˣ) :
    fourGenerator a b c d (Pi.single 1 1) = generatorOne a b c d := by
  simp [fourGenerator]

@[simp]
private theorem fourGenerator_single_two (a b c d : Kˣ) :
    fourGenerator a b c d (Pi.single 2 1) = generatorTwo a b c d := by
  simp [fourGenerator]

@[simp]
private theorem fourGenerator_single_three (a b c d : Kˣ) :
    fourGenerator a b c d (Pi.single 3 1) = generatorThree a b c d := by
  simp [fourGenerator]

private def fourToTensor (a b c d : Kˣ) :
    _root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) →ₐ[K]
      fourQuaternionTensor a b c d :=
  _root_.CliffordAlgebra.lift _ ⟨fourGenerator a b c d, fourGenerator_sq a b c d⟩

@[simp]
private theorem fourToTensor_ue (a b c d : Kˣ) (i : Fin 4) :
    fourToTensor a b c d (_root_.CliffordAlgebra.ι _ (Pi.single i 1)) =
      fourGenerator a b c d (Pi.single i 1) := by
  rw [fourToTensor, _root_.CliffordAlgebra.lift_ι_apply]

private def firstPreimage (a b c d : Kˣ) (x : firstQuaternion a b) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  algebraMap K _ x.re + x.imI • _root_.CliffordAlgebra.ι _ (Pi.single 0 1) +
    x.imJ • _root_.CliffordAlgebra.ι _ (Pi.single 1 1) +
    x.imK • (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single 1 1))

private theorem fourToTensor_firstPreimage (a b c d : Kˣ) (x : firstQuaternion a b) :
    fourToTensor a b c d (firstPreimage a b c d x) = x ⊗ₜ (1 : secondQuaternion a b c d) := by
  rw [firstPreimage, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_mul,
    fourToTensor_ue, fourToTensor_ue]
  have hx : x = (x.re : firstQuaternion a b) +
      x.imI • (_root_.QuaternionAlgebra.Basis.self K).i +
      x.imJ • (_root_.QuaternionAlgebra.Basis.self K).j +
      x.imK • (_root_.QuaternionAlgebra.Basis.self K).k := by
    ext <;> simp
  rw [hx]
  simp [TensorProduct.add_tmul, TensorProduct.smul_tmul']

private def secondIpreimage (a b c d : Kˣ) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  (-((a * b)⁻¹ : Kˣ) : K) •
    (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single 1 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single 2 1))

private def secondJpreimage (a b c d : Kˣ) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  (-((a * b)⁻¹ : Kˣ) : K) •
    (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single 1 1) *
      _root_.CliffordAlgebra.ι _ (Pi.single 3 1))

private theorem fourToTensor_secondIpreimage (a b c d : Kˣ) :
    fourToTensor a b c d (secondIpreimage a b c d) =
      (1 : firstQuaternion a b) ⊗ₜ (_root_.QuaternionAlgebra.Basis.self K).i := by
  rw [secondIpreimage, map_smul, map_mul, map_mul,
    fourToTensor_ue, fourToTensor_ue, fourToTensor_ue]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, Fin.isValue,
    fourGenerator_single_zero, fourGenerator_single_one,
    Algebra.TensorProduct.tmul_mul_tmul, _root_.QuaternionAlgebra.Basis.i_self,
    _root_.QuaternionAlgebra.Basis.j_self, _root_.QuaternionAlgebra.mk_mul_mk, mul_zero,
    mul_one, add_zero, zero_mul, sub_self, zero_add, sub_zero, fourGenerator_single_two,
    _root_.QuaternionAlgebra.Basis.k_self, zero_sub, Units.val_neg, one_mul, neg_smul]
  rw [← neg_smul, TensorProduct.smul_tmul']
  congr 1
  ext <;> simp [mul_assoc]

private theorem fourToTensor_secondJpreimage (a b c d : Kˣ) :
    fourToTensor a b c d (secondJpreimage a b c d) =
      (1 : firstQuaternion a b) ⊗ₜ (_root_.QuaternionAlgebra.Basis.self K).j := by
  rw [secondJpreimage, map_smul, map_mul, map_mul,
    fourToTensor_ue, fourToTensor_ue, fourToTensor_ue]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, Fin.isValue,
    fourGenerator_single_zero, fourGenerator_single_one,
    Algebra.TensorProduct.tmul_mul_tmul, _root_.QuaternionAlgebra.Basis.i_self,
    _root_.QuaternionAlgebra.Basis.j_self, _root_.QuaternionAlgebra.mk_mul_mk, mul_zero,
    mul_one, add_zero, zero_mul, sub_self, zero_add, sub_zero, fourGenerator_single_three,
    _root_.QuaternionAlgebra.Basis.k_self, zero_sub, Units.val_neg, one_mul, neg_smul]
  rw [← neg_smul, TensorProduct.smul_tmul']
  congr 1
  ext <;> simp [mul_assoc]

private def secondPreimage (a b c d : Kˣ) (x : secondQuaternion a b c d) :
    _root_.CliffordAlgebra
      (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) :=
  algebraMap K _ x.re + x.imI • secondIpreimage a b c d +
    x.imJ • secondJpreimage a b c d +
    x.imK • (secondIpreimage a b c d * secondJpreimage a b c d)

private theorem fourToTensor_secondPreimage (a b c d : Kˣ) (x : secondQuaternion a b c d) :
    fourToTensor a b c d (secondPreimage a b c d x) = (1 : firstQuaternion a b) ⊗ₜ x := by
  rw [secondPreimage, map_add, map_add, map_add, (fourToTensor a b c d).commutes,
    map_smul, map_smul, map_smul, map_mul, fourToTensor_secondIpreimage,
    fourToTensor_secondJpreimage]
  have hx : x = (x.re : secondQuaternion a b c d) +
      x.imI • (_root_.QuaternionAlgebra.Basis.self K).i +
      x.imJ • (_root_.QuaternionAlgebra.Basis.self K).j +
      x.imK • (_root_.QuaternionAlgebra.Basis.self K).k := by
    ext <;> simp
  conv_rhs => rw [hx]
  rw [TensorProduct.tmul_add, TensorProduct.tmul_add, TensorProduct.tmul_add,
    Algebra.TensorProduct.algebraMap_apply',
    Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    _root_.QuaternionAlgebra.Basis.i_mul_j]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul]
  rfl

private theorem fourToTensor_surjective (a b c d : Kˣ) :
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

private theorem fourToTensor_bijective [Invertible (2 : K)] (a b c d : Kˣ) :
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

/-- **The Clifford algebra of a four-dimensional diagonal form** as a tensor product of two
quaternion algebras:
`Cl<a,b,c,d> ≃ (a,b) ⊗ (-c/(ab),-d/(ab))`. -/
noncomputable def weightedSumSquaresFourEquivTensorQuaternion [Invertible (2 : K)] (a b c d : Kˣ) :
    _root_.CliffordAlgebra
        (QuadraticMap.weightedSumSquares K ![(a : K), (b : K), (c : K), (d : K)]) ≃ₐ[K]
      (ℍ[K,(a : K),(b : K)] ⊗[K]
        ℍ[K,(-((a * b)⁻¹ * c) : Kˣ),(-((a * b)⁻¹ * d) : Kˣ)]) :=
  AlgEquiv.ofBijective (fourToTensor a b c d) (fourToTensor_bijective a b c d)

end CliffordAlgebra
