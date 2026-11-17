/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basis
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
public import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# The zero-sum coordinate model of the root lattice of type `Aₙ`

The classical coordinate model of the root lattice of type `Aₙ` is

```text
Aₙ = {x ∈ ℤ^{n+1} | x₀ + x₁ + ⋯ + xₙ = 0}
```

with the standard dot product.  It has rank `n`, so it is not a full lattice in `ℚ^{n+1}`.  This
file therefore places it in its rational span, the hyperplane of vectors of `ℚ^{n+1}` with
coordinate sum zero, which is the kernel `TauCeti.singleParityCheckCode ℚ (Fin (n + 1))` of the
coordinate-sum map, and proves that this coordinate model is isometric to the
simple-root model `TauCeti.IntegralLattice.typeARootLattice n`, whose Gram matrix is the Cartan
matrix `CartanMatrix.A n`.

The Bourbaki simple roots `αᵢ = eᵢ - eᵢ₊₁` for `0 ≤ i < n` are the canonical adjacent-difference
basis `TauCeti.singleParityCheckCodeBasis ℚ n` from
`TauCeti.InformationTheory.Coding.Elementary.Basis`, whose coordinates are the initial partial
sums `x₀ + ⋯ + xₖ`.  Their dot products are the entries of `CartanMatrix.A n`, and because the
partial sums of an integral vector are integers, their integral span is exactly the set of
integral vectors in the hyperplane.

## Main declarations

* `TauCeti.IntegralLattice.dotProduct_singleParityCheckCodeBasis`: the dot products of the
  adjacent-difference basis vectors are the entries of `CartanMatrix.A n`.
* `TauCeti.IntegralLattice.zeroSumLattice`: the lattice `Aₙ` with the restricted dot product.
* `TauCeti.IntegralLattice.mem_zeroSumLattice_carrier_iff`: its carrier consists exactly of the
  integral vectors of coordinate sum zero.
* `TauCeti.IntegralLattice.gramMatrix_zeroSumSimpleRootBasis`: its Gram matrix in the simple
  roots is `CartanMatrix.A n`.
* `TauCeti.IntegralLattice.typeAIsometryZeroSumLattice`: the isometry from the simple-root model
  of `Aₙ` onto the coordinate model, carrying the `i`-th simple root to `eᵢ - eᵢ₊₁`.
* `TauCeti.IntegralLattice.typeAIsometryZeroSumLattice_typeAFundamentalWeight_apply`: it carries
  the first fundamental weight `ω₁` to `e₀ - (1 / (n + 1)) (1, …, 1)`.
* `TauCeti.IntegralLattice.typeARootLattice_form_self_eq_dotProduct`: it turns the norm of the
  simple-root model into the dot product of classical coordinates.
* `TauCeti.IntegralLattice.exists_typeAIsometryZeroSumLattice_apply_eq_intCast_sub_of_mk_eq`: the
  classical coordinates of a dual vector in the class `k ω₁` lie in `ℤ - k / (n + 1)`.
* `TauCeti.IntegralLattice.isEven_zeroSumLattice`, `isPosDef_zeroSumLattice` and
  `determinant_zeroSumLattice`: the coordinate model is even and positive definite, of
  determinant `n + 1`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, plate I.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §6.1.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Finset Matrix Module

variable (n : ℕ)

/-! ## The Gram matrix of the simple roots in classical coordinates -/

/-- **The dot products of the adjacent-difference basis vectors are the entries of the Cartan
matrix of type `Aₙ`.** -/
theorem dotProduct_singleParityCheckCodeBasis (i j : Fin n) :
    (singleParityCheckCodeBasis ℚ n i : Fin (n + 1) → ℚ) ⬝ᵥ
      (singleParityCheckCodeBasis ℚ n j : Fin (n + 1) → ℚ) = (CartanMatrix.A n i j : ℚ) := by
  simp only [coe_singleParityCheckCodeBasis_apply, dotProduct_sub, dotProduct_single, mul_one]
  simp only [Pi.sub_apply, Pi.single_apply, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ## The coordinate lattice -/

/-- The dot product of `ℚ^{n+1}`, restricted to the zero-sum hyperplane. -/
noncomputable def zeroSumForm :
    LinearMap.BilinForm ℚ (singleParityCheckCode ℚ (Fin (n + 1))) :=
  LinearMap.BilinForm.restrict (dotProductBilin ℚ ℚ) (singleParityCheckCode ℚ (Fin (n + 1)))

@[simp]
theorem zeroSumForm_apply (x y : singleParityCheckCode ℚ (Fin (n + 1))) :
    zeroSumForm n x y = (x : Fin (n + 1) → ℚ) ⬝ᵥ (y : Fin (n + 1) → ℚ) :=
  (rfl)

/-- **The coordinate model of the root lattice of type `Aₙ`**: the integral vectors of `ℚ^{n+1}`
with coordinate sum zero, with the standard dot product, as a lattice in the zero-sum hyperplane
(`TauCeti.IntegralLattice.mem_zeroSumLattice_carrier_iff`).  It is isometric to the simple-root
model `TauCeti.IntegralLattice.typeARootLattice n` by
`TauCeti.IntegralLattice.typeAIsometryZeroSumLattice`. -/
noncomputable def zeroSumLattice : IntegralLattice (singleParityCheckCode ℚ (Fin (n + 1))) :=
  ofBasis (singleParityCheckCodeBasis ℚ n) (zeroSumForm n)
    (isSymm_dotProductBilin.restrict _) fun i j ↦ by
    rw [zeroSumForm_apply, dotProduct_singleParityCheckCodeBasis]
    exact Submodule.mem_one.mpr ⟨CartanMatrix.A n i j, rfl⟩

@[simp]
theorem zeroSumLattice_form : (zeroSumLattice n).form = zeroSumForm n :=
  ofBasis_form _ _ _ _

theorem zeroSumLattice_carrier :
    (zeroSumLattice n).carrier = Submodule.span ℤ (Set.range (singleParityCheckCodeBasis ℚ n)) :=
  ofBasis_carrier _ _ _ _

/-- **The carrier of the coordinate model consists of the integral vectors with coordinate sum
zero.** Membership in the hyperplane is the coordinate-sum condition, and the simple roots span
its integral vectors over `ℤ` because the partial sums of an integral vector are integers. -/
@[simp]
theorem mem_zeroSumLattice_carrier_iff (x : singleParityCheckCode ℚ (Fin (n + 1))) :
    x ∈ (zeroSumLattice n).carrier ↔ ∀ i, ∃ m : ℤ, (x : Fin (n + 1) → ℚ) i = m := by
  rw [zeroSumLattice_carrier]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro i
      refine ⟨(if i = k.castSucc then 1 else 0) - if i = k.succ then 1 else 0, ?_⟩
      rw [coe_singleParityCheckCodeBasis_apply_apply]
      split_ifs <;> simp
    | zero => exact fun _ ↦ ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro i
      obtain ⟨a, ha⟩ := hy i
      obtain ⟨b, hb⟩ := hz i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul c y _ hy =>
      intro i
      obtain ⟨a, ha⟩ := hy i
      exact ⟨c * a, by simp [ha]⟩
  · intro hx
    choose m hm using hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun k ↦ ∑ j ∈ Iic k.castSucc, m j, ?_⟩
    conv_rhs => rw [← (singleParityCheckCodeBasis ℚ n).sum_repr x]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [singleParityCheckCodeBasis_repr_apply, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_sum]
    simp only [hm]

/-- The simple roots `eᵢ - eᵢ₊₁`, as a `ℤ`-basis of the coordinate model. -/
noncomputable def zeroSumSimpleRootBasis : Basis (Fin n) ℤ (zeroSumLattice n) :=
  ofBasis.basis (singleParityCheckCodeBasis ℚ n) (zeroSumForm n) _ _

@[simp]
theorem coe_zeroSumSimpleRootBasis_apply (i : Fin n) :
    (zeroSumSimpleRootBasis n i : singleParityCheckCode ℚ (Fin (n + 1))) =
      singleParityCheckCodeBasis ℚ n i :=
  ofBasis.coe_basis _ _ _ _ i

/-- **The Gram matrix of the coordinate model in the simple roots is the Cartan matrix of type
`Aₙ`.** -/
@[simp]
theorem gramMatrix_zeroSumSimpleRootBasis :
    (zeroSumLattice n).gramMatrix (zeroSumSimpleRootBasis n) = CartanMatrix.A n := by
  ext i j
  have h := intCast_gramMatrix_apply (zeroSumLattice n) (zeroSumSimpleRootBasis n) i j
  rw [zeroSumLattice_form, zeroSumForm_apply, coe_zeroSumSimpleRootBasis_apply,
    coe_zeroSumSimpleRootBasis_apply, dotProduct_singleParityCheckCodeBasis] at h
  exact_mod_cast h

/-! ## The isometry with the simple-root model -/

/-- **The simple-root model of the root lattice of type `Aₙ` is isometric to the coordinate
model** `{x ∈ ℤ^{n+1} | ∑ xᵢ = 0}`, by the isometry carrying the `i`-th simple root to
`eᵢ - eᵢ₊₁`. -/
noncomputable def typeAIsometryZeroSumLattice :
    Isometry (typeARootLattice n) (zeroSumLattice n) :=
  Isometry.ofGramMatrixEq (typeASimpleRootBasis n) (zeroSumSimpleRootBasis n)
    (by rw [gramMatrix_typeASimpleRootBasis, gramMatrix_zeroSumSimpleRootBasis])

/-- The isometry `typeAIsometryZeroSumLattice` carries the `i`-th simple root of the simple-root
model to `eᵢ - eᵢ₊₁`. -/
@[simp]
theorem typeAIsometryZeroSumLattice_typeASimpleRoot (i : Fin n) :
    typeAIsometryZeroSumLattice n (typeASimpleRoot n i) = singleParityCheckCodeBasis ℚ n i := by
  rw [← coe_typeASimpleRootBasis_apply, typeAIsometryZeroSumLattice,
    Isometry.ofGramMatrixEq_apply_basis, coe_zeroSumSimpleRootBasis_apply]

/-- **The first fundamental weight in classical coordinates.** The isometry
`typeAIsometryZeroSumLattice` carries `ω₁` to `e₀ - (1 / (n + 1)) (1, …, 1)`. -/
@[simp]
theorem typeAIsometryZeroSumLattice_typeAFundamentalWeight_apply (j : Fin (n + 1)) :
    (typeAIsometryZeroSumLattice n (typeAFundamentalWeight n) : Fin (n + 1) → ℚ) j =
      (if j = 0 then 1 else 0) - 1 / ((n : ℚ) + 1) := by
  set w : Fin (n + 1) → ℚ := fun j ↦ (if j = 0 then 1 else 0) - 1 / ((n : ℚ) + 1)
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have hw : w ∈ singleParityCheckCode ℚ (Fin (n + 1)) := by
    rw [mem_singleParityCheckCode]
    simp [w, sum_sub_distrib]
    field_simp
    norm_num
  have key : (typeAIsometryZeroSumLattice n (typeAFundamentalWeight n) : Fin (n + 1) → ℚ) = w := by
    rw [← sum_smul_coe_singleParityCheckCodeBasis ℚ hw]
    conv_lhs => rw [← sum_smul_typeASimpleRoot (typeAFundamentalWeight n), map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul,
      typeAIsometryZeroSumLattice_typeASimpleRoot]
    refine sum_congr rfl fun k _ ↦
      congrArg (· • (singleParityCheckCodeBasis ℚ n k : Fin (n + 1) → ℚ)) ?_
    simp [w, typeAFundamentalWeight_apply, sum_sub_distrib]
    field_simp
    ring
  exact congrFun key j

variable {n} in
/-- The norm of a vector of the ambient space of the simple-root model of `Aₙ` is the dot product
of its classical coordinates with themselves. -/
theorem typeARootLattice_form_self_eq_dotProduct (x : Fin n → ℚ) :
    (typeARootLattice n).form x x =
      (typeAIsometryZeroSumLattice n x : Fin (n + 1) → ℚ) ⬝ᵥ
        (typeAIsometryZeroSumLattice n x : Fin (n + 1) → ℚ) := by
  rw [← (typeAIsometryZeroSumLattice n).map_app, zeroSumLattice_form, zeroSumForm_apply]

variable {n} in
/-- **The classical coordinates of the class `k ω₁`.** The classical coordinates of a dual vector
of `Aₙ` in the discriminant class `k ω₁` all lie in `ℤ - k / (n + 1)`. -/
theorem exists_typeAIsometryZeroSumLattice_apply_eq_intCast_sub_of_mk_eq {k : ℤ}
    (x : (typeARootLattice n).dualCarrier)
    (hx : (Submodule.Quotient.mk x : (typeARootLattice n).DiscriminantGroup) =
      k • typeAFundamentalWeightClass n) (j : Fin (n + 1)) :
    ∃ m : ℤ, (typeAIsometryZeroSumLattice n x : Fin (n + 1) → ℚ) j = m - k / (n + 1) := by
  rw [mk_eq_zsmul_typeAFundamentalWeightClass_iff,
    ← (typeAIsometryZeroSumLattice n).apply_mem_carrier_iff, mem_zeroSumLattice_carrier_iff] at hx
  obtain ⟨m, hm⟩ := hx j
  refine ⟨m + k * if j = 0 then 1 else 0, ?_⟩
  rw [map_sub, map_zsmul] at hm
  simp at hm
  push_cast
  linear_combination hm

/-! ## Invariants of the coordinate model -/

/-- The coordinate model of `Aₙ` is even. -/
theorem isEven_zeroSumLattice : (zeroSumLattice n).IsEven :=
  (typeAIsometryZeroSumLattice n).isEven_iff.mp (isEven_typeARootLattice n)

/-- The coordinate model of `Aₙ` is positive definite. -/
theorem isPosDef_zeroSumLattice : (zeroSumLattice n).IsPosDef :=
  (typeAIsometryZeroSumLattice n).isPosDef_iff.mp (isPosDef_typeARootLattice n)

/-- The determinant of the coordinate model of `Aₙ` is `n + 1`. -/
@[simp]
theorem determinant_zeroSumLattice : (zeroSumLattice n).determinant = (n : ℤ) + 1 := by
  rw [← (typeAIsometryZeroSumLattice n).determinant_eq, determinant_typeARootLattice]

end IntegralLattice

end TauCeti
