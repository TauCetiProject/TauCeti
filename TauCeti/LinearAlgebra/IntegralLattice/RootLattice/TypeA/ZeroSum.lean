/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
public import TauCeti.LinearAlgebra.Matrix.Dual

import TauCeti.Algebra.BigOperators.Finset.PartialSum

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

The Bourbaki simple roots are `αᵢ = eᵢ - eᵢ₊₁` for `0 ≤ i < n`, and their dot products are the
entries of `CartanMatrix.A n`.  The coefficients of a vector in this basis are read off by the
partial sums: pairing `αᵢ` with the indicator vector of the coordinates `0, …, k` gives `1` when
`i = k` and `0` otherwise, while pairing it with the all-ones vector gives `0`.  Consequently

```text
x = ∑ₖ (x₀ + ⋯ + xₖ) αₖ        whenever x₀ + ⋯ + xₙ = 0,
```

because the difference of the two sides has every partial sum equal to zero, and a vector all of
whose partial sums vanish is zero.  This identity shows at once that the simple roots form a
rational basis of the hyperplane and that their integral span is exactly the set of integral
vectors in it, since the partial sums of an integral vector are integers.

## Main declarations

* `TauCeti.IntegralLattice.zeroSumSimpleRoot`: the simple root `eᵢ - eᵢ₊₁`.
* `TauCeti.IntegralLattice.sum_smul_zeroSumSimpleRoot`: the partial-sum expansion of a vector of
  coordinate sum zero in the simple roots.
* `TauCeti.IntegralLattice.zeroSumBasis`: the simple roots as a rational basis of the hyperplane.
* `TauCeti.IntegralLattice.zeroSumLattice`: the lattice `Aₙ` with the restricted dot product.
* `TauCeti.IntegralLattice.mem_zeroSumLattice_carrier_iff`: its carrier consists exactly of the
  integral vectors of coordinate sum zero.
* `TauCeti.IntegralLattice.gramMatrix_zeroSumSimpleRootBasis`: its Gram matrix in the simple
  roots is `CartanMatrix.A n`.
* `TauCeti.IntegralLattice.typeAIsometryZeroSumLattice`: the isometry from the simple-root model
  of `Aₙ` onto the coordinate model, carrying the `i`-th simple root to `eᵢ - eᵢ₊₁`.
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

/-! ## The simple roots in classical coordinates -/

/-- The `i`-th Bourbaki simple root `eᵢ - eᵢ₊₁` of type `Aₙ` in the classical coordinates of
`ℚ^{n+1}`. -/
def zeroSumSimpleRoot (i : Fin n) : Fin (n + 1) → ℚ :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

theorem zeroSumSimpleRoot_apply (i : Fin n) (j : Fin (n + 1)) :
    zeroSumSimpleRoot n i j = (if j = i.castSucc then 1 else 0) - if j = i.succ then 1 else 0 := by
  simp [zeroSumSimpleRoot, Pi.single_apply]

/-- Every simple root has coordinate sum zero. -/
theorem zeroSumSimpleRoot_mem_singleParityCheckCode (i : Fin n) :
    zeroSumSimpleRoot n i ∈ singleParityCheckCode ℚ (Fin (n + 1)) := by
  simp [zeroSumSimpleRoot, sum_sub_distrib]

/-- **The dot products of the simple roots are the entries of the Cartan matrix of type `Aₙ`.** -/
theorem zeroSumSimpleRoot_dotProduct_zeroSumSimpleRoot (i j : Fin n) :
    zeroSumSimpleRoot n i ⬝ᵥ zeroSumSimpleRoot n j = (CartanMatrix.A n i j : ℚ) := by
  simp only [zeroSumSimpleRoot, dotProduct_sub, dotProduct_single, mul_one]
  simp only [Pi.sub_apply, Pi.single_apply, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ## Partial sums and the expansion in the simple roots -/

/-- The partial sum `x₀ + ⋯ + xₖ` of the simple root `αᵢ` is `[i ≤ k] - [i < k]`; it vanishes
for the full sum `k = n`. -/
private theorem sum_Iic_zeroSumSimpleRoot (i : Fin n) (k : Fin (n + 1)) :
    ∑ j ∈ Iic k, zeroSumSimpleRoot n i j =
      (if i.castSucc ≤ k then 1 else 0) - if i.succ ≤ k then 1 else 0 := by
  simp [zeroSumSimpleRoot, sum_sub_distrib, sum_pi_single']

/-- The partial sum `x₀ + ⋯ + xₖ`, for `k < n`, of the combination `∑ᵢ cᵢ αᵢ` is its
coefficient `c_k`. -/
private theorem sum_Iic_castSucc_sum_smul (c : Fin n → ℚ) (k : Fin n) :
    ∑ j ∈ Iic k.castSucc, (∑ i, c i • zeroSumSimpleRoot n i) j = c k := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  simp only [← mul_sum, sum_Iic_zeroSumSimpleRoot, Fin.castSucc_le_castSucc_iff,
    Fin.succ_le_castSucc_iff]
  rw [sum_eq_single k]
  · simp
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with h | h
    · simp [h.le, h]
    · simp [not_le.mpr h, not_lt.mpr h.le]
  · simp

/-- The full sum `x₀ + ⋯ + xₙ` of a combination of the simple roots is zero. -/
private theorem sum_Iic_last_sum_smul (c : Fin n → ℚ) :
    ∑ j ∈ Iic (Fin.last n), (∑ i, c i • zeroSumSimpleRoot n i) j = 0 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  simp [← mul_sum, sum_Iic_zeroSumSimpleRoot, Fin.le_last]

/-- **The partial-sum expansion.** A vector of `ℚ^{n+1}` with coordinate sum zero is the
combination of the simple roots `αₖ = eₖ - eₖ₊₁` whose coefficients are its partial sums
`x₀ + ⋯ + xₖ`. -/
theorem sum_smul_zeroSumSimpleRoot {x : Fin (n + 1) → ℚ}
    (hx : x ∈ singleParityCheckCode ℚ (Fin (n + 1))) :
    ∑ k : Fin n, (∑ j ∈ Iic k.castSucc, x j) • zeroSumSimpleRoot n k = x := by
  rw [mem_singleParityCheckCode] at hx
  refine (sub_eq_zero.mp (eq_zero_of_forall_sum_Iic_eq_zero n fun k ↦ ?_)).symm
  simp only [Pi.sub_apply, sum_sub_distrib]
  induction k using Fin.lastCases with
  | last =>
    rw [sum_Iic_last_sum_smul, ← Fin.top_eq_last, Iic_top, hx, sub_zero]
  | cast k =>
    rw [sum_Iic_castSucc_sum_smul, sub_self]

/-- **The simple roots `eᵢ - eᵢ₊₁` are linearly independent over `ℚ`.** -/
theorem linearIndependent_zeroSumSimpleRoot : LinearIndependent ℚ (zeroSumSimpleRoot n) := by
  refine Fintype.linearIndependent_iff.mpr fun c hc k ↦ ?_
  rw [← sum_Iic_castSucc_sum_smul n c k, hc]
  simp

/-! ## The simple roots as a basis of the hyperplane -/

/-- **The simple roots form a rational basis of the zero-sum hyperplane**
`TauCeti.singleParityCheckCode ℚ (Fin (n + 1))`. -/
noncomputable def zeroSumBasis : Basis (Fin n) ℚ (singleParityCheckCode ℚ (Fin (n + 1))) :=
  Basis.mk (v := fun i ↦ ⟨zeroSumSimpleRoot n i, zeroSumSimpleRoot_mem_singleParityCheckCode n i⟩)
    (LinearIndependent.of_comp (singleParityCheckCode ℚ (Fin (n + 1))).subtype
      (linearIndependent_zeroSumSimpleRoot n))
    fun x _ ↦ by
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨fun k ↦ ∑ j ∈ Iic k.castSucc, (x : Fin (n + 1) → ℚ) j, Subtype.ext <| by
        simpa using sum_smul_zeroSumSimpleRoot n x.2⟩

@[simp]
theorem coe_zeroSumBasis_apply (i : Fin n) :
    (zeroSumBasis n i : Fin (n + 1) → ℚ) = zeroSumSimpleRoot n i := by
  simp [zeroSumBasis]

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
  ofBasis (zeroSumBasis n) (zeroSumForm n) (isSymm_dotProductBilin.restrict _) fun i j ↦ by
    rw [zeroSumForm_apply, coe_zeroSumBasis_apply, coe_zeroSumBasis_apply,
      zeroSumSimpleRoot_dotProduct_zeroSumSimpleRoot]
    exact Submodule.mem_one.mpr ⟨CartanMatrix.A n i j, rfl⟩

@[simp]
theorem zeroSumLattice_form : (zeroSumLattice n).form = zeroSumForm n :=
  ofBasis_form _ _ _ _

theorem zeroSumLattice_carrier :
    (zeroSumLattice n).carrier = Submodule.span ℤ (Set.range (zeroSumBasis n)) :=
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
      rw [coe_zeroSumBasis_apply, zeroSumSimpleRoot_apply]
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
    refine ⟨fun k ↦ ∑ j ∈ Iic k.castSucc, m j, Subtype.ext ?_⟩
    conv_rhs => rw [← sum_smul_zeroSumSimpleRoot n x.2]
    rw [Submodule.coe_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [Submodule.coe_smul_of_tower, coe_zeroSumBasis_apply, ← Int.cast_smul_eq_zsmul ℚ,
      Int.cast_sum]
    simp only [hm]

/-- The simple roots `eᵢ - eᵢ₊₁`, as a `ℤ`-basis of the coordinate model. -/
noncomputable def zeroSumSimpleRootBasis : Basis (Fin n) ℤ (zeroSumLattice n) :=
  ofBasis.basis (zeroSumBasis n) (zeroSumForm n) _ _

@[simp]
theorem coe_zeroSumSimpleRootBasis_apply (i : Fin n) :
    ((zeroSumSimpleRootBasis n i : singleParityCheckCode ℚ (Fin (n + 1))) : Fin (n + 1) → ℚ) =
      zeroSumSimpleRoot n i := by
  rw [← coe_zeroSumBasis_apply]
  exact congrArg Subtype.val (ofBasis.coe_basis _ _ _ _ i)

/-- **The Gram matrix of the coordinate model in the simple roots is the Cartan matrix of type
`Aₙ`.** -/
@[simp]
theorem gramMatrix_zeroSumSimpleRootBasis :
    (zeroSumLattice n).gramMatrix (zeroSumSimpleRootBasis n) = CartanMatrix.A n := by
  ext i j
  have h := intCast_gramMatrix_apply (zeroSumLattice n) (zeroSumSimpleRootBasis n) i j
  rw [zeroSumLattice_form, zeroSumForm_apply, coe_zeroSumSimpleRootBasis_apply,
    coe_zeroSumSimpleRootBasis_apply, zeroSumSimpleRoot_dotProduct_zeroSumSimpleRoot] at h
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
    (typeAIsometryZeroSumLattice n (typeASimpleRoot n i) : Fin (n + 1) → ℚ) =
      zeroSumSimpleRoot n i := by
  rw [← coe_typeASimpleRootBasis_apply, typeAIsometryZeroSumLattice,
    Isometry.ofGramMatrixEq_apply_basis, coe_zeroSumSimpleRootBasis_apply]

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
