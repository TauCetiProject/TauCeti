/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
import Mathlib.Tactic.FinCases

/-!
# The even Clifford algebra of the split quaternary form

Let `R` be a commutative ring and `q₄ = TauCeti.splitEvenForm R 2` the split quadratic form
`(φ, x) ↦ φ x` on `(R²)* × R²`. Its even Clifford algebra is the product `M₂(R) × M₂(R)` of two
matrix algebras. No hypothesis on `2` is needed, so this holds over `ℤ`.

Write `φ₀ = φ e₀`, `φ₁ = φ e₁` for the coordinates of `φ` on the standard basis `e₀, e₁` of `R²`,
and set `B(φ, x) = !![φ₀, φ₁; -x₁, x₀]` and `C(φ, x) = !![x₀, -φ₁; x₁, φ₀]`, the adjugate of
`B(φ, x)`. Both products `B C` and `C B` are `q₄(φ, x)` times the identity. In terms of the
spinor module `⋀ R²`, on which `x` acts by exterior multiplication and `φ` by contraction, `C` is
the action of a vector from the even part `⟨1, e₀ ∧ e₁⟩` to the odd part `⟨e₀, e₁⟩` and `B` the
action from the odd part back to the even part. Hence `ι m₁ ι m₂ ↦ (B m₁ C m₂, C m₁ B m₂)` defines
an algebra map from the even Clifford algebra to `M₂(R) × M₂(R)`, its action on the two halves of
the spinor module.

For the inverse, write `aᵢ = ι (0, eᵢ)` and `bᵢ = ι (εᵢ, 0)`, so that `aᵢ² = bᵢ² = 0`, distinct
generators anticommute, and `aᵢ bᵢ + bᵢ aᵢ = 1`. The even elements `b₀a₀b₁a₁`, `b₁b₀`, `a₀a₁`,
`a₀b₀a₁b₁` form a system of matrix units for the first factor, and `a₀b₀b₁a₁`, `a₀b₁`, `a₁b₀`,
`b₀a₀a₁b₁` one for the second factor, the two systems being orthogonal with total sum `1`.
They define an algebra map from `M₂(R) × M₂(R)` back to the even Clifford algebra.

The equivalence is natural in `R`: along an algebra `R → S`, the base change map of even Clifford
algebras, `ι m₁ ι m₂ ↦ ι m₁_S ι m₂_S`, corresponds to applying `R → S` to the matrix entries.

## Main definitions

* `TauCeti.splitEvenTwoToMatrix`: the linear map `(φ, x) ↦ !![φ₀, φ₁; -x₁, x₀]`.
* `TauCeti.splitEvenTwoToMatrixAdj`: the linear map `(φ, x) ↦ !![x₀, -φ₁; x₁, φ₀]`.
* `TauCeti.splitEvenTwoEvenEquivMatrixProd`: the equivalence
  `CliffordAlgebra.even (splitEvenForm R 2) ≃ₐ[R] M₂(R) × M₂(R)`.
* `TauCeti.splitEvenTwoSpaceBaseChange`, `TauCeti.splitEvenTwoEvenBaseChange`: base change of
  the split quaternary space and of its even Clifford algebra along an algebra `R → S`.

## Main results

* `TauCeti.splitEvenTwoEvenEquivMatrixProd_ι`: the equivalence sends the even element `ι m₁ ι m₂`
  to the pair of matrices `(B m₁ C m₂, C m₁ B m₂)`.
* `TauCeti.splitEvenTwoEvenEquivMatrixProd_splitEvenTwoEvenBaseChange`: naturality of the
  equivalence in `R`.
-/

public section

open scoped Matrix

namespace TauCeti

open _root_.CliffordAlgebra

variable (R : Type*) [CommRing R]

/-- The matrix `!![φ₀, φ₁; -x₁, x₀]` of a vector `(φ, x)` of the split quaternary space, where
`φᵢ = φ eᵢ`. It maps the odd half `⟨e₀, e₁⟩` of the spinor module to the even half
`⟨1, e₀ ∧ e₁⟩`. -/
noncomputable def splitEvenTwoToMatrix :
    SplitEvenSpace R 2 →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun m := !![m.1 (Pi.single 0 1), m.1 (Pi.single 1 1); -m.2 1, m.2 0]
  map_add' m n := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c m := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The matrix of `(φ, x)` is `!![φ e₀, φ e₁; -x₁, x₀]`. -/
@[simp]
theorem splitEvenTwoToMatrix_apply (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrix R m = !![m.1 (Pi.single 0 1), m.1 (Pi.single 1 1); -m.2 1, m.2 0] :=
  (rfl)

/-- The matrix `!![x₀, -φ₁; x₁, φ₀]` of a vector `(φ, x)` of the split quaternary space, the
adjugate of `splitEvenTwoToMatrix R (φ, x)`. It maps the even half `⟨1, e₀ ∧ e₁⟩` of the spinor
module to the odd half `⟨e₀, e₁⟩`. -/
noncomputable def splitEvenTwoToMatrixAdj :
    SplitEvenSpace R 2 →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun m := !![m.2 0, -m.1 (Pi.single 1 1); m.2 1, m.1 (Pi.single 0 1)]
  map_add' m n := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c m := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The adjugate matrix of `(φ, x)` is `!![x₀, -φ e₁; x₁, φ e₀]`. -/
@[simp]
theorem splitEvenTwoToMatrixAdj_apply (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrixAdj R m = !![m.2 0, -m.1 (Pi.single 1 1); m.2 1, m.1 (Pi.single 0 1)] :=
  (rfl)

/-- `splitEvenTwoToMatrixAdj` is the adjugate of `splitEvenTwoToMatrix`. -/
theorem splitEvenTwoToMatrixAdj_eq_adjugate (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrixAdj R m = (splitEvenTwoToMatrix R m).adjugate := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem splitEvenForm_two_apply (m : SplitEvenSpace R 2) :
    splitEvenForm R 2 m = m.1 (Pi.single 0 1) * m.2 0 + m.1 (Pi.single 1 1) * m.2 1 := by
  rw [splitEvenForm_apply]
  conv_lhs => rw [pi_eq_sum_univ' m.2, Fin.sum_univ_two]
  simp [mul_comm]

/-- The determinant of the matrix of `(φ, x)` is `q₄(φ, x) = φ x`. -/
theorem det_splitEvenTwoToMatrix (m : SplitEvenSpace R 2) :
    (splitEvenTwoToMatrix R m).det = splitEvenForm R 2 m := by
  rw [splitEvenForm_two_apply, splitEvenTwoToMatrix_apply, Matrix.det_fin_two_of]
  ring

/-- `B(m) C(m) = q₄(m) • 1`. -/
theorem splitEvenTwoToMatrix_mul_adj (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrix R m * splitEvenTwoToMatrixAdj R m =
      algebraMap R _ (splitEvenForm R 2 m) := by
  rw [splitEvenTwoToMatrixAdj_eq_adjugate, Matrix.mul_adjugate, det_splitEvenTwoToMatrix,
    Algebra.algebraMap_eq_smul_one]

/-- `C(m) B(m) = q₄(m) • 1`. -/
theorem splitEvenTwoToMatrixAdj_mul (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrixAdj R m * splitEvenTwoToMatrix R m =
      algebraMap R _ (splitEvenForm R 2 m) := by
  rw [splitEvenTwoToMatrixAdj_eq_adjugate, Matrix.adjugate_mul, det_splitEvenTwoToMatrix,
    Algebra.algebraMap_eq_smul_one]

/-- The bilinear map `(m₁, m₂) ↦ (B m₁ C m₂, C m₁ B m₂)`, which satisfies the relations of the
even Clifford algebra. -/
private noncomputable def splitEvenTwoEvenHom :
    EvenHom (splitEvenForm R 2) (Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R) where
  bilin := LinearMap.mk₂ R
    (fun m₁ m₂ ↦ (splitEvenTwoToMatrix R m₁ * splitEvenTwoToMatrixAdj R m₂,
      splitEvenTwoToMatrixAdj R m₁ * splitEvenTwoToMatrix R m₂))
    (fun _ _ _ ↦ by simp only [map_add, add_mul, Prod.mk_add_mk])
    (fun _ _ _ ↦ by simp only [map_smul, smul_mul_assoc, Prod.smul_mk])
    (fun _ _ _ ↦ by simp only [map_add, mul_add, Prod.mk_add_mk])
    (fun _ _ _ ↦ by simp only [map_smul, mul_smul_comm, Prod.smul_mk])
  contract m := by
    simp only [LinearMap.mk₂_apply, splitEvenTwoToMatrix_mul_adj, splitEvenTwoToMatrixAdj_mul]
    rfl
  contract_mid m₁ m₂ m₃ := by
    simp only [LinearMap.mk₂_apply, Prod.mk_mul_mk, Prod.smul_mk]
    congr 1
    · rw [mul_assoc, ← mul_assoc (splitEvenTwoToMatrixAdj R m₂), splitEvenTwoToMatrixAdj_mul,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
    · rw [mul_assoc, ← mul_assoc (splitEvenTwoToMatrix R m₂), splitEvenTwoToMatrix_mul_adj,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

/-- The forward map: the action of the even Clifford algebra on the two halves of the spinor
module. -/
private noncomputable def splitEvenTwoEvenToMatrixProd :
    even (splitEvenForm R 2) →ₐ[R] Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R :=
  even.lift _ (splitEvenTwoEvenHom R)

private theorem splitEvenTwoEvenToMatrixProd_ι (m₁ m₂ : SplitEvenSpace R 2) :
    splitEvenTwoEvenToMatrixProd R ((even.ι _).bilin m₁ m₂) =
      (splitEvenTwoToMatrix R m₁ * splitEvenTwoToMatrixAdj R m₂,
        splitEvenTwoToMatrixAdj R m₁ * splitEvenTwoToMatrix R m₂) := by
  simp [splitEvenTwoEvenToMatrixProd, splitEvenTwoEvenHom]

/-! ### Generators and their relations -/

/-- The vector `aᵢ = (0, eᵢ)`. -/
private noncomputable def vecA (i : Fin 2) : SplitEvenSpace R 2 := (0, Pi.single i 1)

/-- The vector `bᵢ = (εᵢ, 0)`, with `εᵢ` the `i`-th coordinate function. -/
private noncomputable def vecB (i : Fin 2) : SplitEvenSpace R 2 := (LinearMap.proj i, 0)

private theorem eq_vec (m : SplitEvenSpace R 2) :
    m = m.2 0 • vecA R 0 + m.2 1 • vecA R 1 + m.1 (Pi.single 0 1) • vecB R 0 +
      m.1 (Pi.single 1 1) • vecB R 1 := by
  obtain ⟨φ, x⟩ := m
  refine Prod.ext ?_ ?_
  · refine LinearMap.ext fun y ↦ ?_
    simp only [vecA, vecB, Prod.fst_add, Prod.smul_fst, smul_zero, zero_add,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    conv_lhs =>
      rw [pi_eq_sum_univ' y, Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul,
        smul_eq_mul]
    ring
  · ext i
    fin_cases i <;> simp [vecA, vecB]

/-- The generator `aᵢ = ι (0, eᵢ)`. -/
private noncomputable def cA (i : Fin 2) : CliffordAlgebra (splitEvenForm R 2) := ι _ (vecA R i)
/-- The generator `bᵢ = ι (εᵢ, 0)`. -/
private noncomputable def cB (i : Fin 2) : CliffordAlgebra (splitEvenForm R 2) := ι _ (vecB R i)

private theorem ι_vecA (i : Fin 2) : ι (splitEvenForm R 2) (vecA R i) = cA R i := rfl
private theorem ι_vecB (i : Fin 2) : ι (splitEvenForm R 2) (vecB R i) = cB R i := rfl

private theorem cA_mul_cA (i : Fin 2) : cA R i * cA R i = 0 := by
  rw [cA, ι_sq_scalar]
  simp [vecA]

private theorem cB_mul_cB (i : Fin 2) : cB R i * cB R i = 0 := by
  rw [cB, ι_sq_scalar]
  simp [vecB]

private theorem cA_add_swap (i j : Fin 2) : cA R i * cA R j + cA R j * cA R i = 0 := by
  rw [cA, cA, ι_mul_ι_add_swap]
  simp [vecA]

private theorem cB_add_swap (i j : Fin 2) : cB R i * cB R j + cB R j * cB R i = 0 := by
  rw [cB, cB, ι_mul_ι_add_swap]
  simp [vecB]

private theorem cB_mul_cA_add_swap (i j : Fin 2) :
    cB R i * cA R j + cA R j * cB R i = if i = j then 1 else 0 := by
  rw [cB, cA, ι_mul_ι_add_swap]
  fin_cases i <;> fin_cases j <;> simp [vecA, vecB]

private theorem cA_one_mul_cA_zero : cA R 1 * cA R 0 = -(cA R 0 * cA R 1) :=
  eq_neg_of_add_eq_zero_left (cA_add_swap R 1 0)

private theorem cB_one_mul_cB_zero : cB R 1 * cB R 0 = -(cB R 0 * cB R 1) :=
  eq_neg_of_add_eq_zero_left (cB_add_swap R 1 0)

private theorem cB_mul_cA_self (i : Fin 2) : cB R i * cA R i = 1 - cA R i * cB R i := by
  rw [eq_sub_iff_add_eq, cB_mul_cA_add_swap, ite_eq_left (rfl : i = i)]

private theorem cB_mul_cA_of_ne {i j : Fin 2} (h : i ≠ j) :
    cB R i * cA R j = -(cA R j * cB R i) := by
  rw [eq_neg_iff_add_eq_zero, cB_mul_cA_add_swap, ite_eq_right h]

private theorem cB_zero_mul_cA_one : cB R 0 * cA R 1 = -(cA R 1 * cB R 0) :=
  cB_mul_cA_of_ne R (by decide)

private theorem cB_one_mul_cA_zero : cB R 1 * cA R 0 = -(cA R 0 * cB R 1) :=
  cB_mul_cA_of_ne R (by decide)

private theorem mul_cA_mul_cA (x : CliffordAlgebra (splitEvenForm R 2)) (i : Fin 2) :
    x * cA R i * cA R i = 0 := by rw [mul_assoc, cA_mul_cA, mul_zero]

private theorem mul_cB_mul_cB (x : CliffordAlgebra (splitEvenForm R 2)) (i : Fin 2) :
    x * cB R i * cB R i = 0 := by rw [mul_assoc, cB_mul_cB, mul_zero]

private theorem mul_cA_one_mul_cA_zero (x : CliffordAlgebra (splitEvenForm R 2)) :
    x * cA R 1 * cA R 0 = -(x * cA R 0 * cA R 1) := by
  rw [mul_assoc, cA_one_mul_cA_zero, mul_neg, mul_assoc]

private theorem mul_cB_one_mul_cB_zero (x : CliffordAlgebra (splitEvenForm R 2)) :
    x * cB R 1 * cB R 0 = -(x * cB R 0 * cB R 1) := by
  rw [mul_assoc, cB_one_mul_cB_zero, mul_neg, mul_assoc]

private theorem mul_cB_mul_cA_self (x : CliffordAlgebra (splitEvenForm R 2)) (i : Fin 2) :
    x * cB R i * cA R i = x - x * cA R i * cB R i := by
  rw [mul_assoc, cB_mul_cA_self, mul_sub, mul_one, mul_assoc]

private theorem mul_cB_zero_mul_cA_one (x : CliffordAlgebra (splitEvenForm R 2)) :
    x * cB R 0 * cA R 1 = -(x * cA R 1 * cB R 0) := by
  rw [mul_assoc, cB_zero_mul_cA_one, mul_neg, mul_assoc]

private theorem mul_cB_one_mul_cA_zero (x : CliffordAlgebra (splitEvenForm R 2)) :
    x * cB R 1 * cA R 0 = -(x * cA R 0 * cB R 1) := by
  rw [mul_assoc, cB_one_mul_cA_zero, mul_neg, mul_assoc]

attribute [local simp] ι_vecA ι_vecB cA_mul_cA cB_mul_cB cA_one_mul_cA_zero
  cB_one_mul_cB_zero cB_mul_cA_self cB_zero_mul_cA_one cB_one_mul_cA_zero mul_cA_mul_cA
  mul_cB_mul_cB mul_cA_one_mul_cA_zero mul_cB_one_mul_cB_zero mul_cB_mul_cA_self
  mul_cB_zero_mul_cA_one mul_cB_one_mul_cA_zero mul_add add_mul mul_sub sub_mul

/-! ### Matrix units -/

/-- The even element `ι m₁ ι m₂`. -/
private noncomputable abbrev pair (m₁ m₂ : SplitEvenSpace R 2) : even (splitEvenForm R 2) :=
  (even.ι _).bilin m₁ m₂

/-- The matrix units: `unit 0 i j` and `unit 1 i j` act as the matrix unit `Eᵢⱼ` on the even and
odd halves of the spinor module respectively, and by zero on the other half. -/
private noncomputable def unit : Fin 2 → Fin 2 → Fin 2 → even (splitEvenForm R 2)
  | 0, 0, 0 => pair R (vecB R 0) (vecA R 0) * pair R (vecB R 1) (vecA R 1)
  | 0, 0, 1 => pair R (vecB R 1) (vecB R 0)
  | 0, 1, 0 => pair R (vecA R 0) (vecA R 1)
  | 0, 1, 1 => pair R (vecA R 0) (vecB R 0) * pair R (vecA R 1) (vecB R 1)
  | 1, 0, 0 => pair R (vecA R 0) (vecB R 0) * pair R (vecB R 1) (vecA R 1)
  | 1, 0, 1 => pair R (vecA R 0) (vecB R 1)
  | 1, 1, 0 => pair R (vecA R 1) (vecB R 0)
  | 1, 1, 1 => pair R (vecB R 0) (vecA R 0) * pair R (vecA R 1) (vecB R 1)

private theorem unit_mul_unit (s i j t k l : Fin 2) :
    unit R s i j * unit R t k l = if s = t ∧ j = k then unit R s i l else 0 := by
  apply Subtype.ext
  fin_cases s <;> fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases k <;> fin_cases l <;>
    simp [unit, ← mul_assoc]
  abel

private theorem sum_unit :
    unit R 0 0 0 + unit R 0 1 1 + unit R 1 0 0 + unit R 1 1 1 = 1 := by
  apply Subtype.ext
  simp [unit, ← mul_assoc]
  abel

/-- The inverse map, sending the matrix units of the two factors to the matrix units `unit 0` and
`unit 1`. -/
private noncomputable def splitEvenTwoMatrixProdToEven :
    Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R →ₐ[R] even (splitEvenForm R 2) :=
  AlgHom.ofLinearMap
    { toFun p := ∑ i, ∑ j, (p.1 i j • unit R 0 i j + p.2 i j • unit R 1 i j)
      map_add' p q := by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, add_smul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        abel
      map_smul' c p := by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply, Finset.smul_sum, smul_add] }
    (by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_one, Prod.snd_one, Fin.sum_univ_two,
        Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_smul, zero_smul, add_zero,
        zero_add, ← sum_unit R]
      abel)
    (fun p q ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, Matrix.mul_apply,
        Fin.sum_univ_two, add_mul, mul_add, smul_mul_smul_comm, unit_mul_unit, add_smul]
      simp
      module)

private theorem splitEvenTwoEvenToMatrixProd_unit (s i j : Fin 2) :
    splitEvenTwoEvenToMatrixProd R (unit R s i j) =
      if s = 0 then (Matrix.single i j 1, 0) else (0, Matrix.single i j 1) := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
  · simp only [unit, pair, map_mul, splitEvenTwoEvenToMatrixProd_ι]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [vecA, vecB, Matrix.mul_apply, Fin.sum_univ_two]

private theorem splitEvenTwoEvenToMatrixProd_comp_inv :
    (splitEvenTwoEvenToMatrixProd R).comp (splitEvenTwoMatrixProdToEven R) = AlgHom.id R _ := by
  refine AlgHom.ext fun p ↦ ?_
  simp only [AlgHom.comp_apply, splitEvenTwoMatrixProdToEven, AlgHom.ofLinearMap_apply,
    LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_add, map_smul,
    splitEvenTwoEvenToMatrixProd_unit, AlgHom.id_apply]
  ext a b <;> fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]

private theorem inv_comp_splitEvenTwoEvenToMatrixProd :
    (splitEvenTwoMatrixProdToEven R).comp (splitEvenTwoEvenToMatrixProd R) = AlgHom.id R _ := by
  refine even.algHom_ext (splitEvenForm R 2)
    (EvenHom.ext (LinearMap.ext₂ fun m₁ m₂ ↦ Subtype.ext ?_))
  simp only [EvenHom.compr₂_bilin, LinearMap.compr₂_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, AlgHom.id_apply, splitEvenTwoEvenToMatrixProd_ι]
  conv_rhs => rw [eq_vec R m₁, eq_vec R m₂]
  simp [splitEvenTwoMatrixProdToEven, Fin.sum_univ_two, unit, ← mul_assoc]
  module

/-- **The even Clifford algebra of the split quaternary form is `M₂(R) × M₂(R)`**, over any
commutative ring `R`. The equivalence sends `ι m₁ ι m₂` to `(B m₁ C m₂, C m₁ B m₂)`, where
`B = splitEvenTwoToMatrix R` and `C = splitEvenTwoToMatrixAdj R`; its two components are the
actions on the even and odd halves of the spinor module `⋀ R²`. -/
noncomputable def splitEvenTwoEvenEquivMatrixProd :
    even (splitEvenForm R 2) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofAlgHom (splitEvenTwoEvenToMatrixProd R) (splitEvenTwoMatrixProdToEven R)
    (splitEvenTwoEvenToMatrixProd_comp_inv R) (inv_comp_splitEvenTwoEvenToMatrixProd R)

/-- The equivalence `splitEvenTwoEvenEquivMatrixProd` sends `ι m₁ ι m₂` to
`(B m₁ C m₂, C m₁ B m₂)`. -/
@[simp]
theorem splitEvenTwoEvenEquivMatrixProd_ι (m₁ m₂ : SplitEvenSpace R 2) :
    splitEvenTwoEvenEquivMatrixProd R ((even.ι _).bilin m₁ m₂) =
      (splitEvenTwoToMatrix R m₁ * splitEvenTwoToMatrixAdj R m₂,
        splitEvenTwoToMatrixAdj R m₁ * splitEvenTwoToMatrix R m₂) :=
  splitEvenTwoEvenToMatrixProd_ι R m₁ m₂

/-! ### Naturality in the base ring -/

section BaseChange

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The base change `(φ, x) ↦ (φ_S, x_S)` of a vector of the split quaternary space along an
algebra `R → S`, where `φ_S` is the functional with the same coordinates `φ eᵢ`, mapped to `S`. -/
noncomputable def splitEvenTwoSpaceBaseChange : SplitEvenSpace R 2 →ₗ[R] SplitEvenSpace S 2 where
  toFun m := (algebraMap R S (m.1 (Pi.single 0 1)) • LinearMap.proj 0 +
      algebraMap R S (m.1 (Pi.single 1 1)) • LinearMap.proj 1, fun i ↦ algebraMap R S (m.2 i))
  map_add' m n := by
    refine Prod.ext (LinearMap.ext fun y ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Prod.fst_add, LinearMap.add_apply, map_add, add_smul]
      abel
    · simp
  map_smul' c m := by
    refine Prod.ext (LinearMap.ext fun y ↦ ?_) (funext fun i ↦ ?_) <;>
      simp [Algebra.smul_def, mul_assoc]

private theorem splitEvenTwoSpaceBaseChange_fst_single (m : SplitEvenSpace R 2) (i : Fin 2) :
    (splitEvenTwoSpaceBaseChange R S m).1 (Pi.single i 1) =
      algebraMap R S (m.1 (Pi.single i 1)) := by
  fin_cases i <;> simp [splitEvenTwoSpaceBaseChange, Algebra.algebraMap_eq_smul_one]

private theorem splitEvenTwoSpaceBaseChange_snd (m : SplitEvenSpace R 2) (i : Fin 2) :
    (splitEvenTwoSpaceBaseChange R S m).2 i = algebraMap R S (m.2 i) :=
  rfl

/-- The base change of a vector has the base-changed value of `q₄`. -/
theorem splitEvenForm_splitEvenTwoSpaceBaseChange (m : SplitEvenSpace R 2) :
    splitEvenForm S 2 (splitEvenTwoSpaceBaseChange R S m) =
      algebraMap R S (splitEvenForm R 2 m) := by
  simp only [splitEvenForm_two_apply, splitEvenTwoSpaceBaseChange_fst_single,
    splitEvenTwoSpaceBaseChange_snd, map_add, map_mul]

/-- The matrix `B` of a base-changed vector is the entrywise image of the matrix `B`. -/
theorem splitEvenTwoToMatrix_splitEvenTwoSpaceBaseChange (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrix S (splitEvenTwoSpaceBaseChange R S m) =
      (splitEvenTwoToMatrix R m).map (algebraMap R S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitEvenTwoSpaceBaseChange_fst_single, splitEvenTwoSpaceBaseChange_snd]

/-- The matrix `C` of a base-changed vector is the entrywise image of the matrix `C`. -/
theorem splitEvenTwoToMatrixAdj_splitEvenTwoSpaceBaseChange (m : SplitEvenSpace R 2) :
    splitEvenTwoToMatrixAdj S (splitEvenTwoSpaceBaseChange R S m) =
      (splitEvenTwoToMatrixAdj R m).map (algebraMap R S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitEvenTwoSpaceBaseChange_fst_single, splitEvenTwoSpaceBaseChange_snd]

/-- The bilinear map `(m₁, m₂) ↦ ι m₁_S ι m₂_S`. -/
private noncomputable def splitEvenTwoEvenBaseChangeHom :
    EvenHom (splitEvenForm R 2) (even (splitEvenForm S 2)) where
  bilin := LinearMap.mk₂ R
    (fun m₁ m₂ ↦ (even.ι _).bilin (splitEvenTwoSpaceBaseChange R S m₁)
      (splitEvenTwoSpaceBaseChange R S m₂))
    (fun _ _ _ ↦ by simp only [map_add, LinearMap.add_apply])
    (fun c _ _ ↦ by
      simp only [map_smul, ← algebraMap_smul S c, LinearMap.smul_apply])
    (fun _ _ _ ↦ by simp only [map_add])
    (fun c _ _ ↦ by simp only [map_smul, ← algebraMap_smul S c])
  contract m := by
    rw [LinearMap.mk₂_apply, (even.ι _).contract, splitEvenForm_splitEvenTwoSpaceBaseChange,
      ← IsScalarTower.algebraMap_apply]
  contract_mid m₁ m₂ m₃ := by
    rw [LinearMap.mk₂_apply, LinearMap.mk₂_apply, LinearMap.mk₂_apply,
      (even.ι _).contract_mid, splitEvenForm_splitEvenTwoSpaceBaseChange, algebraMap_smul]

/-- The base change map `CliffordAlgebra.even (splitEvenForm R 2) → CliffordAlgebra.even
(splitEvenForm S 2)` along an algebra `R → S`, sending `ι m₁ ι m₂` to `ι m₁_S ι m₂_S`. -/
noncomputable def splitEvenTwoEvenBaseChange :
    even (splitEvenForm R 2) →ₐ[R] even (splitEvenForm S 2) :=
  even.lift _ (splitEvenTwoEvenBaseChangeHom R S)

/-- The base change map sends `ι m₁ ι m₂` to `ι m₁_S ι m₂_S`. -/
@[simp]
theorem splitEvenTwoEvenBaseChange_ι (m₁ m₂ : SplitEvenSpace R 2) :
    splitEvenTwoEvenBaseChange R S ((even.ι _).bilin m₁ m₂) =
      (even.ι _).bilin (splitEvenTwoSpaceBaseChange R S m₁)
        (splitEvenTwoSpaceBaseChange R S m₂) := by
  simp [splitEvenTwoEvenBaseChange, splitEvenTwoEvenBaseChangeHom]

/-- **Naturality in the base ring**: the equivalence `splitEvenTwoEvenEquivMatrixProd` commutes
with base change along an algebra `R → S`, acting on matrices entrywise. -/
theorem splitEvenTwoEvenEquivMatrixProd_splitEvenTwoEvenBaseChange
    (x : even (splitEvenForm R 2)) :
    splitEvenTwoEvenEquivMatrixProd S (splitEvenTwoEvenBaseChange R S x) =
      Prod.map (Matrix.map · (algebraMap R S)) (Matrix.map · (algebraMap R S))
        (splitEvenTwoEvenEquivMatrixProd R x) := by
  let f := (Algebra.ofId R S).mapMatrix (m := Fin 2)
  have h : ((splitEvenTwoEvenEquivMatrixProd S).toAlgHom.restrictScalars R).comp
      (splitEvenTwoEvenBaseChange R S) =
        (f.prodMap f).comp (splitEvenTwoEvenEquivMatrixProd R).toAlgHom := by
    refine even.algHom_ext (splitEvenForm R 2)
      (EvenHom.ext (LinearMap.ext₂ fun m₁ m₂ ↦ ?_))
    simp only [EvenHom.compr₂_bilin, AlgHom.comp_toLinearMap, AlgHom.toLinearMap_restrictScalars,
      AlgEquiv.toAlgHom_toLinearMap, LinearMap.compr₂_apply, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv,
      AlgHom.coe_toLinearMap, Function.comp_apply, splitEvenTwoEvenBaseChange_ι,
      splitEvenTwoEvenEquivMatrixProd_ι, splitEvenTwoToMatrix_splitEvenTwoSpaceBaseChange,
      splitEvenTwoToMatrixAdj_splitEvenTwoSpaceBaseChange]
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  exact congr($h x)

end BaseChange

end TauCeti
