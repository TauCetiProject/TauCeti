/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Positivity
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

/-!
# Even Clifford model of the Temperley–Lieb algebra at `δ = √2`

At loop parameter `δ = √2`, the Temperley–Lieb algebra `TemperleyLieb ℂ (√2 : ℂ) m` maps
surjectively onto the even Clifford subalgebra `EvenClifford m` of the complex bilinear sum of
squares `q_m(x) = ∑ j, x_j ^ 2` on `ℂ ^ m` (Jones, *A polynomial invariant for knots via von
Neumann algebras*, p. 107; Iohara–Lehrer–Zhang, *The Jones quotients of the Temperley–Lieb
algebras*, §5.3, Theorem 5.4 and Proposition 5.5).

With Majorana generators `c_j = ι(e_j)` satisfying `c_j ^ 2 = 1` and `c_j c_k = -c_k c_j` for
`j ≠ k`, the adjacent products `d_j = c_j c_{j+1}` give projections
`p_j = (1 + i d_j) / 2` in `EvenClifford m` satisfying Temperley–Lieb relations at `δ = √2`.
Sending `e_j ↦ √2 p_j` defines a surjective algebra homomorphism
`evenCliffordModel m : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m`.

Transporting the positive-form analytic adjoint `a ↦ complexConj (reverse a)` from the
complexification of the real sum-of-squares form yields a conjugate-linear involution
`cliffordAdjoint m` (distinct from Mathlib's complex-linear `star` on `CliffordAlgebra`, which
negates the generators `c_j`), under which `c_j` and `p_j` are self-adjoint and `evenCliffordModel`
is adjoint-preserving. Its scalar coefficient functional `cliffordScalarCoefficient m` agrees with
`CliffordAlgebra.scalarTrace` and satisfies `s_m(a† a) ≥ 0` faithfully.

## Main definitions

* `TauCeti.TemperleyLieb.cliffordForm`, `TauCeti.TemperleyLieb.EvenClifford`,
  `TauCeti.TemperleyLieb.majorana`, `TauCeti.TemperleyLieb.cliffordProjection`,
  `TauCeti.TemperleyLieb.cliffordScalarCoefficient`: the Clifford carrier, Majorana generators,
  Temperley–Lieb projections, and scalar trace functional.
* `TauCeti.TemperleyLieb.cliffordConj`, `TauCeti.TemperleyLieb.cliffordAdjoint`,
  `TauCeti.TemperleyLieb.evenCliffordAdjoint`: the complex conjugation and positive-form analytic
  adjoint preserving `c_j` and `p_j`.
* `TauCeti.TemperleyLieb.evenCliffordModel`: the canonical comparison homomorphism
  `TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m`.

## Main results

* `TauCeti.TemperleyLieb.cliffordScalarCoefficient_adjoint_mul_self_nonneg` and
  `TauCeti.TemperleyLieb.cliffordScalarCoefficient_adjoint_mul_self_eq_zero_iff`: faithful
  positivity of `s_m(a† a)`.
* `TauCeti.TemperleyLieb.evenCliffordModel_star` and
  `TauCeti.TemperleyLieb.evenCliffordModel_surjective`: `evenCliffordModel` preserves the analytic
  adjoint and is surjective.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* K. Iohara, G. I. Lehrer, and R. B. Zhang, *The Jones quotients of the Temperley–Lieb algebras*,
  arXiv:1903.00520, Section 5.3 (Theorem 5.4 and Proposition 5.5).
-/

public section

noncomputable section

open scoped ComplexConjugate ComplexOrder TensorProduct
open CliffordAlgebra Module

namespace TauCeti.TemperleyLieb

/-- `√2 : ℂ` is self-adjoint, equipping `TemperleyLieb ℂ (√2 : ℂ) m` with the analytic
adjoint. -/
instance instFactIsSelfAdjointSqrtTwo : Fact (IsSelfAdjoint (Real.sqrt 2 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

/-! ### Carriers, Majorana generators, and scalar trace -/

section Carriers

/-- The complex bilinear sum of squares `q_m(x) = ∑ j, x_j ^ 2` on `Fin m → ℂ`. -/
def cliffordForm (m : ℕ) : QuadraticForm ℂ (Fin m → ℂ) :=
  QuadraticMap.weightedSumSquares ℂ (fun _ : Fin m ↦ (1 : ℂ))

/-- The even Clifford subalgebra `Cl_m⁰ = CliffordAlgebra.even (cliffordForm m)`, modeling the
Jones quotient of the Temperley–Lieb algebra at `δ = √2`. -/
abbrev EvenClifford (m : ℕ) : Subalgebra ℂ (CliffordAlgebra (cliffordForm m)) :=
  CliffordAlgebra.even (cliffordForm m)

/-- The Majorana generators `c_j = ι(e_j)` of `CliffordAlgebra (cliffordForm m)`, satisfying
`c_j ^ 2 = 1` and `c_j c_k = -c_k c_j` for `j ≠ k`. -/
def majorana (m : ℕ) (j : Fin m) : CliffordAlgebra (cliffordForm m) :=
  ι (cliffordForm m) (Pi.single j 1)

theorem majorana_def (m : ℕ) (j : Fin m) :
    majorana m j = ι (cliffordForm m) (Pi.single j 1) :=
  (rfl)

/-- The Clifford projections `p_j = (1 + i c_j c_{j+1}) / 2` in `EvenClifford m`. -/
def cliffordProjection (m : ℕ) (j : Fin (m - 1)) : CliffordAlgebra (cliffordForm m) :=
  (2 : ℂ)⁻¹ •
    (1 + Complex.I • (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩))

theorem cliffordProjection_def (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j = (2 : ℂ)⁻¹ • (1 + Complex.I •
      (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩)) :=
  (rfl)

/-- The scalar coefficient `s_m(a)` of `1` in the ordered-monomial basis of
`CliffordAlgebra (cliffordForm m)` attached to the standard basis of `Fin m → ℂ`. -/
def cliffordScalarCoefficient (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) : ℂ :=
  (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a ∅

theorem cliffordForm_apply (m : ℕ) (x : Fin m → ℂ) :
    cliffordForm m x = ∑ j : Fin m, x j * x j := by
  simp [cliffordForm, QuadraticMap.weightedSumSquares_apply]

@[simp]
theorem cliffordForm_single (m : ℕ) (j : Fin m) (c : ℂ) :
    cliffordForm m (Pi.single j c) = c * c := by
  simp [cliffordForm_apply, Pi.single_apply]

theorem cliffordForm_nondegenerate (m : ℕ) : (cliffordForm m).Nondegenerate := by
  unfold cliffordForm
  exact QuadraticMap.nondegenerate_weightedSumSquares fun _ ↦ isRegular_one

@[simp]
theorem majorana_mul_self (m : ℕ) (j : Fin m) :
    majorana m j * majorana m j = 1 := by
  rw [majorana, ι_sq_scalar, cliffordForm_single, mul_one, map_one]

theorem majorana_mul_majorana_add_swap (m : ℕ) {j k : Fin m} (hjk : j ≠ k) :
    majorana m j * majorana m k + majorana m k * majorana m j = 0 := by
  rw [majorana, majorana, ι_mul_ι_add_swap]
  have hpolar : QuadraticMap.polar (cliffordForm m) (Pi.single j 1) (Pi.single k 1) = 0 := by
    simp only [QuadraticMap.polar, cliffordForm_apply, Pi.add_apply, Pi.single_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    by_cases hij : i = j <;> by_cases hik : i = k
    · exact absurd (hij.symm.trans hik) hjk
    · simp [hij, hjk]
    · simp [hik, hjk.symm]
    · simp [hij, hik]
  rw [hpolar, map_zero]

theorem majorana_mul_comm_neg (m : ℕ) {j k : Fin m} (hjk : j ≠ k) :
    majorana m j * majorana m k = -(majorana m k * majorana m j) :=
  eq_neg_of_add_eq_zero_left (majorana_mul_majorana_add_swap m hjk)

theorem majorana_injective (m : ℕ) : Function.Injective (majorana m) := by
  intro j k hjk
  have hsingle : Pi.single j (1 : ℂ) = Pi.single k (1 : ℂ) :=
    ι_injective (cliffordForm m) (by simpa [majorana] using hjk)
  by_contra hne
  have h := congrFun hsingle j
  simp [hne] at h

/-- Any product of two Majorana generators `c_j c_k` lies in `EvenClifford m`. -/
theorem majorana_mul_mem_even (m : ℕ) (j k : Fin m) :
    majorana m j * majorana m k ∈ EvenClifford m := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  simpa [majorana] using ι_mul_ι_mem_evenOdd_zero (cliffordForm m) _ _

theorem majorana_mul_succ_mem_even (m : ℕ) (j : Fin (m - 1)) :
    majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩ ∈ EvenClifford m :=
  majorana_mul_mem_even m _ _

theorem cliffordProjection_mem_even (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j ∈ EvenClifford m := by
  unfold cliffordProjection
  exact Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (Subalgebra.one_mem _)
      (Subalgebra.smul_mem _ (majorana_mul_succ_mem_even m j) _)) _

theorem majorana_mul_succ_sq (m : ℕ) (j : Fin (m - 1)) :
    (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) ^ 2 = -1 := by
  set c₁ := majorana m ⟨j.val, by omega⟩
  set c₂ := majorana m ⟨j.val + 1, by omega⟩
  have hne : (⟨j.val, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by simp [Fin.ext_iff]
  calc
    (c₁ * c₂) ^ 2 = c₁ * c₂ * (c₁ * c₂) := sq _
    _ = c₁ * (c₂ * c₁) * c₂ := by simp only [mul_assoc]
    _ = c₁ * (-(c₁ * c₂)) * c₂ := by rw [majorana_mul_comm_neg m hne.symm]
    _ = -((c₁ * c₁) * (c₂ * c₂)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [majorana_mul_self, majorana_mul_self, mul_one]

/-- Adjacent products `c_i c_{i+1}` and `c_j c_{j+1}` with `j = i + 1` anticommute. -/
theorem majorana_mul_succ_anticomm_of_adj (m : ℕ) {i j : Fin (m - 1)} (hij : (i : ℕ) + 1 = j) :
    (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩) *
      (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) =
      -((majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) *
        (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩)) := by
  have hjv : (j : ℕ) = (i : ℕ) + 1 := hij.symm
  set c0 := majorana m ⟨i.val, by omega⟩
  set c1 := majorana m ⟨i.val + 1, by omega⟩
  set c2 := majorana m ⟨j.val + 1, by omega⟩
  have hc1' : majorana m ⟨j.val, by omega⟩ = c1 := by congr 1; exact Fin.ext hjv
  have h01 : (⟨i.val, by omega⟩ : Fin m) ≠ ⟨i.val + 1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨i.val, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, hjv]; omega
  have h12 : (⟨i.val + 1, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, hjv]; omega
  rw [hc1']
  calc
    (c0 * c1) * (c1 * c2) = c0 * ((c1 * c1) * c2) := by simp only [mul_assoc]
    _ = c0 * c2 := by rw [majorana_mul_self, one_mul]
    _ = -((c1 * c2) * (c0 * c1)) := by
      calc
        c0 * c2 = -(c2 * c0) := majorana_mul_comm_neg m h02
        _ = -(c2 * (c1 * c1) * c0) := by rw [majorana_mul_self, mul_one]
        _ = -((c2 * c1) * (c1 * c0)) := by simp only [mul_assoc]
        _ = -((-(c1 * c2)) * (-(c0 * c1))) := by
          rw [majorana_mul_comm_neg m h12.symm, majorana_mul_comm_neg m h01.symm]
        _ = -((c1 * c2) * (c0 * c1)) := by simp only [neg_mul, mul_neg, neg_neg]

/-- Products `c_i c_{i+1}` and `c_j c_{j+1}` at distance `≥ 2` commute. -/
theorem majorana_mul_succ_comm_of_dist (m : ℕ) {i j : Fin (m - 1)}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩)
      (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) := by
  have hdisj : ∀ a ∈ ({i.val, i.val + 1} : Finset ℕ),
      ∀ b ∈ ({j.val, j.val + 1} : Finset ℕ), a ≠ b := by
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases hij with hij | hij <;> omega
  have h00 : (⟨i.val, by omega⟩ : Fin m) ≠ ⟨j.val, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; exact hdisj _ (by simp) _ (by simp)
  have h01 : (⟨i.val, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; exact hdisj _ (by simp) _ (by simp)
  have h10 : (⟨i.val + 1, by omega⟩ : Fin m) ≠ ⟨j.val, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; exact hdisj _ (by simp) _ (by simp)
  have h11 : (⟨i.val + 1, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; exact hdisj _ (by simp) _ (by simp)
  set c0 := majorana m ⟨i.val, by omega⟩
  set c1 := majorana m ⟨i.val + 1, by omega⟩
  set c2 := majorana m ⟨j.val, by omega⟩
  set c3 := majorana m ⟨j.val + 1, by omega⟩
  rw [commute_iff_eq]
  calc
    (c0 * c1) * (c2 * c3) = c0 * (c1 * c2) * c3 := by simp only [mul_assoc]
    _ = c0 * (-(c2 * c1)) * c3 := by rw [majorana_mul_comm_neg m h10]
    _ = -((c0 * c2) * (c1 * c3)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = -((-(c2 * c0)) * (-(c3 * c1))) := by
      rw [majorana_mul_comm_neg m h00, majorana_mul_comm_neg m h11]
    _ = -(c2 * (c0 * c3) * c1) := by simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
    _ = -(c2 * (-(c3 * c0)) * c1) := by rw [majorana_mul_comm_neg m h01]
    _ = (c2 * c3) * (c0 * c1) := by simp only [mul_neg, neg_mul, neg_neg, mul_assoc]

/-- The scalar coefficient `s_m(a)` agrees with `CliffordAlgebra.scalarTrace (cliffordForm m) a`.
-/
theorem cliffordScalarCoefficient_eq_scalarTrace (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m a = scalarTrace (cliffordForm m) a :=
  basis_repr_empty (Pi.basisFun ℂ (Fin m)) a

@[simp]
theorem cliffordScalarCoefficient_one (m : ℕ) :
    cliffordScalarCoefficient m 1 = 1 := by
  rw [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_one]

@[simp]
theorem cliffordScalarCoefficient_algebraMap (m : ℕ) (z : ℂ) :
    cliffordScalarCoefficient m (algebraMap ℂ _ z) = z := by
  rw [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_algebraMap]

@[simp]
theorem cliffordScalarCoefficient_add (m : ℕ) (a b : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m (a + b) =
      cliffordScalarCoefficient m a + cliffordScalarCoefficient m b := by
  simp only [cliffordScalarCoefficient_eq_scalarTrace, map_add]

@[simp]
theorem cliffordScalarCoefficient_smul (m : ℕ) (z : ℂ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m (z • a) = z * cliffordScalarCoefficient m a := by
  simp only [cliffordScalarCoefficient_eq_scalarTrace, map_smul, smul_eq_mul]

theorem cliffordScalarCoefficient_mul_comm (m : ℕ) (a b : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m (a * b) = cliffordScalarCoefficient m (b * a) := by
  simp only [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_mul_comm]

@[simp]
theorem cliffordScalarCoefficient_reverse (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m (reverse a) = cliffordScalarCoefficient m a := by
  simp only [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_reverse]

@[simp]
theorem cliffordScalarCoefficient_involute (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m (involute a) = cliffordScalarCoefficient m a := by
  simp only [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_involute]

end Carriers

/-! ### Complexification bridge and the analytic adjoint -/

section Adjoint

private def realCliffordForm (m : ℕ) : QuadraticForm ℝ (Fin m → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin m ↦ (1 : ℝ))

private theorem realCliffordForm_posDef (m : ℕ) : (realCliffordForm m).PosDef := by
  intro x hx
  simp only [realCliffordForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, one_mul]
  refine Finset.sum_pos' (fun i _ ↦ mul_self_nonneg (x i)) ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

private noncomputable def cliffordFormIsoBaseChange (m : ℕ) :
    (cliffordForm m).IsometryEquiv ((realCliffordForm m).baseChange ℂ) where
  toLinearEquiv := (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin m)).symm
  map_app' x := by
    have hQ : (realCliffordForm m).baseChange ℂ =
        (cliffordForm m).comp (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin m)).toLinearMap := by
      apply baseChange_ext
      intro v
      simp only [QuadraticForm.baseChange_tmul, realCliffordForm,
        QuadraticMap.weightedSumSquares_apply, smul_eq_mul, one_mul, QuadraticMap.comp_apply,
        LinearEquiv.coe_coe, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, cliffordForm_apply, Complex.coe_algebraMap,
        Algebra.smul_def, mul_one]
      rw [← Complex.coe_algebraMap, map_sum]
      simp [Complex.coe_algebraMap]
    have hx := congrArg (fun Q : QuadraticForm ℂ _ ↦
      Q ((TensorProduct.piScalarRight ℝ ℂ ℂ (Fin m)).symm x)) hQ
    simpa [LinearEquiv.apply_symm_apply] using hx

private theorem cliffordFormIsoBaseChange_toIsometry_apply (m : ℕ) (x : Fin m → ℂ) :
    (cliffordFormIsoBaseChange m).toIsometry x =
      (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin m)).symm x :=
  (rfl)

private noncomputable def cliffordEquivBaseChange (m : ℕ) :
    CliffordAlgebra (cliffordForm m) ≃ₐ[ℂ]
      CliffordAlgebra ((realCliffordForm m).baseChange ℂ) :=
  equivOfIsometry (cliffordFormIsoBaseChange m)

private theorem cliffordEquivBaseChange_majorana (m : ℕ) (j : Fin m) :
    cliffordEquivBaseChange m (majorana m j) =
      ι ((realCliffordForm m).baseChange ℂ) (1 ⊗ₜ Pi.single j 1) := by
  simp only [cliffordEquivBaseChange, majorana, equivOfIsometry_apply, map_apply_ι]
  congr 1
  rw [cliffordFormIsoBaseChange_toIsometry_apply, TensorProduct.piScalarRight_symm_single]

private theorem cliffordEquivBaseChange_reverse (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordEquivBaseChange m (reverse a) = reverse (cliffordEquivBaseChange m a) := by
  simp [cliffordEquivBaseChange, equivOfIsometry_apply]

private theorem cliffordEquivBaseChange_symm_reverse (m : ℕ)
    (a : CliffordAlgebra ((realCliffordForm m).baseChange ℂ)) :
    (cliffordEquivBaseChange m).symm (reverse a) =
      reverse ((cliffordEquivBaseChange m).symm a) := by
  simp [cliffordEquivBaseChange, equivOfIsometry_symm, equivOfIsometry_apply]

/-- Coefficientwise complex conjugation on `CliffordAlgebra (cliffordForm m)` with respect to the
standard real basis `Fin m → ℝ`. -/
def cliffordConj (m : ℕ) :
    CliffordAlgebra (cliffordForm m) ≃+* CliffordAlgebra (cliffordForm m) :=
  ((cliffordEquivBaseChange m).toRingEquiv.trans
    (complexConj (realCliffordForm m))).trans
    (cliffordEquivBaseChange m).symm.toRingEquiv

private theorem cliffordConj_apply (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordConj m a =
      (cliffordEquivBaseChange m).symm
        (complexConj (realCliffordForm m) (cliffordEquivBaseChange m a)) :=
  rfl

@[simp]
theorem cliffordConj_smul (m : ℕ) (z : ℂ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordConj m (z • a) = conj z • cliffordConj m a := by
  simp only [cliffordConj_apply, map_smul, complexConj_smul]

@[simp]
theorem cliffordConj_algebraMap (m : ℕ) (z : ℂ) :
    cliffordConj m (algebraMap ℂ _ z) = algebraMap ℂ _ (conj z) := by
  simp [cliffordConj_apply]

@[simp]
theorem cliffordConj_cliffordConj (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordConj m (cliffordConj m a) = a := by
  simp [cliffordConj_apply]

@[simp]
theorem cliffordConj_majorana (m : ℕ) (j : Fin m) :
    cliffordConj m (majorana m j) = majorana m j := by
  rw [cliffordConj_apply, cliffordEquivBaseChange_majorana, complexConj_ι_tmul, map_one,
    ← cliffordEquivBaseChange_majorana, AlgEquiv.symm_apply_apply]

@[simp]
theorem cliffordConj_reverse (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordConj m (reverse a) = reverse (cliffordConj m a) := by
  simp only [cliffordConj_apply, cliffordEquivBaseChange_reverse, complexConj_reverse,
    cliffordEquivBaseChange_symm_reverse]

@[simp]
theorem cliffordConj_involute (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordConj m (involute a) = involute (cliffordConj m a) := by
  rw [cliffordConj_apply, cliffordConj_apply]
  have h1 : cliffordEquivBaseChange m (involute a) =
      involute (cliffordEquivBaseChange m a) := by
    simp [cliffordEquivBaseChange, equivOfIsometry_apply]
  have h2 : ∀ y : CliffordAlgebra ((realCliffordForm m).baseChange ℂ),
      (cliffordEquivBaseChange m).symm (involute y) =
        involute ((cliffordEquivBaseChange m).symm y) := by
    intro y
    simp [cliffordEquivBaseChange, equivOfIsometry_symm, equivOfIsometry_apply]
  rw [h1, complexConj_involute, h2]

theorem cliffordConj_mem_even_iff (m : ℕ) {a : CliffordAlgebra (cliffordForm m)} :
    cliffordConj m a ∈ EvenClifford m ↔ a ∈ EvenClifford m := by
  simp only [EvenClifford, ← Subalgebra.mem_toSubmodule, even_toSubmodule,
    ← involute_eq_self_iff, ← cliffordConj_involute]
  exact ⟨fun h ↦ by simpa using congrArg (cliffordConj m) h, fun h ↦ by rw [h]⟩

/-- The positive-form analytic adjoint `a† = complexConj (reverse a)` on
`CliffordAlgebra (cliffordForm m)`: it is conjugate-linear, product-reversing, and fixes every
Majorana generator `c_j`. -/
def cliffordAdjoint (m : ℕ) :
    CliffordAlgebra (cliffordForm m) →ₗ⋆[ℂ] CliffordAlgebra (cliffordForm m) where
  toFun a := cliffordConj m (reverse a)
  map_add' a b := by simp
  map_smul' z a := by simp

theorem cliffordAdjoint_apply (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m a = cliffordConj m (reverse a) :=
  (rfl)

@[simp]
theorem cliffordAdjoint_cliffordAdjoint (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m (cliffordAdjoint m a) = a := by
  simp [cliffordAdjoint_apply, cliffordConj_reverse]

@[simp]
theorem cliffordAdjoint_one (m : ℕ) : cliffordAdjoint m 1 = 1 := by
  simp [cliffordAdjoint_apply]

@[simp]
theorem cliffordAdjoint_mul (m : ℕ) (a b : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m (a * b) = cliffordAdjoint m b * cliffordAdjoint m a := by
  simp [cliffordAdjoint_apply, reverse.map_mul, map_mul]

@[simp]
theorem cliffordAdjoint_algebraMap (m : ℕ) (z : ℂ) :
    cliffordAdjoint m (algebraMap ℂ _ z) = algebraMap ℂ _ (conj z) := by
  simp [cliffordAdjoint_apply]

@[simp]
theorem cliffordAdjoint_majorana (m : ℕ) (j : Fin m) :
    cliffordAdjoint m (majorana m j) = majorana m j := by
  rw [cliffordAdjoint_apply, majorana, reverse_ι, ← majorana, cliffordConj_majorana]

theorem cliffordAdjoint_majorana_mul_succ (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) =
      -(majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) := by
  have hne : (⟨j.val, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by simp [Fin.ext_iff]
  rw [cliffordAdjoint_mul, cliffordAdjoint_majorana, cliffordAdjoint_majorana,
    majorana_mul_comm_neg m hne.symm]

@[simp]
theorem cliffordAdjoint_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (cliffordProjection m j) = cliffordProjection m j := by
  rw [cliffordProjection, map_smulₛₗ, map_add, cliffordAdjoint_one, map_smulₛₗ,
    cliffordAdjoint_majorana_mul_succ]
  simp [map_ofNat]

theorem cliffordAdjoint_mem_even (m : ℕ) {a : CliffordAlgebra (cliffordForm m)}
    (ha : a ∈ EvenClifford m) : cliffordAdjoint m a ∈ EvenClifford m := by
  rw [cliffordAdjoint_apply, cliffordConj_mem_even_iff]
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at ha ⊢
  exact (reverse_mem_evenOdd_iff (cliffordForm m)).2 ha

/-- Restriction of the positive-form analytic adjoint to `EvenClifford m`. -/
def evenCliffordAdjoint (m : ℕ) : EvenClifford m →ₗ⋆[ℂ] EvenClifford m where
  toFun a := ⟨cliffordAdjoint m a, cliffordAdjoint_mem_even m a.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' z a := Subtype.ext (by simp)

@[simp]
theorem coe_evenCliffordAdjoint (m : ℕ) (a : EvenClifford m) :
    (evenCliffordAdjoint m a : CliffordAlgebra (cliffordForm m)) = cliffordAdjoint m a :=
  (rfl)

@[simp]
theorem evenCliffordAdjoint_involutive (m : ℕ) (a : EvenClifford m) :
    evenCliffordAdjoint m (evenCliffordAdjoint m a) = a :=
  Subtype.ext (cliffordAdjoint_cliffordAdjoint m a)

@[simp]
theorem evenCliffordAdjoint_mul (m : ℕ) (a b : EvenClifford m) :
    evenCliffordAdjoint m (a * b) = evenCliffordAdjoint m b * evenCliffordAdjoint m a :=
  Subtype.ext (cliffordAdjoint_mul m a b)

private theorem scalarTrace_cliffordAdjoint_eq (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) =
      scalarTrace ((realCliffordForm m).baseChange ℂ)
        (complexConj (realCliffordForm m) (reverse (cliffordEquivBaseChange m a)) *
          cliffordEquivBaseChange m a) := by
  rw [← scalarTrace_eq_of_algEquiv (cliffordEquivBaseChange m), map_mul]
  congr 1
  simp [cliffordAdjoint_apply, cliffordConj_apply, cliffordEquivBaseChange_reverse]

/-- Positivity of the scalar trace pairing `(a, a) ↦ s_m(a† a)`. -/
theorem cliffordScalarCoefficient_adjoint_mul_self_nonneg (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) :
    0 ≤ cliffordScalarCoefficient m (cliffordAdjoint m a * a) := by
  rw [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_cliffordAdjoint_eq]
  exact scalarTrace_complexConj_reverse_mul_self_nonneg
    (fun v ↦ (realCliffordForm_posDef m).nonneg v) (cliffordEquivBaseChange m a)

/-- Faithfulness of the scalar trace pairing `(a, a) ↦ s_m(a† a)`. -/
@[simp]
theorem cliffordScalarCoefficient_adjoint_mul_self_eq_zero_iff (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient m (cliffordAdjoint m a * a) = 0 ↔ a = 0 := by
  rw [cliffordScalarCoefficient_eq_scalarTrace, scalarTrace_cliffordAdjoint_eq,
    scalarTrace_complexConj_reverse_mul_self_eq_zero_iff (realCliffordForm_posDef m)]
  exact map_eq_zero_iff (cliffordEquivBaseChange m) (cliffordEquivBaseChange m).injective

end Adjoint

/-! ### The comparison homomorphism from `TemperleyLieb ℂ (√2 : ℂ) m` -/

section ComparisonMap

/-- `cliffordProjection m j` is idempotent. -/
theorem cliffordProjection_mul_self (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j * cliffordProjection m j = cliffordProjection m j := by
  set u := Complex.I • (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩)
  have hu2 : u * u = 1 := by
    simp only [u, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, Complex.I_mul_I]
    have hsq : (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) *
        (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) = -1 := by
      simpa [sq] using majorana_mul_succ_sq m j
    rw [hsq, neg_smul, one_smul, neg_neg]
  calc
    cliffordProjection m j * cliffordProjection m j
        = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((1 + u) * (1 + u)) := by
          simp only [cliffordProjection, u, smul_mul_smul_comm]
    _ = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((2 : ℂ) • (1 + u)) := by
          congr 1
          calc
            (1 + u) * (1 + u) = 1 + u * u + u + u := by noncomm_ring
            _ = (2 : ℂ) • (1 + u) := by
              rw [hu2]
              module
    _ = cliffordProjection m j := by
          rw [smul_smul]
          norm_num [cliffordProjection, u]

/-- Adjacent Clifford projections satisfy `p_i p_j p_i = p_i / 2`. -/
theorem cliffordProjection_mul_adj (m : ℕ) {i j : Fin (m - 1)}
    (hij : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cliffordProjection m i * cliffordProjection m j * cliffordProjection m i =
      (2 : ℂ)⁻¹ • cliffordProjection m i := by
  set u := Complex.I • (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩)
  set v := Complex.I • (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩)
  have hu2 : u * u = 1 := by
    simp only [u, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, Complex.I_mul_I]
    have hsq : (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩) *
        (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩) = -1 := by
      simpa [sq] using majorana_mul_succ_sq m i
    rw [hsq, neg_smul, one_smul, neg_neg]
  have huv : u * v = -(v * u) := by
    have hadj : (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩) *
        (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) =
        -((majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) *
          (majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩)) :=
      hij.elim (fun h ↦ majorana_mul_succ_anticomm_of_adj m h)
        (fun h ↦ by rw [majorana_mul_succ_anticomm_of_adj m h, neg_neg])
    simp only [u, v, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hadj, smul_neg]
  have hpi : cliffordProjection m i = (2 : ℂ)⁻¹ • (1 + u) := rfl
  have hpj : cliffordProjection m j = (2 : ℂ)⁻¹ • (1 + v) := rfl
  have hcalc : (1 + u) * (1 + v) * (1 + u) = (2 : ℂ) • (1 + u) := by
    calc
      (1 + u) * (1 + v) * (1 + u)
          = (1 + u + v + u * v) * (1 + u) := by noncomm_ring
      _ = 1 + u + v + u * v + (u + u * u + v * u + (u * v) * u) := by noncomm_ring
      _ = 1 + u + v + u * v + (u + 1 - u * v + -(v * u * u)) := by
          rw [hu2, huv]
          noncomm_ring
      _ = 1 + u + v + (u + 1) - v * (u * u) := by noncomm_ring
      _ = (2 : ℂ) • (1 + u) := by
          rw [hu2, mul_one]
          module
  rw [hpi, hpj, smul_mul_smul_comm, smul_mul_smul_comm, hcalc, smul_smul, smul_smul]
  congr 1
  norm_num

/-- Disjoint Clifford projections commute. -/
theorem cliffordProjection_commute (m : ℕ) {i j : Fin (m - 1)}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cliffordProjection m i) (cliffordProjection m j) := by
  have hc := majorana_mul_succ_comm_of_dist m hij
  simp only [cliffordProjection]
  exact ((Commute.one_right _).add_right ((Commute.one_left _).add_left
    ((hc.smul_left Complex.I).smul_right Complex.I))).smul_left (2 : ℂ)⁻¹
    |>.smul_right (2 : ℂ)⁻¹

private lemma two_inv_mul_sqrt_two_sq :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- **The comparison homomorphism** `F_m : TL_m(√2) → Cl_m⁰`, sending `e_j` to `√2 p_j`. -/
def evenCliffordModel (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₐ[ℂ] EvenClifford m :=
  TemperleyLieb.lift
    (fun j ↦ ⟨(Real.sqrt 2 : ℂ) • cliffordProjection m j,
      Subalgebra.smul_mem _ (cliffordProjection_mem_even m j) _⟩)
    (fun j ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, cliffordProjection_mul_self, smul_smul])
    (fun hij ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, cliffordProjection_mul_adj m hij, smul_smul]
      congr 1
      calc
        _ = (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹ *
            (Real.sqrt 2 : ℂ) := by ring
        _ = (Real.sqrt 2 : ℂ) := by rw [two_inv_mul_sqrt_two_sq, one_mul])
    (fun hij ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm]
      rw [(cliffordProjection_commute m hij).eq])

@[simp]
theorem evenCliffordModel_e (m : ℕ) (j : Fin (m - 1)) :
    (evenCliffordModel m (e (Real.sqrt 2 : ℂ) j) : CliffordAlgebra (cliffordForm m)) =
      (Real.sqrt 2 : ℂ) • cliffordProjection m j :=
  congrArg Subtype.val (TemperleyLieb.lift_e _ _ _ _ j)

/-- The comparison map `evenCliffordModel m` intertwines the analytic adjoint on
`TemperleyLieb ℂ (√2 : ℂ) m` with `evenCliffordAdjoint m`. -/
@[simp]
theorem evenCliffordModel_star (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    evenCliffordModel m (star x) = evenCliffordAdjoint m (evenCliffordModel m x) := by
  induction x using TemperleyLieb.induction with
  | e j =>
    ext1
    rw [star_e, evenCliffordModel_e, coe_evenCliffordAdjoint, evenCliffordModel_e,
      map_smulₛₗ, cliffordAdjoint_cliffordProjection]
    simp
  | algebraMap z =>
    ext1
    simp only [Algebra.algebraMap_eq_smul_one, StarModule.star_smul, star_one, map_smul, map_one,
      Subalgebra.coe_smul, OneMemClass.coe_one, coe_evenCliffordAdjoint,
      Complex.star_def]
    simp
  | add x y hx hy => simp only [star_add, map_add, hx, hy]
  | mul x y hx hy => simp only [star_mul, map_mul, hx, hy, evenCliffordAdjoint_mul]

private theorem majorana_mul_succ_mem_evenCliffordModel_range (m : ℕ) (j : ℕ) (hj : j + 1 < m) :
    (⟨majorana m ⟨j, by omega⟩ * majorana m ⟨j + 1, hj⟩,
      majorana_mul_succ_mem_even m ⟨j, by omega⟩⟩ : EvenClifford m) ∈
      (evenCliffordModel m).range := by
  let jj : Fin (m - 1) := ⟨j, by omega⟩
  refine ⟨(-Complex.I) • ((Real.sqrt 2 : ℂ) • e (Real.sqrt 2 : ℂ) jj - 1), ?_⟩
  ext1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul, map_sub, map_one,
    Subalgebra.coe_smul, Subalgebra.coe_sub, OneMemClass.coe_one, evenCliffordModel_e,
    cliffordProjection, smul_smul]
  rw [← mul_assoc, two_inv_mul_sqrt_two_sq, one_smul, add_sub_cancel_left, smul_smul]
  simp [jj]

private theorem majorana_mul_mem_evenCliffordModel_range (m : ℕ) (j k : Fin m) :
    (⟨majorana m j * majorana m k, majorana_mul_mem_even m j k⟩ : EvenClifford m) ∈
      (evenCliffordModel m).range := by
  have hmem_step : ∀ (d j : ℕ) (hjd : j + d + 1 < m),
      (⟨majorana m ⟨j, by omega⟩ * majorana m ⟨j + d + 1, hjd⟩,
        majorana_mul_mem_even m _ _⟩ : EvenClifford m) ∈
        (evenCliffordModel m).range := by
    intro d
    induction d with
    | zero => intro j hj; exact majorana_mul_succ_mem_evenCliffordModel_range m j hj
    | succ d ih =>
      intro j hj
      have h1 := ih j (by omega)
      have h2 := majorana_mul_succ_mem_evenCliffordModel_range m (j + d + 1) (by omega)
      convert (evenCliffordModel m).range.mul_mem h1 h2 using 1
      ext1
      simp only [Subalgebra.coe_mul, mul_assoc]
      rw [← mul_assoc (majorana m ⟨j + d + 1, by omega⟩), majorana_mul_self, one_mul]
      simp [add_assoc]
  rcases lt_trichotomy j.val k.val with hjk | hjk | hjk
  · obtain ⟨d, hd⟩ : ∃ d, j.val + d + 1 = k.val := ⟨k.val - j.val - 1, by omega⟩
    convert hmem_step d j.val (by omega) using 2
    congr 2
    exact Fin.ext hd.symm
  · have hjkeq : j = k := Fin.ext hjk
    subst hjkeq
    convert (evenCliffordModel m).range.one_mem using 2
    simp
  · obtain ⟨d, hd⟩ : ∃ d, k.val + d + 1 = j.val := ⟨j.val - k.val - 1, by omega⟩
    have hne : j ≠ k := fun h ↦ by omega
    have hsub := (evenCliffordModel m).range.neg_mem (hmem_step d k.val (by omega))
    convert hsub using 2
    simp only [Subalgebra.coe_neg, majorana_mul_comm_neg m hne]
    congr 3
    exact Fin.ext hd.symm

private theorem ι_mul_ι_mem_evenCliffordModel_range (m : ℕ) (u v : Fin m → ℂ) :
    (⟨ι (cliffordForm m) u * ι (cliffordForm m) v, by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
      simpa using ι_mul_ι_mem_evenOdd_zero (cliffordForm m) u v⟩ : EvenClifford m) ∈
      (evenCliffordModel m).range := by
  have hu : u = ∑ j : Fin m, u j • Pi.single j 1 := by ext i; simp [Pi.single_apply]
  have hv : v = ∑ k : Fin m, v k • Pi.single k 1 := by ext i; simp [Pi.single_apply]
  have hsum : ι (cliffordForm m) u * ι (cliffordForm m) v =
      ∑ j : Fin m, ∑ k : Fin m, (u j * v k) • (majorana m j * majorana m k) := by
    conv_lhs => rw [hu, hv]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, map_smul, smul_mul_smul_comm]
    rfl
  have hr : ∑ j : Fin m, ∑ k : Fin m, (u j * v k) •
      (⟨majorana m j * majorana m k, majorana_mul_mem_even m j k⟩ : EvenClifford m) ∈
      (evenCliffordModel m).range :=
    Subalgebra.sum_mem _ fun j _ ↦ Subalgebra.sum_mem _ fun k _ ↦
      Subalgebra.smul_mem _ (majorana_mul_mem_evenCliffordModel_range m j k) _
  convert hr using 1
  ext1
  simpa using hsum

/-- The comparison map `evenCliffordModel m` is surjective onto `EvenClifford m`. -/
theorem evenCliffordModel_surjective (m : ℕ) :
    Function.Surjective (evenCliffordModel m) := by
  suffices h : ∀ (x : CliffordAlgebra (cliffordForm m))
      (hx : x ∈ CliffordAlgebra.even (cliffordForm m)),
      ∃ a, evenCliffordModel m a =
        ⟨x, by rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact hx⟩ by
    rintro ⟨x, hx⟩
    exact h x (by rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx)
  intro x hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap z => exact ⟨algebraMap ℂ _ z, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨ax, hax⟩ := ihx
    obtain ⟨ay, hay⟩ := ihy
    exact ⟨ax + ay, Subtype.ext (by simp [hax, hay])⟩
  | ι_mul_ι_mul u v y hy ihy =>
    obtain ⟨ay, hay⟩ := ihy
    have huv := ι_mul_ι_mem_evenCliffordModel_range m u v
    have hy' : (⟨y, by rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact hy⟩ :
        EvenClifford m) ∈ (evenCliffordModel m).range := ⟨ay, hay⟩
    obtain ⟨a, ha⟩ := (evenCliffordModel m).range.mul_mem huv hy'
    exact ⟨a, Subtype.ext (by simpa [mul_assoc] using congrArg Subtype.val ha)⟩

end ComparisonMap

end TauCeti.TemperleyLieb

end
