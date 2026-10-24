/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.BaseChange
import Mathlib.Basic.Complex.BigOperators
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# Positivity of the complexified negative Clifford trace

For a real quadratic form `Q`, Clifford conjugation negates generators. Consequently the
scalar-trace pairing with this conjugation has diagonal weights `∏ i ∈ s, -Q (b i)` in the
ordered-product basis of an orthogonal basis `b`. On the complexification, the tensor-product
star also conjugates coefficients, giving squared absolute values in the diagonal formula.
This proves positivity for nonpositive forms and faithfulness for negative definite forms.
The results use the native tensor carrier and its locally enabled star module structure;
no new star instance is installed globally.

The coefficient formula holds for arbitrary real forms, including degenerate and indefinite
ones. Faithfulness is equivalent to negative definiteness: a nonzero null vector or a vector of
positive quadratic value gives a nonzero Clifford element of zero squared trace norm. All finite
ranks, including zero, are allowed.

The diagonal computation extends `CliffordAlgebra.scalarTrace_reverse_basis_mul_basis`;
the comparison of the two carriers uses `CliffordAlgebra.equivBaseChange` and
`CliffordAlgebra.toBaseChange_conjStar`.

## Main results

* `TauCeti.baseChange_scalarTrace_star_mul_self`: the weighted squared-coefficient formula.
* `TauCeti.baseChange_scalarTrace_star_mul_self_nonneg`: positivity on the tensor carrier.
* `TauCeti.exists_ne_zero_scalarTrace_star_mul_self_eq_zero`: a real obstruction to faithfulness.
* `TauCeti.scalarTrace_conjStar_mul_self_eq_zero_iff`: faithfulness on the Clifford carrier.
* `TauCeti.scalarTrace_conjStar_faithful_iff`: the intrinsic negative-definiteness criterion.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

open scoped TensorProduct ComplexConjugate ComplexOrder

namespace TauCeti

open CliffordAlgebra

attribute [local instance] CliffordAlgebra.starModule_of_trivialStar

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder I]
  {Q : QuadraticForm ℝ V} {b : Module.Basis I ℝ V}

/-- The complexified Clifford trace pairing in orthogonal coordinates, conjugate-linear in its
first argument. The diagonal weight uses the negative of the quadratic form. -/
theorem baseChange_scalarTrace_star_mul [Fintype I] (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (x y : ℂ ⊗[ℝ] CliffordAlgebra Q) :
    Module.Dual.baseChange ℂ (scalarTrace Q) (star x * y) =
      ∑ s : Finset I, conj (((basis Q b).baseChange ℂ).repr x s) *
        (((∏ i ∈ s, -Q (b i) : ℝ) : ℂ) * ((basis Q b).baseChange ℂ).repr y s) := by
  let c := (basis Q b).baseChange ℂ
  conv_lhs => rw [← c.sum_repr x, ← c.sum_repr y]
  simp only [c, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one, star_sum, Finset.sum_mul, Finset.mul_sum, TensorProduct.star_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, map_sum, Module.Dual.baseChange_apply_tmul,
    scalarTrace_star_basis_mul_basis hb]
  rw [Finset.sum_comm]
  simp [Algebra.smul_def, apply_ite, ite_mul, mul_left_comm]

/-- The scalar trace of `x* x` is a real sum of squared complex coefficients with the
negative quadratic weights. This identity also applies to degenerate and indefinite forms. -/
theorem baseChange_scalarTrace_star_mul_self [Fintype I]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (x : ℂ ⊗[ℝ] CliffordAlgebra Q) :
    Module.Dual.baseChange ℂ (scalarTrace Q) (star x * x) =
      ((∑ s : Finset I, Complex.normSq (((basis Q b).baseChange ℂ).repr x s) *
        ∏ i ∈ s, -Q (b i) : ℝ) : ℂ) := by
  rw [baseChange_scalarTrace_star_mul hb]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- The complexified scalar trace is positive for the negative Clifford convention when
`Q` is nonpositive on an orthogonal basis. Complex nonnegativity includes reality. -/
theorem baseChange_scalarTrace_star_mul_self_nonneg [Finite I]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) ≤ 0)
    (x : ℂ ⊗[ℝ] CliffordAlgebra Q) :
    0 ≤ Module.Dual.baseChange ℂ (scalarTrace Q) (star x * x) := by
  let := Fintype.ofFinite I
  rw [baseChange_scalarTrace_star_mul_self hb]
  exact Complex.zero_le_real.mpr <| Finset.sum_nonneg fun s _ ↦
    mul_nonneg (Complex.normSq_nonneg _) (Finset.prod_nonneg fun i _ ↦ neg_nonneg.mpr (hQ i))

/-- The positive complexified trace is faithful if the quadratic form is strictly negative on
an orthogonal basis. This includes rank zero, whose single Clifford coefficient is scalar. -/
theorem baseChange_scalarTrace_star_mul_self_eq_zero_iff [Finite I]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) < 0)
    {x : ℂ ⊗[ℝ] CliffordAlgebra Q} :
    Module.Dual.baseChange ℂ (scalarTrace Q) (star x * x) = 0 ↔ x = 0 := by
  let := Fintype.ofFinite I
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [baseChange_scalarTrace_star_mul_self hb, Complex.ofReal_eq_zero] at h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun s (_ : s ∈ Finset.univ) ↦
    mul_nonneg (Complex.normSq_nonneg _) <|
      Finset.prod_nonneg fun i _ ↦ (neg_pos.mpr (hQ i)).le).mp h
  apply ((basis Q b).baseChange ℂ).repr.injective
  ext s
  have hs := hterm s (Finset.mem_univ s)
  have hpos : 0 < ∏ i ∈ s, -Q (b i) := Finset.prod_pos fun i _ ↦ neg_pos.mpr (hQ i)
  simpa only [map_zero, Finsupp.zero_apply] using
    Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hpos.ne')

/-- A nonzero vector of nonnegative quadratic value gives a nonzero real Clifford element
of zero squared trace norm. No finite-dimensionality hypothesis is needed. -/
theorem exists_ne_zero_scalarTrace_star_mul_self_eq_zero {v : V} (hv : v ≠ 0)
    (hQ : 0 ≤ Q v) : ∃ y : CliffordAlgebra Q, y ≠ 0 ∧ scalarTrace Q (star y * y) = 0 := by
  refine ⟨algebraMap ℝ _ (Real.sqrt (Q v)) + ι Q v, ?_, ?_⟩
  · intro hy
    exact hv (by simpa using congrArg (ιInv Q) hy)
  · simp [add_mul, mul_add, Algebra.algebraMap_eq_smul_one,
      ← mul_smul, Real.mul_self_sqrt hQ]

variable [FiniteDimensional ℝ V]

/-- Positivity on the native base-changed Clifford carrier for every nonpositive real quadratic
form, with the conjugate-linear negative-metric adjoint `conjStar`. -/
theorem scalarTrace_conjStar_mul_self_nonneg (hQ : ∀ v, Q v ≤ 0)
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    0 ≤ scalarTrace (Q.baseChange ℂ) (conjStar Q x * x) := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated Q) (QuadraticForm.associated_isSymm ℝ Q)
  rw [← baseChange_scalarTrace_toBaseChange, map_mul, toBaseChange_conjStar]
  exact baseChange_scalarTrace_star_mul_self_nonneg hb (fun i ↦ hQ (b i)) _

/-- Faithfulness on the native base-changed Clifford carrier for every negative definite real
quadratic form. -/
@[simp]
theorem scalarTrace_conjStar_mul_self_eq_zero_iff (hQ : (-Q).PosDef)
    {x : CliffordAlgebra (Q.baseChange ℂ)} :
    scalarTrace (Q.baseChange ℂ) (conjStar Q x * x) = 0 ↔ x = 0 := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated Q) (QuadraticForm.associated_isSymm ℝ Q)
  have hbQ (i) : Q (b i) < 0 := neg_pos.mp (hQ (b i) (b.ne_zero i))
  rw [← baseChange_scalarTrace_toBaseChange, map_mul, toBaseChange_conjStar,
    baseChange_scalarTrace_star_mul_self_eq_zero_iff hb hbQ]
  exact (equivBaseChange ℂ Q).map_eq_zero_iff

/-- The complexified negative Clifford trace is faithful exactly for negative definite real
quadratic forms. Null vectors and vectors of positive quadratic value obstruct faithfulness. -/
theorem scalarTrace_conjStar_faithful_iff :
    (∀ x : CliffordAlgebra (Q.baseChange ℂ),
      scalarTrace (Q.baseChange ℂ) (conjStar Q x * x) = 0 ↔ x = 0) ↔ (-Q).PosDef := by
  refine ⟨fun h v hv ↦ ?_, fun h x ↦ scalarTrace_conjStar_mul_self_eq_zero_iff h⟩
  apply neg_pos.mpr
  by_contra hneg
  obtain ⟨y, hy, htrace⟩ :=
    exists_ne_zero_scalarTrace_star_mul_self_eq_zero hv (le_of_not_gt hneg)
  apply hy
  apply ofBaseChangeAux_injective (A := ℂ) Q
  simpa only [map_zero] using (h (ofBaseChangeAux ℂ Q y)).mp (by
    rw [conjStar_ofBaseChangeAux, ← map_mul, scalarTrace_ofBaseChangeAux, htrace, map_zero])

end TauCeti
