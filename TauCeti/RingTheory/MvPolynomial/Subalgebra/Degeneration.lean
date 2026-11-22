/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.UnitFiber
public import TauCeti.RingTheory.MvPolynomial.Subalgebra.Symbol
import TauCeti.RingTheory.TensorProduct.BaseChangeEval

/-!
# Fibres of the subalgebra weight Rees algebra

For a subalgebra `A` of `MvPolynomial σ R` over a commutative ring `R` and nonnegative integral
weights `w : σ → ℕ`, `TauCeti.RingTheory.MvPolynomial.Subalgebra.Symbol` constructs the symbol map
`A.weightReesSymbol w : A.weightReesAlgebra w →ₐ[R] MvPolynomial σ R`, its corestriction
`A.weightReesSymbolToInitial w : A.weightReesAlgebra w →ₐ[R] A.weightInitialAlgebra w`, and its
kernel `Subalgebra.ker_weightReesSymbol`.

This file identifies the special fibre at `t = 0` and the fibres at units of `R` of the induced
Rees algebra `A.weightReesAlgebra w` over `R[t]` (exhausting all `k`-rational fibres when `R` is
a field `k`):

* **Special fibre at `t = 0`**: quotienting by `t`
  (`Subalgebra.quotientSpanXWeightReesAlgebraEquiv`) and tensor base change `R ⊗[R[t]] -` along
  evaluation at `0` (`Subalgebra.baseChangeZeroWeightReesAlgebraEquiv`) both recover
  `A.weightInitialAlgebra w` via `Subalgebra.weightReesSymbolToInitial`.
* **General fibre at units**: for every unit `a` of `R`, the generic unit-fibre comparisons
  `TauCeti.coeffSubalgebra.quotientSpanXSubAlgebraMapEquiv` and
  `TauCeti.coeffSubalgebra.baseChangeEvalEquiv` apply directly to `A.weightReesAlgebra w` (using
  `A.weightFiltration_mono w` and `A.iSup_weightFiltration w`). At `t = 1`, quotienting by `t - 1`
  (`Subalgebra.quotientSpanXSubOneWeightReesAlgebraEquiv`) and tensor base change along evaluation
  at `1` (`Subalgebra.baseChangeOneWeightReesAlgebraEquiv`) recover `A` with explicit lifts given
  by `weightedTotalDegree w`.

Over a field `k`, `A.weightReesAlgebra w` is flat over `k[t]` (`Subalgebra.flat_weightReesAlgebra`),
and `a = 0` versus `a ≠ 0` identifies every `k`-rational fibre and base change of the degeneration,
without any finite-generation or SAGBI assumption on `A`.

## Main definitions

* `Subalgebra.quotientSpanXWeightReesAlgebraEquiv`,
  `Subalgebra.baseChangeZeroWeightReesAlgebraEquiv`: the special fibre at `t = 0`.
* `Subalgebra.quotientSpanXSubOneWeightReesAlgebraEquiv`,
  `Subalgebra.baseChangeOneWeightReesAlgebraEquiv`: the fibre at `t = 1`.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150, §15.8.
-/

public section

open scoped Polynomial TensorProduct
open DirectSum MvPolynomial TauCeti TauCeti.MvPolynomial

namespace Subalgebra

section Fibres

variable {σ R : Type*} [CommRing R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)

/-- **Special fibre at `t = 0`, quotient form.** Quotienting `A.weightReesAlgebra w` by the Rees
parameter gives the weight-initial algebra of `A`. -/
noncomputable def quotientSpanXWeightReesAlgebraEquiv :
    (A.weightReesAlgebra w ⧸
      Ideal.span {coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)})
      ≃ₐ[R] A.weightInitialAlgebra w :=
  (Ideal.quotientEquivAlgOfEq R
    ((A.ker_weightReesSymbolToInitial w).trans (A.ker_weightReesSymbol w)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (A.weightReesSymbolToInitial_surjective w))

@[simp]
theorem quotientSpanXWeightReesAlgebraEquiv_mk (g : A.weightReesAlgebra w) :
    A.quotientSpanXWeightReesAlgebraEquiv w (Ideal.Quotient.mk _ g) =
      A.weightReesSymbolToInitial w g := by
  simp [quotientSpanXWeightReesAlgebraEquiv]

@[simp]
theorem quotientSpanXWeightReesAlgebraEquiv_symm_weightReesSymbolToInitial
    (g : A.weightReesAlgebra w) :
    (A.quotientSpanXWeightReesAlgebraEquiv w).symm (A.weightReesSymbolToInitial w g) =
      Ideal.Quotient.mk _ g := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanXWeightReesAlgebraEquiv_mk]

theorem coe_quotientSpanXWeightReesAlgebraEquiv_mk (g : A.weightReesAlgebra w) :
    (A.quotientSpanXWeightReesAlgebraEquiv w (Ideal.Quotient.mk _ g) : MvPolynomial σ R) =
      A.weightReesSymbol w g := by
  simp

theorem quotientSpanXWeightReesAlgebraEquiv_symm_weightInitialForm
    {f : MvPolynomial σ R} (hf : f ∈ A) :
    (A.quotientSpanXWeightReesAlgebraEquiv w).symm
      ⟨weightInitialForm w f, A.weightInitialForm_mem_weightInitialAlgebra w hf⟩ =
      Ideal.Quotient.mk _ (coeffSubalgebra.monomial (A.weightFiltration w)
        (f.weightedTotalDegree w) ⟨f, hf⟩
        ((A.mem_weightFiltration_iff w).mpr
          (mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl))) := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanXWeightReesAlgebraEquiv_mk,
    weightReesSymbolToInitial_monomial_weightedTotalDegree]

/-- **Special fibre at `t = 0`, base-change form.** Tensor base change of `A.weightReesAlgebra w`
along evaluation `R[t] → R` at `0` recovers the weight-initial algebra of `A`. -/
noncomputable def baseChangeZeroWeightReesAlgebraEquiv :
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    (R ⊗[R[X]] A.weightReesAlgebra w) ≃ₐ[R] A.weightInitialAlgebra w :=
  (A.weightReesSymbolToInitial w).baseChangeEvalEquivOfSurjective (a := (0 : R))
    (Subtype.ext (by simp))
    (A.weightReesSymbolToInitial_surjective w)
    (fun g hg ↦ by
      rw [coeffSubalgebra.algebraMap_X, map_zero, sub_zero, ← A.ker_weightReesSymbol w,
        ← A.ker_weightReesSymbolToInitial w]
      exact hg)

@[simp]
theorem baseChangeZeroWeightReesAlgebraEquiv_tmul (r : R) (g : A.weightReesAlgebra w) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    A.baseChangeZeroWeightReesAlgebraEquiv w (r ⊗ₜ[R[X]] g) =
      r • A.weightReesSymbolToInitial w g := by
  let := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
  simp [baseChangeZeroWeightReesAlgebraEquiv]

@[simp]
theorem baseChangeZeroWeightReesAlgebraEquiv_symm_weightReesSymbolToInitial
    (g : A.weightReesAlgebra w) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    (A.baseChangeZeroWeightReesAlgebraEquiv w).symm (A.weightReesSymbolToInitial w g) =
      1 ⊗ₜ[R[X]] g := by
  let := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
  rw [AlgEquiv.symm_apply_eq, baseChangeZeroWeightReesAlgebraEquiv_tmul, one_smul]

theorem coe_baseChangeZeroWeightReesAlgebraEquiv_tmul (r : R) (g : A.weightReesAlgebra w) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    (A.baseChangeZeroWeightReesAlgebraEquiv w (r ⊗ₜ[R[X]] g) : MvPolynomial σ R) =
      r • A.weightReesSymbol w g := by
  let := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
  simp

theorem baseChangeZeroWeightReesAlgebraEquiv_symm_weightInitialForm
    {f : MvPolynomial σ R} (hf : f ∈ A) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    (A.baseChangeZeroWeightReesAlgebraEquiv w).symm
      ⟨weightInitialForm w f, A.weightInitialForm_mem_weightInitialAlgebra w hf⟩ =
      1 ⊗ₜ[R[X]] coeffSubalgebra.monomial (A.weightFiltration w) (f.weightedTotalDegree w) ⟨f, hf⟩
        ((A.mem_weightFiltration_iff w).mpr
          (mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl)) := by
  let := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
  rw [AlgEquiv.symm_apply_eq, baseChangeZeroWeightReesAlgebraEquiv_tmul, one_smul,
    weightReesSymbolToInitial_monomial_weightedTotalDegree]

/-- **Fibre at `t = 1`, quotient form.** Quotienting `A.weightReesAlgebra w` by `t - 1` recovers
`A`. -/
noncomputable def quotientSpanXSubOneWeightReesAlgebraEquiv :
    (A.weightReesAlgebra w ⧸
      Ideal.span {coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w) - 1})
      ≃ₐ[R] A :=
  coeffSubalgebra.quotientSpanXSubOneEquiv (A.weightFiltration w)
    (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w) (A.iSup_weightFiltration w)

@[simp]
theorem quotientSpanXSubOneWeightReesAlgebraEquiv_mk (g : A.weightReesAlgebra w) :
    A.quotientSpanXSubOneWeightReesAlgebraEquiv w (Ideal.Quotient.mk _ g) =
      coeffSubalgebra.evalOne (A.weightFiltration w) g :=
  coeffSubalgebra.quotientSpanXSubOneEquiv_mk _ _ _ _ g

@[simp]
theorem quotientSpanXSubOneWeightReesAlgebraEquiv_symm_evalOne (g : A.weightReesAlgebra w) :
    (A.quotientSpanXSubOneWeightReesAlgebraEquiv w).symm
      (coeffSubalgebra.evalOne (A.weightFiltration w) g) = Ideal.Quotient.mk _ g :=
  coeffSubalgebra.quotientSpanXSubOneEquiv_symm_evalOne _ _ _ _ g

theorem quotientSpanXSubOneWeightReesAlgebraEquiv_symm_apply (f : A) :
    (A.quotientSpanXSubOneWeightReesAlgebraEquiv w).symm f =
      Ideal.Quotient.mk _ (coeffSubalgebra.monomial (A.weightFiltration w)
        ((f : MvPolynomial σ R).weightedTotalDegree w) f
        ((A.mem_weightFiltration_iff w).mpr
          (mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl))) :=
  coeffSubalgebra.quotientSpanXSubOneEquiv_symm_of_mem _ _ _ _ _

/-- **Fibre at `t = 1`, base-change form.** Tensor base change of `A.weightReesAlgebra w` along
evaluation `R[t] → R` at `1` recovers `A`. -/
noncomputable def baseChangeOneWeightReesAlgebraEquiv :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    (R ⊗[R[X]] A.weightReesAlgebra w) ≃ₐ[R] A :=
  coeffSubalgebra.baseChangeEvalOneEquiv (A.weightFiltration w)
    (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w) (A.iSup_weightFiltration w)

@[simp]
theorem baseChangeOneWeightReesAlgebraEquiv_tmul (r : R) (g : A.weightReesAlgebra w) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    A.baseChangeOneWeightReesAlgebraEquiv w (r ⊗ₜ[R[X]] g) =
      r • coeffSubalgebra.evalOne (A.weightFiltration w) g :=
  coeffSubalgebra.baseChangeEvalOneEquiv_tmul _ _ _ _ r g

@[simp]
theorem baseChangeOneWeightReesAlgebraEquiv_symm_evalOne (g : A.weightReesAlgebra w) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    (A.baseChangeOneWeightReesAlgebraEquiv w).symm
      (coeffSubalgebra.evalOne (A.weightFiltration w) g) = 1 ⊗ₜ[R[X]] g :=
  coeffSubalgebra.baseChangeEvalOneEquiv_symm_evalOne _ _ _ _ g

theorem baseChangeOneWeightReesAlgebraEquiv_symm_apply (f : A) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    (A.baseChangeOneWeightReesAlgebraEquiv w).symm f =
      1 ⊗ₜ[R[X]] coeffSubalgebra.monomial (A.weightFiltration w)
        ((f : MvPolynomial σ R).weightedTotalDegree w) f
        ((A.mem_weightFiltration_iff w).mpr
          (mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl)) :=
  coeffSubalgebra.baseChangeEvalOneEquiv_symm_of_mem _ _ _ _ _

end Fibres

end Subalgebra
