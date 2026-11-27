/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.Moment
public import TauCeti.RingTheory.MvPolynomial.JetPairing
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The Fischer pairing of polynomial vectors in the Fock model

Let `ω_ε` be the Weil representation of `U(ε)` on the Fock space `𝓕(ε)` and `v_P` the polynomial
vector of a complex polynomial `P` (`TauCeti.Fock.polyVector`). This file computes the inner
products of polynomial vectors and the matrix coefficients of `ω_ε` between them, and shows that
the polynomial vectors are dense.

* The overlap of `ω_ε(u) e` with the vacuum is `(ω_ε(u) e)(0) = det(u₋₋)⁻¹`, for the block `u₋₋`
  of `u` on the coordinates of sign `-1`.
* *Commutation rules.* The raising and lowering operators `A_j`, `B_j` move across `ω_ε(u)` in a
  matrix coefficient:
  `⟨v_Q, ω_ε(u) v_{A_j P}⟩ = ∑ i, u_{ij} ε_i ⟨v_{B_i Q}, ω_ε(u) v_P⟩` and
  `⟨v_Q, ω_ε(u) v_{B_j P}⟩ = ε_j ∑ i, conj (u_{ij}) ⟨v_{A_i Q}, ω_ε(u) v_P⟩`.
* *The Fischer pairing.* Multiplication by `X_i` is adjoint to `∂_i`, so `⟨v_P, v_Q⟩` is the
  constant term of `(conj P)(∂) Q`, with `conj P` the polynomial with conjugate coefficients: the
  jet pairing `MvPolynomial.jetPairing`. The vectors of distinct monomials are orthogonal and
  `⟨v_{X^μ}, v_{X^μ}⟩ = μ!`.
* *Density.* The polynomial vectors are dense in `𝓕(ε)`.

The commutation rules come from differentiating, at `t = 0`, the identity
`⟨v_Q, ω_ε(u) ϱ(t x) v_P⟩ = conj ⟨ω_ε(u) v_P, ϱ(-t u x) v_Q⟩`, which holds because `ω_ε(u)` moves
`ϱ(x)` to `ϱ(u x)` and `ϱ(-y)` is the adjoint of `ϱ(y)`; the Heisenberg derivatives of polynomial
vectors are `TauCeti.Fock.hasDerivAt_heisenbergRep_polyVector`. Taking `x = c eⱼ` with `c = 1`
and `c = I` separates the two rules, and `u = 1` gives the adjointness of `X_i` and `∂_i`. Density
holds because every translate `ϱ(y) e` of the vacuum has finite moments, so is a limit of
polynomial vectors (`TauCeti.Fock.exists_tendsto_moment`), and a bounded map is determined by its
values on these translates (`TauCeti.ReproducingModel.hom_ext`).

## Main results

* `TauCeti.Fock.weilRep_vacuum_apply_zero`: `(ω_ε(u) e)(0) = det(u₋₋)⁻¹`.
* `TauCeti.Fock.innerSL_weilRep_raiseOp`, `TauCeti.Fock.innerSL_weilRep_lowerOp`: the commutation
  rules.
* `TauCeti.Fock.innerSL_polyVector_X_mul`: `⟨v_{X_i P}, v_Q⟩ = ⟨v_P, v_{∂_i Q}⟩`.
* `TauCeti.Fock.innerSL_polyVector`: `⟨v_P, v_Q⟩ = ((conj P)(∂) Q)(0)`.
* `TauCeti.Fock.innerSL_polyVector_monomial`: the monomial vectors are orthogonal with squared
  norms `μ!`.
* `TauCeti.Fock.denseRange_polyVector`: the polynomial vectors are dense.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit 72fead1, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/Lib/Weil/Fock/PolynomialVectors.lean`
(`New.Fock.realWeil_vacVector_apply_zero`, `New.Fock.fockMatrixCoeff_raiseOp`,
`New.Fock.fockMatrixCoeff_lowerOp`, `New.Fock.fockInner_X_mul`, `New.Fock.fockInner_polyVector`,
`New.Fock.fockInner_polyVector_monomial`, `New.Fock.denseRange_polyVector`). The source's
`fockPairing` of two polynomials is here the jet pairing of a polynomial with a polynomial viewed
as a power series, and its lowering rule is stated with the sign on the right.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform,
  part I*, Comm. Pure Appl. Math. 14 (1961), 187–214.
* G. B. Folland, *Harmonic analysis in phase space*, Ann. of Math. Stud. 122 (1989), Chapter 1.
-/

public noncomputable section

open MeasureTheory Complex Finset MvPolynomial
open scoped ComplexConjugate

namespace TauCeti.Fock

open ReproducingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### The vacuum coefficient -/

/-- The overlap of `ω_ε(u) e` with the vacuum is the inverse of the determinant of the block
`u₋₋` of `u` on the coordinates of sign `-1`. -/
@[simp]
theorem weilRep_vacuum_apply_zero (u : unitaryGroup ε) :
    weilRep ε u vacuum 0 = (negBlock ε ((u : GL ι ℂ) : Matrix ι ι ℂ)).det⁻¹ := by
  have h := conj_mul_weilRep_vacuum_apply_zero (multiplier ε) u cocycle_multiplier
  rw [multiplier_apply, conj_conj] at h
  exact eq_inv_of_mul_eq_one_right h

/-! ### Commutation rules -/

/-- The derivative at `t = 0` of `⟨v_Q, ω_ε(u) ϱ(t x) v_P⟩ = conj ⟨ω_ε(u) v_P, ϱ(-t u x) v_Q⟩`. -/
private theorem innerSL_weilRep_heisenbergDeriv (u : unitaryGroup ε) (x : ι → ℂ)
    (P Q : MvPolynomial ι ℂ) :
    ReproducingModel.innerSL (polyVector ε Q)
        (weilRep ε u (polyVector ε (heisenbergDeriv ε x P))) =
      conj (ReproducingModel.innerSL (weilRep ε u (polyVector ε P))
        (polyVector ε (heisenbergDeriv ε (-(u • x)) Q))) := by
  have h_move (t : ℝ) :
      ReproducingModel.innerSL (polyVector ε Q)
          (weilRep ε u (heisenbergRep (t • x) (polyVector ε P))) =
        conj (ReproducingModel.innerSL (weilRep ε u (polyVector ε P))
          (heisenbergRep (t • -(u • x)) (polyVector ε Q))) := by
    rw [weilRep_heisenbergRep, ← conj_innerSL, innerSL_heisenbergRep_left, smul_def, smul_def,
      Matrix.mulVec_smul, smul_neg]
  have h₁ := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (((ReproducingModel.innerSL (polyVector ε Q)).comp (weilRep ε u)).restrictScalars
      ℝ).hasFDerivAt (hasDerivAt_heisenbergRep_polyVector x P)
  have h₂ := (HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((ReproducingModel.innerSL (weilRep ε u (polyVector ε P))).restrictScalars ℝ).hasFDerivAt
      (hasDerivAt_heisenbergRep_polyVector (-(u • x)) Q)).star
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply, h_move, starRingEnd_apply] at h₁
  rw [starRingEnd_apply]
  exact h₁.unique h₂

/-- If `c a = conj c b` for every complex `c`, then `a = 0` and `b = 0`. -/
private theorem eq_zero_of_forall_mul_eq_conj_mul {a b : ℂ} (h : ∀ c : ℂ, c * a = conj c * b) :
    a = 0 ∧ b = 0 := by
  have h₁ := h 1
  have h₂ := h Complex.I
  simp only [one_mul, map_one, Complex.conj_I] at h₁ h₂
  exact ⟨by linear_combination (h₁ - Complex.I * h₂) / 2 + (a + b) / 2 * Complex.I_sq,
    by linear_combination (-h₁ - Complex.I * h₂) / 2 + (a + b) / 2 * Complex.I_sq⟩

/-- Both commutation rules, as the vanishing of their two differences. -/
private theorem commutation_rules (u : unitaryGroup ε) (P Q : MvPolynomial ι ℂ) (j : ι) :
    ReproducingModel.innerSL (polyVector ε Q) (weilRep ε u (polyVector ε (raiseOp ε j P))) -
        ∑ i, ((u : GL ι ℂ) : Matrix ι ι ℂ) i j * ((ε i : ℤ) : ℂ) *
          ReproducingModel.innerSL (polyVector ε (lowerOp ε i Q))
            (weilRep ε u (polyVector ε P)) = 0 ∧
      ((ε j : ℤ) : ℂ) * ReproducingModel.innerSL (polyVector ε Q)
          (weilRep ε u (polyVector ε (lowerOp ε j P))) -
        ∑ i, conj (((u : GL ι ℂ) : Matrix ι ι ℂ) i j) *
          ReproducingModel.innerSL (polyVector ε (raiseOp ε i Q))
            (weilRep ε u (polyVector ε P)) = 0 := by
  refine eq_zero_of_forall_mul_eq_conj_mul fun c ↦ ?_
  have h := innerSL_weilRep_heisenbergDeriv u (Pi.single j c) P Q
  simp only [heisenbergDeriv_single, smul_def, heisenbergDeriv_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_sub, map_smul, map_sum, smul_eq_mul, Pi.neg_apply,
    Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero,
    sum_ite_eq', mem_univ, ite_true, conj_innerSL, map_mul, map_neg, conj_conj, conj_sign] at h
  set U := ((u : GL ι ℂ) : Matrix ι ι ℂ)
  -- `h` reads `c a₁ - conj c ε_j a₂ = ∑ i, (-(conj (U i j) conj c) b₁ i - -(U i j c) ε i b₂ i)`.
  have h_sum : ∑ i, (-(conj (U i j) * conj c) *
        ReproducingModel.innerSL (polyVector ε (raiseOp ε i Q)) (weilRep ε u (polyVector ε P)) -
      -(U i j * c) * ((ε i : ℤ) : ℂ) *
        ReproducingModel.innerSL (polyVector ε (lowerOp ε i Q)) (weilRep ε u (polyVector ε P))) =
      c * ∑ i, U i j * ((ε i : ℤ) : ℂ) *
          ReproducingModel.innerSL (polyVector ε (lowerOp ε i Q)) (weilRep ε u (polyVector ε P)) -
        conj c * ∑ i, conj (U i j) *
          ReproducingModel.innerSL (polyVector ε (raiseOp ε i Q))
            (weilRep ε u (polyVector ε P)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  linear_combination h + h_sum

/-- **The raising rule.** The raising operator `A_j` on the right of a matrix coefficient of
`ω_ε(u)` becomes `∑ i, u_{ij} ε_i B_i` on the left:
`⟨v_Q, ω_ε(u) v_{A_j P}⟩ = ∑ i, u_{ij} ε_i ⟨v_{B_i Q}, ω_ε(u) v_P⟩`. -/
theorem innerSL_weilRep_raiseOp (u : unitaryGroup ε) (P Q : MvPolynomial ι ℂ) (j : ι) :
    ReproducingModel.innerSL (polyVector ε Q) (weilRep ε u (polyVector ε (raiseOp ε j P))) =
      ∑ i, ((u : GL ι ℂ) : Matrix ι ι ℂ) i j * ((ε i : ℤ) : ℂ) *
        ReproducingModel.innerSL (polyVector ε (lowerOp ε i Q)) (weilRep ε u (polyVector ε P)) :=
  sub_eq_zero.1 (commutation_rules u P Q j).1

/-- **The lowering rule.** The lowering operator `B_j` on the right of a matrix coefficient of
`ω_ε(u)` becomes `ε_j ∑ i, conj (u_{ij}) A_i` on the left:
`⟨v_Q, ω_ε(u) v_{B_j P}⟩ = ε_j ∑ i, conj (u_{ij}) ⟨v_{A_i Q}, ω_ε(u) v_P⟩`. -/
theorem innerSL_weilRep_lowerOp (u : unitaryGroup ε) (P Q : MvPolynomial ι ℂ) (j : ι) :
    ReproducingModel.innerSL (polyVector ε Q) (weilRep ε u (polyVector ε (lowerOp ε j P))) =
      ((ε j : ℤ) : ℂ) * ∑ i, conj (((u : GL ι ℂ) : Matrix ι ι ℂ) i j) *
        ReproducingModel.innerSL (polyVector ε (raiseOp ε i Q)) (weilRep ε u (polyVector ε P)) := by
  rw [← sub_eq_zero.1 (commutation_rules u P Q j).2, ← mul_assoc, sign_mul_sign, one_mul]

/-! ### The Fischer pairing -/

/-- Multiplication by `X_i` is adjoint to `∂_i`: `⟨v_{X_i P}, v_Q⟩ = ⟨v_P, v_{∂_i Q}⟩`. -/
theorem innerSL_polyVector_X_mul (P Q : MvPolynomial ι ℂ) (i : ι) :
    ReproducingModel.innerSL (polyVector ε (X i * P)) (polyVector ε Q) =
      ReproducingModel.innerSL (polyVector ε P) (polyVector ε (pderiv i Q)) := by
  -- The case `u = 1` of the lowering rule if `ε i = 1` and of the raising rule if `ε i = -1`.
  rcases Int.units_eq_one_or (ε i) with hε | hε
  · simpa [hε, Matrix.one_apply] using (innerSL_weilRep_lowerOp (ε := ε) 1 Q P i).symm
  · simpa [hε, Matrix.one_apply] using (innerSL_weilRep_raiseOp (ε := ε) 1 Q P i).symm

/-- **The Fischer pairing**: `⟨v_P, v_Q⟩ = ((conj P)(∂) Q)(0)`, the jet pairing of `Q` with the
polynomial `conj P` with conjugate coefficients. -/
theorem innerSL_polyVector (P Q : MvPolynomial ι ℂ) :
    ReproducingModel.innerSL (polyVector ε P) (polyVector ε Q) =
      jetPairing (map (starRingEnd ℂ) P) (Q : MvPowerSeries ι ℂ) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a =>
    have h_C : polyVector ε (C a) = a • vacuum := by
      rw [C_eq_smul_one, map_smul, polyVector_one]
    have h_zero : holomorphicCoord ε 0 = 0 := by
      ext i
      simp [holomorphicCoord_apply]
    simp [h_C, h_zero, gaussian_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPolynomial.coeff_coe, eval_zero, constantCoeff_eq]
  | add P P' hP hP' => simp [hP, hP']
  | mul_X P i hP =>
    rw [mul_comm P (X i), innerSL_polyVector_X_mul, hP, ← MvPowerSeries.pderiv_coe,
      ← jetPairing_mul_X, mul_comm (X i) P, map_mul (MvPolynomial.map (starRingEnd ℂ)), map_X]

/-- The vectors of distinct monomials are orthogonal, and `⟨v_{X^μ}, v_{X^μ}⟩ = μ!`. -/
theorem innerSL_polyVector_monomial (μ μ' : ι →₀ ℕ) :
    ReproducingModel.innerSL (polyVector ε (monomial μ 1)) (polyVector ε (monomial μ' 1)) =
      if μ = μ' then μ.prod fun _ n ↦ (n.factorial : ℂ) else 0 := by
  rw [innerSL_polyVector, map_monomial, map_one, jetPairing_monomial, MvPolynomial.coeff_coe,
    coeff_monomial]
  simp [eq_comm]

/-! ### Density -/

/-- **Density**: the polynomial vectors are dense in the Fock space. -/
theorem denseRange_polyVector : DenseRange (polyVector ε) := by
  -- The closure `V` of the range contains every translate of the vacuum: it has finite moments,
  -- so it is a limit of polynomial vectors in the moment of order `0`, which is the norm.
  let V := (LinearMap.range (polyVector ε)).topologicalClosure
  -- The quotient by `V` is a Banach space because `V` is closed.
  have hV : IsClosed (V : Set (FockSpace ε)) := Submodule.isClosed_topologicalClosure _
  have h_mem (y : ι → ℂ) : heisenbergRep y (vacuum : FockSpace ε) ∈ V := by
    obtain ⟨P, hP⟩ := exists_tendsto_moment (hasFiniteMoments_vacuum.heisenbergRep y)
    have h_tendsto : Filter.Tendsto (fun n ↦ polyVector ε (P n)) Filter.atTop
        (nhds (heisenbergRep y vacuum)) := by
      simpa [moment_zero, eNorm_sub_rev, tendsto_iff_eNorm_sub_tendsto_zero] using hP 0
    exact mem_closure_of_tendsto h_tendsto
      (.of_forall fun n ↦ LinearMap.mem_range_self _ (P n))
  -- A bounded map is determined by its values on these translates, so the quotient map vanishes.
  have h_zero : V.mkQL = 0 := hom_ext fun y ↦ by simpa using h_mem y
  intro v
  have hv : v ∈ V := (Submodule.Quotient.mk_eq_zero _).1 congr($h_zero v)
  rwa [← LinearMap.coe_range]

end TauCeti.Fock
