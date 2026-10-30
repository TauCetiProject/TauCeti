/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.EReal.Basic
public import TauCeti.Analysis.Matrix.FunctionalCalculus

/-!
# Entropy and relative entropy of finite matrices

This file develops the entropy calculus of finite quantum systems. A state of such a system is a
*density matrix*: a positive semidefinite matrix of trace one. The matrices have entries in any
`RCLike` field, the physical case being `ℂ`.

* The *von Neumann entropy* of `ρ` is `S(ρ) = -Tr (ρ log ρ) = ∑ᵢ -λᵢ log λᵢ`, the trace of the
  functional calculus of `Real.negMulLog`; the convention `0 log 0 = 0` is built in.
  `Matrix.vonNeumannEntropy`.
* The *relative entropy* (Umegaki) of `ρ` with respect to `σ` is
  `D(ρ ‖ σ) = Tr (ρ (log ρ - log σ))` when the kernel of `σ` is contained in the kernel of `ρ`,
  and `⊤` otherwise. It takes values in `EReal`, since for references `σ` which are not
  normalized it may be negative. `Matrix.relativeEntropy`.

The basic inequality is **Klein's inequality** `Tr ρ - Tr σ ≤ D(ρ ‖ σ)` for positive
semidefinite `ρ` and `σ`, which gives the positivity of relative entropy between density matrices.
The trace formula `Matrix.IsHermitian.trace_cfc_mul_cfc` reduces it to the scalar inequality
`a - b ≤ a log a - a log b` between the eigenvalues `a` of `ρ` and `b` of `σ`, weighted by the
doubly stochastic overlaps `‖⟪uᵢ, vⱼ⟫‖²` of their eigenvectors; the support condition removes the
pairs with `b = 0 < a`, for which the scalar inequality fails.

## Main results

* `Matrix.PosSemidef.re_trace_sub_trace_le_relativeEntropy` — Klein's inequality: for positive
  semidefinite `ρ` and `σ`, `Tr ρ - Tr σ ≤ D(ρ ‖ σ)`;
* `Matrix.PosSemidef.relativeEntropy_nonneg` — positivity of the relative entropy of two positive
  semidefinite matrices of equal trace, in particular of two density matrices;
* `Matrix.PosSemidef.vonNeumannEntropy_nonneg` and
  `Matrix.PosSemidef.vonNeumannEntropy_le_log_card` — `0 ≤ S(ρ) ≤ log (card n)` for a density
  matrix `ρ`.

## References

* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Section 11.3 (von Neumann entropy, quantum relative entropy and Klein's
  inequality).
* E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemporary
  Mathematics 529 (2010), Section 2 (Klein's inequality).
* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second
  edition, Springer (1997), Section 6.2 (the entropy of quantum spin systems).
-/

public section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

namespace IsHermitian

variable {A B : Matrix n n 𝕜}

/-- The real part of the trace formula `Matrix.IsHermitian.trace_cfc_mul_cfc`. -/
private theorem re_trace_cfc_mul_cfc (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    RCLike.re (cfc f A * cfc g B).trace = ∑ i, ∑ j, f (hA.eigenvalues i) *
      g (hB.eigenvalues j) * ‖⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
  simp only [hA.trace_cfc_mul_cfc hB, map_sum, RCLike.ofReal_re]

end IsHermitian

/-! ### Von Neumann entropy -/

/-- The *von Neumann entropy* `S(ρ) = -Tr (ρ log ρ)` of a matrix `ρ`: the real part of the trace
of the functional calculus of `x ↦ -x log x`, so that `0 log 0 = 0`. It is the entropy of a
quantum state when `ρ` is a density matrix. The functional calculus of a non-Hermitian matrix is
zero, so then `S(ρ) = 0`. -/
def vonNeumannEntropy (ρ : Matrix n n 𝕜) : ℝ :=
  RCLike.re (cfc Real.negMulLog ρ).trace

variable {ρ σ : Matrix n n 𝕜}

/-- The von Neumann entropy of a Hermitian matrix is `∑ᵢ -λᵢ log λᵢ` over its eigenvalues. -/
theorem IsHermitian.vonNeumannEntropy_eq_sum_negMulLog (hρ : ρ.IsHermitian) :
    ρ.vonNeumannEntropy = ∑ i, Real.negMulLog (hρ.eigenvalues i) := by
  simp only [vonNeumannEntropy, hρ.trace_cfc, map_sum, RCLike.ofReal_re]

/-- The von Neumann entropy of a Hermitian matrix is `-Tr (ρ log ρ)`. -/
theorem IsHermitian.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log (hρ : ρ.IsHermitian) :
    ρ.vonNeumannEntropy = -RCLike.re (ρ * cfc Real.log ρ).trace := by
  rw [vonNeumannEntropy, Real.negMulLog_eq_neg, cfc_neg, trace_neg, map_neg, ← hρ.mul_cfc]

/-- The von Neumann entropy of a positive semidefinite matrix of trace at most one is
nonnegative. -/
theorem PosSemidef.vonNeumannEntropy_nonneg (hρ : ρ.PosSemidef) (htr : RCLike.re ρ.trace ≤ 1) :
    0 ≤ ρ.vonNeumannEntropy := by
  have hsum : ∑ i, hρ.1.eigenvalues i ≤ 1 := by
    simpa [hρ.1.trace_eq_sum_eigenvalues] using htr
  rw [hρ.1.vonNeumannEntropy_eq_sum_negMulLog]
  refine Finset.sum_nonneg fun i _ ↦ Real.negMulLog_nonneg (hρ.eigenvalues_nonneg i) ?_
  exact (Finset.single_le_sum (fun j _ ↦ hρ.eigenvalues_nonneg j) (Finset.mem_univ i)).trans hsum

/-! ### Relative entropy -/

open Classical in
/-- The *relative entropy* (Umegaki) `D(ρ ‖ σ) = Tr (ρ (log ρ - log σ))` of a matrix `ρ` with
respect to `σ`. It is finite exactly when the support condition holds, that is, when the kernel
of `σ` is contained in the kernel of `ρ`; otherwise it is `⊤`. For density matrices it is the
quantum analogue of the Kullback–Leibler divergence, and it is nonnegative,
`Matrix.PosSemidef.relativeEntropy_nonneg`. -/
def relativeEntropy (ρ σ : Matrix n n 𝕜) : EReal :=
  if LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin then
    (RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace : EReal)
  else ⊤

/-- Under the support condition the relative entropy is the real number
`Tr (ρ (log ρ - log σ))`. -/
theorem relativeEntropy_of_ker_le (h : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    relativeEntropy ρ σ = (RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace : EReal) := by
  classical
  simp only [relativeEntropy, h, ite_true]

/-- Without the support condition the relative entropy is `⊤`. -/
theorem relativeEntropy_of_not_ker_le
    (h : ¬LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) : relativeEntropy ρ σ = ⊤ := by
  classical
  simp only [relativeEntropy, h, ite_false]

/-- The relative entropy is infinite exactly when the support condition fails. -/
@[simp]
theorem relativeEntropy_eq_top_iff :
    relativeEntropy ρ σ = ⊤ ↔ ¬LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  refine ⟨fun h hle ↦ ?_, relativeEntropy_of_not_ker_le⟩
  rw [relativeEntropy_of_ker_le hle] at h
  exact EReal.coe_ne_top _ h

@[simp]
theorem relativeEntropy_self (ρ : Matrix n n 𝕜) : relativeEntropy ρ ρ = 0 := by
  simp [relativeEntropy_of_ker_le le_rfl]

/-- The relative entropy with respect to a positive definite reference is always finite: the
support condition holds for every `ρ`. -/
theorem relativeEntropy_of_posDef (hσ : σ.PosDef) :
    relativeEntropy ρ σ = (RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace : EReal) := by
  refine relativeEntropy_of_ker_le ?_
  rw [LinearMap.ker_eq_bot.mpr (by exact hσ.mulVec_injective)]
  exact bot_le

/-- Under the support condition, `D(ρ ‖ σ) = -S(ρ) - Tr (ρ log σ)`. -/
theorem IsHermitian.relativeEntropy_eq_neg_vonNeumannEntropy_sub (hρ : ρ.IsHermitian)
    (h : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    relativeEntropy ρ σ =
      ((-ρ.vonNeumannEntropy - RCLike.re (ρ * cfc Real.log σ).trace : ℝ) : EReal) := by
  rw [relativeEntropy_of_ker_le h, hρ.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log, mul_sub,
    trace_sub, map_sub, neg_neg]

/-- Under the support condition, an eigenvector of `σ` with eigenvalue zero is orthogonal to every
eigenvector of `ρ` with nonzero eigenvalue. -/
private theorem IsHermitian.eigenvalues_eq_zero_of_inner_ne_zero (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (h : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) {i j : n}
    (hij : ⟪hρ.eigenvectorBasis i, hσ.eigenvectorBasis j⟫_𝕜 ≠ 0) (hj : hσ.eigenvalues j = 0) :
    hρ.eigenvalues i = 0 := by
  have hker : ρ *ᵥ ⇑(hσ.eigenvectorBasis j) = 0 := by
    have hv : σ *ᵥ ⇑(hσ.eigenvectorBasis j) = 0 := by
      rw [hσ.mulVec_eigenvectorBasis, hj, zero_smul]
    exact h hv
  have hsymm := isSymmetric_toEuclideanLin_iff.mpr hρ (hρ.eigenvectorBasis i)
    (hσ.eigenvectorBasis j)
  simp only [toLpLin_apply, hρ.mulVec_eigenvectorBasis, hker, WithLp.toLp_zero, inner_zero_right,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, WithLp.toLp_ofLp, inner_smul_left,
    RCLike.conj_ofReal, mul_eq_zero, RCLike.ofReal_eq_zero] at hsymm
  exact hsymm.resolve_right hij

/-- The scalar inequality behind the positivity of relative entropy:
`a - b ≤ a log a - a log b` for `a, b ≥ 0`, provided `a = 0` whenever `b = 0`. -/
private theorem sub_le_mul_log_sub_mul_log {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) : a - b ≤ a * Real.log a - a * Real.log b := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hb
  have hb : 0 < b := hb.lt_of_ne fun h ↦ ha.ne' (hab h.symm)
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
  rw [Real.log_div hb.ne' ha.ne', mul_sub, mul_sub, mul_div_cancel₀ b ha.ne', mul_one] at hlog
  linarith

/-- **Klein's inequality for the relative entropy.** For positive semidefinite `ρ` and `σ`,
`Tr ρ - Tr σ ≤ D(ρ ‖ σ)`. -/
theorem PosSemidef.re_trace_sub_trace_le_relativeEntropy (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) :
    ((RCLike.re (ρ.trace - σ.trace) : ℝ) : EReal) ≤ relativeEntropy ρ σ := by
  by_cases h : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin
  swap
  · rw [relativeEntropy_of_not_ker_le h]
    exact le_top
  rw [relativeEntropy_of_ker_le h, EReal.coe_le_coe_iff]
  -- Write every term as the trace of a product of a function of `ρ` and a function of `σ`.
  have hD : ρ * (cfc Real.log ρ - cfc Real.log σ) =
      cfc (fun x ↦ x * Real.log x) ρ * cfc (fun _ : ℝ ↦ (1 : ℝ)) σ -
        cfc (fun x : ℝ ↦ x) ρ * cfc Real.log σ := by
    rw [mul_sub, hρ.1.mul_cfc, cfc_const_one ℝ σ hσ.1.isSelfAdjoint, mul_one,
      cfc_id' ℝ ρ hρ.1.isSelfAdjoint]
  have hρtr : RCLike.re ρ.trace = ∑ i, ∑ j, hρ.1.eigenvalues i *
      ‖⟪hρ.1.eigenvectorBasis i, hσ.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    simpa only [cfc_const_one ℝ σ hσ.1.isSelfAdjoint, mul_one,
      cfc_id' ℝ ρ hρ.1.isSelfAdjoint] using
      IsHermitian.re_trace_cfc_mul_cfc hρ.1 hσ.1 (fun x ↦ x) (fun _ ↦ 1)
  have hσtr : RCLike.re σ.trace = ∑ i, ∑ j, hσ.1.eigenvalues j *
      ‖⟪hρ.1.eigenvectorBasis i, hσ.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    simpa only [cfc_const_one ℝ ρ hρ.1.isSelfAdjoint, one_mul,
      cfc_id' ℝ σ hσ.1.isSelfAdjoint] using
      IsHermitian.re_trace_cfc_mul_cfc hρ.1 hσ.1 (fun _ ↦ 1) (fun x ↦ x)
  rw [hD, trace_sub, map_sub, map_sub, IsHermitian.re_trace_cfc_mul_cfc hρ.1 hσ.1,
    IsHermitian.re_trace_cfc_mul_cfc hρ.1 hσ.1, hρtr, hσtr, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  simp only [mul_one]
  -- Each term is a scalar inequality between eigenvalues, weighted by the overlap.
  by_cases hij : ⟪hρ.1.eigenvectorBasis i, hσ.1.eigenvectorBasis j⟫_𝕜 = 0
  · simp [hij]
  have key := sub_le_mul_log_sub_mul_log (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j)
    (hρ.1.eigenvalues_eq_zero_of_inner_ne_zero hσ.1 h hij)
  have hw : 0 ≤ ‖⟪hρ.1.eigenvectorBasis i, hσ.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right key hw]

/-- **Positivity of relative entropy.** For positive semidefinite `ρ` and `σ` of equal trace, in
particular for two density matrices, `0 ≤ D(ρ ‖ σ)`. -/
theorem PosSemidef.relativeEntropy_nonneg (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htr : ρ.trace = σ.trace) : 0 ≤ relativeEntropy ρ σ := by
  simpa [htr] using hρ.re_trace_sub_trace_le_relativeEntropy hσ

/-- The von Neumann entropy of a density matrix is at most `log (card n)`, the entropy of the
maximally mixed state `(card n)⁻¹ • 1`. -/
theorem PosSemidef.vonNeumannEntropy_le_log_card (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ρ.vonNeumannEntropy ≤ Real.log (Fintype.card n) := by
  have : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    simp [trace] at htr
  have hn : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  set c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hσ : (c • 1 : Matrix n n 𝕜).PosDef := PosDef.one.smul (inv_pos.mpr hn)
  have hσtr : (c • 1 : Matrix n n 𝕜).trace = 1 := by
    rw [trace_smul, trace_one, RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_natCast,
      ← RCLike.ofReal_mul, inv_mul_cancel₀ hn.ne', RCLike.ofReal_one]
  have hnonneg := hρ.relativeEntropy_nonneg hσ.posSemidef (htr.trans hσtr.symm)
  rw [hρ.1.relativeEntropy_eq_neg_vonNeumannEntropy_sub (by
    rw [LinearMap.ker_eq_bot.mpr (by exact hσ.mulVec_injective)]; exact bot_le),
    ← Algebra.algebraMap_eq_smul_one, cfc_algebraMap, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, trace_smul, htr, RCLike.smul_re, RCLike.one_re, mul_one,
    ← EReal.coe_zero, EReal.coe_le_coe_iff, Real.log_inv] at hnonneg
  linarith

end Matrix
