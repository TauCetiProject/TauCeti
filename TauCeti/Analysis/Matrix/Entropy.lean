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
public import TauCeti.LinearAlgebra.Matrix.Trace.Partial
import TauCeti.Analysis.Matrix.Kronecker
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

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

Klein's inequality against a product state gives the **subadditivity** of the von Neumann entropy:
for a density matrix `ρ` of a bipartite system, indexed by `m × n`, with reduced density matrices
`ρ_A = Tr₂ ρ` and `ρ_B = Tr₁ ρ`, `S(ρ) ≤ S(ρ_A) + S(ρ_B)`. Since
`log (σ_A ⊗ₖ σ_B) = log σ_A ⊗ₖ 1 + 1 ⊗ₖ log σ_B` for positive definite `σ_A` and `σ_B`, the partial
traces turn `Tr (ρ log (σ_A ⊗ₖ σ_B))` into `Tr (ρ_A log σ_A) + Tr (ρ_B log σ_B)`. The reduced
density matrices may be singular, so we compare `ρ` with `σ_A ⊗ₖ σ_B`, where `σ_A` and `σ_B`
replace the zero eigenvalues of `ρ_A` and `ρ_B` by `t > 0`. This leaves `Tr (ρ_A log σ_A) = -S(ρ_A)`
unchanged, and the error in the traces vanishes as `t → 0`.

## Main results

* `Matrix.PosSemidef.re_trace_sub_trace_le_relativeEntropy` — Klein's inequality: for positive
  semidefinite `ρ` and `σ`, `Tr ρ - Tr σ ≤ D(ρ ‖ σ)`;
* `Matrix.PosSemidef.relativeEntropy_nonneg` — positivity of the relative entropy of two positive
  semidefinite matrices of equal trace, in particular of two density matrices;
* `Matrix.PosSemidef.vonNeumannEntropy_nonneg` and
  `Matrix.PosSemidef.vonNeumannEntropy_le_log_card` — `0 ≤ S(ρ) ≤ log (card n)` for a density
  matrix `ρ`;
* `Matrix.PosSemidef.vonNeumannEntropy_le_partialTraceRight_add_partialTraceLeft` —
  subadditivity, `S(ρ) ≤ S(Tr₂ ρ) + S(Tr₁ ρ)` for a density matrix `ρ` of a bipartite system.

## References

* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Section 11.3 (von Neumann entropy, quantum relative entropy, Klein's
  inequality and subadditivity).
* E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemporary
  Mathematics 529 (2010), Section 2 (Klein's inequality).
* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second
  edition, Springer (1997), Section 6.2 (the entropy of quantum spin systems).
-/

public section

noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexOrder Kronecker

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Von Neumann entropy -/

/-- The *von Neumann entropy* `S(ρ) = -Tr (ρ log ρ)` of a matrix `ρ`: the real part of the trace
of the functional calculus of `x ↦ -x log x`, so that `0 log 0 = 0`. It is the entropy of a
quantum state when `ρ` is a density matrix. The functional calculus of a non-Hermitian matrix is
zero, so then `S(ρ) = 0`. -/
def vonNeumannEntropy (ρ : Matrix n n 𝕜) : ℝ :=
  RCLike.re (cfc Real.negMulLog ρ).trace

/-- The defining equation of the von Neumann entropy, valid for every matrix `ρ`. -/
theorem vonNeumannEntropy_def (ρ : Matrix n n 𝕜) :
    ρ.vonNeumannEntropy = RCLike.re (cfc Real.negMulLog ρ).trace := by
  rw [vonNeumannEntropy]

@[simp]
theorem vonNeumannEntropy_zero : (0 : Matrix n n 𝕜).vonNeumannEntropy = 0 := by
  simp [vonNeumannEntropy_def, cfc_apply_zero]

@[simp]
theorem vonNeumannEntropy_one : (1 : Matrix n n 𝕜).vonNeumannEntropy = 0 := by
  simp [vonNeumannEntropy_def, cfc_apply_one]

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

@[simp]
theorem relativeEntropy_zero_left (σ : Matrix n n 𝕜) : relativeEntropy 0 σ = 0 := by
  rw [relativeEntropy_of_ker_le fun v _ ↦ by simp]
  simp

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

/-- The relative entropy with respect to a nonzero real multiple `c • 1` of the identity is
`D(ρ ‖ c • 1) = -S(ρ) - log c · Tr ρ`. -/
theorem IsHermitian.relativeEntropy_smul_one (hρ : ρ.IsHermitian) {c : ℝ} (hc : c ≠ 0) :
    relativeEntropy ρ (c • 1 : Matrix n n 𝕜) =
      ((-ρ.vonNeumannEntropy - Real.log c * RCLike.re ρ.trace : ℝ) : EReal) := by
  have hker : LinearMap.ker (c • 1 : Matrix n n 𝕜).mulVecLin ≤ LinearMap.ker ρ.mulVecLin :=
    fun v hv ↦ by simp_all
  rw [hρ.relativeEntropy_eq_neg_vonNeumannEntropy_sub hker, ← Algebra.algebraMap_eq_smul_one,
    cfc_algebraMap, Algebra.algebraMap_eq_smul_one]
  simp [RCLike.smul_re]

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
  have key := Real.sub_le_mul_log_sub_mul_log (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j)
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
  rw [hρ.1.relativeEntropy_smul_one (inv_ne_zero hn.ne'), htr, RCLike.one_re, mul_one,
    Real.log_inv, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hnonneg
  linarith

/-! ### Subadditivity -/

/-- Replacing the zero eigenvalues of a positive semidefinite `P` by `t > 0` gives a positive
definite `σ` with `Tr (P log σ) = -S(P)` and `Tr σ ≤ Tr P + t · card n`. -/
private theorem PosSemidef.exists_posDef_regularization {P : Matrix n n 𝕜} (hP : P.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    ∃ σ : Matrix n n 𝕜, σ.PosDef ∧ RCLike.re (P * cfc Real.log σ).trace = -P.vonNeumannEntropy ∧
      ∃ r : ℝ, σ.trace = r ∧ 0 ≤ r ∧ r ≤ RCLike.re P.trace + t * Fintype.card n := by
  set g : ℝ → ℝ := fun x ↦ if x = 0 then t else x
  have hgc : ContinuousOn g (spectrum ℝ P) := P.finite_real_spectrum.continuousOn _
  have hg : ∀ x ∈ spectrum ℝ P, 0 < g x := by
    intro x hx
    rw [hP.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    by_cases h0 : hP.1.eigenvalues i = 0
    · simp [g, h0, ht]
    · simpa [g, h0] using lt_of_le_of_ne (hP.eigenvalues_nonneg i) (Ne.symm h0)
  have hgle (i : n) : g (hP.1.eigenvalues i) ≤ hP.1.eigenvalues i + t := by
    by_cases h0 : hP.1.eigenvalues i = 0 <;> simp [g, h0, ht.le]
  refine ⟨cfc g P, ?_, ?_, ∑ i, g (hP.1.eigenvalues i), by simp [hP.1.trace_cfc], ?_, ?_⟩
  · open scoped MatrixOrder in
    exact isStrictlyPositive_iff_posDef.1
      ((cfc_isStrictlyPositive_iff g P hgc hP.1.isSelfAdjoint).2 hg)
  · -- `x * log (g x) = x * log x` for every `x`, since `g` only changes the value at `0`.
    rw [← cfc_comp' Real.log g P ((P.finite_real_spectrum.image g).continuousOn _) hgc
      hP.1.isSelfAdjoint, hP.1.mul_cfc, hP.1.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log,
      hP.1.mul_cfc, neg_neg]
    congr 3
    funext x
    by_cases hx : x = 0 <;> simp [g, hx]
  · exact Finset.sum_nonneg fun i _ ↦ (hg _ (hP.1.eigenvalues_mem_spectrum_real i)).le
  · calc ∑ i, g (hP.1.eigenvalues i) ≤ ∑ i, (hP.1.eigenvalues i + t) :=
          Finset.sum_le_sum fun i _ ↦ hgle i
      _ = RCLike.re P.trace + t * Fintype.card n := by
        simp [Finset.sum_add_distrib, hP.1.trace_eq_sum_eigenvalues, mul_comm]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Subadditivity of the von Neumann entropy.** For a density matrix `ρ` of a bipartite system,
indexed by `m × n`, the entropy is at most the sum of the entropies of its reduced density
matrices: `S(ρ) ≤ S(Tr₂ ρ) + S(Tr₁ ρ)`. -/
theorem PosSemidef.vonNeumannEntropy_le_partialTraceRight_add_partialTraceLeft
    {ρ : Matrix (m × n) (m × n) 𝕜} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ρ.vonNeumannEntropy ≤
      ρ.partialTraceRight.vonNeumannEntropy + ρ.partialTraceLeft.vonNeumannEntropy := by
  set SA := ρ.partialTraceRight.vonNeumannEntropy
  set SB := ρ.partialTraceLeft.vonNeumannEntropy
  set a : ℝ := (Fintype.card m : ℝ)
  set b : ℝ := (Fintype.card n : ℝ)
  -- Klein's inequality against the regularized product state `σ_A ⊗ₖ σ_B` at level `t`.
  have key (t : ℝ) (ht : 0 < t) :
      ρ.vonNeumannEntropy ≤ SA + SB + ((1 + t * a) * (1 + t * b) - 1) := by
    obtain ⟨σA, hσA, hlogA, rA, htrA, -, hrA⟩ :=
      hρ.partialTraceRight.exists_posDef_regularization ht
    obtain ⟨σB, hσB, hlogB, rB, htrB, hrB0, hrB⟩ :=
      hρ.partialTraceLeft.exists_posDef_regularization ht
    have hσ := hσA.kronecker hσB
    have hker : LinearMap.ker (σA ⊗ₖ σB).mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
      rw [LinearMap.ker_eq_bot.mpr (by exact hσ.mulVec_injective)]
      exact bot_le
    -- The partial traces split `Tr (ρ log (σ_A ⊗ₖ σ_B))` into the two reduced terms.
    have hlog : RCLike.re (ρ * cfc Real.log (σA ⊗ₖ σB)).trace = -SA - SB := by
      rw [hσA.cfc_log_kronecker hσB, mul_add, trace_add, map_add,
        ← trace_partialTraceRight (ρ * _), partialTraceRight_mul_kronecker_one,
        ← trace_partialTraceLeft (ρ * _), partialTraceLeft_mul_one_kronecker, hlogA, hlogB]
      ring
    have htrace : RCLike.re (ρ.trace - (σA ⊗ₖ σB).trace) = 1 - rA * rB := by
      simp [trace_kronecker, htrA, htrB, htr]
    have hklein := hρ.re_trace_sub_trace_le_relativeEntropy hσ.posSemidef
    rw [hρ.1.relativeEntropy_eq_neg_vonNeumannEntropy_sub hker, EReal.coe_le_coe_iff, hlog,
      htrace] at hklein
    simp only [trace_partialTraceRight, trace_partialTraceLeft, htr, RCLike.one_re] at hrA hrB
    have hprod : rA * rB ≤ (1 + t * a) * (1 + t * b) :=
      mul_le_mul (by linarith) (by linarith) hrB0 (by positivity)
    linarith
  -- The error term `(1 + t a)(1 + t b) - 1` vanishes as `t → 0⁺`.
  have hlim : Tendsto (fun t : ℝ ↦ SA + SB + ((1 + t * a) * (1 + t * b) - 1)) (𝓝[>] 0)
      (𝓝 (SA + SB)) := by
    have : Continuous fun t : ℝ ↦ SA + SB + ((1 + t * a) * (1 + t * b) - 1) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

end Matrix
