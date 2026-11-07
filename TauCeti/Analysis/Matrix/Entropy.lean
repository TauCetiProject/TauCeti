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
import TauCeti.LinearAlgebra.Matrix.PosSemidef

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

If `0 ≤ A ≤ B`, that is `A` and `B - A` are positive semidefinite, then
`Tr (A log A) ≤ Tr (A log B)`, or equivalently `D(A ‖ B) ≤ 0`; this trace inequality is a
consequence of the operator monotonicity of the logarithm. It bounds the entropy of a sum:
`S(A + B) ≤ S(A) + S(B)` for positive semidefinite `A` and `B`, and hence the upper mixture bound
`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) - ∑ᵢ pᵢ log pᵢ` for density matrices `ρᵢ` and a probability vector `p`.
The matching lower bound is the **concavity** of the entropy: `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`.
Together these mixture bounds control the entropy of a mixture by the entropies of its components
up to the Shannon entropy of the weights, as needed for the affinity of the mean entropy of quantum
spin systems.

## Main results

* `Matrix.PosSemidef.re_trace_sub_trace_le_relativeEntropy` — Klein's inequality: for positive
  semidefinite `ρ` and `σ`, `Tr ρ - Tr σ ≤ D(ρ ‖ σ)`;
* `Matrix.PosSemidef.relativeEntropy_nonneg` — positivity of the relative entropy of two positive
  semidefinite matrices of equal trace, in particular of two density matrices;
* `Matrix.PosSemidef.vonNeumannEntropy_nonneg` and
  `Matrix.PosSemidef.vonNeumannEntropy_le_log_card` — `0 ≤ S(ρ) ≤ log (card n)` for a density
  matrix `ρ`;
* `Matrix.PosSemidef.vonNeumannEntropy_le_partialTraceRight_add_partialTraceLeft` —
  subadditivity, `S(ρ) ≤ S(Tr₂ ρ) + S(Tr₁ ρ)` for a density matrix `ρ` of a bipartite system;
* `Matrix.PosSemidef.re_trace_mul_cfc_log_le` and `Matrix.PosSemidef.relativeEntropy_nonpos` —
  if `0 ≤ A ≤ B`, then `Tr (A log A) ≤ Tr (A log B)` and `D(A ‖ B) ≤ 0`;
* `Matrix.concaveOn_vonNeumannEntropy` and `Matrix.sum_mul_vonNeumannEntropy_le` — concavity,
  `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`;
* `Matrix.vonNeumannEntropy_sum_smul_le` — the upper mixture bound
  `S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ (pᵢ S(ρᵢ) - pᵢ log pᵢ · Tr ρᵢ)`.

## References

* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Section 11.3 (von Neumann entropy, quantum relative entropy, Klein's
  inequality, subadditivity, concavity and the upper mixture bound).
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

/-! ### The relative entropy below the reference in the Loewner order -/

/-- **A trace inequality for the logarithm.** If `A` and `B - A` are positive semidefinite, that is
`0 ≤ A ≤ B`, then `Tr (A log A) ≤ Tr (A log B)`. The matrix `A` may be
singular; the convention `0 log 0 = 0` applies. -/
theorem PosSemidef.re_trace_mul_cfc_log_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hBA : (B - A).PosSemidef) :
    RCLike.re (A * cfc Real.log A).trace ≤ RCLike.re (A * cfc Real.log B).trace := by
  have hB : B.PosSemidef := by simpa using hA.add hBA
  have hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := fun x hx ↦
    hA.mulVec_eq_zero_of_posSemidef_sub hBA hx
  have hAB : A * cfc Real.log B = cfc (fun x : ℝ ↦ x) A * cfc Real.log B := by
    rw [cfc_id' ℝ A hA.1.isSelfAdjoint]
  -- Expand both traces in the eigenbases of `A` and `B`.
  rw [hAB, hA.1.mul_cfc, ← mul_one (cfc _ A), ← cfc_const_one ℝ B hB.1.isSelfAdjoint,
    IsHermitian.re_trace_cfc_mul_cfc hA.1 hB.1, IsHermitian.re_trace_cfc_mul_cfc hA.1 hB.1,
    ← sub_nonpos, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun i _ ↦ ?_
  set a := hA.1.eigenvalues i
  set w : n → ℝ := fun j ↦ ‖⟪hA.1.eigenvectorBasis i, hB.1.eigenvectorBasis j⟫_𝕜‖ ^ 2
  have hw : ∑ j, w j = 1 := by
    simp only [w]
    rw [OrthonormalBasis.sum_sq_norm_inner_left, hA.1.eigenvectorBasis.orthonormal.1 i, one_pow]
  obtain ha | ha := (hA.eigenvalues_nonneg i).eq_or_lt
  · simp [a, ← ha]
  rw [← Finset.sum_sub_distrib]
  -- Bound each term by `log x ≤ x - 1`; the bounds sum to `a (a ∑ⱼ bⱼ⁻¹ wⱼ - 1)`, which is
  -- nonpositive by the inverse bound `a ⟪u, B⁻¹ u⟫ ≤ 1` for the eigenvector `u` of `a`.
  calc ∑ j, (a * Real.log a * 1 * w j - a * Real.log (hB.1.eigenvalues j) * w j)
      ≤ ∑ j, a * (a * (hB.1.eigenvalues j)⁻¹ - 1) * w j := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        by_cases hij : ⟪hA.1.eigenvectorBasis i, hB.1.eigenvectorBasis j⟫_𝕜 = 0
        · simp [w, hij]
        have hb : 0 < hB.1.eigenvalues j := (hB.eigenvalues_nonneg j).lt_of_ne fun h ↦
          ha.ne' (hA.1.eigenvalues_eq_zero_of_inner_ne_zero hB.1 hker hij h.symm)
        have key := Real.log_le_sub_one_of_pos (div_pos ha hb)
        rw [Real.log_div ha.ne' hb.ne', div_eq_mul_inv] at key
        have hw0 : 0 ≤ w j := by positivity
        nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg ha.le hw0)]
    _ = a * (a * ∑ j, (hB.1.eigenvalues j)⁻¹ * w j - ∑ j, w j) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ ≤ 0 := by
        rw [hw]
        exact mul_nonpos_of_nonneg_of_nonpos ha.le
          (by linarith [hA.eigenvalues_mul_sum_inv_mul_le_one hBA hB.1 ha])

/-- **Nonpositivity of the relative entropy under Loewner domination.** If `A` and `B - A` are
positive semidefinite, that is `0 ≤ A ≤ B`, then `D(A ‖ B) ≤ 0`. The support condition holds
automatically, so the relative entropy is finite. -/
theorem PosSemidef.relativeEntropy_nonpos {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hBA : (B - A).PosSemidef) : relativeEntropy A B ≤ 0 := by
  rw [relativeEntropy_of_ker_le fun x hx ↦ hA.mulVec_eq_zero_of_posSemidef_sub hBA hx, mul_sub,
    trace_sub, map_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff, sub_nonpos]
  exact hA.re_trace_mul_cfc_log_le hBA

/-! ### Concavity and mixture bounds -/

/-- Scaling a Hermitian matrix by a real number `c` scales its entropy and adds `-c log c` times its
trace: `S(c ρ) = c S(ρ) - c log c · Tr ρ`. -/
theorem IsHermitian.vonNeumannEntropy_smul (hρ : ρ.IsHermitian) (c : ℝ) :
    (c • ρ).vonNeumannEntropy =
      c * ρ.vonNeumannEntropy + Real.negMulLog c * RCLike.re ρ.trace := by
  rw [vonNeumannEntropy_def, ← cfc_comp_smul c Real.negMulLog ρ
    Real.continuous_negMulLog.continuousOn hρ.isSelfAdjoint, hρ.trace_cfc,
    hρ.vonNeumannEntropy_eq_sum_negMulLog, hρ.trace_eq_sum_eigenvalues]
  simp only [map_sum, RCLike.ofReal_re, smul_eq_mul, Real.negMulLog_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The von Neumann entropy is subadditive on positive semidefinite summands:
`S(A + B) ≤ S(A) + S(B)`. -/
theorem PosSemidef.vonNeumannEntropy_add_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    (A + B).vonNeumannEntropy ≤ A.vonNeumannEntropy + B.vonNeumannEntropy := by
  -- Both summands lie below the sum, so `D(A ‖ A + B) ≤ 0` and `D(B ‖ A + B) ≤ 0` in trace form.
  have hlA := hA.re_trace_mul_cfc_log_le (B := A + B) (by simpa using hB)
  have hlB := hB.re_trace_mul_cfc_log_le (B := A + B) (by simpa using hA)
  rw [hA.1.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log,
    hB.1.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log,
    (hA.1.add hB.1).vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log, add_mul, trace_add, map_add]
  linarith

/-- The entropy of a finite sum of positive semidefinite matrices is at most the sum of their
entropies. -/
theorem vonNeumannEntropy_sum_le {ι : Type*} (s : Finset ι) {ρ : ι → Matrix n n 𝕜}
    (hρ : ∀ i ∈ s, (ρ i).PosSemidef) :
    (∑ i ∈ s, ρ i).vonNeumannEntropy ≤ ∑ i ∈ s, (ρ i).vonNeumannEntropy := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs := posSemidef_sum s fun j hj ↦ hρ j (Finset.mem_insert_of_mem hj)
    refine ((hρ i (Finset.mem_insert_self i s)).vonNeumannEntropy_add_le hs).trans ?_
    gcongr
    exact ih fun j hj ↦ hρ j (Finset.mem_insert_of_mem hj)

/-- **Upper mixture bound for the entropy.** For positive semidefinite `ρᵢ` and weights `pᵢ ≥ 0`,
`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ (pᵢ S(ρᵢ) - pᵢ log pᵢ · Tr ρᵢ)`. For density matrices and a probability vector
`p` the error term is the Shannon entropy `-∑ᵢ pᵢ log pᵢ` of `p`. -/
theorem vonNeumannEntropy_sum_smul_le {ι : Type*} (s : Finset ι) {p : ι → ℝ}
    {ρ : ι → Matrix n n 𝕜} (hp : ∀ i ∈ s, 0 ≤ p i) (hρ : ∀ i ∈ s, (ρ i).PosSemidef) :
    (∑ i ∈ s, p i • ρ i).vonNeumannEntropy ≤
      ∑ i ∈ s, (p i * (ρ i).vonNeumannEntropy + Real.negMulLog (p i) * RCLike.re (ρ i).trace) :=
  (vonNeumannEntropy_sum_le s fun i hi ↦ (hρ i hi).smul (hp i hi)).trans_eq <|
    Finset.sum_congr rfl fun i hi ↦ (hρ i hi).1.vonNeumannEntropy_smul (p i)

/-- **Concavity of the von Neumann entropy** on the positive semidefinite matrices: for positive
semidefinite `x` and `y` and weights `a, b ≥ 0` with `a + b = 1`,
`a S(x) + b S(y) ≤ S(a x + b y)`. -/
theorem concaveOn_vonNeumannEntropy :
    ConcaveOn ℝ {ρ : Matrix n n 𝕜 | ρ.PosSemidef} vonNeumannEntropy := by
  refine ⟨fun x hx y hy a b ha hb _ ↦ (hx.smul ha).add (hy.smul hb), ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy
  obtain rfl | ha := ha.eq_or_lt
  · obtain rfl : b = 1 := by simpa using hab
    simp
  obtain rfl | hb := hb.eq_or_lt
  · obtain rfl : a = 1 := by simpa using hab
    simp
  set ρ := a • x + b • y
  have hρ : ρ.PosSemidef := (hx.smul ha.le).add (hy.smul hb.le)
  -- Klein's inequality for a summand `z` of the mixture, relative to the mixture `ρ`.
  have klein {z : Matrix n n 𝕜} (hz : z.PosSemidef) {c : ℝ} (hc : 0 < c)
      (hρz : (ρ - c • z).PosSemidef) :
      RCLike.re z.trace - RCLike.re ρ.trace ≤
        -z.vonNeumannEntropy - RCLike.re (z * cfc Real.log ρ).trace := by
    have hker : LinearMap.ker ρ.mulVecLin ≤ LinearMap.ker z.mulVecLin := fun v hv ↦ by
      have h := (hz.smul hc.le).mulVec_eq_zero_of_posSemidef_sub hρz hv
      rw [smul_mulVec, smul_eq_zero] at h
      exact h.resolve_left hc.ne'
    have h := hz.re_trace_sub_trace_le_relativeEntropy hρ
    rwa [hz.1.relativeEntropy_eq_neg_vonNeumannEntropy_sub hker, EReal.coe_le_coe_iff,
      map_sub] at h
  -- The weighted sum of the two Klein inequalities is `0 ≤ S(ρ) - a S(x) - b S(y)`.
  have hkx := klein hx ha (by simpa [ρ] using hy.smul hb.le)
  have hky := klein hy hb (by simpa [ρ] using hx.smul ha.le)
  have hS := hρ.1.vonNeumannEntropy_eq_neg_re_trace_mul_cfc_log
  have htr : RCLike.re ρ.trace = a * RCLike.re x.trace + b * RCLike.re y.trace := by
    simp [ρ, trace_add, trace_smul, RCLike.smul_re]
  have hlog : RCLike.re (ρ * cfc Real.log ρ).trace =
      a * RCLike.re (x * cfc Real.log ρ).trace + b * RCLike.re (y * cfc Real.log ρ).trace := by
    simp only [ρ, add_mul, smul_mul_assoc, trace_add, trace_smul, map_add, RCLike.smul_re]
  have hab' := congrArg (· * RCLike.re ρ.trace) hab
  simp only [smul_eq_mul, add_mul, one_mul] at hab' ⊢
  nlinarith [mul_le_mul_of_nonneg_left hkx ha.le, mul_le_mul_of_nonneg_left hky hb.le]

/-- **Lower mixture bound for the entropy**, the finite form of its concavity: for positive
semidefinite `ρᵢ` and a probability vector `p`, `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`. -/
theorem sum_mul_vonNeumannEntropy_le {ι : Type*} (s : Finset ι) {p : ι → ℝ}
    {ρ : ι → Matrix n n 𝕜} (hp : ∀ i ∈ s, 0 ≤ p i) (hp₁ : ∑ i ∈ s, p i = 1)
    (hρ : ∀ i ∈ s, (ρ i).PosSemidef) :
    ∑ i ∈ s, p i * (ρ i).vonNeumannEntropy ≤ (∑ i ∈ s, p i • ρ i).vonNeumannEntropy :=
  concaveOn_vonNeumannEntropy.le_map_sum (t := s) (w := p) (p := ρ) hp hp₁ hρ

end Matrix
