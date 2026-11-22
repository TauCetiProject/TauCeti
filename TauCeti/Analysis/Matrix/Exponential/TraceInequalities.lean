/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.Analysis.Matrix.Exponential.Bounds
public import TauCeti.Analysis.Matrix.Exponential.Log
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.Matrix.StrongSubadditivity
import TauCeti.Analysis.Matrix.Trace.Basic
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Trace inequalities for the matrix exponential: Lieb's concavity and Golden–Thompson

Deterministic trace inequalities for the matrix exponential over any `RCLike` scalar field (`ℝ` or
`ℂ`): Loewner monotonicity of `Re Tr (exp ·)`, Lieb's concavity theorem via Klein's inequality and
joint convexity of the Umegaki relative entropy (following Tropp 2012, Proc. AMS), and the
Golden–Thompson inequality.

## Main results

* `Matrix.IsHermitian.re_trace_exp_le_of_le` and `TauCeti.re_trace_exp_le_card_mul_exp`: Loewner
  monotonicity of `Re Tr (exp ·)` and the scalar upper bound.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`: Lieb's concavity theorem.
* `Matrix.IsHermitian.re_trace_exp_add_le_re_trace_exp_mul_exp`: the Golden–Thompson inequality.

## References

* S. Golden, *Lower bounds for the Helmholtz function*, Phys. Rev. **137** (1965), B1127–B1128.
* C. J. Thompson, *Inequality with applications in statistical mechanics*, J. Math. Phys. **6**
  (1965), 1812–1813.
* E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*, Adv. Math. **11**
  (1973), 267–288.
* E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemporary
  Mathematics 529 (2010), Section 7.
* J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of Lieb*,
  Proc. Amer. Math. Soc. **140** (2012), 1757–1760.
* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math.
  **12** (2012), 389–434, Section 3.
-/

public section

noncomputable section

open Filter NormedSpace Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-! ### Trace and Loewner monotonicity of the matrix exponential -/

/-- The real part of the trace of `exp A` for a Hermitian matrix `A` is the sum of the exponentials
of its eigenvalues. -/
theorem IsHermitian.re_trace_exp_eq_sum_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (exp A).trace = ∑ i, Real.exp (hA.eigenvalues i) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hA.trace_cfc]
  simp

/-- For a Hermitian matrix `A`, `Re Tr (exp A)` is nonnegative. -/
theorem IsHermitian.re_trace_exp_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    0 ≤ RCLike.re (exp A).trace :=
  hA.re_trace_exp_eq_sum_exp ▸ Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le

/-- **Loewner monotonicity of `Re Tr exp`.** If `B` is Hermitian and `A ≤ B` in the Loewner order,
then `Re Tr (exp A) ≤ Re Tr (exp B)`. -/
theorem IsHermitian.re_trace_exp_le_of_le {A B : Matrix n n 𝕜} (hB : B.IsHermitian)
    (hle : A ≤ B) :
    RCLike.re (exp A).trace ≤ RCLike.re (exp B).trace := by
  have hA := TauCeti.isHermitian_of_le hB hle
  rw [hA.re_trace_exp_eq_sum_exp, hB.re_trace_exp_eq_sum_exp]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [← e.sum_comp, ← e.sum_comp]
  exact Finset.sum_le_sum fun k _ ↦ Real.exp_le_exp.2 <| by
    simpa only [e, hA.eigenvalues_apply_equivOfCardEq k, hB.eigenvalues_apply_equivOfCardEq k] using
      hA.eigenvalues₀_mono hB hle k

/-- Each exponential eigenvalue `exp (λₖ(A))` of a Hermitian matrix is bounded above by
`Re Tr (exp A)`. -/
theorem IsHermitian.exp_eigenvalues₀_le_re_trace_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    Real.exp (hA.eigenvalues₀ k) ≤ RCLike.re (exp A).trace := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [hA.re_trace_exp_eq_sum_exp, ← hA.eigenvalues_apply_equivOfCardEq k]
  exact Finset.single_le_sum (fun _ _ ↦ (Real.exp_pos _).le) (Finset.mem_univ (e k))

/-- On a nonempty index type, `exp (λ_max(A)) ≤ Re Tr (exp A)` for every Hermitian matrix `A`. -/
theorem IsHermitian.exp_sSup_spectrum_real_le_re_trace_exp [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    Real.exp (sSup (spectrum ℝ A)) ≤ RCLike.re (exp A).trace := by
  rw [hA.sSup_spectrum_real_eq_eigenvalues₀_zero]
  exact hA.exp_eigenvalues₀_le_re_trace_exp ⟨0, Fintype.card_pos⟩

end Matrix

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- If `A ≤ c • 1` in the Loewner order, then `Re Tr (exp A) ≤ card n * exp c`. -/
theorem re_trace_exp_le_card_mul_exp {A : Matrix n n 𝕜} {c : ℝ}
    (hle : A ≤ c • (1 : Matrix n n 𝕜)) :
    RCLike.re (NormedSpace.exp A).trace ≤ (Fintype.card n : ℝ) * Real.exp c := by
  refine ((Matrix.isHermitian_one.smul (IsSelfAdjoint.all c)).re_trace_exp_le_of_le hle).trans_eq ?_
  have hexp : NormedSpace.exp (c • (1 : Matrix n n 𝕜)) = Real.exp c • (1 : Matrix n n 𝕜) := by
    let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ]
  rw [hexp, Matrix.trace_smul, Matrix.trace_one, RCLike.smul_re, RCLike.natCast_re, mul_comm]

end TauCeti

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-! ### Lieb's concavity theorem -/

/-- **Lieb's concavity theorem** (Lieb 1973; Tropp 2012 FoCM, Theorem 3.2). For a fixed Hermitian
matrix `H` over any `RCLike` field, the functional `A ↦ Re Tr (exp (H + log A))` is concave on the
positive definite cone. The proof follows Tropp (Proc. Amer. Math. Soc. 140 (2012), 1757–1760),
combining Klein's inequality with joint convexity of the Umegaki relative entropy. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      (fun A ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace) := by
  refine ⟨TauCeti.convex_setOfPred_posDef, fun A₁ hA₁ A₂ hA₂ a b ha hb hab ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hA₁ hA₂
  rcases ha.eq_or_lt with rfl | ha
  · have hb1 : b = 1 := by simpa using hab
    subst hb1
    simp
  rcases hb.eq_or_lt with rfl | hb
  · have ha1 : a = 1 := by simpa using hab
    subst ha1
    simp
  set A := a • A₁ + b • A₂
  have hA : A.PosDef := (hA₁.smul ha).add (hA₂.smul hb)
  have hherm (X : Matrix n n 𝕜) : (H + cfc Real.log X).IsHermitian :=
    hH.add (cfc_predicate Real.log X).isHermitian
  set σ₁ := NormedSpace.exp (H + cfc Real.log A₁)
  set σ₂ := NormedSpace.exp (H + cfc Real.log A₂)
  set ρ := a • σ₁ + b • σ₂
  set σ := NormedSpace.exp (H + cfc Real.log A)
  have hρ : ρ.PosDef := ((hherm A₁).posDef_exp.smul ha).add ((hherm A₂).posDef_exp.smul hb)
  have hσ : σ.PosDef := (hherm A).posDef_exp
  -- Klein's inequality for `ρ` and `σ`, rewritten via `log σ = H + log A`.
  have hklein := hρ.posSemidef.re_trace_sub_trace_le_relativeEntropy hσ.posSemidef
  rw [relativeEntropy_of_posDef hσ, EReal.coe_le_coe_iff, map_sub, (hherm A).cfc_log_exp] at hklein
  -- Joint convexity of relative entropy for `(a σ₁ + b σ₂, a A₁ + b A₂)`.
  have hjoint := (hherm A₁).posDef_exp.relativeEntropy_smul_add_smul_le
    (hherm A₂).posDef_exp hA₁ hA₂ ha.le hb.le
  rw [relativeEntropy_of_posDef hA, relativeEntropy_of_posDef hA₁, relativeEntropy_of_posDef hA₂,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
    (hherm A₁).cfc_log_exp, (hherm A₂).cfc_log_exp, add_sub_cancel_right,
    add_sub_cancel_right] at hjoint
  have hmul : ρ * (cfc Real.log ρ - (H + cfc Real.log A)) =
      ρ * (cfc Real.log ρ - cfc Real.log A) - ρ * H := by
    rw [← mul_sub]
    congr 1
    abel
  have hsplit : RCLike.re (ρ * (cfc Real.log ρ - (H + cfc Real.log A))).trace =
      RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log A)).trace - RCLike.re (ρ * H).trace := by
    rw [hmul, trace_sub, map_sub]
  simp only [ρ, add_mul, smul_mul_assoc, trace_add, trace_smul, map_add, RCLike.smul_re,
    smul_eq_mul] at hklein hjoint hsplit ⊢
  linarith

/-! ### The Golden–Thompson inequality -/

/-- Along the affine path `t ↦ (1 - t) • 1 + t • P` on `[0, 1]` into the positive definite cone,
the matrix logarithm has right derivative `P - 1` at `0`. -/
private theorem hasDerivWithinAt_cfc_log_one_sub_smul_add_smul_zero {P : Matrix n n 𝕜}
    (hP : P.PosDef) :
    HasDerivWithinAt (fun t : ℝ ↦ cfc Real.log ((1 - t) • (1 : Matrix n n 𝕜) + t • P))
      (P - 1) (Set.Icc 0 1) 0 := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let h : ℝ → Matrix n n 𝕜 := fun t ↦ (1 - t) • (1 : Matrix n n 𝕜) + t • P
  have hh_pos {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (h t).PosDef :=
    PosDef.one.one_sub_smul_add_smul hP ht
  have hh_d' : HasDerivWithinAt (F := Matrix n n 𝕜) h (P - 1) (Set.Icc 0 1) 0 := by
    convert ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).smul_const
      (1 : Matrix n n 𝕜)).add ((hasDerivAt_id 0).smul_const P)).hasDerivWithinAt
      (s := Set.Icc 0 1) using 1
    · ext t; rfl
    · simp [sub_eq_add_neg, add_comm]
  have hh0 : h 0 = 1 := by simp [h]
  have hlog_d := (hh0 ▸ ((contDiffOn_cfc_log (𝕜 := 𝕜) (n := n) (k := 1)).differentiableOn
    one_ne_zero 1 PosDef.one).hasFDerivWithinAt.restrictScalars ℝ).comp_hasDerivWithinAt 0 hh_d'
    fun _ ht ↦ hh_pos ht
  have hlog0 : cfc Real.log (h 0) = 0 := by simp [h, cfc_apply_one]
  have hL_val : (fderivWithin 𝕜 (cfc Real.log) {Q : Matrix n n 𝕜 | Q.PosDef} (h 0)) (P - 1) =
      P - 1 := by
    have h1 := ((hlog0 ▸ (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) (0 : Matrix n n 𝕜)).restrictScalars
      ℝ).comp_hasDerivWithinAt 0 hlog_d).congr (fun t ht ↦ (hh_pos ht).exp_cfc_log.symm)
      (hh_pos ⟨le_rfl, zero_le_one⟩).exp_cfc_log.symm
    have hu := uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩
    simpa [hlog0, TauCeti.expFDeriv_zero] using
      (h1.derivWithin hu).symm.trans (hh_d'.derivWithin hu)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', hL_val] using hlog_d

/-- **The Golden–Thompson inequality** (Golden 1965; Thompson 1965). For Hermitian matrices `A` and
`B` over any `RCLike` field, `Re Tr (exp (A + B)) ≤ Re Tr (exp A * exp B)`. -/
theorem IsHermitian.re_trace_exp_add_le_re_trace_exp_mul_exp {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (NormedSpace.exp (A + B)).trace ≤
      RCLike.re (NormedSpace.exp A * NormedSpace.exp B).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let h : ℝ → Matrix n n 𝕜 := fun t ↦ (1 - t) • (1 : Matrix n n 𝕜) + t • NormedSpace.exp B
  let f : ℝ → ℝ := fun t ↦ RCLike.re (NormedSpace.exp (A + cfc Real.log (h t))).trace
  have hh_pos {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (h t).PosDef :=
    PosDef.one.one_sub_smul_add_smul hB.posDef_exp ht
  -- `f` is concave on `[0, 1]` by Lieb's concavity theorem.
  have hf_conc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f := by
    refine ⟨convex_Icc 0 1, fun s hs t ht a b ha hb hab ↦ ?_⟩
    have hcoeff : 1 - (a * s + b * t) = a * (1 - s) + b * (1 - t) := by linarith
    have haff : h (a * s + b * t) = a • h s + b • h t := by
      simp only [h, hcoeff, add_smul, smul_add, smul_smul]
      abel
    simpa only [f, smul_eq_mul, haff] using
      hA.concaveOn_re_trace_exp_add_cfc_log.2 (hh_pos hs) (hh_pos ht) ha hb hab
  -- Right derivative `f'(0) = Re Tr (exp A * (exp B - 1))`.
  have hlog_d := hasDerivWithinAt_cfc_log_one_sub_smul_add_smul_zero hB.posDef_exp
  have hA0 : A + cfc Real.log (h 0) = A := by simp [h, cfc_apply_one]
  have hf_d : HasDerivWithinAt f
      (RCLike.re (TauCeti.expFDeriv 𝕜 A (NormedSpace.exp B - 1)).trace) (Set.Icc 0 1) 0 := by
    have hexpA := (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) A).restrictScalars ℝ
    have hd := ((TauCeti.reTraceCLM n 𝕜).hasFDerivAt.comp (A + cfc Real.log (h 0))
      (hA0 ▸ hexpA)).comp_hasDerivWithinAt 0 (hlog_d.const_add A)
    simpa only [f, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', TauCeti.reTraceCLM_apply, hA0] using hd
  -- Apply convexity of `-f` on `[0, 1]` between `0` and `1`: `-f'(0) ≤ (-f 1 - (-f 0)) / (1 - 0)`.
  have hbound := hf_conc.neg.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hf_d.neg
  rw [slope_def_field, sub_zero, div_one, Pi.neg_apply, Pi.neg_apply, neg_sub_neg] at hbound
  rw [trace_expFDeriv, mul_sub, mul_one, trace_sub, map_sub] at hbound
  have hf0 : f 0 = RCLike.re (NormedSpace.exp A).trace := by simp [f, h, cfc_apply_one]
  have hf1 : f 1 = RCLike.re (NormedSpace.exp (A + B)).trace := by simp [f, h, hB.cfc_log_exp]
  linarith

end Matrix
