/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.Exponential.Derivative
public import TauCeti.Analysis.Matrix.Exponential.Log
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.Analysis.Matrix.StrongSubadditivity
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Trace inequalities for the matrix exponential: Lieb's concavity and Golden–Thompson

Deterministic trace and operator-order inequalities for the matrix exponential of Hermitian
matrices over any `RCLike` scalar field (`ℝ` or `ℂ`):

* Order and norm bounds: `1 + A ≤ exp A`, `exp (-M) • 1 ≤ exp A ≤ exp M • 1`, `‖exp A‖ ≤ exp M`.
* Loewner monotonicity of `Re Tr (exp ·)` via sorted eigenvalue monotonicity.
* **Lieb's concavity theorem** (Lieb 1973; Tropp 2012, Theorem 3.2): `A ↦ Re Tr (exp (H + log A))`
  is concave on the positive definite cone, via Klein's inequality and joint convexity of the
  Umegaki relative entropy.
* **Trace of the exponential derivative**: `Tr (expFDeriv A Y) = Tr (exp A * Y)`.
* **The Golden–Thompson inequality** (Golden 1965; Thompson 1965):
  `Re Tr (exp (A + B)) ≤ Re Tr (exp A * exp B)`, deduced by differentiating the concave path
  `t ↦ Re Tr (exp (A + log ((1 - t) • 1 + t • exp B)))` at `t = 0`.

## Main results

* `Matrix.IsHermitian.one_add_le_exp`, `Matrix.IsHermitian.smul_one_le_exp_and_le_smul_one`,
  `Matrix.IsHermitian.l2_opNorm_exp_le`: Loewner and operator-norm bounds for `exp A`.
* `Matrix.IsHermitian.re_trace_exp_le_of_le`: Loewner monotonicity of `Re Tr (exp ·)`.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`: Lieb's concavity theorem.
* `Matrix.IsHermitian.trace_expFDeriv`: `Tr (expFDeriv A Y) = Tr (exp A * Y)`.
* `Matrix.IsHermitian.re_trace_exp_add_le_re_trace_exp_mul_exp`: the Golden–Thompson inequality.

## References

* S. Golden, *Lower bounds for the Helmholtz function*, Phys. Rev. **137** (1965), B1127–B1128.
* C. J. Thompson, *Inequality with applications in statistical mechanics*, J. Math. Phys. **6**
  (1965), 1812–1813.
* E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*, Adv. Math. **11**
  (1973), 267–288.
* E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemporary
  Mathematics 529 (2010), Section 7.
* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math.
  **12** (2012), 389–434, Section 3.
-/

public section

noncomputable section

open Filter NormedSpace Topology
open scoped ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Pointwise

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-! ### Order, norm, and monotonicity bounds for the matrix exponential -/

/-- For a Hermitian matrix `A`, `1 + A ≤ exp A` in the Loewner order. -/
theorem IsHermitian.one_add_le_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    1 + A ≤ exp A := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  have h1A : 1 + A = cfc (fun x : ℝ ↦ 1 + x) A := by
    rw [cfc_add A (fun _ ↦ 1) (fun x ↦ x) (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _), cfc_const_one ℝ A hA.isSelfAdjoint,
      cfc_id' ℝ A hA.isSelfAdjoint]
  exact h1A ▸ cfc_mono fun x _ ↦ by linarith [Real.add_one_le_exp x]

/-- For a Hermitian matrix with `‖A‖ ≤ M`, `exp (-M) • 1 ≤ exp A ≤ exp M • 1` in the Loewner
order. -/
theorem IsHermitian.smul_one_le_exp_and_le_smul_one {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {M : ℝ} (hbdd : ‖A‖ ≤ M) :
    Real.exp (-M) • (1 : Matrix n n 𝕜) ≤ exp A ∧
      exp A ≤ Real.exp M • (1 : Matrix n n 𝕜) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hspec (x : ℝ) (hx : x ∈ spectrum ℝ A) : -M ≤ x ∧ x ≤ M := by
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have h := norm_le_pi_norm hA.eigenvalues i
    rw [Real.norm_eq_abs, ← hA.l2_opNorm_eq_norm_eigenvalues] at h
    exact abs_le.1 (h.trans hbdd)
  have hconst (r : ℝ) : r • (1 : Matrix n n 𝕜) = cfc (fun _ : ℝ ↦ r) A := by
    rw [← Algebra.algebraMap_eq_smul_one, cfc_const r A hA.isSelfAdjoint]
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hconst, hconst]
  exact ⟨cfc_mono fun x hx ↦ Real.exp_le_exp.2 (hspec x hx).1,
    cfc_mono fun x hx ↦ Real.exp_le_exp.2 (hspec x hx).2⟩

/-- For a Hermitian matrix with `‖A‖ ≤ M`, `‖exp A‖ ≤ exp M`. -/
theorem IsHermitian.l2_opNorm_exp_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {M : ℝ} (hbdd : ‖A‖ ≤ M) :
    ‖exp A‖ ≤ Real.exp M :=
  hA.posDef_exp.posSemidef.l2_opNorm_le_of_le_smul_one (Real.exp_pos M).le
    (hA.smul_one_le_exp_and_le_smul_one hbdd).2

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

/-- **Loewner monotonicity of `Re Tr exp`.** If `A ≤ B` for Hermitian matrices `A` and `B`, then
`Re Tr (exp A) ≤ Re Tr (exp B)`. -/
theorem IsHermitian.re_trace_exp_le_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hle : A ≤ B) :
    RCLike.re (exp A).trace ≤ RCLike.re (exp B).trace := by
  rw [hA.re_trace_exp_eq_sum_exp, hB.re_trace_exp_eq_sum_exp]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [← e.sum_comp, ← e.sum_comp]
  exact Finset.sum_le_sum fun k _ ↦ Real.exp_le_exp.2 <| by
    simpa [IsHermitian.eigenvalues, e] using hA.eigenvalues₀_mono hB hle k

/-- Each exponential eigenvalue `exp (λₖ(A))` of a Hermitian matrix is bounded above by
`Re Tr (exp A)`. -/
theorem IsHermitian.exp_eigenvalues₀_le_re_trace_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    Real.exp (hA.eigenvalues₀ k) ≤ RCLike.re (exp A).trace := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [hA.re_trace_exp_eq_sum_exp]
  have hk : hA.eigenvalues (e k) = hA.eigenvalues₀ k := by simp [IsHermitian.eigenvalues, e]
  exact hk ▸ Finset.single_le_sum (fun _ _ ↦ (Real.exp_pos _).le) (Finset.mem_univ (e k))

/-- On a nonempty index type, `exp (λ_max(A)) ≤ Re Tr (exp A)` for every Hermitian matrix `A`. -/
theorem IsHermitian.exp_sSup_spectrum_real_le_re_trace_exp [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    Real.exp (sSup (spectrum ℝ A)) ≤ RCLike.re (exp A).trace := by
  rw [hA.sSup_spectrum_real_eq_eigenvalues₀_zero]
  exact hA.exp_eigenvalues₀_le_re_trace_exp ⟨0, Fintype.card_pos⟩

/-- If `A ≤ c • 1` for a Hermitian matrix `A`, then `Re Tr (exp A) ≤ card n * exp c`. -/
theorem IsHermitian.re_trace_exp_le_card_mul_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ}
    (hle : A ≤ c • (1 : Matrix n n 𝕜)) :
    RCLike.re (exp A).trace ≤ (Fintype.card n : ℝ) * Real.exp c := by
  refine (hA.re_trace_exp_le_of_le (isHermitian_one.smul (IsSelfAdjoint.all c)) hle).trans_eq ?_
  have hexp : NormedSpace.exp (c • (1 : Matrix n n 𝕜)) = Real.exp c • (1 : Matrix n n 𝕜) := by
    let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ]
  rw [hexp, trace_smul, trace_one, RCLike.smul_re, RCLike.natCast_re, mul_comm]

/-! ### Lieb's concavity theorem -/

/-- **Lieb's concavity theorem** (Lieb 1973; Tropp 2012, Theorem 3.2). For a fixed Hermitian
matrix `H` over any `RCLike` field, the functional `A ↦ Re Tr (exp (H + log A))` is concave on the
positive definite cone. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      (fun A ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace) := by
  refine ⟨TauCeti.convex_setOfPred_posDef, fun A₁ hA₁ A₂ hA₂ a b ha hb hab ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hA₁ hA₂
  rcases ha.eq_or_lt with rfl | ha
  · obtain rfl : b = 1 := by simpa using hab
    simp
  rcases hb.eq_or_lt with rfl | hb
  · obtain rfl : a = 1 := by simpa using hab
    simp
  set A := a • A₁ + b • A₂
  have hA : A.PosDef := (hA₁.smul ha).add (hA₂.smul hb)
  have hherm (X : Matrix n n 𝕜) : (H + cfc Real.log X).IsHermitian :=
    hH.add (cfc_predicate Real.log X).isHermitian
  set σ₁ := NormedSpace.exp (H + cfc Real.log A₁)
  set σ₂ := NormedSpace.exp (H + cfc Real.log A₂)
  set ρ := a • σ₁ + b • σ₂
  set σ := NormedSpace.exp (H + cfc Real.log A)
  have hσ₁ : σ₁.PosDef := (hherm A₁).posDef_exp
  have hσ₂ : σ₂.PosDef := (hherm A₂).posDef_exp
  have hρ : ρ.PosDef := (hσ₁.smul ha).add (hσ₂.smul hb)
  have hσ : σ.PosDef := (hherm A).posDef_exp
  -- Klein's inequality for `ρ` and `σ`, rewritten via `log σ = H + log A`.
  have hklein := hρ.posSemidef.re_trace_sub_trace_le_relativeEntropy hσ.posSemidef
  rw [relativeEntropy_of_posDef hσ, EReal.coe_le_coe_iff, map_sub, (hherm A).cfc_log_exp] at hklein
  -- Joint convexity of relative entropy for `(a σ₁ + b σ₂, a A₁ + b A₂)`.
  have hjoint := hσ₁.relativeEntropy_smul_add_smul_le hσ₂ hA₁ hA₂ ha.le hb.le
  rw [relativeEntropy_of_posDef hA, relativeEntropy_of_posDef hA₁, relativeEntropy_of_posDef hA₂,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
    (hherm A₁).cfc_log_exp, (hherm A₂).cfc_log_exp, add_sub_cancel_right,
    add_sub_cancel_right] at hjoint
  have hsplit : RCLike.re (ρ * (cfc Real.log ρ - (H + cfc Real.log A))).trace =
      RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log A)).trace - RCLike.re (ρ * H).trace := by
    rw [show ρ * (cfc Real.log ρ - (H + cfc Real.log A)) =
        ρ * (cfc Real.log ρ - cfc Real.log A) - ρ * H by rw [← mul_sub]; congr 1; abel,
      trace_sub, map_sub]
  simp only [ρ, add_mul, smul_mul_assoc, trace_add, trace_smul, map_add, RCLike.smul_re,
    smul_eq_mul] at hklein hjoint hsplit ⊢
  linarith

/-! ### Trace of the exponential derivative and the Golden–Thompson inequality -/

/-- **Trace of the exponential derivative.** For a Hermitian matrix `A` and any matrix `Y`,
`Tr (expFDeriv A Y) = Tr (exp A * Y)`. -/
theorem IsHermitian.trace_expFDeriv {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Y : Matrix n n 𝕜) :
    (TauCeti.expFDeriv 𝕜 A Y).trace = (NormedSpace.exp A * Y).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let e := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) (star hA.eigenvectorUnitary)
  have htr (Z : Matrix n n 𝕜) : (e Z).trace = Z.trace := by
    simp [e, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  rw [← htr (TauCeti.expFDeriv 𝕜 A Y), ← htr (NormedSpace.exp A * Y),
    hA.expFDeriv_eigenbasis Y, map_mul]
  let f : Matrix n n 𝕜 →A[𝕜] Matrix n n 𝕜 :=
    { e.toAlgEquiv.toAlgHom with
      cont := e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous }
  have heA : e (NormedSpace.exp A) = diagonal (fun i ↦ (Real.exp (hA.eigenvalues i) : 𝕜)) := by
    have hmap : e (NormedSpace.exp A) = NormedSpace.exp (e A) := map_exp f f.continuous A
    rw [hmap, hA.conjStarAlgAut_star_eigenvectorUnitary, exp_diagonal]
    exact congrArg diagonal (funext fun i ↦ by simp [RCLike.exp_ofReal])
  rw [heA]
  simp only [trace, diag_apply, of_apply, diagonal_mul, dslope_same, Real.deriv_exp]
  rfl

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
  have hconc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 - t) * f 0 + t * f 1 ≤ f t := fun t ht ↦ by
    simpa only [f, h, sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add,
      smul_eq_mul] using hA.concaveOn_re_trace_exp_add_cfc_log.2 (PosDef.one (n := n) (R := 𝕜))
        hB.posDef_exp (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
  -- Right derivative at `0` of `t ↦ log ((1 - t) • 1 + t • exp B)` is `exp B - 1`, by chain rule
  -- on `exp (log (h t)) = h t`.
  have hh_d := ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).smul_const
    (1 : Matrix n n 𝕜)).add ((hasDerivAt_id 0).smul_const (NormedSpace.exp B))).hasDerivWithinAt
    (s := Set.Icc 0 1)
  have hh_d' : HasDerivWithinAt (F := Matrix n n 𝕜) h (NormedSpace.exp B - 1) (Set.Icc 0 1) 0 := by
    convert hh_d using 1
    · ext t; rfl
    · simp [sub_eq_add_neg, add_comm]
  have hlog_fd := ((contDiffOn_cfc_log (𝕜 := 𝕜) (n := n) (k := 1)).differentiableOn
    one_ne_zero 1 PosDef.one).hasFDerivWithinAt.restrictScalars ℝ
  have hh0 : h 0 = 1 := by simp [h]
  have hlog_d := (hh0 ▸ hlog_fd).comp_hasDerivWithinAt 0 hh_d' fun _ ht ↦ hh_pos ht
  have hlog0 : cfc Real.log (h 0) = 0 := by simp [h, cfc_apply_one]
  have hexp0 := (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) (0 : Matrix n n 𝕜)).restrictScalars ℝ
  have hexp_d := (hlog0 ▸ hexp0).comp_hasDerivWithinAt 0 hlog_d
  have hL_val : (fderivWithin 𝕜 (cfc Real.log) {P : Matrix n n 𝕜 | P.PosDef} (h 0))
      (NormedSpace.exp B - 1) = NormedSpace.exp B - 1 := by
    have h1 := hexp_d.congr (fun t ht ↦ (hh_pos ht).exp_cfc_log.symm)
      (hh_pos ⟨le_rfl, zero_le_one⟩).exp_cfc_log.symm
    have hu := uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩
    have huniq := (h1.derivWithin hu).symm.trans (hh_d'.derivWithin hu)
    simpa [hlog0, TauCeti.expFDeriv_zero] using huniq
  -- Compute the right derivative `f'(0) = Re Tr (exp A * (exp B - 1))`.
  let trRe : Matrix n n 𝕜 →L[ℝ] ℝ :=
    RCLike.reCLM.comp ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap
  have hA0 : A + cfc Real.log (h 0) = A := by simp [h, cfc_apply_one]
  have hexpA := (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) A).restrictScalars ℝ
  have hf_d : HasDerivWithinAt f
      (RCLike.re (TauCeti.expFDeriv 𝕜 A (NormedSpace.exp B - 1)).trace) (Set.Icc 0 1) 0 := by
    have hd := (trRe.hasFDerivAt.comp (A + cfc Real.log (h 0))
      (hA0 ▸ hexpA)).comp_hasDerivWithinAt 0 (hlog_d.const_add A)
    simpa only [f, trRe, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_restrictScalars, traceLinearMap_apply, RCLike.reCLM_apply, hA0,
      hL_val] using hd
  -- Pass to the limit `t → 0⁺` in the secant inequality `f 1 - f 0 ≤ (f t - f 0) / t`.
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ * (f t - f 0)) (𝓝[>] 0)
      (𝓝 (RCLike.re (TauCeti.expFDeriv 𝕜 A (NormedSpace.exp B - 1)).trace)) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc 0 1 \ {0}] 0 :=
      nhdsWithin_le_iff.2 (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun _ ht ↦
        ⟨⟨ht.1.le, ht.2.le⟩, ht.1.ne'⟩)
    have hs : Tendsto (fun t ↦ slope f 0 t) (𝓝[>] 0) _ :=
      (hasDerivWithinAt_iff_tendsto_slope.1 hf_d).mono_left hle
    simpa only [slope_def_field, sub_zero, div_eq_inv_mul] using hs
  have hsec : ∀ᶠ t : ℝ in 𝓝[>] 0, f 1 - f 0 ≤ t⁻¹ * (f t - f 0) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    rw [le_inv_mul_iff₀ ht.1]
    linarith [hconc t ht]
  have hbound := ge_of_tendsto hslope hsec
  rw [hA.trace_expFDeriv, mul_sub, mul_one, trace_sub, map_sub] at hbound
  have hf0 : f 0 = RCLike.re (NormedSpace.exp A).trace := by simp [f, h, cfc_apply_one]
  have hf1 : f 1 = RCLike.re (NormedSpace.exp (A + B)).trace := by simp [f, h, hB.cfc_log_exp]
  linarith

end Matrix
