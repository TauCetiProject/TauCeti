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
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.Analysis.Matrix.StrongSubadditivity
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Trace inequalities for the matrix exponential: Lieb's concavity and Golden–Thompson

This file proves the deterministic trace and operator-order inequalities for the matrix exponential
of Hermitian matrices over any `RCLike` scalar field (`ℝ` or `ℂ`):

* **Order and norm bounds for `exp`**: `1 + A ≤ exp A` (`Matrix.IsHermitian.one_add_le_exp`),
  `exp (-M) • 1 ≤ exp A ≤ exp M • 1` (`Matrix.IsHermitian.smul_one_le_exp_and_le_smul_one`), and
  `‖exp A‖ ≤ exp M` (`Matrix.IsHermitian.l2_opNorm_exp_le`).
* **Loewner monotonicity of `Re Tr exp`**: if `A ≤ B` for Hermitian `A` and `B`, then
  `Re Tr (exp A) ≤ Re Tr (exp B)` (`Matrix.IsHermitian.re_trace_exp_le_of_le`), via Loewner
  monotonicity of the sorted eigenvalues (`Matrix.IsHermitian.eigenvalues₀_mono`).
* **Lieb's concavity theorem** (Lieb 1973; Tropp 2012, Theorem 3.2): for a fixed Hermitian
  matrix `H`, the functional `A ↦ Re Tr (exp (H + log A))` is concave on the positive definite
  cone (`Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`). We deduce this directly from
  Klein's inequality (`Matrix.PosSemidef.re_trace_sub_trace_le_relativeEntropy`) and the joint
  convexity of the Umegaki relative entropy
  (`Matrix.PosDef.relativeEntropy_smul_add_smul_le`).
* **Trace of the exponential derivative**: for Hermitian `A` and arbitrary `Y`,
  `Tr (expFDeriv A Y) = Tr (exp A * Y)` (`Matrix.IsHermitian.trace_expFDeriv`), computed in a
  unitary eigenbasis of `A`.
* **The Golden–Thompson inequality** (Golden 1965; Thompson 1965): for Hermitian `A` and `B`,
  `Re Tr (exp (A + B)) ≤ Re Tr (exp A * exp B)`
  (`Matrix.IsHermitian.re_trace_exp_add_le_re_trace_exp_mul_exp`), deduced by differentiating the
  concave path `t ↦ Re Tr (exp (A + log ((1 - t) • 1 + t • exp B)))` at `t = 0`.

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
  rw [h1A]
  exact cfc_mono fun x _ ↦ by linarith [Real.add_one_le_exp x]

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
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  constructor
  · have hlo : Real.exp (-M) • (1 : Matrix n n 𝕜) = cfc (fun _ : ℝ ↦ Real.exp (-M)) A := by
      rw [← Algebra.algebraMap_eq_smul_one, cfc_const (Real.exp (-M)) A hA.isSelfAdjoint]
    rw [hlo]
    exact cfc_mono fun x hx ↦ Real.exp_le_exp.2 (hspec x hx).1
  · have hhi : Real.exp M • (1 : Matrix n n 𝕜) = cfc (fun _ : ℝ ↦ Real.exp M) A := by
      rw [← Algebra.algebraMap_eq_smul_one, cfc_const (Real.exp M) A hA.isSelfAdjoint]
    rw [hhi]
    exact cfc_mono fun x hx ↦ Real.exp_le_exp.2 (hspec x hx).2

/-- For a Hermitian matrix with `‖A‖ ≤ M`, `‖exp A‖ ≤ exp M`. -/
theorem IsHermitian.l2_opNorm_exp_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {M : ℝ} (hbdd : ‖A‖ ≤ M) :
    ‖exp A‖ ≤ Real.exp M := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hpos := hA.posDef_exp
  rw [← cfc_id' ℝ (NormedSpace.exp A) hpos.1.isSelfAdjoint]
  refine norm_cfc_le (Real.exp_pos M).le fun t ht ↦ ?_
  have h1 := (StarOrderedRing.nonneg_iff_spectrum_nonneg _ hpos.1.isSelfAdjoint).1
    hpos.posSemidef.nonneg t ht
  have h2 := (le_algebraMap_iff_spectrum_le (ha := hpos.1.isSelfAdjoint)).1
    (by simpa [Algebra.algebraMap_eq_smul_one] using (hA.smul_one_le_exp_and_le_smul_one hbdd).2)
    t ht
  rwa [Real.norm_eq_abs, abs_of_nonneg h1]

/-- The real part of the trace of `exp A` for a Hermitian matrix `A` is the sum of the exponentials
of its eigenvalues. -/
theorem IsHermitian.re_trace_exp_eq_sum_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (exp A).trace = ∑ i, Real.exp (hA.eigenvalues i) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hA.trace_cfc]
  simp

/-- For a Hermitian matrix `A`, `Re Tr (exp A)` is nonnegative. -/
theorem IsHermitian.re_trace_exp_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    0 ≤ RCLike.re (exp A).trace := by
  rw [hA.re_trace_exp_eq_sum_exp]
  exact Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le

/-- **Loewner monotonicity of `Re Tr exp`.** If `A ≤ B` for Hermitian matrices `A` and `B`, then
`Re Tr (exp A) ≤ Re Tr (exp B)`. -/
theorem IsHermitian.re_trace_exp_le_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hle : A ≤ B) :
    RCLike.re (exp A).trace ≤ RCLike.re (exp B).trace := by
  rw [hA.re_trace_exp_eq_sum_exp, hB.re_trace_exp_eq_sum_exp]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [← e.sum_comp, ← e.sum_comp]
  refine Finset.sum_le_sum fun k _ ↦ Real.exp_le_exp.2 ?_
  simpa [IsHermitian.eigenvalues, e] using hA.eigenvalues₀_mono hB hle k

/-- Each exponential eigenvalue `exp (λₖ(A))` of a Hermitian matrix is bounded above by
`Re Tr (exp A)`. -/
theorem IsHermitian.exp_eigenvalues₀_le_re_trace_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    Real.exp (hA.eigenvalues₀ k) ≤ RCLike.re (exp A).trace := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [hA.re_trace_exp_eq_sum_exp]
  have hk : hA.eigenvalues (e k) = hA.eigenvalues₀ k := by simp [IsHermitian.eigenvalues, e]
  rw [← hk]
  exact Finset.single_le_sum (fun i _ ↦ (Real.exp_pos _).le) (Finset.mem_univ (e k))

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
  have hc : (c • (1 : Matrix n n 𝕜)).IsHermitian :=
    isHermitian_one.smul (IsSelfAdjoint.all c)
  have h := hA.re_trace_exp_le_of_le hc hle
  refine h.trans_eq ?_
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
  have hσ₁_herm : (H + cfc Real.log A₁).IsHermitian :=
    hH.add (cfc_predicate Real.log A₁).isHermitian
  have hσ₂_herm : (H + cfc Real.log A₂).IsHermitian :=
    hH.add (cfc_predicate Real.log A₂).isHermitian
  have hσ_herm : (H + cfc Real.log A).IsHermitian :=
    hH.add (cfc_predicate Real.log A).isHermitian
  set σ₁ := NormedSpace.exp (H + cfc Real.log A₁)
  set σ₂ := NormedSpace.exp (H + cfc Real.log A₂)
  set ρ := a • σ₁ + b • σ₂
  set σ := NormedSpace.exp (H + cfc Real.log A)
  have hσ₁ : σ₁.PosDef := hσ₁_herm.posDef_exp
  have hσ₂ : σ₂.PosDef := hσ₂_herm.posDef_exp
  have hρ : ρ.PosDef := (hσ₁.smul ha).add (hσ₂.smul hb)
  have hσ : σ.PosDef := hσ_herm.posDef_exp
  -- Klein's inequality for `ρ` and `σ`, rewritten via `log σ = H + log A`.
  have hklein := hρ.posSemidef.re_trace_sub_trace_le_relativeEntropy hσ.posSemidef
  rw [relativeEntropy_of_posDef hσ, EReal.coe_le_coe_iff, map_sub, hσ_herm.cfc_log_exp] at hklein
  -- Joint convexity of relative entropy for `(a σ₁ + b σ₂, a A₁ + b A₂)`.
  have hjoint := hσ₁.relativeEntropy_smul_add_smul_le hσ₂ hA₁ hA₂ ha.le hb.le
  rw [relativeEntropy_of_posDef hA, relativeEntropy_of_posDef hA₁, relativeEntropy_of_posDef hA₂,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
    hσ₁_herm.cfc_log_exp, hσ₂_herm.cfc_log_exp, add_sub_cancel_right,
    add_sub_cancel_right] at hjoint
  have hsplit : RCLike.re (ρ * (cfc Real.log ρ - (H + cfc Real.log A))).trace =
      RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log A)).trace - RCLike.re (ρ * H).trace := by
    have : ρ * (cfc Real.log ρ - (H + cfc Real.log A)) =
        ρ * (cfc Real.log ρ - cfc Real.log A) - ρ * H := by
      rw [← mul_sub]
      congr 1
      abel
    rw [this, trace_sub, map_sub]
  have hρH : RCLike.re (ρ * H).trace =
      a * RCLike.re (σ₁ * H).trace + b * RCLike.re (σ₂ * H).trace := by
    simp only [ρ, add_mul, smul_mul_assoc, trace_add, trace_smul, map_add, RCLike.smul_re]
  have hρtr : RCLike.re ρ.trace = a * RCLike.re σ₁.trace + b * RCLike.re σ₂.trace := by
    simp only [ρ, trace_add, trace_smul, map_add, RCLike.smul_re]
  simp only [smul_eq_mul]
  linarith

/-! ### Trace of the exponential derivative and the Golden–Thompson inequality -/

/-- **Trace of the exponential derivative.** For a Hermitian matrix `A` and any matrix `Y`,
`Tr (expFDeriv A Y) = Tr (exp A * Y)`. -/
theorem IsHermitian.trace_expFDeriv {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Y : Matrix n n 𝕜) :
    (TauCeti.expFDeriv 𝕜 A Y).trace = (NormedSpace.exp A * Y).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let U := star hA.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) U
  have htr (Z : Matrix n n 𝕜) : (e Z).trace = Z.trace := by
    simp [e, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  rw [← htr (TauCeti.expFDeriv 𝕜 A Y), ← htr (NormedSpace.exp A * Y),
    hA.expFDeriv_eigenbasis Y, map_mul]
  have heA : e (NormedSpace.exp A) = diagonal (fun i ↦ (Real.exp (hA.eigenvalues i) : 𝕜)) := by
    let f : Matrix n n 𝕜 →A[𝕜] Matrix n n 𝕜 :=
      { e.toAlgEquiv.toAlgHom with
        cont := e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous }
    have hmap : e (NormedSpace.exp A) = NormedSpace.exp (e A) := map_exp f f.continuous A
    rw [hmap, hA.conjStarAlgAut_star_eigenvectorUnitary, exp_diagonal]
    congr 1
    funext i
    simp [RCLike.exp_ofReal]
  rw [heA]
  simp only [trace, diag_apply, of_apply, diagonal_mul, dslope_same, Real.deriv_exp]
  rfl

/-- Functional calculus of a real diagonal matrix is the diagonal of the transformed entries. -/
private theorem cfc_diagonal_ofReal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (diagonal (fun i ↦ (d i : 𝕜))) = diagonal (fun i ↦ (f (d i) : 𝕜)) := by
  have hD : (diagonal (fun i ↦ (d i : 𝕜))).IsHermitian := by
    rw [IsHermitian, diagonal_conjTranspose]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  ext i j
  have heig : (diagonal (fun k ↦ (d k : 𝕜))).toEuclideanLin (PiLp.single 2 j (1 : 𝕜)) =
      (d j : 𝕜) • PiLp.single 2 j (1 : 𝕜) := by
    apply WithLp.ofLp_injective 2
    ext k
    by_cases hkj : k = j
    · subst hkj
      simp [toEuclideanLin, toLpLin_apply, RCLike.real_smul_eq_coe_mul]
    · simp [toEuclideanLin, toLpLin_apply, hkj]
  have hact := hD.toEuclideanLin_cfc_apply_of_apply_eq_smul f heig
  have hcoord := congrFun (congrArg WithLp.ofLp hact) i
  by_cases hij : i = j
  · subst hij
    simpa [toEuclideanLin, toLpLin_apply, mulVec_single, RCLike.real_smul_eq_coe_mul] using hcoord
  · simpa [toEuclideanLin, toLpLin_apply, mulVec_single, hij] using hcoord

/-- Derivative at `t = 0` of `t ↦ log ((1 - t) • 1 + t • exp B)` is `exp B - 1`. -/
private theorem hasDerivAt_cfc_log_segment_exp {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    HasDerivAt (fun t : ℝ ↦ cfc Real.log ((1 - t) • (1 : Matrix n n 𝕜) + t • NormedSpace.exp B))
      (NormedSpace.exp B - 1) 0 := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let U := hB.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) U
  let d := hB.eigenvalues
  have heB : NormedSpace.exp B = e (diagonal (fun i ↦ (Real.exp (d i) : 𝕜))) := by
    let f : Matrix n n 𝕜 →A[𝕜] Matrix n n 𝕜 :=
      { e.toAlgEquiv.toAlgHom with
        cont := e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous }
    have hspec : B = f (diagonal (fun i ↦ (d i : 𝕜))) := hB.spectral_theorem
    have hmap : NormedSpace.exp B = e (NormedSpace.exp (diagonal (fun i ↦ (d i : 𝕜)))) := by
      rw [hspec, ← map_exp f f.continuous]
      rfl
    rw [hmap, exp_diagonal]
    congr 1
    congr 1
    funext i
    simp [RCLike.exp_ofReal]
  -- Conjugating real diagonal matrices `v ↦ e (diagonal v)` is a continuous `ℝ`-linear map.
  let L : (n → ℝ) →L[ℝ] Matrix n n 𝕜 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ e (diagonal (fun i ↦ (v i : 𝕜)))
        map_add' := fun u v ↦ by
          rw [← map_add]
          congr 1
          ext i j
          by_cases hij : i = j <;> simp [hij]
        map_smul' := fun r v ↦ by
          rw [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := 𝕜) r (e _), ← map_smul]
          congr 1
          ext i j
          by_cases hij : i = j <;> simp [hij] }
  let g : ℝ → n → ℝ := fun t i ↦ Real.log (1 + t * (Real.exp (d i) - 1))
  have hg_deriv : HasDerivAt g (fun i ↦ Real.exp (d i) - 1) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have hlin : HasDerivAt (fun t : ℝ ↦ 1 + t * (Real.exp (d i) - 1)) (Real.exp (d i) - 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Real.exp (d i) - 1)).const_add 1
    have hlog := hlin.log (by norm_num : (1 + (0 : ℝ) * (Real.exp (d i) - 1)) ≠ 0)
    simpa [g] using hlog
  have hL_deriv : HasDerivAt (fun t : ℝ ↦ L (g t)) (L (fun i ↦ Real.exp (d i) - 1)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hg_deriv
  have hval : L (fun i ↦ Real.exp (d i) - 1) = NormedSpace.exp B - 1 := by
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [heB, ← map_one e, ← map_sub]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hval] at hL_deriv
  -- Near `t = 0`, `1 + t * (exp (d i) - 1) > 0`, so `cfc Real.log` acts on the diagonal entries.
  have hev : (fun t : ℝ ↦
        cfc Real.log ((1 - t) • (1 : Matrix n n 𝕜) + t • NormedSpace.exp B)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ L (g t)) := by
    have hpos : ∀ᶠ t : ℝ in 𝓝 0, ∀ i : n, 0 < 1 + t * (Real.exp (d i) - 1) := by
      rw [eventually_all]
      intro i
      have hc : Continuous fun t : ℝ ↦ 1 + t * (Real.exp (d i) - 1) := by fun_prop
      have ht0 : Tendsto (fun t : ℝ ↦ 1 + t * (Real.exp (d i) - 1)) (𝓝 0) (𝓝 1) := by
        simpa using hc.tendsto 0
      exact ht0.eventually (Ioi_mem_nhds one_pos)
    filter_upwards [hpos] with t _
    have hseg : (1 - t) • (1 : Matrix n n 𝕜) + t • NormedSpace.exp B =
        e.toStarAlgHom (diagonal (fun i ↦ ((1 + t * (Real.exp (d i) - 1) : ℝ) : 𝕜))) := by
      rw [StarAlgEquiv.toStarAlgHom_apply, heB, ← map_one e,
        RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜),
        ← map_smul, ← map_smul, ← map_add]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
        ring
      · simp [hij]
    have hD_sa :
        IsSelfAdjoint (diagonal (fun i ↦ ((1 + t * (Real.exp (d i) - 1) : ℝ) : 𝕜))) := by
      rw [isSelfAdjoint_iff, star_eq_conjTranspose, diagonal_conjTranspose]
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have he_cont : Continuous (e.toStarAlgHom : Matrix n n 𝕜 → Matrix n n 𝕜) :=
      e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous
    rw [hseg, ← StarAlgHom.map_cfc e.toStarAlgHom Real.log _
      ((diagonal _).finite_real_spectrum.continuousOn _) he_cont hD_sa (hD_sa.map e.toStarAlgHom),
      cfc_diagonal_ofReal]
    rfl
  exact hL_deriv.congr_of_eventuallyEq hev

/-- **The Golden–Thompson inequality** (Golden 1965; Thompson 1965). For Hermitian matrices `A` and
`B` over any `RCLike` field, `Re Tr (exp (A + B)) ≤ Re Tr (exp A * exp B)`. -/
theorem IsHermitian.re_trace_exp_add_le_re_trace_exp_mul_exp {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (NormedSpace.exp (A + B)).trace ≤
      RCLike.re (NormedSpace.exp A * NormedSpace.exp B).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let f : ℝ → ℝ := fun t ↦
    RCLike.re (NormedSpace.exp (A + cfc Real.log
      ((1 - t) • (1 : Matrix n n 𝕜) + t • NormedSpace.exp B))).trace
  -- `f` is concave on `[0, 1]` by Lieb's concavity theorem.
  have hconc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 - t) * f 0 + t * f 1 ≤ f t := by
    intro t ht
    have h := hA.concaveOn_re_trace_exp_add_cfc_log.2 (PosDef.one (n := n) (R := 𝕜))
      hB.posDef_exp (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    simpa only [f, sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add,
      smul_eq_mul] using h
  -- Compute `f'(0) = Re Tr (exp A * (exp B - 1))`.
  let trRe : Matrix n n 𝕜 →L[ℝ] ℝ :=
    RCLike.reCLM.comp ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap
  let γ : ℝ → Matrix n n 𝕜 := fun t ↦
    A + cfc Real.log ((1 - t) • (1 : Matrix n n 𝕜) + t • NormedSpace.exp B)
  have hγ_deriv : HasDerivAt γ (NormedSpace.exp B - 1) 0 :=
    (hasDerivAt_cfc_log_segment_exp hB).const_add A
  have hγ_zero : γ 0 = A := by simp [γ, cfc_apply_one]
  have hexp_deriv : HasFDerivAt (NormedSpace.exp : Matrix n n 𝕜 → Matrix n n 𝕜)
      ((TauCeti.expFDeriv 𝕜 A).restrictScalars ℝ) (γ 0) := by
    rw [hγ_zero]
    exact (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) A).restrictScalars ℝ
  have hf_deriv : HasDerivAt f
      (RCLike.re (TauCeti.expFDeriv 𝕜 A (NormedSpace.exp B - 1)).trace) 0 := by
    exact (trRe.hasFDerivAt.comp (γ 0) hexp_deriv).comp_hasDerivAt 0 hγ_deriv
  -- Pass to the limit `t → 0⁺` in the secant inequality `f 1 - f 0 ≤ (f t - f 0) / t`.
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ * (f t - f 0)) (𝓝[>] 0)
      (𝓝 (RCLike.re (TauCeti.expFDeriv 𝕜 A (NormedSpace.exp B - 1)).trace)) := by
    simpa only [slope_def_field, zero_add, smul_eq_mul, div_eq_inv_mul] using
      hf_deriv.tendsto_slope_zero_right
  have hsec : ∀ᶠ t : ℝ in 𝓝[>] 0, f 1 - f 0 ≤ t⁻¹ * (f t - f 0) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    have hle := hconc t ht
    rw [le_inv_mul_iff₀ ht.1]
    linarith
  have hbound : f 1 - f 0 ≤ RCLike.re (TauCeti.expFDeriv 𝕜 A (NormedSpace.exp B - 1)).trace :=
    ge_of_tendsto hslope hsec
  rw [hA.trace_expFDeriv, mul_sub, mul_one, trace_sub, map_sub] at hbound
  have hf0 : f 0 = RCLike.re (NormedSpace.exp A).trace := by simp [f, cfc_apply_one]
  have hf1 : f 1 = RCLike.re (NormedSpace.exp (A + B)).trace := by
    simp [f, hB.cfc_log_exp]
  linarith

end Matrix
