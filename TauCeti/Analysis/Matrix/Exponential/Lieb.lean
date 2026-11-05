/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Matrix.Exponential.Log
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.PosDef

/-!
# Joint convexity of relative entropy and Lieb's concavity theorem

For positive definite matrices `X, Y` over any `RCLike` field, `(X, Y) ↦ Re Tr (X (log X - log Y))`
is jointly convex via Effros's perspective integral, and for Hermitian `B`,
`A ↦ Re Tr (exp (B + log A))` is concave on `{A | A.PosDef}` (**Lieb's concavity theorem**).

## Main results

* `Matrix.convexOn_re_trace_mul_cfc_log_sub_cfc_log`: joint convexity of quantum relative entropy.
* `Matrix.PosDef.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log`: Gibbs lower bound.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`: **Lieb's concavity theorem**.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log_posSemidef_sub_smul_one`.

## References

* E. H. Lieb, Adv. Math. 11 (1973); J. A. Tropp, Proc. Amer. Math. Soc. 140 (2012), 1757–1760.
-/

public section

open NormedSpace
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

private theorem pos_interp_of_mem_uIcc {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) : 0 < (1 - t) * y + t * x := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  rcases le_or_gt t (1 / 2) with h | h <;> nlinarith [ht.1, ht.2]

private theorem mul_log_sub_log_eq_add_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * (Real.log x - Real.log y) =
      (x - y) + ∫ t in (0 : ℝ)..1, (1 - t) * (x - y) ^ 2 / ((1 - t) * y + t * x) := by
  have hcont_den : ContinuousOn (fun t : ℝ ↦ (1 - t) * y + t * x) (Set.uIcc (0 : ℝ) 1) :=
    (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).continuousOn
  have hne : ∀ t ∈ Set.uIcc (0 : ℝ) 1, (1 - t) * y + t * x ≠ 0 :=
    fun t ht ↦ (pos_interp_of_mem_uIcc hx hy ht).ne'
  have hint₁ : IntervalIntegrable (fun t : ℝ ↦ (x - y) / ((1 - t) * y + t * x))
      MeasureTheory.volume 0 1 := (continuousOn_const.div hcont_den hne).intervalIntegrable
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ Real.log ((1 - s) * y + s * x))
        ((x - y) / ((1 - t) * y + t * x)) t := fun t ht ↦
    ((((hasDerivAt_id t).const_sub 1).mul_const y).add
      ((hasDerivAt_id t).mul_const x) |>.congr_deriv (by ring)).log (hne t ht)
  have hlog : ∫ t in (0 : ℝ)..1, (x - y) / ((1 - t) * y + t * x) = Real.log x - Real.log y := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint₁
  rw [intervalIntegral.integral_congr (g := fun t ↦ x * ((x - y) / ((1 - t) * y + t * x)) - (x - y))
    (fun t ht ↦ by have := hne t ht; field_simp; ring),
    intervalIntegral.integral_sub (hint₁.const_mul x) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hlog, intervalIntegral.integral_const]
  simp

private theorem two_mul_re_conj_mul_sub_le {c : ℝ} (hc : 0 < c) (w z : 𝕜) :
    2 * RCLike.re (conj w * z) - c * ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 / c := by
  have hcs : RCLike.re (conj w * z) ≤ ‖w‖ * ‖z‖ :=
    (RCLike.re_le_norm _).trans_eq (by rw [norm_mul, RCLike.norm_conj])
  rw [le_div_iff₀ hc]; nlinarith [sq_nonneg (c * ‖w‖ - ‖z‖)]

private theorem two_mul_re_conj_mul_sub_eq {c : ℝ} (hc : 0 < c) (z : 𝕜) :
    2 * RCLike.re (conj ((c⁻¹ : ℝ) • z) * z) - c * ‖(c⁻¹ : ℝ) • z‖ ^ 2 = ‖z‖ ^ 2 / c := by
  have hconj : conj ((c⁻¹ : ℝ) • z) * z = (c⁻¹ : ℝ) • ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.real_smul_eq_coe_mul, map_mul, RCLike.conj_ofReal, mul_assoc,
      ← RCLike.real_smul_eq_coe_mul, mul_comm (conj z), RCLike.mul_conj, RCLike.ofReal_pow]
  rw [hconj, RCLike.smul_re, RCLike.ofReal_re, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  have := hc.ne'; field_simp; ring

omit [DecidableEq n] in
private def liebLinearForm (t : ℝ) (M X Y : Matrix n n 𝕜) : ℝ :=
  2 * RCLike.re (Mᴴ * (X - Y)).trace - RCLike.re (Mᴴ * (t • (X * M) + (1 - t) • (M * Y))).trace

omit [DecidableEq n] in
private theorem liebLinearForm_combo (t : ℝ) (M X₁ X₂ Y₁ Y₂ : Matrix n n 𝕜) (a b : ℝ) :
    liebLinearForm t M (a • X₁ + b • X₂) (a • Y₁ + b • Y₂) =
      a * liebLinearForm t M X₁ Y₁ + b * liebLinearForm t M X₂ Y₂ := by
  simp only [liebLinearForm, sub_eq_add_neg, Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, add_smul, neg_smul, smul_smul, trace_add,
    trace_neg, trace_smul, map_add, map_neg, RCLike.smul_re]
  ring

section EigenbasisForm

open scoped Matrix.Norms.Frobenius

private theorem liebLinearForm_eq_sum {X Y : Matrix n n 𝕜} (hX : X.PosDef) (hY : Y.PosDef)
    (t : ℝ) (M : Matrix n n 𝕜) :
    let U : Matrix n n 𝕜 := ↑hX.1.eigenvectorUnitary
    let V : Matrix n n 𝕜 := ↑hY.1.eigenvectorUnitary
    let W : Matrix n n 𝕜 := star U * M * V
    liebLinearForm t M X Y =
      ∑ i, ∑ j, (2 * RCLike.re (conj (W i j) *
          (((hX.1.eigenvalues i - hY.1.eigenvalues j : ℝ) : 𝕜) *
            ⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜)) -
        ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i) * ‖W i j‖ ^ 2) := by
  intro U V W
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self _
  let dX : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hX.1.eigenvalues)
  let dY : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hY.1.eigenvalues)
  have hM : M = U * W * star V := by
    simpa only [W, Matrix.mul_assoc] using (show M = (U * star U) * M * (V * star V) by
      rw [hUU', hVV', one_mul, mul_one])
  have hMstar : Mᴴ = V * Wᴴ * star U := by
    simp only [hM, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hXdiag : star U * X * U = dX := by
    simpa [U, dX, Unitary.conjStarAlgAut_apply] using hX.1.conjStarAlgAut_star_eigenvectorUnitary
  have hYdiag : star V * Y * V = dY := by
    simpa [V, dY, Unitary.conjStarAlgAut_apply] using hY.1.conjStarAlgAut_star_eigenvectorUnitary
  let Z : Matrix n n 𝕜 := dX * (star U * V) - (star U * V) * dY
  have hZ_eq : star U * (X - Y) * V = Z := by
    have h1 : star U * X * V = dX * (star U * V) := by
      rw [← hXdiag, show star U * X * U * (star U * V) = star U * X * (U * star U) * V by
        simp only [Matrix.mul_assoc], hUU', mul_one]
    have h2 : star U * Y * V = (star U * V) * dY := by
      rw [← hYdiag, show (star U * V) * (star V * Y * V) = star U * (V * star V) * Y * V by
        simp only [Matrix.mul_assoc], hVV', mul_one]
    simp only [Z, Matrix.mul_sub, Matrix.sub_mul, h1, h2]
  have htr1 : (Mᴴ * (X - Y)).trace = (Wᴴ * Z).trace := by
    rw [← hZ_eq, hMstar, show V * Wᴴ * star U * (X - Y) = V * (Wᴴ * (star U * (X - Y))) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm V, Matrix.mul_assoc, Matrix.mul_assoc]
  have hXM : (Mᴴ * (X * M)).trace = (Wᴴ * (dX * W)).trace := by
    rw [hMstar, hM, show V * Wᴴ * star U * (X * (U * W * star V)) =
      V * (Wᴴ * ((star U * X * U) * W) * star V) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm V, hXdiag]
    simp only [Matrix.mul_assoc, hVV, mul_one]
  have hMY : (Mᴴ * (M * Y)).trace = (Wᴴ * (W * dY)).trace := by
    have hY' : star V * (Y * V) = dY := by simpa [Matrix.mul_assoc] using hYdiag
    rw [hMstar, hM, show V * Wᴴ * star U * (U * W * star V * Y) =
      V * (Wᴴ * ((star U * U) * W * (star V * Y))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm V, hUU, one_mul]
    simp only [Matrix.mul_assoc, hY']
  let L : Matrix n n 𝕜 := t • (dX * W) + (1 - t) • (W * dY)
  have htr2 : (Mᴴ * (t • (X * M) + (1 - t) • (M * Y))).trace = (Wᴴ * L).trace := by
    simp only [L, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, hXM, hMY]
  rw [liebLinearForm, htr1, htr2, ← frobenius_inner_eq_trace_conjTranspose_mul,
    ← frobenius_inner_eq_trace_conjTranspose_mul, frobenius_inner_eq_sum_conj_mul,
    frobenius_inner_eq_sum_conj_mul]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hZij : Z i j = ((hX.1.eigenvalues i - hY.1.eigenvalues j : ℝ) : 𝕜) *
      ⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜 := by
    simp only [Z, dX, dY, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Function.comp_apply, U, V, hX.1.star_eigenvectorUnitary_mul_eigenvectorUnitary_apply hY.1 i j,
      RCLike.ofReal_sub]
    ring
  have hLij : L i j =
      (((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) * W i j := by
    simp only [L, dX, dY, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Function.comp_apply, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_add,
      RCLike.ofReal_mul]
    ring
  rw [hZij, hLij, show conj (W i j) *
      ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) * W i j) =
      (((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) *
        (W i j * conj (W i j)) by ring,
    RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

end EigenbasisForm

private theorem norm_ofReal_mul_sq (r : ℝ) (z : 𝕜) :
    ‖(r : 𝕜) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]

private noncomputable def perspectiveIntegrand {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 *
    ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 /
      ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)

private theorem liebLinearForm_le_perspectiveIntegrand {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) (M : Matrix n n 𝕜) :
    liebLinearForm t M X Y ≤ perspectiveIntegrand hX hY t := by
  rw [liebLinearForm_eq_sum hX hY t M, perspectiveIntegrand]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  exact (two_mul_re_conj_mul_sub_le
    (pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht) _ _).trans_eq
    (by rw [norm_ofReal_mul_sq])

private theorem exists_liebLinearForm_eq_perspectiveIntegrand {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    ∃ M : Matrix n n 𝕜, liebLinearForm t M X Y = perspectiveIntegrand hX hY t := by
  let U : Matrix n n 𝕜 := ↑hX.1.eigenvectorUnitary
  let V : Matrix n n 𝕜 := ↑hY.1.eigenvectorUnitary
  let W₀ : Matrix n n 𝕜 := Matrix.of fun i j ↦
    ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)⁻¹ : ℝ) •
      (((hX.1.eigenvalues i - hY.1.eigenvalues j : ℝ) : 𝕜) *
        ⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜))
  refine ⟨U * W₀ * star V, ?_⟩
  have hW : star U * (U * W₀ * star V) * V = W₀ := by
    rw [show star U * (U * W₀ * star V) * V = (star U * U) * W₀ * (star V * V) by
      simp only [Matrix.mul_assoc], Unitary.coe_star_mul_self _, Unitary.coe_star_mul_self _,
      one_mul, mul_one]
  rw [liebLinearForm_eq_sum hX hY t (U * W₀ * star V), perspectiveIntegrand]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [congrArg (fun A : Matrix n n 𝕜 ↦ A i j) hW]
  simp only [W₀, of_apply, two_mul_re_conj_mul_sub_eq
    (pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht), norm_ofReal_mul_sq]

private theorem intervalIntegrable_one_sub_mul_perspectiveIntegrand {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - t) * perspectiveIntegrand hX hY t)
      MeasureTheory.volume 0 1 :=
  ContinuousOn.intervalIntegrable ((continuous_const.sub continuous_id).continuousOn.mul <|
    continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      continuousOn_const.div ((((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)).continuousOn) fun _ ht ↦
        (pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht).ne')

private theorem re_trace_mul_cfc_log_sub_eq_add_integral {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    RCLike.re (X * (cfc Real.log X - cfc Real.log Y)).trace =
      RCLike.re (X - Y).trace +
        ∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX hY t := by
  have hD : X * (cfc Real.log X - cfc Real.log Y) =
      cfc (fun x ↦ x * Real.log x) X * cfc (fun _ : ℝ ↦ (1 : ℝ)) Y -
        cfc (fun x : ℝ ↦ x) X * cfc Real.log Y := by
    rw [mul_sub, hX.1.mul_cfc, cfc_const_one ℝ Y hY.1.isSelfAdjoint, mul_one,
      cfc_id' ℝ X hX.1.isSelfAdjoint]
  have hXtr : RCLike.re X.trace = ∑ i, ∑ j, hX.1.eigenvalues i *
      ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    simpa only [cfc_const_one ℝ Y hY.1.isSelfAdjoint, mul_one, cfc_id' ℝ X hX.1.isSelfAdjoint]
      using IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1 (fun x ↦ x) (fun _ ↦ 1)
  have hYtr : RCLike.re Y.trace = ∑ i, ∑ j, hY.1.eigenvalues j *
      ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    simpa only [cfc_const_one ℝ X hX.1.isSelfAdjoint, one_mul, cfc_id' ℝ Y hY.1.isSelfAdjoint]
      using IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1 (fun _ ↦ 1) (fun x ↦ x)
  let g (i j : n) (t : ℝ) : ℝ :=
    ((1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
      ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
        ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2
  have hint_ij (i j : n) : IntervalIntegrable (g i j) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable (((continuous_const.sub continuous_id).mul
      continuous_const).continuousOn.div ((((continuous_const.sub continuous_id).mul
        continuous_const).add (continuous_id.mul continuous_const)).continuousOn)
      (fun _ ht ↦ (pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht).ne')
      |>.mul continuousOn_const)
  have hint_i (i : n) : IntervalIntegrable (fun t ↦ ∑ j, g i j t) MeasureTheory.volume 0 1 :=
    (IntervalIntegrable.sum Finset.univ fun j _ ↦ hint_ij i j).congr fun _ _ ↦ by simp
  have hsum_int : ∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX hY t =
      ∑ i, ∑ j, (∫ t in (0 : ℝ)..1, (1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
        ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
          ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    rw [show (fun t : ℝ ↦ (1 - t) * perspectiveIntegrand hX hY t) = fun t ↦ ∑ i, ∑ j, g i j t by
      ext t; simp only [perspectiveIntegrand, g, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring,
      intervalIntegral.integral_finsetSum fun i _ ↦ hint_i i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_finsetSum fun j _ ↦ hint_ij i j]
    exact Finset.sum_congr rfl fun j _ ↦ intervalIntegral.integral_mul_const _ _
  rw [hD, trace_sub, map_sub, IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1,
    IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1, trace_sub, map_sub, hXtr, hYtr, hsum_int]
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 *
    mul_log_sub_log_eq_add_integral (hX.eigenvalues_pos i) (hY.eigenvalues_pos j)

/-- **Joint convexity of quantum relative entropy** on positive definite matrices:
`(X, Y) ↦ Re Tr (X (log X - log Y))` is convex on `{X | X.PosDef} ×ˢ {Y | Y.PosDef}`. -/
theorem convexOn_re_trace_mul_cfc_log_sub_cfc_log :
    ConvexOn ℝ ({X : Matrix n n 𝕜 | X.PosDef} ×ˢ {Y : Matrix n n 𝕜 | Y.PosDef})
      (fun p ↦ RCLike.re (p.1 * (cfc Real.log p.1 - cfc Real.log p.2)).trace) := by
  rw [convexOn_iff_forall_pos]
  refine ⟨TauCeti.convex_setOfPred_posDef.prod TauCeti.convex_setOfPred_posDef, ?_⟩
  rintro ⟨X₁, Y₁⟩ ⟨hX₁, hY₁⟩ ⟨X₂, Y₂⟩ ⟨hX₂, hY₂⟩ a b ha hb hab
  have hX : (a • X₁ + b • X₂).PosDef := (hX₁.smul ha).add (hX₂.smul hb)
  have hY : (a • Y₁ + b • Y₂).PosDef := (hY₁.smul ha).add (hY₂.smul hb)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [re_trace_mul_cfc_log_sub_eq_add_integral hX hY,
    re_trace_mul_cfc_log_sub_eq_add_integral hX₁ hY₁,
    re_trace_mul_cfc_log_sub_eq_add_integral hX₂ hY₂]
  have hlin_tr : RCLike.re ((a • X₁ + b • X₂) - (a • Y₁ + b • Y₂)).trace =
      a * RCLike.re (X₁ - Y₁).trace + b * RCLike.re (X₂ - Y₂).trace := by
    rw [show (a • X₁ + b • X₂) - (a • Y₁ + b • Y₂) = a • (X₁ - Y₁) + b • (X₂ - Y₂) by
      simp only [smul_sub]; abel]; simp [trace_add, trace_smul, RCLike.smul_re]
  have hi := intervalIntegrable_one_sub_mul_perspectiveIntegrand hX hY
  have hi₁ := intervalIntegrable_one_sub_mul_perspectiveIntegrand hX₁ hY₁
  have hi₂ := intervalIntegrable_one_sub_mul_perspectiveIntegrand hX₂ hY₂
  have hint : ∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX hY t ≤
      a * (∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX₁ hY₁ t) +
        b * (∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX₂ hY₂ t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi₁.const_mul a) (hi₂.const_mul b)]
    refine intervalIntegral.integral_mono_on zero_le_one hi
      ((hi₁.const_mul a).add (hi₂.const_mul b)) fun t ht ↦ ?_
    have ht_uIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one]
    obtain ⟨M, hM⟩ := exists_liebLinearForm_eq_perspectiveIntegrand hX hY ht_uIcc
    have h1 := liebLinearForm_le_perspectiveIntegrand hX₁ hY₁ ht_uIcc M
    have h2 := liebLinearForm_le_perspectiveIntegrand hX₂ hY₂ ht_uIcc M
    have hle : perspectiveIntegrand hX hY t ≤
        a * perspectiveIntegrand hX₁ hY₁ t + b * perspectiveIntegrand hX₂ hY₂ t := by
      rw [← hM, liebLinearForm_combo]; nlinarith
    exact (mul_le_mul_of_nonneg_left hle (sub_nonneg.2 ht.2)).trans_eq (by ring)
  linarith

/-- **Gibbs variational bound.** For positive definite `ρ`, arbitrary `A`, and Hermitian `B`,
`Re Tr ρ + Re Tr (ρ B) - Re Tr (ρ (log ρ - log A)) ≤ Re Tr (exp (B + log A))`. -/
theorem PosDef.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log
    {ρ B : Matrix n n 𝕜} (hρ : ρ.PosDef) (A : Matrix n n 𝕜) (hB : B.IsHermitian) :
    RCLike.re ρ.trace + RCLike.re (ρ * B).trace -
        RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log A)).trace ≤
      RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace := by
  have hH : (B + cfc Real.log A).IsHermitian :=
    hB.add (isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc)
  have hklein := hρ.posSemidef.re_trace_sub_trace_le_relativeEntropy hH.posDef_exp.posSemidef
  rw [relativeEntropy_of_posDef hH.posDef_exp, EReal.coe_le_coe_iff, hH.cfc_log_exp,
    show ρ * (cfc Real.log ρ - (B + cfc Real.log A)) =
      ρ * (cfc Real.log ρ - cfc Real.log A) - ρ * B by
      simp only [Matrix.mul_sub, Matrix.mul_add]; abel,
    trace_sub, map_sub, map_sub] at hklein
  linarith

/-- **Lieb's concavity theorem.** For every Hermitian matrix `B`, the map
`A ↦ Re Tr (exp (B + log A))` is concave on the positive definite cone `{A | A.PosDef}`. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      (fun A ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace) := by
  rw [concaveOn_iff_forall_pos]
  refine ⟨TauCeti.convex_setOfPred_posDef, fun A₁ hA₁ A₂ hA₂ a b ha hb hab ↦ ?_⟩
  set ρ₁ : Matrix n n 𝕜 := NormedSpace.exp (B + cfc Real.log A₁)
  set ρ₂ : Matrix n n 𝕜 := NormedSpace.exp (B + cfc Real.log A₂)
  have hρ (A : Matrix n n 𝕜) : (NormedSpace.exp (B + cfc Real.log A)).PosDef :=
    (hB.add (isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc)).posDef_exp
  have hvar (A : Matrix n n 𝕜) :
      let σ := NormedSpace.exp (B + cfc Real.log A)
      RCLike.re σ.trace + RCLike.re (σ * B).trace -
        RCLike.re (σ * (cfc Real.log σ - cfc Real.log A)).trace = RCLike.re σ.trace := by
    dsimp only; rw [(hB.add (isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc)).cfc_log_exp,
      add_sub_cancel_right]; ring
  have hD := (convexOn_iff_forall_pos.1
    (convexOn_re_trace_mul_cfc_log_sub_cfc_log (n := n) (𝕜 := 𝕜))).2
    (x := (ρ₁, A₁)) ⟨hρ A₁, hA₁⟩ (y := (ρ₂, A₂)) ⟨hρ A₂, hA₂⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hD ⊢
  have htrρ : RCLike.re (a • ρ₁ + b • ρ₂).trace =
      a * RCLike.re ρ₁.trace + b * RCLike.re ρ₂.trace := by
    simp [trace_add, trace_smul, RCLike.smul_re]
  have htrρB : RCLike.re ((a • ρ₁ + b • ρ₂) * B).trace =
      a * RCLike.re (ρ₁ * B).trace + b * RCLike.re (ρ₂ * B).trace := by
    simp [Matrix.add_mul, trace_add, trace_smul, RCLike.smul_re]
  have hρ_mix : (a • ρ₁ + b • ρ₂).PosDef := (hρ A₁ |>.smul ha).add (hρ A₂ |>.smul hb)
  nlinarith [hvar A₁, hvar A₂,
    hρ_mix.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log (a • A₁ + b • A₂) hB]

/-- For `ε > 0`, Lieb's concavity holds on the closed shifted cone `{A | (A - ε • 1).PosSemidef}`,
every member of which is positive definite. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log_posSemidef_sub_smul_one
    {B : Matrix n n 𝕜} (hB : B.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | (A - ε • 1).PosSemidef}
      (fun A ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace) := by
  refine hB.concaveOn_re_trace_exp_add_cfc_log.subset
    (fun A hA ↦ by simpa [sub_add_cancel] using PosDef.posSemidef_add hA (PosDef.one.smul hε))
    fun A₁ hA₁ A₂ hA₂ a b ha hb hab ↦ ?_
  have hlin : (a • A₁ + b • A₂) - ε • (1 : Matrix n n 𝕜) =
      a • (A₁ - ε • 1) + b • (A₂ - ε • 1) :=
    calc (a • A₁ + b • A₂) - ε • (1 : Matrix n n 𝕜)
        = (a • A₁ + b • A₂) - (a + b) • (ε • 1) := by rw [hab, one_smul]
      _ = a • (A₁ - ε • 1) + b • (A₂ - ε • 1) := by rw [add_smul, smul_sub, smul_sub]; abel
  simpa only [Set.mem_ofPred, hlin] using (hA₁.smul ha).add (hA₂.smul hb)

end Matrix
