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

For positive definite matrices `X` and `Y` over `ℝ` or `ℂ` (any `RCLike` field), the unnormalized
quantum relative entropy `(X, Y) ↦ Re Tr (X (log X - log Y))` is jointly convex, and for every
Hermitian matrix `B` the map

`A ↦ Re Tr (exp (B + log A))`

is concave on the cone of positive definite matrices (**Lieb's concavity theorem**).

The proof combines Effros's perspective-integral representation with Klein's variational formula:

1. For positive reals `x` and `y`,
   `x (log x - log y) = (x - y) + ∫₀¹ (1 - t) (x - y)² / ((1 - t) y + t x) dt`.
   Expanding `Re Tr (X (log X - log Y))` in the eigenbases of `X` and `Y` via
   `Matrix.IsHermitian.re_trace_cfc_mul_cfc` expresses the integrand at each `t ∈ [0, 1]` as the
   supremum over all auxiliary matrices `M` of the real-linear functional
   `(X, Y) ↦ 2 Re Tr (Mᴴ (X - Y)) - Re Tr (Mᴴ (t • X M + (1 - t) • M Y))`,
   attained explicitly at the divided-difference matrix in the eigenbases of `X` and `Y`.
   Integrating over `t ∈ [0, 1]` yields joint convexity of `(X, Y) ↦ Re Tr (X (log X - log Y))`.
2. Klein's inequality (`Matrix.PosSemidef.re_trace_sub_trace_le_relativeEntropy`) applied to any
   positive definite `ρ` and `σ = exp (B + log A)` gives the Gibbs variational principle
   `Re Tr (exp (B + log A)) = max_{ρ > 0} (Re Tr ρ + Re Tr (ρ B) - Re Tr (ρ (log ρ - log A)))`,
   attained at `ρ = exp (B + log A)`. Joint convexity of the subtracted relative-entropy term
   immediately makes the maximum concave in `A`.

## Main results

* `Matrix.convexOn_re_trace_mul_cfc_log_sub_cfc_log`: `(X, Y) ↦ Re Tr (X (log X - log Y))` is
  jointly convex on `{X | X.PosDef} ×ˢ {Y | Y.PosDef}`.
* `Matrix.PosDef.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log`: the Gibbs variational
  lower bound `Re Tr ρ + Re Tr (ρ B) - Re Tr (ρ (log ρ - log A)) ≤ Re Tr (exp (B + log A))` for
  positive definite `ρ`, arbitrary `A`, and Hermitian `B`.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`: **Lieb's concavity theorem**, concavity
  of `A ↦ Re Tr (exp (B + log A))` on `{A | A.PosDef}`.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log_posSemidef_sub_smul_one`: concavity of the
  same functional on the closed shifted cone `{A | (A - ε • 1).PosSemidef}` for `0 < ε`.

## References

* E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*, Adv. Math. 11
  (1973), 267–288.
* E. G. Effros, *A matrix convexity approach to some celebrated quantum inequalities*, Proc. Natl.
  Acad. Sci. USA 106 (2009), 1006–1008.
* J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of Lieb*,
  Proc. Amer. Math. Soc. 140 (2012), 1757–1760.
-/

public section

open NormedSpace
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix

noncomputable section

namespace Matrix

section RelativeEntropyConvexity

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

private theorem pos_interp_of_mem_uIcc {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) : 0 < (1 - t) * y + t * x := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  obtain ⟨ht0, ht1⟩ := ht
  rcases le_or_gt t (1 / 2) with h | h <;> nlinarith

/-- Scalar integral representation of `x (log x - log y)` with a nonsingular integrand. -/
private theorem mul_log_sub_log_eq_add_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * (Real.log x - Real.log y) =
      (x - y) + ∫ t in (0 : ℝ)..1, (1 - t) * (x - y) ^ 2 / ((1 - t) * y + t * x) := by
  have hcont_den : ContinuousOn (fun t : ℝ ↦ (1 - t) * y + t * x) (Set.uIcc (0 : ℝ) 1) :=
    ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const) |>.continuousOn
  have hne : ∀ t ∈ Set.uIcc (0 : ℝ) 1, (1 - t) * y + t * x ≠ 0 :=
    fun t ht ↦ (pos_interp_of_mem_uIcc hx hy ht).ne'
  have hint₁ : IntervalIntegrable (fun t : ℝ ↦ (x - y) / ((1 - t) * y + t * x))
      MeasureTheory.volume 0 1 :=
    (continuousOn_const.div hcont_den hne).intervalIntegrable
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ Real.log ((1 - s) * y + s * x))
        ((x - y) / ((1 - t) * y + t * x)) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ ↦ (1 - s) * y + s * x) (x - y) t := by
      have h1 := ((hasDerivAt_id t).const_sub 1).mul_const y
      have h2 := (hasDerivAt_id t).mul_const x
      exact (h1.add h2).congr_deriv (by ring)
    exact hlin.log (hne t ht)
  have hlog : ∫ t in (0 : ℝ)..1, (x - y) / ((1 - t) * y + t * x) = Real.log x - Real.log y := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint₁
  have hconst : ∫ _t in (0 : ℝ)..1, (x - y) = x - y := by simp
  have hrew : ∫ t in (0 : ℝ)..1, (1 - t) * (x - y) ^ 2 / ((1 - t) * y + t * x) =
      ∫ t in (0 : ℝ)..1, (x * ((x - y) / ((1 - t) * y + t * x)) - (x - y)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have hd := hne t ht
    field_simp
    ring
  rw [hrew, intervalIntegral.integral_sub (hint₁.const_mul x) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hlog, hconst]
  ring

/-- Scalar Legendre inequality `2 Re (conj w · z) - c ‖w‖² ≤ ‖z‖² / c` for `c > 0`. -/
private theorem two_mul_re_conj_mul_sub_le {c : ℝ} (hc : 0 < c) (w z : 𝕜) :
    2 * RCLike.re (conj w * z) - c * ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 / c := by
  have hcs : RCLike.re (conj w * z) ≤ ‖w‖ * ‖z‖ :=
    (RCLike.re_le_norm _).trans_eq (by rw [norm_mul, RCLike.norm_conj])
  rw [le_div_iff₀ hc]
  nlinarith [sq_nonneg (c * ‖w‖ - ‖z‖)]

/-- Equality in `two_mul_re_conj_mul_sub_le` at `w = c⁻¹ • z`. -/
private theorem two_mul_re_conj_mul_sub_eq {c : ℝ} (hc : 0 < c) (z : 𝕜) :
    2 * RCLike.re (conj ((c⁻¹ : ℝ) • z) * z) - c * ‖(c⁻¹ : ℝ) • z‖ ^ 2 = ‖z‖ ^ 2 / c := by
  have hconj : conj ((c⁻¹ : ℝ) • z) * z = (c⁻¹ : ℝ) • ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.real_smul_eq_coe_mul, map_mul, RCLike.conj_ofReal, mul_assoc,
      ← RCLike.real_smul_eq_coe_mul]
    congr 1
    rw [mul_comm, RCLike.mul_conj, RCLike.ofReal_pow]
  have hre : RCLike.re (conj ((c⁻¹ : ℝ) • z) * z) = c⁻¹ * ‖z‖ ^ 2 := by
    simp only [hconj, RCLike.smul_re, RCLike.ofReal_re]
  have hnorm0 : ‖(c⁻¹ : ℝ) • z‖ = c⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  rw [hre, hnorm0]
  have hc0 : c ≠ 0 := hc.ne'
  field_simp
  ring

omit [DecidableEq n] in
/-- The linear functional in `(X, Y)` whose supremum over `M` is the perspective quadratic form. -/
private def liebLinearForm (t : ℝ) (M X Y : Matrix n n 𝕜) : ℝ :=
  2 * RCLike.re (Mᴴ * (X - Y)).trace - RCLike.re (Mᴴ * (t • (X * M) + (1 - t) • (M * Y))).trace

omit [DecidableEq n] in
private theorem liebLinearForm_combo (t : ℝ) (M X₁ X₂ Y₁ Y₂ : Matrix n n 𝕜) (a b : ℝ) :
    liebLinearForm t M (a • X₁ + b • X₂) (a • Y₁ + b • Y₂) =
      a * liebLinearForm t M X₁ Y₁ + b * liebLinearForm t M X₂ Y₂ := by
  have h1 : Mᴴ * ((a • X₁ + b • X₂) - (a • Y₁ + b • Y₂)) =
      a • (Mᴴ * (X₁ - Y₁)) + b • (Mᴴ * (X₂ - Y₂)) := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, smul_sub]
    abel
  have h2 : Mᴴ * (t • ((a • X₁ + b • X₂) * M) + (1 - t) • (M * (a • Y₁ + b • Y₂))) =
      a • (Mᴴ * (t • (X₁ * M) + (1 - t) • (M * Y₁))) +
        b • (Mᴴ * (t • (X₂ * M) + (1 - t) • (M * Y₂))) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul]
    rw [mul_comm t a, mul_comm t b, mul_comm (1 - t) a, mul_comm (1 - t) b]
    abel
  simp only [liebLinearForm, h1, h2, trace_add, trace_smul, map_add, RCLike.smul_re]
  ring

section EigenbasisForm

open scoped Matrix.Norms.Frobenius

/-- In the eigenbases `U` of `X` and `V` of `Y`, `liebLinearForm` separates over entry pairs. -/
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
  have hM : M = U * W * star V := by
    calc M = (U * star U) * M * (V * star V) := by rw [hUU', hVV', one_mul, mul_one]
      _ = U * W * star V := by simp only [W, Matrix.mul_assoc]
  have hXdiag : star U * X * U = diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hX.1.conjStarAlgAut_star_eigenvectorUnitary
  have hYdiag : star V * Y * V = diagonal (RCLike.ofReal ∘ hY.1.eigenvalues) := by
    simpa [V, Unitary.conjStarAlgAut_apply] using hY.1.conjStarAlgAut_star_eigenvectorUnitary
  let Z : Matrix n n 𝕜 := star U * (X - Y) * V
  have hZ_entry (i j : n) :
      Z i j = ((hX.1.eigenvalues i - hY.1.eigenvalues j : ℝ) : 𝕜) *
        ⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜 := by
    have h1 : star U * X * V = (star U * X * U) * (star U * V) := by
      calc star U * X * V = star U * X * (U * star U) * V := by rw [hUU', mul_one]
        _ = (star U * X * U) * (star U * V) := by simp only [Matrix.mul_assoc]
    have h2 : star U * Y * V = (star U * V) * (star V * Y * V) := by
      calc star U * Y * V = star U * (V * star V) * Y * V := by rw [hVV', mul_one]
        _ = (star U * V) * (star V * Y * V) := by simp only [Matrix.mul_assoc]
    have hZ : Z = diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) * (star U * V) -
        (star U * V) * diagonal (RCLike.ofReal ∘ hY.1.eigenvalues) := by
      simp only [Z, Matrix.mul_sub, Matrix.sub_mul, h1, h2, hXdiag, hYdiag]
    rw [hZ, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply,
      Function.comp_apply, hX.1.star_eigenvectorUnitary_mul_eigenvectorUnitary_apply hY.1 i j,
      RCLike.ofReal_sub]
    ring
  have htr1 : (Mᴴ * (X - Y)).trace = (Wᴴ * Z).trace := by
    have hMstar : Mᴴ = V * Wᴴ * star U := by
      rw [hM]
      simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    calc (Mᴴ * (X - Y)).trace
        = (V * (Wᴴ * (star U * (X - Y)))).trace := by
            rw [hMstar]
            simp only [Matrix.mul_assoc]
      _ = (Wᴴ * (star U * (X - Y)) * V).trace := Matrix.trace_mul_comm V _
      _ = (Wᴴ * Z).trace := by simp only [Z, Matrix.mul_assoc]
  let L : Matrix n n 𝕜 :=
    t • (diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) * W) +
      (1 - t) • (W * diagonal (RCLike.ofReal ∘ hY.1.eigenvalues))
  have hL_entry (i j : n) :
      L i j = (((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) * W i j := by
    dsimp only [L]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Function.comp_apply, Function.comp_apply,
      RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_add,
      RCLike.ofReal_mul, RCLike.ofReal_mul]
    ring
  have htr2 : (Mᴴ * (t • (X * M) + (1 - t) • (M * Y))).trace = (Wᴴ * L).trace := by
    have hMstar : Mᴴ = V * Wᴴ * star U := by
      rw [hM]
      simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    have hXM : (Mᴴ * (X * M)).trace =
        (Wᴴ * (diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) * W)).trace := by
      have hprod : Wᴴ * (star U * (X * (U * (W * (star V * V))))) =
          Wᴴ * (diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) * W) := by
        rw [hVV, mul_one]
        have hmid : star U * (X * (U * W)) = (star U * X * U) * W := by
          simp only [Matrix.mul_assoc]
        rw [hmid, hXdiag]
      calc (Mᴴ * (X * M)).trace
          = (V * (Wᴴ * (star U * (X * (U * (W * star V)))))).trace := by
              rw [hMstar, hM]
              simp only [Matrix.mul_assoc]
        _ = (Wᴴ * (star U * (X * (U * (W * (star V * V)))))).trace := by
              rw [Matrix.trace_mul_comm V _]
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hprod]
    have hMY : (Mᴴ * (M * Y)).trace =
        (Wᴴ * (W * diagonal (RCLike.ofReal ∘ hY.1.eigenvalues))).trace := by
      have hprod : Wᴴ * (star U * (U * (W * (star V * (Y * V))))) =
          Wᴴ * (W * diagonal (RCLike.ofReal ∘ hY.1.eigenvalues)) := by
        have h1 : star U * (U * (W * (star V * (Y * V)))) =
            (star U * U) * (W * (star V * Y * V)) := by
          simp only [Matrix.mul_assoc]
        rw [h1, hUU, one_mul, hYdiag]
      calc (Mᴴ * (M * Y)).trace
          = (V * (Wᴴ * (star U * (U * (W * (star V * Y)))))).trace := by
              rw [hMstar, hM]
              simp only [Matrix.mul_assoc]
        _ = (Wᴴ * (star U * (U * (W * (star V * (Y * V)))))).trace := by
              rw [Matrix.trace_mul_comm V _]
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hprod]
    simp only [L, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, hXM, hMY]
  rw [liebLinearForm, htr1, htr2, ← frobenius_inner_eq_trace_conjTranspose_mul,
    ← frobenius_inner_eq_trace_conjTranspose_mul, frobenius_inner_eq_sum_conj_mul,
    frobenius_inner_eq_sum_conj_mul]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hZ_entry i j, hL_entry i j]
  have hnormW : RCLike.re (conj (W i j) *
      ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) * W i j)) =
      ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i) * ‖W i j‖ ^ 2 := by
    have hmul : conj (W i j) *
        ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) * W i j) =
        ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i) * ‖W i j‖ ^ 2 : ℝ) : 𝕜) := by
      calc conj (W i j) *
            ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) * W i j)
          = (((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i : ℝ) : 𝕜) *
              (W i j * conj (W i j)) := by ring
        _ = ((((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i) * ‖W i j‖ ^ 2 : ℝ) : 𝕜) := by
              rw [RCLike.mul_conj, RCLike.ofReal_mul, RCLike.ofReal_pow]
    rw [hmul, RCLike.ofReal_re]
  rw [hnormW]

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
  have hc : 0 < (1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i :=
    pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht
  have hle := two_mul_re_conj_mul_sub_le hc
    ((star (hX.1.eigenvectorUnitary : Matrix n n 𝕜) * M * hY.1.eigenvectorUnitary) i j)
    (((hX.1.eigenvalues i - hY.1.eigenvalues j : ℝ) : 𝕜) *
      ⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜)
  refine hle.trans_eq ?_
  rw [norm_ofReal_mul_sq]

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
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hW : star U * (U * W₀ * star V) * V = W₀ := by
    calc star U * (U * W₀ * star V) * V
        = (star U * U) * W₀ * (star V * V) := by simp only [Matrix.mul_assoc]
      _ = W₀ := by rw [hUU, hVV, one_mul, mul_one]
  rw [liebLinearForm_eq_sum hX hY t (U * W₀ * star V), perspectiveIntegrand]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hWij : (star (hX.1.eigenvectorUnitary : Matrix n n 𝕜) * (U * W₀ * star V) *
      hY.1.eigenvectorUnitary) i j = W₀ i j := congrArg (fun A : Matrix n n 𝕜 ↦ A i j) hW
  rw [hWij]
  simp only [W₀, of_apply]
  have hc : 0 < (1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i :=
    pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht
  rw [two_mul_re_conj_mul_sub_eq hc, norm_ofReal_mul_sq]

private theorem intervalIntegrable_one_sub_mul_perspectiveIntegrand {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - t) * perspectiveIntegrand hX hY t)
      MeasureTheory.volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuous_const.sub continuous_id).continuousOn.mul ?_
  unfold perspectiveIntegrand
  refine continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦ ?_
  refine continuousOn_const.div ?_ fun t ht ↦
    (pos_interp_of_mem_uIcc (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) ht).ne'
  exact (((continuous_const.sub continuous_id).mul continuous_const).add
    (continuous_id.mul continuous_const)).continuousOn

/-- Spectral integral representation of `Re Tr (X (log X - log Y))` for positive definite `X, Y`. -/
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
    simpa only [cfc_const_one ℝ Y hY.1.isSelfAdjoint, mul_one,
      cfc_id' ℝ X hX.1.isSelfAdjoint] using
      IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1 (fun x ↦ x) (fun _ ↦ 1)
  have hYtr : RCLike.re Y.trace = ∑ i, ∑ j, hY.1.eigenvalues j *
      ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    simpa only [cfc_const_one ℝ X hX.1.isSelfAdjoint, one_mul,
      cfc_id' ℝ Y hY.1.isSelfAdjoint] using
      IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1 (fun _ ↦ 1) (fun x ↦ x)
  have hint_ij (i j : n) :
      IntervalIntegrable
        (fun t : ℝ ↦ ((1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
          ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
            ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2)
        MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ((((continuous_const.sub continuous_id).mul continuous_const).continuousOn.div ?_
      fun t ht ↦ (pos_interp_of_mem_uIcc (hX.eigenvalues_pos i)
        (hY.eigenvalues_pos j) ht).ne').mul continuousOn_const)
    exact (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).continuousOn
  have hint_i (i : n) :
      IntervalIntegrable
        (fun t : ℝ ↦ ∑ j, ((1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
          ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
            ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2)
        MeasureTheory.volume 0 1 := by
    have hfn :
        (fun t : ℝ ↦ ∑ j, ((1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
          ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
            ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2) =
        ∑ j, fun t : ℝ ↦ ((1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
          ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
            ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
      ext t
      simp
    rw [hfn]
    exact IntervalIntegrable.sum Finset.univ fun j _ ↦ hint_ij i j
  have hsum_int :
      ∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX hY t =
        ∑ i, ∑ j, (∫ t in (0 : ℝ)..1,
          (1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
            ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
          ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
    have hcongr :
        (fun t : ℝ ↦ (1 - t) * perspectiveIntegrand hX hY t) =
          fun t : ℝ ↦ ∑ i, ∑ j, ((1 - t) * (hX.1.eigenvalues i - hY.1.eigenvalues j) ^ 2 /
            ((1 - t) * hY.1.eigenvalues j + t * hX.1.eigenvalues i)) *
              ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by
      funext t
      simp only [perspectiveIntegrand, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [hcongr, intervalIntegral.integral_finsetSum fun i _ ↦ hint_i i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_finsetSum fun j _ ↦ hint_ij i j]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact intervalIntegral.integral_mul_const _ _
  rw [hD, trace_sub, map_sub, IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1,
    IsHermitian.re_trace_cfc_mul_cfc hX.1 hY.1, trace_sub, map_sub, hXtr, hYtr, hsum_int,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hscalar := mul_log_sub_log_eq_add_integral (hX.eigenvalues_pos i) (hY.eigenvalues_pos j)
  calc hX.1.eigenvalues i * Real.log (hX.1.eigenvalues i) * 1 *
          ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 -
        hX.1.eigenvalues i * Real.log (hY.1.eigenvalues j) *
          ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2
      = (hX.1.eigenvalues i * (Real.log (hX.1.eigenvalues i) - Real.log (hY.1.eigenvalues j))) *
          ‖⟪hX.1.eigenvectorBasis i, hY.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 := by ring
    _ = _ := by
        rw [hscalar]
        ring

/-- **Joint convexity of quantum relative entropy** on positive definite matrices:
`(X, Y) ↦ Re Tr (X (log X - log Y))` is convex on `{X | X.PosDef} ×ˢ {Y | Y.PosDef}`. -/
theorem convexOn_re_trace_mul_cfc_log_sub_cfc_log :
    ConvexOn ℝ ({X : Matrix n n 𝕜 | X.PosDef} ×ˢ {Y : Matrix n n 𝕜 | Y.PosDef})
      (fun p ↦ RCLike.re (p.1 * (cfc Real.log p.1 - cfc Real.log p.2)).trace) := by
  have hconv_set :
      Convex ℝ ({X : Matrix n n 𝕜 | X.PosDef} ×ˢ {Y : Matrix n n 𝕜 | Y.PosDef}) :=
    TauCeti.convex_setOfPred_posDef.prod TauCeti.convex_setOfPred_posDef
  rw [convexOn_iff_forall_pos]
  refine ⟨hconv_set, ?_⟩
  rintro ⟨X₁, Y₁⟩ ⟨hX₁, hY₁⟩ ⟨X₂, Y₂⟩ ⟨hX₂, hY₂⟩ a b ha hb hab
  have hX : (a • X₁ + b • X₂).PosDef := (hX₁.smul ha).add (hX₂.smul hb)
  have hY : (a • Y₁ + b • Y₂).PosDef := (hY₁.smul ha).add (hY₂.smul hb)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [re_trace_mul_cfc_log_sub_eq_add_integral hX hY,
    re_trace_mul_cfc_log_sub_eq_add_integral hX₁ hY₁,
    re_trace_mul_cfc_log_sub_eq_add_integral hX₂ hY₂]
  have hlin_tr : RCLike.re ((a • X₁ + b • X₂) - (a • Y₁ + b • Y₂)).trace =
      a * RCLike.re (X₁ - Y₁).trace + b * RCLike.re (X₂ - Y₂).trace := by
    have hsub : (a • X₁ + b • X₂) - (a • Y₁ + b • Y₂) = a • (X₁ - Y₁) + b • (X₂ - Y₂) := by
      simp only [smul_sub]
      abel
    simp only [hsub, trace_add, trace_smul, map_add, RCLike.smul_re]
  have hint :
      ∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX hY t ≤
        a * (∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX₁ hY₁ t) +
          b * (∫ t in (0 : ℝ)..1, (1 - t) * perspectiveIntegrand hX₂ hY₂ t) := by
    have hi := intervalIntegrable_one_sub_mul_perspectiveIntegrand hX hY
    have hi₁ := intervalIntegrable_one_sub_mul_perspectiveIntegrand hX₁ hY₁
    have hi₂ := intervalIntegrable_one_sub_mul_perspectiveIntegrand hX₂ hY₂
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi₁.const_mul a) (hi₂.const_mul b)]
    refine intervalIntegral.integral_mono_on zero_le_one hi
      ((hi₁.const_mul a).add (hi₂.const_mul b)) fun t ht ↦ ?_
    have ht_uIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one]
    obtain ⟨M, hM⟩ := exists_liebLinearForm_eq_perspectiveIntegrand hX hY ht_uIcc
    have h1 := liebLinearForm_le_perspectiveIntegrand hX₁ hY₁ ht_uIcc M
    have h2 := liebLinearForm_le_perspectiveIntegrand hX₂ hY₂ ht_uIcc M
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht.2
    have hcomb : perspectiveIntegrand hX hY t ≤
        a * perspectiveIntegrand hX₁ hY₁ t + b * perspectiveIntegrand hX₂ hY₂ t := by
      rw [← hM, liebLinearForm_combo]
      nlinarith
    calc (1 - t) * perspectiveIntegrand hX hY t
        ≤ (1 - t) * (a * perspectiveIntegrand hX₁ hY₁ t + b * perspectiveIntegrand hX₂ hY₂ t) :=
          mul_le_mul_of_nonneg_left hcomb h1t
      _ = a * ((1 - t) * perspectiveIntegrand hX₁ hY₁ t) +
            b * ((1 - t) * perspectiveIntegrand hX₂ hY₂ t) := by ring
  linarith

end RelativeEntropyConvexity

section LiebConcavity

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Gibbs variational bound.** For positive definite `ρ`, arbitrary `A`, and Hermitian `B`,
`Re Tr ρ + Re Tr (ρ B) - Re Tr (ρ (log ρ - log A)) ≤ Re Tr (exp (B + log A))`. -/
theorem PosDef.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log
    {ρ B : Matrix n n 𝕜} (hρ : ρ.PosDef) (A : Matrix n n 𝕜) (hB : B.IsHermitian) :
    RCLike.re ρ.trace + RCLike.re (ρ * B).trace -
        RCLike.re (ρ * (cfc Real.log ρ - cfc Real.log A)).trace ≤
      RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace := by
  have hlogA : (cfc Real.log A).IsHermitian := isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hH : (B + cfc Real.log A).IsHermitian := hB.add hlogA
  set σ : Matrix n n 𝕜 := NormedSpace.exp (B + cfc Real.log A)
  have hσ : σ.PosDef := hH.posDef_exp
  have hklein := hρ.posSemidef.re_trace_sub_trace_le_relativeEntropy hσ.posSemidef
  rw [relativeEntropy_of_posDef hσ, EReal.coe_le_coe_iff, hH.cfc_log_exp] at hklein
  have hsub : ρ * (cfc Real.log ρ - (B + cfc Real.log A)) =
      ρ * (cfc Real.log ρ - cfc Real.log A) - ρ * B := by
    simp only [Matrix.mul_sub, Matrix.mul_add]
    abel
  rw [hsub, trace_sub, map_sub, map_sub] at hklein
  linarith

/-- Equality in the Gibbs variational bound is attained at `ρ = exp (B + log A)`. -/
private theorem re_trace_exp_add_cfc_log_eq_variational (A : Matrix n n 𝕜) {B : Matrix n n 𝕜}
    (hB : B.IsHermitian) :
    let σ := NormedSpace.exp (B + cfc Real.log A)
    RCLike.re σ.trace + RCLike.re (σ * B).trace -
        RCLike.re (σ * (cfc Real.log σ - cfc Real.log A)).trace =
      RCLike.re σ.trace := by
  intro σ
  have hlogA : (cfc Real.log A).IsHermitian := isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hH : (B + cfc Real.log A).IsHermitian := hB.add hlogA
  have hlogσ : cfc Real.log σ = B + cfc Real.log A := hH.cfc_log_exp
  rw [hlogσ, add_sub_cancel_right]
  ring

/-- **Lieb's concavity theorem.** For every Hermitian matrix `B`, the map
`A ↦ Re Tr (exp (B + log A))` is concave on the positive definite cone `{A | A.PosDef}`. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      (fun A ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace) := by
  rw [concaveOn_iff_forall_pos]
  refine ⟨TauCeti.convex_setOfPred_posDef, ?_⟩
  intro A₁ hA₁ A₂ hA₂ a b ha hb hab
  have hlogA₁ : (cfc Real.log A₁).IsHermitian := isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hlogA₂ : (cfc Real.log A₂).IsHermitian := isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  set ρ₁ : Matrix n n 𝕜 := NormedSpace.exp (B + cfc Real.log A₁)
  set ρ₂ : Matrix n n 𝕜 := NormedSpace.exp (B + cfc Real.log A₂)
  have hρ₁ : ρ₁.PosDef := (hB.add hlogA₁).posDef_exp
  have hρ₂ : ρ₂.PosDef := (hB.add hlogA₂).posDef_exp
  have hρ : (a • ρ₁ + b • ρ₂).PosDef := (hρ₁.smul ha).add (hρ₂.smul hb)
  have hD := (convexOn_iff_forall_pos.1
    (convexOn_re_trace_mul_cfc_log_sub_cfc_log (n := n) (𝕜 := 𝕜))).2
    (x := (ρ₁, A₁)) ⟨hρ₁, hA₁⟩ (y := (ρ₂, A₂)) ⟨hρ₂, hA₂⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hD ⊢
  have htrρ :
      RCLike.re (a • ρ₁ + b • ρ₂).trace = a * RCLike.re ρ₁.trace + b * RCLike.re ρ₂.trace := by
    simp [trace_add, trace_smul, RCLike.smul_re]
  have htrρB : RCLike.re ((a • ρ₁ + b • ρ₂) * B).trace =
      a * RCLike.re (ρ₁ * B).trace + b * RCLike.re (ρ₂ * B).trace := by
    simp [Matrix.add_mul, trace_add, trace_smul, RCLike.smul_re]
  have heq₁ : RCLike.re ρ₁.trace + RCLike.re (ρ₁ * B).trace -
      RCLike.re (ρ₁ * (cfc Real.log ρ₁ - cfc Real.log A₁)).trace = RCLike.re ρ₁.trace :=
    re_trace_exp_add_cfc_log_eq_variational A₁ hB
  have heq₂ : RCLike.re ρ₂.trace + RCLike.re (ρ₂ * B).trace -
      RCLike.re (ρ₂ * (cfc Real.log ρ₂ - cfc Real.log A₂)).trace = RCLike.re ρ₂.trace :=
    re_trace_exp_add_cfc_log_eq_variational A₂ hB
  have hvar :=
    hρ.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log (a • A₁ + b • A₂) hB
  nlinarith

/-- For `ε > 0`, Lieb's concavity holds on the closed shifted cone `{A | (A - ε • 1).PosSemidef}`,
every member of which is positive definite. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log_posSemidef_sub_smul_one
    {B : Matrix n n 𝕜} (hB : B.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | (A - ε • 1).PosSemidef}
      (fun A ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace) := by
  have hsub : {A : Matrix n n 𝕜 | (A - ε • 1).PosSemidef} ⊆ {A : Matrix n n 𝕜 | A.PosDef} := by
    intro A hA
    have h1 : (ε • (1 : Matrix n n 𝕜)).PosDef := Matrix.PosDef.one.smul hε
    simpa [sub_add_cancel] using PosDef.posSemidef_add hA h1
  have hconv : Convex ℝ {A : Matrix n n 𝕜 | (A - ε • 1).PosSemidef} := by
    intro A₁ hA₁ A₂ hA₂ a b ha hb hab
    have hlin : (a • A₁ + b • A₂) - ε • (1 : Matrix n n 𝕜) =
        a • (A₁ - ε • 1) + b • (A₂ - ε • 1) := by
      calc (a • A₁ + b • A₂) - ε • (1 : Matrix n n 𝕜)
          = (a • A₁ + b • A₂) - (a + b) • (ε • 1) := by rw [hab, one_smul]
        _ = a • (A₁ - ε • 1) + b • (A₂ - ε • 1) := by
            rw [add_smul, smul_sub, smul_sub]
            abel
    -- Unfold set-builder membership so `rw [hlin]` rewrites the shifted matrix inside `PosSemidef`.
    change ((a • A₁ + b • A₂) - ε • 1).PosSemidef
    rw [hlin]
    exact (hA₁.smul ha).add (hA₂.smul hb)
  exact hB.concaveOn_re_trace_exp_add_cfc_log.subset hsub hconv

end LiebConcavity

end Matrix
