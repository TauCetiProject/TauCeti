/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.PSeries
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.CotlarStein
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint
import TauCeti.Topology.Algebra.InfiniteSum.PiProd

/-!
# The Calderón–Vaillancourt theorem

Let `a` be a symbol of order `0` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Its left quantization
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.quantizeSchwartzValue`) extends
from Schwartz functions to a bounded operator on `L²(ℝⁿ)`. Unlike the Sobolev mapping theorem for
symbols with compact spatial support (`TauCeti.Symbol.exists_quantizeSobolev`), no support
condition in the position is needed, so this covers symbols such as `a(x, ξ) = b(x)` with `b`
bounded together with all its derivatives, or classical symbols with bounded coefficients.

## Main results

* `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`: for complex Hilbert spaces `V` and `W`, a
  bounded operator `T : L²(ℝⁿ; V) → L²(ℝⁿ; W)` with `T u = Op(a) u` almost everywhere for every
  Schwartz function `u`.
* `TauCeti.Symbol.exists_quantizeUniformOrderZero`: for finite-dimensional `V` and `W`, the same
  statement on the Bessel-potential space `H⁰ = L²`, in the form of
  `TauCeti.Symbol.exists_quantizeSobolev`.

## Proof

The symbol is cut into pieces localized at unit scale both in the position and in the frequency:
for the smooth partition of unity `∑_{j ∈ ℤⁿ} χ(x - j) = 1` by integer translates of
`χ = TauCeti.latticeBump n`, the piece at `ν = (j, k) ∈ ℤⁿ × ℤⁿ` is the integral operator `G_ν` on
`L²` with the bounded, compactly supported kernel `𝐞⟪ζ, x⟫ χ(x - j) χ(ζ - k) a(x, 2πζ)`, and
`G_ν ∘ 𝓕` is the quantization of `χ(x - j) χ(ξ / 2π - k) a(x, ξ)`. The kernel of `G_ν† G_μ` is,
up to the cut-offs in the frequency, the Fourier transform in the position of
`χ(x - j) χ(x - j') a(x, 2πζ')† a(x, 2πζ)`. It vanishes unless the cells of `j` and `j'` are
neighbours, and integrating by parts `4n` times in the position
(`TauCeti.one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset`) shows that it decays like
`(1 + |k - k'|)^(-4n)`. Symmetrically the kernel of `G_ν G_μ†` is a Fourier transform in the
frequency, vanishes unless the frequency cells are neighbours, and decays in `j - j'`. By Schur's
test both operator norms are at most `C ∏ᵢ (1 + |jᵢ - j'ᵢ|)⁻⁴ (1 + |kᵢ - k'ᵢ|)⁻⁴`, whose square root
is summable over `ℤⁿ × ℤⁿ`. The Cotlar–Stein lemma
(`TauCeti.exists_hasSum_apply_of_almost_orthogonal`) then sums the pieces to a bounded operator
on `L²`, and at every point the pieces of the quantization integral sum to `Op(a) u`, which
identifies the two
(`MeasureTheory.Lp.ae_eq_of_hasSum_of_ae_hasSum`).

Only the derivatives of order at most `4n` in the position and in the frequency separately
enter, and their decay in the frequency is not used: this is the argument for the class
`S⁰_{0,0}`, which contains the uniform symbols of order `0`.

## References

* A. P. Calderón and R. Vaillancourt, *On the boundedness of pseudo-differential operators*,
  J. Math. Soc. Japan **23** (1971), 374–378.
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VII, §2.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.1).
-/

public section

open scoped SchwartzMap FourierTransform RealInnerProductSpace ENNReal NNReal ContDiff
  BesselPotentialSpace
open MeasureTheory Real Finset ContinuousLinearMap Metric

noncomputable section

namespace TauCeti

/-! ### The lattice weights -/

/-- The weight `∏ᵢ (1 + |dᵢ|)⁻²` on `ℤⁿ`, which is summable. -/
private def latticeWeight {n : ℕ} (d : Fin n → ℤ) : ℝ :=
  ∏ i, ((1 + |(d i : ℝ)|) ^ 2)⁻¹

private theorem latticeWeight_nonneg {n : ℕ} (d : Fin n → ℤ) : 0 ≤ latticeWeight d :=
  prod_nonneg fun _ _ ↦ by positivity

private theorem summable_latticeWeight {n : ℕ} : Summable (latticeWeight (n := n)) := by
  refine summable_prod_pi_of_nonneg (ι := Fin n) (f := fun m : ℤ ↦ ((1 + |(m : ℝ)|) ^ 2)⁻¹) ?_
    fun m ↦ by positivity
  rw [summable_int_iff_summable_nat_and_neg]
  have h : Summable fun m : ℕ ↦ (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  have e : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ = ((1 + |((m : ℤ) : ℝ)|) ^ 2)⁻¹ := fun m ↦ by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m), Nat.cast_succ, add_comm]
  have e' : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ = ((1 + |((-(m : ℤ) : ℤ) : ℝ)|) ^ 2)⁻¹ :=
    fun m ↦ by rw [Int.cast_neg, abs_neg, ← e]
  exact ⟨h.congr e, h.congr e'⟩

/-- Two lattice indices `j, j'` whose coordinates differ by at most one have weight at least
`16⁻ⁿ`. -/
private theorem one_le_latticeWeight_sq {n : ℕ} {d : Fin n → ℤ} (hd : ∀ i, |d i| ≤ 1) :
    1 ≤ 16 ^ n * latticeWeight d ^ 2 := by
  have h : ∀ i, (16 : ℝ)⁻¹ ≤ (((1 + |(d i : ℝ)|) ^ 2)⁻¹) ^ 2 := fun i ↦ by
    have : |(d i : ℝ)| ≤ 1 := by exact_mod_cast hd i
    rw [inv_pow, ← pow_mul]
    calc (16 : ℝ)⁻¹ = (2 ^ (2 * 2))⁻¹ := by norm_num
      _ ≤ ((1 + |(d i : ℝ)|) ^ (2 * 2))⁻¹ := by gcongr; linarith
  have : (16 : ℝ)⁻¹ ^ n ≤ latticeWeight d ^ 2 := by
    rw [latticeWeight, ← prod_pow, ← Fin.prod_const]
    exact prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ h i
  rw [inv_pow] at this
  have h16 : (0 : ℝ) < 16 ^ n := by positivity
  calc 1 = 16 ^ n * (16 ^ n)⁻¹ := (mul_inv_cancel₀ h16.ne').symm
    _ ≤ 16 ^ n * latticeWeight d ^ 2 := by gcongr

/-- Decay at distance `‖x - y‖` between points of the unit cells of `j` and `j'` controls the
lattice weight of `j - j'`. -/
private theorem inv_one_add_norm_pow_le {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    {j j' : Fin n → ℤ} (hx : x ∈ closedBall (latticePoint j) √n)
    (hy : y ∈ closedBall (latticePoint j') √n) :
    ((1 + ‖x - y‖) ^ (4 * n))⁻¹ ≤ (1 + 2 * √n) ^ (4 * n) * latticeWeight (j - j') ^ 2 := by
  set d := j - j'
  have hd : 1 + ‖latticePoint d‖ ≤ (1 + 2 * √n) * (1 + ‖x - y‖) := by
    rw [mem_closedBall, dist_eq_norm] at hx hy
    have : latticePoint d = (x - y) - (x - latticePoint j) + (y - latticePoint j') := by
      rw [latticePoint_sub]; abel
    have h := norm_add₃_le (a := x - y) (b := -(x - latticePoint j)) (c := y - latticePoint j')
    rw [norm_neg, ← sub_eq_add_neg, ← this] at h
    nlinarith [norm_nonneg (x - y), Real.sqrt_nonneg n]
  have hcoord : ∀ i, 1 + |(d i : ℝ)| ≤ 1 + ‖latticePoint d‖ := fun i ↦ by
    have := PiLp.norm_apply_le (latticePoint d) i
    simpa using this
  have hprod : ∏ i, (1 + |(d i : ℝ)|) ^ 4 ≤ (1 + ‖latticePoint d‖) ^ (4 * n) := by
    rw [pow_mul, ← Fin.prod_const]
    exact prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ by gcongr; simpa using hcoord i
  have hw : latticeWeight d ^ 2 = (∏ i, (1 + |(d i : ℝ)|) ^ 4)⁻¹ := by
    rw [latticeWeight, ← prod_pow, ← prod_inv_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [inv_pow, ← pow_mul]
  have hpos : 0 < ∏ i, (1 + |(d i : ℝ)|) ^ 4 := prod_pos fun _ _ ↦ by positivity
  rw [hw]
  calc ((1 + ‖x - y‖) ^ (4 * n))⁻¹
      = (1 + 2 * √n) ^ (4 * n) * (((1 + 2 * √n) * (1 + ‖x - y‖)) ^ (4 * n))⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ (1 + 2 * √n) ^ (4 * n) * ((1 + ‖latticePoint d‖) ^ (4 * n))⁻¹ := by
        gcongr
    _ ≤ (1 + 2 * √n) ^ (4 * n) * (∏ i, (1 + |(d i : ℝ)|) ^ 4)⁻¹ := by
        gcongr
/-! ### The unit cells -/

/-- The volume of the closed ball of radius `√n` in `ℝⁿ`, which contains the support of
`latticeBump n`. -/
private def cellVolume (n : ℕ) : ℝ≥0 :=
  (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) √n)).toNNReal

private theorem volume_closedBall_eq_cellVolume {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) :
    volume (closedBall c √n) = cellVolume n := by
  rw [cellVolume, Measure.addHaar_closedBall_center, ENNReal.coe_toNNReal
    measure_closedBall_lt_top.ne]

/-- The row and column integrals of a kernel bounded by `c` and supported in the product of the
cells of `j` and `k`. -/
private theorem ae_lintegral_enorm_le_of_cell {n : ℕ} {Y Z : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → Y →L[ℂ] Z} {c : ℝ≥0}
    {j k : Fin n → ℤ}
    (hsupp : ∀ x y, K x y ≠ 0 →
      x ∈ closedBall (latticePoint j) √n ∧ y ∈ closedBall (latticePoint k) √n)
    (hc : ∀ x y, ‖K x y‖ ≤ c) :
    (∀ᵐ x ∂volume, ∫⁻ y, ‖K x y‖ₑ ≤ ↑(c * cellVolume n)) ∧
      ∀ᵐ y ∂volume, ∫⁻ x, ‖K x y‖ₑ ≤ ↑(c * cellVolume n) := by
  have h : ∀ x y, ‖K x y‖ₑ ≤ (closedBall (latticePoint j) √n).indicator
      (fun _ ↦ (closedBall (latticePoint k) √n).indicator (fun _ ↦ (c : ℝ≥0∞)) y) x := by
    intro x y
    by_cases hK : K x y = 0
    · rw [hK, enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero]
      exact zero_le
    obtain ⟨hx, hy⟩ := hsupp x y hK
    simpa [hx, hy, enorm_le_coe, ← NNReal.coe_le_coe] using hc x y
  refine ⟨.of_forall fun x ↦ ?_, .of_forall fun y ↦ ?_⟩
  · refine (lintegral_enorm_row_le_of_le_indicator measurableSet_closedBall h x).trans_eq ?_
    rw [volume_closedBall_eq_cellVolume, ENNReal.coe_mul]
  · refine (lintegral_enorm_column_le_of_le_indicator measurableSet_closedBall h y).trans_eq ?_
    rw [volume_closedBall_eq_cellVolume, ENNReal.coe_mul]

/-- The weight `∏ᵢ (1 + |jᵢ|)⁻² (1 + |kᵢ|)⁻²` of a pair of lattice displacements. -/
private def pairWeight {n : ℕ} (d : (Fin n → ℤ) × (Fin n → ℤ)) : ℝ :=
  latticeWeight d.1 * latticeWeight d.2

private theorem pairWeight_nonneg {n : ℕ} (d : (Fin n → ℤ) × (Fin n → ℤ)) : 0 ≤ pairWeight d :=
  mul_nonneg (latticeWeight_nonneg _) (latticeWeight_nonneg _)

private theorem summable_pairWeight {n : ℕ} : Summable (pairWeight (n := n)) :=
  summable_latticeWeight.mul_of_nonneg summable_latticeWeight latticeWeight_nonneg
    latticeWeight_nonneg

/-- A bound decaying like `(1 + ‖x - y‖)^(-4n)` for `x, y` in the cells of `k, k'`, for cells
`j, j'` that are neighbours, is a multiple of the square of the weight of `(j - j', k - k')`. -/
private theorem le_mul_latticeWeight_sq {n : ℕ} {K F₀ : ℝ} (hK : 0 ≤ K) {j j' k k' : Fin n → ℤ}
    {x y : EuclideanSpace ℝ (Fin n)} (hj : ∀ i, |(j - j') i| ≤ 1)
    (hx : x ∈ closedBall (latticePoint k) √n) (hy : y ∈ closedBall (latticePoint k') √n)
    (hF : F₀ ≤ K * ((1 + ‖x - y‖) ^ (4 * n))⁻¹) :
    F₀ ≤ K * ((1 + 2 * √n) ^ (4 * n) * 16 ^ n) *
      (latticeWeight (j - j') * latticeWeight (k - k')) ^ 2 := by
  have h1 := one_le_latticeWeight_sq hj
  have h2 := inv_one_add_norm_pow_le hx hy
  calc F₀ ≤ K * ((1 + 2 * √n) ^ (4 * n) * latticeWeight (k - k') ^ 2) :=
        hF.trans (mul_le_mul_of_nonneg_left h2 hK)
    _ ≤ K * ((1 + 2 * √n) ^ (4 * n) * latticeWeight (k - k') ^ 2) *
          (16 ^ n * latticeWeight (j - j') ^ 2) :=
        le_mul_of_one_le_right (by positivity) h1
    _ = _ := by ring

/-- The constant in the almost-orthogonality estimates for the phase-space pieces. -/
private def pieceConst (n : ℕ) (Cχ C : ℝ) : ℝ :=
  2 ^ (4 * n) * (4 ^ (4 * n) * (2 ^ (4 * n) * (Cχ * Cχ) * (C * C)) * cellVolume n) *
    ((1 + 2 * √n) ^ (4 * n) * 16 ^ n)

private theorem pieceConst_nonneg (n : ℕ) (Cχ C : ℝ) : 0 ≤ pieceConst n Cχ C := by
  unfold pieceConst
  have := mul_self_nonneg Cχ
  have := mul_self_nonneg C
  positivity

/-- **Fourier decay of a cut-off product.** If `f` and `g` have derivatives of order at most
`N = 4n` bounded by `C`, then the Fourier transform of
`x ↦ χ(x - j) χ(x - j') • B (f x) (g x)` decays like `(1 + ‖w‖)^(-N)`, with a constant
depending only on `C`, on `n` and on a bound `Cχ` for the derivatives of `χ = latticeBump n`. -/
private theorem norm_fourier_cutoff_bilinear_le {n : ℕ} {F G U : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup U]
    [NormedSpace ℂ U] (B : F →L[ℝ] G →L[ℝ] U) (hB : ‖B‖ ≤ 1)
    {f : EuclideanSpace ℝ (Fin n) → F} {g : EuclideanSpace ℝ (Fin n) → G}
    (hf : ContDiff ℝ (4 * n) f) (hg : ContDiff ℝ (4 * n) g) {Cχ C : ℝ}
    (hχ : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p (latticeBump n) x‖ ≤ Cχ)
    (hfC : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p f x‖ ≤ C)
    (hgC : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p g x‖ ≤ C) (j j' : Fin n → ℤ)
    (w : EuclideanSpace ℝ (Fin n)) :
    ‖𝓕 (fun x ↦ (latticeBump n (x - latticePoint j) * latticeBump n (x - latticePoint j')) •
      B (f x) (g x)) w‖ ≤
      2 ^ (4 * n) * (4 ^ (4 * n) * (2 ^ (4 * n) * (Cχ * Cχ) * (C * C)) * cellVolume n) *
        ((1 + ‖w‖) ^ (4 * n))⁻¹ := by
  set N := 4 * n
  have hχ' : ∀ c : EuclideanSpace ℝ (Fin n), ∀ p ≤ N, ∀ x,
      ‖iteratedFDeriv ℝ p (fun y ↦ latticeBump n (y - c)) x‖ ≤ Cχ := fun c p hp x ↦ by
    rw [iteratedFDeriv_comp_sub]; exact hχ p hp _
  have hφ : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv ℝ p
      (fun y ↦ latticeBump n (y - latticePoint j) * latticeBump n (y - latticePoint j')) x‖ ≤
        2 ^ p * (Cχ * Cχ) := fun p hp x ↦ by
    have := (mul ℝ ℝ).norm_iteratedFDeriv_le_two_pow_mul_of_bilinear (opNorm_mul_le ℝ ℝ)
      (contDiff_latticeBump.comp (contDiff_id.sub contDiff_const))
      (contDiff_latticeBump.comp (contDiff_id.sub contDiff_const))
      (hχ' (latticePoint j)) (hχ' (latticePoint j')) hp x
    simpa only [mul_apply', Function.comp_def, id] using this
  have hφ' : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv ℝ p
      (fun y ↦ latticeBump n (y - latticePoint j) * latticeBump n (y - latticePoint j')) x‖ ≤
        2 ^ N * (Cχ * Cχ) := fun p hp x ↦ (hφ p hp x).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hp) (mul_self_nonneg Cχ))
  have hcont : ContDiff ℝ N (fun y ↦ latticeBump n (y - latticePoint j) *
      latticeBump n (y - latticePoint j')) :=
    (contDiff_latticeBump.comp (contDiff_id.sub contDiff_const)).mul
      (contDiff_latticeBump.comp (contDiff_id.sub contDiff_const))
  have hsupp : tsupport (fun x ↦ (latticeBump n (x - latticePoint j) *
      latticeBump n (x - latticePoint j')) • B (f x) (g x)) ⊆ closedBall (latticePoint j) √n :=
    closure_minimal (fun x hx ↦ mem_closedBall_of_latticeBump_sub_ne_zero
      (left_ne_zero_of_mul (left_ne_zero_of_smul hx))) isClosed_closedBall
  -- The derivatives of `B (f x) (g x)`, and then of its product with the cut-off, are bounded.
  have hBfg : ∀ q ≤ N, ∀ y, ‖iteratedFDeriv ℝ q (fun y ↦ B (f y) (g y)) y‖ ≤ 2 ^ N * (C * C) :=
    fun q hq y ↦ (B.norm_iteratedFDeriv_le_two_pow_mul_of_bilinear hB hf hg hfC hgC hq y).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hq) (mul_self_nonneg C))
  have hsmul : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv ℝ p (fun y ↦ (latticeBump n (y - latticePoint j) *
      latticeBump n (y - latticePoint j')) • B (f y) (g y)) x‖ ≤
        4 ^ N * (2 ^ N * (Cχ * Cχ) * (C * C)) := fun p hp x ↦ by
    have h := (lsmul ℝ ℝ).norm_iteratedFDeriv_le_two_pow_mul_of_bilinear opNorm_lsmul_le hcont
      ((B.contDiff.comp hf).clm_apply hg) hφ' hBfg hp x
    simp only [lsmul_apply] at h
    have := mul_self_nonneg Cχ
    have := mul_self_nonneg C
    refine h.trans ?_
    calc 2 ^ p * (2 ^ N * (Cχ * Cχ) * (2 ^ N * (C * C)))
        ≤ 2 ^ N * (2 ^ N * (Cχ * Cχ) * (2 ^ N * (C * C))) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hp) (by positivity)
      _ = 4 ^ N * (2 ^ N * (Cχ * Cχ) * (C * C)) := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
  have h := one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset
    (hcont.smul ((B.contDiff.comp hf).clm_apply hg)) measurableSet_closedBall
    measure_closedBall_lt_top.ne hsupp hsmul w
  rw [Measure.real, volume_closedBall_eq_cellVolume, ENNReal.coe_toReal] at h
  have hpos : 0 < (1 + ‖w‖) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos, mul_comm]
  exact h

/-! ### The real-bilinear compositions with an adjoint -/

section Bilinear

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The real-bilinear map `(S, T) ↦ S† ∘ T`. -/
private def adjointCompL : (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] V) :=
  (bilinearRestrictScalars ℝ (compL ℂ V W V)).comp adjointRealCLM

private theorem adjointCompL_apply (S T : V →L[ℂ] W) : adjointCompL S T = adjoint S ∘L T := by
  simp [adjointCompL]

private theorem norm_adjointCompL_apply_le (S T : V →L[ℂ] W) :
    ‖adjointCompL S T‖ ≤ 1 * ‖S‖ * ‖T‖ := by
  rw [adjointCompL_apply, one_mul, ← LinearIsometryEquiv.norm_map adjoint S]
  exact opNorm_comp_le _ _

/-- The real-bilinear map `(T, S) ↦ S ∘ T†`. -/
private def compAdjointL : (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (W →L[ℂ] W) :=
  (bilinearRestrictScalars ℝ (compL ℂ W V W)).flip.comp adjointRealCLM

private theorem compAdjointL_apply (T S : V →L[ℂ] W) : compAdjointL T S = S ∘L adjoint T := by
  simp [compAdjointL]

private theorem norm_compAdjointL_apply_le (T S : V →L[ℂ] W) :
    ‖compAdjointL T S‖ ≤ 1 * ‖T‖ * ‖S‖ := by
  rw [compAdjointL_apply, one_mul, mul_comm, ← LinearIsometryEquiv.norm_map adjoint T]
  exact opNorm_comp_le _ _

end Bilinear

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### Derivative bounds for uniform symbols of order zero -/

omit [CompleteSpace V] [CompleteSpace W] in
/-- A uniform symbol of order `0` has bounded derivatives of every order in the position and in
the frequency separately. -/
private theorem IsUniform.exists_norm_iteratedFDeriv_le {a : Symbol n V W 0} (ha : a.IsUniform)
    (N : ℕ) : ∃ C, ∀ p ≤ N, ∀ x ξ,
      ‖iteratedFDeriv ℝ p (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ p (fun η ↦ a.coefficient (x, η)) ξ‖ ≤ C := by
  choose B hB0 hB using isUniform_iff.1 ha
  set S : ℕ → ℝ := fun p ↦ ∑ r : Fin p → Fin n, (B (List.ofFn r) [] + B [] (List.ofFn r))
  have hS0 : ∀ p, 0 ≤ S p := fun p ↦ sum_nonneg fun r _ ↦ add_nonneg (hB0 _ _) (hB0 _ _)
  refine ⟨∑ p ∈ range (N + 1), S p, fun p hp x ξ ↦ ?_⟩
  have hle : S p ≤ ∑ p ∈ range (N + 1), S p :=
    single_le_sum (fun q _ ↦ hS0 q) (mem_range.2 (Nat.lt_succ_of_le hp))
  constructor
  · have hc : ContDiff ℝ ∞ fun y ↦ a.coefficient (y, ξ) :=
      a.contDiff_coefficient.comp (contDiff_id.prodMk contDiff_const)
    refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (contDiff_infty.1 hc p) x).trans
      (le_trans (sum_le_sum fun r _ ↦ ?_) hle)
    have h := hB (List.ofFn r) [] x ξ
    simp only [mixedDeriv_def, coordinateDeriv_nil, List.length_nil, CharP.cast_eq_zero,
      sub_self, zero_div, rpow_zero, mul_one] at h
    exact h.trans (le_add_of_nonneg_right (hB0 _ _))
  · have hc : ContDiff ℝ ∞ fun η ↦ a.coefficient (x, η) :=
      a.contDiff_coefficient.comp (contDiff_const.prodMk contDiff_id)
    refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (contDiff_infty.1 hc p) ξ).trans
      (le_trans (sum_le_sum fun r _ ↦ ?_) hle)
    have h := hB [] (List.ofFn r) x ξ
    simp only [mixedDeriv_def, coordinateDeriv_nil] at h
    refine (h.trans ?_).trans (le_add_of_nonneg_left (hB0 _ _))
    refine mul_le_of_le_one_right (hB0 _ _) (rpow_le_one_of_one_le_of_nonpos ?_ ?_)
    · nlinarith [sq_nonneg ‖ξ‖]
    · rw [List.length_ofFn]; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]

/-- Rescaling the variable by `2π` multiplies the bounds for the derivatives of order at most
`N` by at most `(2π) ^ N`. -/
private theorem norm_iteratedFDeriv_comp_two_pi_smul_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {N : ℕ} {f : CoordinateSpace n → F} (hf : ContDiff ℝ ∞ f) {C : ℝ}
    (hC : ∀ p ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ p f ξ‖ ≤ C) {p : ℕ} (hp : p ≤ N)
    (ζ : CoordinateSpace n) :
    ‖iteratedFDeriv ℝ p (fun ζ ↦ f ((2 * π) • ζ)) ζ‖ ≤ (2 * π) ^ N * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
  set L : CoordinateSpace n →L[ℝ] CoordinateSpace n := (2 * π) • ContinuousLinearMap.id ℝ _
    with hLdef
  have hL : ‖L‖ ≤ 2 * π :=
    calc ‖L‖ ≤ ‖2 * π‖ * ‖ContinuousLinearMap.id ℝ (CoordinateSpace n)‖ := by
          rw [hLdef]; exact norm_smul_le (2 * π) (ContinuousLinearMap.id ℝ (CoordinateSpace n))
      _ ≤ 2 * π * 1 := by
          rw [Real.norm_of_nonneg two_pi_pos.le]
          exact mul_le_mul_of_nonneg_left norm_id_le two_pi_pos.le
      _ = 2 * π := mul_one _
  have hfun : (fun ζ ↦ f ((2 * π) • ζ)) = f ∘ L := by
    ext ζ; simp [L]
  rw [hfun, L.iteratedFDeriv_comp_right hf ζ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [prod_const, card_univ, Fintype.card_fin, mul_comm]
  have h2π : 1 ≤ 2 * π := by linarith [two_le_pi]
  calc ‖L‖ ^ p * ‖iteratedFDeriv ℝ p f (L ζ)‖ ≤ (2 * π) ^ p * C := by
        gcongr
        exact hC p hp _
    _ ≤ (2 * π) ^ N * C := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2π hp) hC0

/-! ### The phase-space pieces -/

/-- The kernel `𝐞⟪ζ, x⟫ χ(x - j) χ(ζ - k) a(x, 2πζ)` of the phase-space piece of `a` at
`ν = (j, k)`, for `χ = latticeBump n`. It is supported in the product of the cells of `j` in
position and of `k` in frequency, and integrating it against `𝓕 u` gives the part of `Op(a) u`
localized there. -/
private def pieceKernel (a : Symbol n V W 0) (ν : (Fin n → ℤ) × (Fin n → ℤ))
    (x ζ : CoordinateSpace n) : V →L[ℂ] W :=
  𝐞 ⟪ζ, x⟫ • ((latticeBump n (x - latticePoint ν.1) * latticeBump n (ζ - latticePoint ν.2)) •
    a.coefficient (x, (2 * π) • ζ))

omit [CompleteSpace V] [CompleteSpace W] in
private theorem continuous_pieceKernel (a : Symbol n V W 0) (ν : (Fin n → ℤ) × (Fin n → ℤ)) :
    Continuous (Function.uncurry (pieceKernel a ν)) :=
  ((Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).smul
    ((((contDiff_latticeBump (k := 0)).continuous.comp (continuous_fst.sub continuous_const)).mul
      ((contDiff_latticeBump (k := 0)).continuous.comp (continuous_snd.sub continuous_const))).smul
        (a.contDiff_coefficient.continuous.comp
          (continuous_fst.prodMk (continuous_snd.const_smul (2 * π))))))

omit [CompleteSpace V] [CompleteSpace W] in
private theorem pieceKernel_ne_zero {a : Symbol n V W 0} {ν : (Fin n → ℤ) × (Fin n → ℤ)}
    {x ζ : CoordinateSpace n} (h : pieceKernel a ν x ζ ≠ 0) :
    x ∈ closedBall (latticePoint ν.1) √n ∧ ζ ∈ closedBall (latticePoint ν.2) √n := by
  have h' := right_ne_zero_of_smul h
  have h'' := left_ne_zero_of_smul h'
  exact ⟨mem_closedBall_of_latticeBump_sub_ne_zero (left_ne_zero_of_mul h''),
    mem_closedBall_of_latticeBump_sub_ne_zero (right_ne_zero_of_mul h'')⟩

omit [CompleteSpace V] [CompleteSpace W] in
private theorem norm_pieceKernel_le {a : Symbol n V W 0} {C : ℝ}
    (hC : ∀ p, ‖a.coefficient p‖ ≤ C) (ν : (Fin n → ℤ) × (Fin n → ℤ))
    (x ζ : CoordinateSpace n) : ‖pieceKernel a ν x ζ‖ ≤ C := by
  rw [pieceKernel, Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_latticeBump_mul_le _ _)).trans (hC _)

/-! ### The kernels of the products of two pieces -/

private theorem adjoint_pieceKernel_comp_pieceKernel (a : Symbol n V W 0)
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) (x ζ' ζ : CoordinateSpace n) :
    adjoint (pieceKernel a ν x ζ') ∘L pieceKernel a μ x ζ =
      ((latticeBump n (ζ' - latticePoint ν.2) * latticeBump n (ζ - latticePoint μ.2) : ℝ) : ℂ) •
        (𝐞 (-⟪x, ζ' - ζ⟫) • ((latticeBump n (x - latticePoint ν.1) *
          latticeBump n (x - latticePoint μ.1)) •
            adjointCompL (a.coefficient (x, (2 * π) • ζ')) (a.coefficient (x, (2 * π) • ζ)))) := by
  simp only [pieceKernel, adjointCompL_apply, Circle.smul_def, ← Complex.coe_smul, map_smulₛₗ,
    smul_smul]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  have hph : (𝐞 (-⟪x, ζ' - ζ⟫) : ℂ) = (starRingEnd ℂ) (𝐞 ⟪ζ', x⟫ : ℂ) * 𝐞 ⟪ζ, x⟫ := by
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul, inner_sub_right, real_inner_comm x ζ', real_inner_comm x ζ,
      neg_sub, neg_add_eq_sub]
  rw [hph, map_mul, Complex.conj_ofReal]
  push_cast
  ring

private theorem pieceKernel_comp_adjoint_pieceKernel (a : Symbol n V W 0)
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) (x y ζ : CoordinateSpace n) :
    pieceKernel a ν x ζ ∘L adjoint (pieceKernel a μ y ζ) =
      ((latticeBump n (x - latticePoint ν.1) * latticeBump n (y - latticePoint μ.1) : ℝ) : ℂ) •
        (𝐞 (-⟪ζ, y - x⟫) • ((latticeBump n (ζ - latticePoint ν.2) *
          latticeBump n (ζ - latticePoint μ.2)) •
            compAdjointL (a.coefficient (y, (2 * π) • ζ)) (a.coefficient (x, (2 * π) • ζ)))) := by
  simp only [pieceKernel, compAdjointL_apply, Circle.smul_def, ← Complex.coe_smul, map_smulₛₗ,
    smul_smul]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  have hph : (𝐞 (-⟪ζ, y - x⟫) : ℂ) = (𝐞 ⟪ζ, x⟫ : ℂ) * (starRingEnd ℂ) (𝐞 ⟪ζ, y⟫ : ℂ) := by
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul, inner_sub_right, neg_sub, sub_eq_add_neg]
  rw [hph, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The kernel `∫ x, (G_ν x ζ')† G_μ x ζ` of `T_ν† T_μ` is a Fourier transform in the position. -/
private theorem integral_adjoint_pieceKernel_comp (a : Symbol n V W 0)
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) (ζ' ζ : CoordinateSpace n) :
    ∫ x, adjoint (pieceKernel a ν x ζ') ∘L pieceKernel a μ x ζ =
      ((latticeBump n (ζ' - latticePoint ν.2) * latticeBump n (ζ - latticePoint μ.2) : ℝ) : ℂ) •
        𝓕 (fun x ↦ (latticeBump n (x - latticePoint ν.1) * latticeBump n (x - latticePoint μ.1)) •
          adjointCompL (a.coefficient (x, (2 * π) • ζ')) (a.coefficient (x, (2 * π) • ζ)))
          (ζ' - ζ) := by
  simp_rw [adjoint_pieceKernel_comp_pieceKernel]
  rw [integral_smul, Real.fourier_eq]

/-- The kernel `∫ ζ, G_ν x ζ (G_μ y ζ)†` of `T_ν T_μ†` is a Fourier transform in the
frequency. -/
private theorem integral_pieceKernel_comp_adjoint (a : Symbol n V W 0)
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) (x y : CoordinateSpace n) :
    ∫ ζ, pieceKernel a ν x ζ ∘L adjoint (pieceKernel a μ y ζ) =
      ((latticeBump n (x - latticePoint ν.1) * latticeBump n (y - latticePoint μ.1) : ℝ) : ℂ) •
        𝓕 (fun ζ ↦ (latticeBump n (ζ - latticePoint ν.2) * latticeBump n (ζ - latticePoint μ.2)) •
          compAdjointL (a.coefficient (y, (2 * π) • ζ)) (a.coefficient (x, (2 * π) • ζ)))
          (y - x) := by
  simp_rw [pieceKernel_comp_adjoint_pieceKernel]
  rw [integral_smul, Real.fourier_eq]

/-! ### Almost orthogonality of the pieces -/

/-- The kernel of `T_ν† T_μ` decays in the frequency displacement and vanishes unless the
position cells of `ν` and `μ` are neighbours. -/
private theorem norm_integral_adjoint_pieceKernel_comp_le (a : Symbol n V W 0) {Cχ C : ℝ}
    (hχ : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p (latticeBump n) x‖ ≤ Cχ)
    (hC : ∀ p ≤ 4 * n, ∀ x ξ, ‖iteratedFDeriv ℝ p (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C)
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) (ζ' ζ : CoordinateSpace n) :
    ‖∫ x, adjoint (pieceKernel a ν x ζ') ∘L pieceKernel a μ x ζ‖ ≤
      pieceConst n Cχ C * pairWeight (ν - μ) ^ 2 := by
  rw [integral_adjoint_pieceKernel_comp, norm_smul, Complex.norm_real]
  have hRHS := mul_nonneg (pieceConst_nonneg n Cχ C) (sq_nonneg (pairWeight (ν - μ)))
  by_cases hc : latticeBump n (ζ' - latticePoint ν.2) * latticeBump n (ζ - latticePoint μ.2) = 0
  · simpa [hc] using hRHS
  by_cases hj : ∀ i, |(ν.1 - μ.1) i| ≤ 1
  · have hf : ∀ ξ : CoordinateSpace n, ContDiff ℝ (4 * n) fun y ↦ a.coefficient (y, ξ) :=
      fun ξ ↦ contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_id.prodMk contDiff_const)) _
    have hF := norm_fourier_cutoff_bilinear_le (adjointCompL (V := V) (W := W))
      (opNorm_le_bound₂ _ zero_le_one norm_adjointCompL_apply_le) (hf ((2 * π) • ζ'))
      (hf ((2 * π) • ζ)) hχ (fun p hp x ↦ hC p hp x ((2 * π) • ζ'))
      (fun p hp x ↦ hC p hp x ((2 * π) • ζ)) ν.1 μ.1 (ζ' - ζ)
    refine (mul_le_of_le_one_left (norm_nonneg _) (norm_latticeBump_mul_le _ _)).trans ?_
    have := le_mul_latticeWeight_sq (by
      have := mul_self_nonneg Cχ; have := mul_self_nonneg C; positivity) hj
      (mem_closedBall_of_latticeBump_sub_ne_zero (left_ne_zero_of_mul hc))
      (mem_closedBall_of_latticeBump_sub_ne_zero (right_ne_zero_of_mul hc)) hF
    rwa [pieceConst, pairWeight, Prod.fst_sub, Prod.snd_sub]
  · have hzero : (fun x ↦ (latticeBump n (x - latticePoint ν.1) *
        latticeBump n (x - latticePoint μ.1)) •
          adjointCompL (a.coefficient (x, (2 * π) • ζ')) (a.coefficient (x, (2 * π) • ζ))) =
        0 := by
      funext x
      have : latticeBump n (x - latticePoint ν.1) * latticeBump n (x - latticePoint μ.1) = 0 :=
        by_contra fun h ↦ hj fun i ↦ by
          simpa using abs_sub_le_one_of_latticeBump_mul_ne_zero h i
      simp [this]
    simpa [hzero, Real.fourier_eq, Circle.smul_def] using hRHS

/-- The kernel of `T_ν T_μ†` decays in the position displacement and vanishes unless the
frequency cells of `ν` and `μ` are neighbours. -/
private theorem norm_integral_pieceKernel_comp_adjoint_le (a : Symbol n V W 0) {Cχ C : ℝ}
    (hχ : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p (latticeBump n) x‖ ≤ Cχ)
    (hC : ∀ p ≤ 4 * n, ∀ x ξ, ‖iteratedFDeriv ℝ p (fun η ↦ a.coefficient (x, η)) ξ‖ ≤ C)
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) (x y : CoordinateSpace n) :
    ‖∫ ζ, pieceKernel a ν x ζ ∘L adjoint (pieceKernel a μ y ζ)‖ ≤
      pieceConst n Cχ ((2 * π) ^ (4 * n) * C) * pairWeight (ν - μ) ^ 2 := by
  rw [integral_pieceKernel_comp_adjoint, norm_smul, Complex.norm_real]
  have hRHS := mul_nonneg (pieceConst_nonneg n Cχ ((2 * π) ^ (4 * n) * C))
    (sq_nonneg (pairWeight (ν - μ)))
  by_cases hc : latticeBump n (x - latticePoint ν.1) * latticeBump n (y - latticePoint μ.1) = 0
  · simpa [hc] using hRHS
  by_cases hk : ∀ i, |(ν.2 - μ.2) i| ≤ 1
  · have hc' : ∀ z : CoordinateSpace n, ContDiff ℝ ∞ fun η ↦ a.coefficient (z, η) :=
      fun z ↦ a.contDiff_coefficient.comp (contDiff_const.prodMk contDiff_id)
    have hf : ∀ z : CoordinateSpace n,
        ContDiff ℝ (4 * n) fun ζ : CoordinateSpace n ↦ a.coefficient (z, (2 * π) • ζ) :=
      fun z ↦ contDiff_infty.1 ((hc' z).comp (contDiff_const_smul _)) _
    have hF := norm_fourier_cutoff_bilinear_le (compAdjointL (V := V) (W := W))
      (opNorm_le_bound₂ _ zero_le_one norm_compAdjointL_apply_le) (hf y) (hf x) hχ
      (fun p hp ζ ↦ norm_iteratedFDeriv_comp_two_pi_smul_le (hc' y) (hC · · y) hp ζ)
      (fun p hp ζ ↦ norm_iteratedFDeriv_comp_two_pi_smul_le (hc' x) (hC · · x) hp ζ)
      ν.2 μ.2 (y - x)
    rw [norm_sub_rev] at hF
    refine (mul_le_of_le_one_left (norm_nonneg _) (norm_latticeBump_mul_le _ _)).trans ?_
    have := le_mul_latticeWeight_sq (by
      have := mul_self_nonneg Cχ; have := mul_self_nonneg ((2 * π) ^ (4 * n) * C); positivity) hk
      (mem_closedBall_of_latticeBump_sub_ne_zero (left_ne_zero_of_mul hc))
      (mem_closedBall_of_latticeBump_sub_ne_zero (right_ne_zero_of_mul hc)) hF
    rwa [pieceConst, pairWeight, Prod.fst_sub, Prod.snd_sub, mul_comm (latticeWeight _)]
  · have hzero : (fun ζ ↦ (latticeBump n (ζ - latticePoint ν.2) *
        latticeBump n (ζ - latticePoint μ.2)) •
          compAdjointL (a.coefficient (y, (2 * π) • ζ)) (a.coefficient (x, (2 * π) • ζ))) =
        0 := by
      funext ζ
      have : latticeBump n (ζ - latticePoint ν.2) * latticeBump n (ζ - latticePoint μ.2) = 0 :=
        by_contra fun h ↦ hk fun i ↦ by
          simpa using abs_sub_le_one_of_latticeBump_mul_ne_zero h i
      simp [this]
    simpa [hzero, Real.fourier_eq, Circle.smul_def] using hRHS

/-! ### The pieces as operators on `L²` -/

/-- The phase-space piece of `a` at `ν`, as the integral operator on `L²` with kernel
`pieceKernel a ν`. Composed with the Fourier transform it is the quantization of the symbol
`χ(x - j) χ(ξ / 2π - k) a(x, ξ)`. -/
private def pieceOp (a : Symbol n V W 0) {C : ℝ≥0} (hC : ∀ p, ‖a.coefficient p‖ ≤ C)
    (ν : (Fin n → ℤ) × (Fin n → ℤ)) :
    Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
      Lp W 2 (volume : Measure (CoordinateSpace n)) :=
  integralOperatorLp (pieceKernel a ν) 2 (continuous_pieceKernel a ν).aestronglyMeasurable
    (ae_lintegral_enorm_le_of_cell (fun _ _ h ↦ pieceKernel_ne_zero h)
      (norm_pieceKernel_le hC ν)).1
    (ae_lintegral_enorm_le_of_cell (fun _ _ h ↦ pieceKernel_ne_zero h)
      (norm_pieceKernel_le hC ν)).2

private theorem norm_adjoint_pieceOp_comp_pieceOp_le (a : Symbol n V W 0) {C : ℝ≥0}
    (hC : ∀ p, ‖a.coefficient p‖ ≤ C) {Cχ C' : ℝ}
    (hχ : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p (latticeBump n) x‖ ≤ Cχ)
    (hC' : ∀ p ≤ 4 * n, ∀ x ξ, ‖iteratedFDeriv ℝ p (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C')
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) :
    ‖adjoint (pieceOp a hC ν) ∘L pieceOp a hC μ‖ ≤
      pieceConst n Cχ C' * pairWeight (ν - μ) ^ 2 * cellVolume n := by
  have hr := mul_nonneg (pieceConst_nonneg n Cχ C') (sq_nonneg (pairWeight (ν - μ)))
  have hsupp : ∀ ζ' ζ, ∫ x, adjoint (pieceKernel a ν x ζ') ∘L pieceKernel a μ x ζ ≠ 0 →
      ζ' ∈ closedBall (latticePoint ν.2) √n ∧ ζ ∈ closedBall (latticePoint μ.2) √n := by
    intro ζ' ζ h
    rw [integral_adjoint_pieceKernel_comp] at h
    have h' := Complex.ofReal_ne_zero.1 (left_ne_zero_of_smul h)
    exact ⟨mem_closedBall_of_latticeBump_sub_ne_zero (left_ne_zero_of_mul h'),
      mem_closedBall_of_latticeBump_sub_ne_zero (right_ne_zero_of_mul h')⟩
  obtain ⟨hA, hB⟩ := ae_lintegral_enorm_le_of_cell hsupp fun ζ' ζ ↦
    (norm_integral_adjoint_pieceKernel_comp_le a hχ hC' ν μ ζ' ζ).trans
      (Real.le_coe_toNNReal _)
  rw [pieceOp, pieceOp, adjoint_comp_integralOperatorLp (hA := hA) (hB := hB)]
  refine norm_integralOperatorLp_le_max.trans ?_
  rw [max_self, NNReal.coe_mul, Real.coe_toNNReal _ hr]

private theorem norm_pieceOp_comp_adjoint_pieceOp_le (a : Symbol n V W 0) {C : ℝ≥0}
    (hC : ∀ p, ‖a.coefficient p‖ ≤ C) {Cχ C' : ℝ}
    (hχ : ∀ p ≤ 4 * n, ∀ x, ‖iteratedFDeriv ℝ p (latticeBump n) x‖ ≤ Cχ)
    (hC' : ∀ p ≤ 4 * n, ∀ x ξ, ‖iteratedFDeriv ℝ p (fun η ↦ a.coefficient (x, η)) ξ‖ ≤ C')
    (ν μ : (Fin n → ℤ) × (Fin n → ℤ)) :
    ‖pieceOp a hC ν ∘L adjoint (pieceOp a hC μ)‖ ≤
      pieceConst n Cχ ((2 * π) ^ (4 * n) * C') * pairWeight (ν - μ) ^ 2 * cellVolume n := by
  have hr := mul_nonneg (pieceConst_nonneg n Cχ ((2 * π) ^ (4 * n) * C'))
    (sq_nonneg (pairWeight (ν - μ)))
  have hsupp : ∀ x y, ∫ ζ, pieceKernel a ν x ζ ∘L adjoint (pieceKernel a μ y ζ) ≠ 0 →
      x ∈ closedBall (latticePoint ν.1) √n ∧ y ∈ closedBall (latticePoint μ.1) √n := by
    intro x y h
    rw [integral_pieceKernel_comp_adjoint] at h
    have h' := Complex.ofReal_ne_zero.1 (left_ne_zero_of_smul h)
    exact ⟨mem_closedBall_of_latticeBump_sub_ne_zero (left_ne_zero_of_mul h'),
      mem_closedBall_of_latticeBump_sub_ne_zero (right_ne_zero_of_mul h')⟩
  obtain ⟨hA, hB⟩ := ae_lintegral_enorm_le_of_cell hsupp fun x y ↦
    (norm_integral_pieceKernel_comp_adjoint_le a hχ hC' ν μ x y).trans
      (Real.le_coe_toNNReal _)
  rw [pieceOp, pieceOp, integralOperatorLp_comp_adjoint (hA := hA) (hB := hB)]
  refine norm_integralOperatorLp_le_max.trans ?_
  rw [max_self, NNReal.coe_mul, Real.coe_toNNReal _ hr]

/-- A sum over a finite set of translates of the summable weight is at most its total sum. -/
private theorem sum_pairWeight_sub_le (ν : (Fin n → ℤ) × (Fin n → ℤ))
    (s : Finset ((Fin n → ℤ) × (Fin n → ℤ))) :
    ∑ μ ∈ s, pairWeight (ν - μ) ≤ ∑' d, pairWeight (n := n) d := by
  rw [← (Equiv.subLeft ν).tsum_eq]
  exact ((Equiv.subLeft ν).summable_iff.2 summable_pairWeight).sum_le_tsum s
    fun μ _ ↦ pairWeight_nonneg _

/-- **Cotlar–Stein for the phase-space pieces.** The pieces of a uniform symbol of order `0`
are almost orthogonal, so their sum converges strongly to a bounded operator on `L²`. -/
private theorem exists_hasSum_pieceOp (a : Symbol n V W 0) (ha : a.IsUniform) :
    ∃ (C : ℝ≥0) (hC : ∀ p, ‖a.coefficient p‖ ≤ C)
      (S : Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
        Lp W 2 (volume : Measure (CoordinateSpace n))),
      ∀ f, HasSum (fun ν ↦ pieceOp a hC ν f) (S f) := by
  obtain ⟨Cχ, hχ⟩ := exists_norm_iteratedFDeriv_latticeBump_le (n := n) (4 * n)
  obtain ⟨Ca, hCa⟩ := ha.exists_norm_iteratedFDeriv_le (4 * n)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0 (Nat.zero_le _) 0 0).1
  have h0 : ∀ p, ‖a.coefficient p‖ ≤ (⟨Ca, hCa0⟩ : ℝ≥0) := fun p ↦ by
    simpa using (hCa 0 (Nat.zero_le _) p.1 p.2).1
  set C' := (2 * π) ^ (4 * n) * Ca
  have hCaC' : Ca ≤ C' := le_mul_of_one_le_left hCa0 (one_le_pow₀ (by linarith [two_le_pi]))
  have hx : ∀ p ≤ 4 * n, ∀ x ξ,
      ‖iteratedFDeriv ℝ p (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C' :=
    fun p hp x ξ ↦ (hCa p hp x ξ).1.trans hCaC'
  have hξ : ∀ p ≤ 4 * n, ∀ x ξ,
      ‖iteratedFDeriv ℝ p (fun η ↦ a.coefficient (x, η)) ξ‖ ≤ Ca :=
    fun p hp x ξ ↦ (hCa p hp x ξ).2
  set D := √(pieceConst n Cχ C' * cellVolume n)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  -- A bound `P ≤ K w² v` gives `√P ≤ √(K v) w`.
  have sqrt_le_of_le_mul_sq {P K w v : ℝ} (hK : 0 ≤ K) (hw : 0 ≤ w) (hv : 0 ≤ v)
      (h : P ≤ K * w ^ 2 * v) : √P ≤ √(K * v) * w :=
    calc √P ≤ √(K * w ^ 2 * v) := Real.sqrt_le_sqrt h
      _ = √(K * v) * w := by
          rw [show K * w ^ 2 * v = K * v * w ^ 2 by ring, Real.sqrt_mul (mul_nonneg hK hv),
            Real.sqrt_sq hw]
  have h₁ : ∀ ν (s : Finset ((Fin n → ℤ) × (Fin n → ℤ))),
      ∑ μ ∈ s, √‖adjoint (pieceOp a h0 ν) ∘L pieceOp a h0 μ‖ ≤ D * ∑' d, pairWeight d :=
    fun ν s ↦ by
      calc ∑ μ ∈ s, √‖adjoint (pieceOp a h0 ν) ∘L pieceOp a h0 μ‖
          ≤ ∑ μ ∈ s, D * pairWeight (ν - μ) := by
            refine sum_le_sum fun μ _ ↦ ?_
            exact sqrt_le_of_le_mul_sq (pieceConst_nonneg _ _ _) (pairWeight_nonneg _)
              (NNReal.coe_nonneg _) (norm_adjoint_pieceOp_comp_pieceOp_le a h0 hχ hx ν μ)
        _ ≤ D * ∑' d, pairWeight d := by
            rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_pairWeight_sub_le ν s) hD
  have h₂ : ∀ ν (s : Finset ((Fin n → ℤ) × (Fin n → ℤ))),
      ∑ μ ∈ s, √‖pieceOp a h0 ν ∘L adjoint (pieceOp a h0 μ)‖ ≤ D * ∑' d, pairWeight d :=
    fun ν s ↦ by
      calc ∑ μ ∈ s, √‖pieceOp a h0 ν ∘L adjoint (pieceOp a h0 μ)‖
          ≤ ∑ μ ∈ s, D * pairWeight (ν - μ) := by
            refine sum_le_sum fun μ _ ↦ ?_
            exact sqrt_le_of_le_mul_sq (pieceConst_nonneg _ _ _) (pairWeight_nonneg _)
              (NNReal.coe_nonneg _) (norm_pieceOp_comp_adjoint_pieceOp_le a h0 hχ hξ ν μ)
        _ ≤ D * ∑' d, pairWeight d := by
            rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_pairWeight_sub_le ν s) hD
  obtain ⟨S, -, hS⟩ := exists_hasSum_apply_of_almost_orthogonal (pieceOp a h0)
    (mul_nonneg hD (tsum_nonneg pairWeight_nonneg)) h₁ h₂
  exact ⟨⟨Ca, hCa0⟩, h0, S, hS⟩

/-! ### Summing the pieces -/

omit [CompleteSpace V] [CompleteSpace W] in
/-- The products `χ(x - j) χ(ζ - k)` over `(j, k) ∈ ℤⁿ × ℤⁿ` sum to one. -/
private theorem hasSum_latticeBump_mul (x ζ : CoordinateSpace n) :
    HasSum (fun ν : (Fin n → ℤ) × (Fin n → ℤ) ↦
      latticeBump n (x - latticePoint ν.1) * latticeBump n (ζ - latticePoint ν.2)) 1 := by
  simpa using (hasSum_latticeBump_sub x).mul (hasSum_latticeBump_sub ζ)
    ((hasSum_latticeBump_sub x).summable.mul_of_nonneg (hasSum_latticeBump_sub ζ).summable
      (fun _ ↦ latticeBump_nonneg _) fun _ ↦ latticeBump_nonneg _)

omit [CompleteSpace V] [CompleteSpace W] in
/-- At every position the pieces of the quantization integral sum to `Op(a) u (x)`. -/
private theorem hasSum_integral_pieceKernel (a : Symbol n V W 0) {C : ℝ}
    (hC : ∀ p, ‖a.coefficient p‖ ≤ C) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    HasSum (fun ν ↦ ∫ ζ, pieceKernel a ν x ζ (𝓕 u ζ))
      (quantizeSchwartzValue a.coefficient u x) := by
  set g : CoordinateSpace n → W := fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)
  have hg : Integrable g := integrable_quantizeSchwartzValue_integrand (m := 0)
    (a.continuous_coefficient_slice x).aestronglyMeasurable (fun ξ ↦ by simpa using hC (x, ξ))
    (𝓕 u)
  have hF : ∀ ν ζ, pieceKernel a ν x ζ (𝓕 u ζ) =
      (latticeBump n (x - latticePoint ν.1) * latticeBump n (ζ - latticePoint ν.2)) • g ζ :=
    fun ν ζ ↦ by simp only [pieceKernel, g, Circle.smul_def, smul_apply, smul_comm (_ : ℝ)]
  rw [quantizeSchwartzValue_def]
  simp_rw [hF]
  refine hasSum_integral_of_dominated_convergence
    (fun ν ζ ↦ latticeBump n (x - latticePoint ν.1) * latticeBump n (ζ - latticePoint ν.2) *
      ‖g ζ‖) (fun ν ↦ ?_) (fun ν ↦ .of_forall fun ζ ↦ ?_)
    (.of_forall fun ζ ↦ ((hasSum_latticeBump_mul x ζ).mul_right _).summable) ?_
    (.of_forall fun ζ ↦ by simpa using (hasSum_latticeBump_mul x ζ).smul_const (g ζ))
  · exact (((contDiff_latticeBump (k := 0)).continuous.comp
      (continuous_const.sub continuous_const)).mul ((contDiff_latticeBump (k := 0)).continuous.comp
        (continuous_id.sub continuous_const))).aestronglyMeasurable.smul hg.1
  · rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (latticeBump_nonneg _) (latticeBump_nonneg _))]
  · simpa [((hasSum_latticeBump_mul x _).mul_right _).tsum_eq] using hg.norm

/-! ### The Calderón–Vaillancourt theorem -/

/-- **The Calderón–Vaillancourt theorem.** The quantization of a symbol of order `0` whose
estimates hold uniformly in the position extends from Schwartz functions to a bounded operator on
`L²(ℝⁿ)`: there is a bounded operator `T` on `L²` with `T u = Op(a) u` almost everywhere for every
Schwartz function `u`. No support condition in the position is needed. -/
theorem exists_quantizeUniformOrderZeroLp (a : Symbol n V W 0) (ha : a.IsUniform) :
    ∃ T : Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
        Lp W 2 (volume : Measure (CoordinateSpace n)),
      ∀ u : 𝓢(CoordinateSpace n, V),
        T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u := by
  obtain ⟨C, hC, S, hS⟩ := exists_hasSum_pieceOp a ha
  refine ⟨S ∘L ((Lp.fourierTransformₗᵢ (CoordinateSpace n) V).toContinuousLinearEquiv :
    Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp V 2 volume), fun u ↦ ?_⟩
  have hu : (Lp.fourierTransformₗᵢ (CoordinateSpace n) V) (u.toLp 2) = (𝓕 u).toLp 2 :=
    SchwartzMap.toLp_fourier_eq u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, hu]
  refine Lp.ae_eq_of_hasSum_of_ae_hasSum (hS _) ?_
  have h1 : ∀ᵐ x ∂volume, ∀ ν, (pieceOp a hC ν ((𝓕 u).toLp 2) : CoordinateSpace n → W) x =
      ∫ ζ, pieceKernel a ν x ζ (𝓕 u ζ) := by
    refine ae_all_iff.2 fun ν ↦ ?_
    filter_upwards [coeFn_integralOperatorLp (K := pieceKernel a ν) (p := 2)
      (hK := (continuous_pieceKernel a ν).aestronglyMeasurable) ((𝓕 u).toLp 2)] with x hx
    rw [pieceOp, hx]
    exact integral_congr_ae (by
      filter_upwards [(𝓕 u).coeFn_toLp 2] with ζ hζ
      rw [hζ])
  filter_upwards [h1] with x hx
  simpa only [hx] using hasSum_integral_pieceKernel a hC u x

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **The Calderón–Vaillancourt theorem** on `H⁰ = L²`, for finite-dimensional coefficient
spaces. The quantization of a symbol of order `0` whose estimates hold uniformly in the position
extends from Schwartz functions to a bounded operator `H⁰(ℝⁿ; V) → H⁰(ℝⁿ; W)`.

The norms of `V` and `W` need not come from inner products: as for
`TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms `e₁ : V ≃L[ℂ] ℂ^k` and `e₂ : W ≃L[ℂ] ℂ^l`
reduce the statement to `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`. -/
theorem exists_quantizeUniformOrderZero (a : Symbol n V W 0) (ha : a.IsUniform) :
    ∃ T : H^{0}(CoordinateSpace n, V) →L[ℂ] H^{0}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  obtain ⟨T₀, hT₀⟩ := (a.map Φ).exists_quantizeUniformOrderZeroLp (ha.map Φ)
  set V' := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  set W' := EuclideanSpace ℂ (Fin (Module.finrank ℂ W))
  refine ⟨BesselPotentialSpace.postcomp _ _ 2 (e₂.symm : W' →L[ℂ] W) ∘L
    ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) W' 0 2).symm.toContinuousLinearEquiv :
      Lp W' 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] H^{0}(CoordinateSpace n, W')) ∘L
    T₀ ∘L ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V' 0 2).toContinuousLinearEquiv :
      H^{0}(CoordinateSpace n, V') →L[ℂ] Lp V' 2 (volume : Measure (CoordinateSpace n))) ∘L
    BesselPotentialSpace.postcomp _ 0 2 (e₁ : V →L[ℂ] V'), fun u φ ↦ ?_⟩
  have hc : (a.map Φ).coefficient = fun p ↦ e₁.arrowCongr e₂ (a.coefficient p) :=
    funext fun p ↦ by simp [Φ]
  have hq (x : CoordinateSpace n) :
      quantizeSchwartzValue (a.map Φ).coefficient (u.postcompCLM (e₁ : V →L[ℂ] V')) x =
        e₂ (quantizeSchwartzValue a.coefficient u x) := by
    rw [hc, quantizeSchwartzValue_arrowCongr]
  have hlp : (SchwartzMap.toBesselPotentialSpaceCLM 0 2
      (u.postcompCLM (e₁ : V →L[ℂ] V'))).toLp = (u.postcompCLM (e₁ : V →L[ℂ] V')).toLp 2 := by
    simp [SchwartzMap.fourierMultiplierCLM_const]
  simp only [ContinuousLinearMap.comp_apply, ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    BesselPotentialSpace.toLpₗᵢ_apply, hlp, BesselPotentialSpace.toDistr_postcomp_apply]
  rw [BesselPotentialSpace.toLpₗᵢ_symm_apply, neg_zero, TemperedDistribution.besselPotential_zero,
    ContinuousLinearMap.id_apply, Lp.toTemperedDistribution_apply,
    integral_congr_ae (g := fun x ↦ φ x • quantizeSchwartzValue (a.map Φ).coefficient
      (u.postcompCLM (e₁ : V →L[ℂ] V')) x) (by
        filter_upwards [hT₀ (u.postcompCLM (e₁ : V →L[ℂ] V'))] with x hx
        rw [hx])]
  simp only [hq, ← map_smul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.symm_apply_apply]

end FiniteDimensional

end Symbol

end TauCeti
