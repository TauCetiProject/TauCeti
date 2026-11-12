/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.RightQuantization.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import TauCeti.Analysis.Calculus.CoordinateDeriv.Series
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Pseudodifferential.OutputSupport
import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Topology.Algebra.InfiniteSum.PiProd

/-!
# The left symbol of the right quantization of a uniform symbol

The right quantization of a symbol `c(y, ξ)` is `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ`;
formal adjoints of left (Kohn–Nirenberg) quantizations are of this form. For `c` with compact
spatial support, `TauCeti.Symbol.ofRight` rewrites it as the left quantization of a symbol given
by an absolutely convergent integral. This file removes the support condition: for a symbol `c`
of order `m` whose estimates hold uniformly in the position, the left symbol
`TauCeti.Symbol.ofRightUniform` of its right quantization is again a symbol of order `m` with
uniform estimates. This is what passing from right to left quantizations needs in the calculus of
symbols with uniform estimates, whose symbols in general have no compact spatial support.

## Main declarations

* `TauCeti.Symbol.ofRightUniform`: the left symbol of the right quantization of a uniform
  symbol, uniform by `TauCeti.Symbol.isUniform_ofRightUniform`.
* `TauCeti.Symbol.quantizeSchwartzValue_ofRightUniform`: its quantization is the right
  quantization, `Op(b) v (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ) dζ`.
* `TauCeti.Symbol.ofRightUniform_eq_ofRight`: for symbols with compact spatial support it is
  `TauCeti.Symbol.ofRight`.

## Construction

Cut `c` by the partition of unity `∑_{j ∈ ℤⁿ} χ(y - j) = 1` by translates of
`χ = TauCeti.latticeBump n`, and let `b_j` be the left symbol (`TauCeti.Symbol.ofRight`) of the
compactly supported piece `χ(y - j) c(y, ξ)`; then `b = ∑_j b_j`. The `b_j` decay away from `j`.
First, `‖b_j(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` with `C` independent of `j`. Second,
`(x - j)ᵢ b_j = b'_j + i b''_j` for the left symbols `b'_j`, `b''_j` of `(y - j)ᵢ χ(y - j) c(y, ξ)`
and `χ(y - j) ∂_{ξᵢ} c(y, ξ)`: writing `x - j = (x - y) + (y - j)`, both sides have the same
quantization at `x` (`TauCeti.Symbol.quantizeSchwartzValue_smulLeftCLM_coord_sub`), and a symbol
is determined by its quantization (`TauCeti.eq_of_forall_quantizeSchwartzValue_eq`). Iterating,
`∏ᵢ (1 + (x - j)ᵢ²) ∂_x^α ∂_ξ^β b_j(x, ξ)` is bounded by `C ⟨ξ⟩ ^ (m - |β|)` uniformly in `j`, and
the lattice sums of `∏ᵢ (1 + (x - j)ᵢ²)⁻¹` are bounded uniformly in `x`, so the series converges
with all its derivatives (`TauCeti.contDiff_tsum_of_locallySummableMixedDeriv`). Its quantization
is the sum of the right quantizations of the pieces, which is the right quantization of `c`
because the Fourier transforms of `χ(y - j) c(y, 2πζ) v(y)` decay both in `ζ` and in `j`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.7.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped RealInnerProductSpace SchwartzMap ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### Lattice weights -/

section Weight

/-- Peetre's inequality in one variable: `1 + b² ≤ 2 (1 + (a - b)²) (1 + a²)`. -/
private theorem one_add_sq_le_two_mul (a b : ℝ) :
    1 + b ^ 2 ≤ 2 * (1 + (a - b) ^ 2) * (1 + a ^ 2) := by
  have h := one_add_norm_add_sq_le (b - a) a
  simp only [sub_add_cancel, Real.norm_eq_abs, sq_abs] at h
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - a)]

/-- If every coordinate of `x - y` is at most `R` in absolute value, the weight
`∏ᵢ (1 + (x - j)ᵢ²)⁻¹` is at most `(2 (1 + R²))ⁿ` times the weight at `y`. -/
private theorem prod_inv_le_of_abs_sub_le {R : ℝ} {x y : Fin n → ℝ} (hxy : ∀ i, |x i - y i| ≤ R)
    (j : Fin n → ℝ) :
    (∏ i, (1 + (x i - j i) ^ 2))⁻¹ ≤ (2 * (1 + R ^ 2)) ^ n * (∏ i, (1 + (y i - j i) ^ 2))⁻¹ := by
  have hpos : 0 < ∏ i, (1 + (x i - j i) ^ 2) := Finset.prod_pos fun i _ ↦ by positivity
  have hpos' : 0 < ∏ i, (1 + (y i - j i) ^ 2) := Finset.prod_pos fun i _ ↦ by positivity
  rw [← div_eq_mul_inv, inv_le_comm₀ hpos (div_pos (by positivity) hpos'), inv_div,
    div_le_iff₀ (by positivity)]
  calc ∏ i, (1 + (y i - j i) ^ 2)
      ≤ ∏ i, (2 * (1 + R ^ 2) * (1 + (x i - j i) ^ 2)) := by
        refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
        have h2 : (x i - j i - (y i - j i)) ^ 2 ≤ R ^ 2 := by
          rw [sub_sub_sub_cancel_right, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hxy i) 2
        calc 1 + (y i - j i) ^ 2
            ≤ 2 * (1 + (x i - j i - (y i - j i)) ^ 2) * (1 + (x i - j i) ^ 2) :=
              one_add_sq_le_two_mul _ _
          _ ≤ _ := by gcongr
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, mul_comm]

/-- The case `R = 1` of `prod_inv_le_of_abs_sub_le`. -/
private theorem prod_inv_le_four_pow_mul {x y : Fin n → ℝ} (hxy : ∀ i, |x i - y i| ≤ 1)
    (j : Fin n → ℝ) :
    (∏ i, (1 + (x i - j i) ^ 2))⁻¹ ≤ 4 ^ n * (∏ i, (1 + (y i - j i) ^ 2))⁻¹ := by
  have h := prod_inv_le_of_abs_sub_le hxy j
  norm_num at h
  exact h

/-- The weight `k ↦ (1 + (s - k)²)⁻¹` is summable over `ℤ`. -/
private theorem summable_inv_one_add_sub_sq (s : ℝ) :
    Summable fun k : ℤ ↦ (1 + (s - k) ^ 2)⁻¹ := by
  have h₀ : Summable fun k : ℤ ↦ (1 + (k : ℝ) ^ 2)⁻¹ := by
    refine (Real.summable_one_div_int_pow.2 one_lt_two).of_norm_bounded_eventually ?_
    filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
    have hk : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [Real.norm_of_nonneg (by positivity), one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  refine (h₀.mul_left (2 * (1 + s ^ 2))).of_nonneg_of_le (fun k ↦ by positivity) fun k ↦ ?_
  have h := one_add_sq_le_two_mul s k
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  linarith

/-- The lattice weight `j ↦ ∏ᵢ (1 + (x - j)ᵢ²)⁻¹` is summable over `ℤⁿ`. -/
private theorem summable_prod_inv (x : Fin n → ℝ) :
    Summable fun j : Fin n → ℤ ↦ (∏ i, (1 + (x i - j i) ^ 2))⁻¹ := by
  simp_rw [← Finset.prod_inv_distrib]
  exact Summable.prod_pi_of_nonneg (f := fun i (k : ℤ) ↦ (1 + (x i - k) ^ 2)⁻¹)
    (fun i ↦ summable_inv_one_add_sub_sq (x i)) fun i k ↦ by positivity

/-- The lattice sums of the weight are bounded uniformly in `x`. -/
private theorem tsum_prod_inv_le (x : Fin n → ℝ) :
    ∑' j : Fin n → ℤ, (∏ i, (1 + (x i - j i) ^ 2))⁻¹ ≤
      4 ^ n * ∑' k : Fin n → ℤ, (∏ i, (1 + ((k i : ℤ) : ℝ) ^ 2))⁻¹ := by
  set y : Fin n → ℝ := fun i ↦ (⌊x i⌋ : ℝ)
  have hxy : ∀ i, |x i - y i| ≤ 1 := fun i ↦ by
    rw [abs_of_nonneg (sub_nonneg.2 (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (x i)]
  set G : (Fin n → ℤ) → ℝ := fun k ↦ (∏ i, (1 + ((k i : ℤ) : ℝ) ^ 2))⁻¹
  have hk : ∑' j : Fin n → ℤ, (∏ i, (1 + (y i - j i) ^ 2))⁻¹ = ∑' k, G k := by
    rw [← (Equiv.subLeft (fun i ↦ ⌊x i⌋)).tsum_eq G]
    refine tsum_congr fun j ↦ ?_
    simp only [G, y, Equiv.subLeft_apply, Pi.sub_apply, Int.cast_sub]
  rw [← hk, ← tsum_mul_left]
  exact (summable_prod_inv x).tsum_le_tsum (fun j ↦ prod_inv_le_four_pow_mul hxy _)
    ((summable_prod_inv y).mul_left _)

end Weight

/-! ### Spatial cutoffs -/

section Cutoff

variable {ψ : CoordinateSpace n → ℝ} {hψ : ContDiff ℝ ∞ ψ} {t : CoordinateSpace n}
  {c : Symbol n V W m}

/-- The symbol `ψ(y - t) c(y, ξ)`: `c` cut off in the position by a translate of `ψ`. -/
private def cutoff (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (t : CoordinateSpace n)
    (c : Symbol n V W m) : Symbol n V W m :=
  inclusion (zero_add m).le
    ((ofSpatial (fun y ↦ ((ψ (y - t) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ W)
      ((Complex.ofRealCLM.contDiff.comp (hψ.comp (contDiff_id.sub contDiff_const))).smul
        contDiff_const)).comp c)

private theorem coefficient_cutoff (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoff ψ hψ t c).coefficient p = ψ (p.1 - t) • c.coefficient p := by
  simp [cutoff, coefficient_inclusion, coefficient_comp, Complex.coe_smul]

private theorem coefficient_cutoff_eq_zero {R : ℝ} (hR : tsupport ψ ⊆ Metric.closedBall 0 R)
    {y : CoordinateSpace n} (hy : y ∉ Metric.closedBall t R) (ξ : CoordinateSpace n) :
    (cutoff ψ hψ t c).coefficient (y, ξ) = 0 := by
  rw [coefficient_cutoff, image_eq_zero_of_notMem_tsupport (f := ψ) (fun h ↦ hy ?_), zero_smul]
  have := hR h
  rwa [mem_closedBall_zero_iff, ← dist_eq_norm, ← Metric.mem_closedBall] at this

private theorem hasCompactSpatialSupport_cutoff (hψc : HasCompactSupport ψ) :
    (cutoff ψ hψ t c).HasCompactSpatialSupport := by
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  exact hasCompactSpatialSupport_iff.2
    ⟨_, isCompact_closedBall t R, fun y hy ξ ↦ coefficient_cutoff_eq_zero hR hy ξ⟩

private theorem frequencyDeriv_cutoff (j : Fin n) :
    frequencyDeriv j (cutoff ψ hψ t c) = cutoff ψ hψ t (frequencyDeriv j c) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_frequencyDeriv, coefficient_cutoff, coefficient_frequencyDeriv]
  simp_rw [coefficient_cutoff]
  exact congrFun (coordinateDeriv_const_smul [j] (fun η ↦ c.coefficient (x, η)) (ψ (x - t))) ξ

private theorem spatialDeriv_cutoff (j : Fin n) :
    spatialDeriv j (cutoff ψ hψ t c) =
      cutoff (coordinateDeriv [j] ψ) (hψ.coordinateDeriv [j]) t c +
        cutoff ψ hψ t (spatialDeriv j c) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv, coefficient_add, Pi.add_apply, coefficient_cutoff,
    coefficient_cutoff, coefficient_spatialDeriv]
  simp_rw [coefficient_cutoff]
  have hψ' : DifferentiableAt ℝ (fun y ↦ ψ (y - t)) x :=
    ((hψ.comp (contDiff_id.sub contDiff_const)).differentiable (by simp)) x
  have hc' : DifferentiableAt ℝ (fun y ↦ c.coefficient (y, ξ)) x :=
    ((c.contDiff_coefficient_slice ξ).differentiable (by simp)) x
  simp only [coordinateDeriv_cons, coordinateDeriv_nil]
  have hsub : fderiv ℝ (fun y ↦ ψ (y - t)) x = fderiv ℝ ψ (x - t) := by
    simpa [sub_eq_add_neg] using fderiv_comp_add_right (f := ψ) (x := x) (-t)
  rw [fderiv_fun_smul hψ' hc', hsub]
  simp [add_comm]

end Cutoff

/-! ### Bounds on the cut-off left symbols -/

section Bounds

variable {ψ : CoordinateSpace n → ℝ} {hψ : ContDiff ℝ ∞ ψ} {c : Symbol n V W m}

/-- The Fourier transforms of the position slices of the cutoffs `ψ(y - t) c(y, ξ)` decay
faster than `(1 + ‖θ‖) ^ (-N)`, uniformly in the translation `t`. -/
private theorem exists_one_add_norm_pow_mul_norm_fourier_cutoff_le (hψc : HasCompactSupport ψ)
    (hc : c.IsUniform) (N : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ t θ ξ : CoordinateSpace n,
      (1 + ‖θ‖) ^ N * ‖𝓕 (fun z ↦ (cutoff ψ hψ t c).coefficient (z, ξ)) θ‖ ≤
        K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨B, hB0, hB⟩ := hψc.exists_bound_iteratedFDeriv hψ N
  obtain ⟨A, hA0, hA⟩ := hc.exists_norm_iteratedFDeriv_slice_le N
  set V₀ := volume.real (Metric.closedBall (0 : CoordinateSpace n) R)
  refine ⟨2 ^ N * (2 ^ N * B * A * V₀), by positivity, fun t θ ξ ↦ ?_⟩
  set f : CoordinateSpace n → V →L[ℂ] W := fun z ↦ (cutoff ψ hψ t c).coefficient (z, ξ)
  have hf : f = fun z ↦ ψ (z - t) • c.coefficient (z, ξ) := funext fun z ↦ coefficient_cutoff _
  have hψt : ContDiff ℝ ∞ fun z ↦ ψ (z - t) := hψ.comp (contDiff_id.sub contDiff_const)
  have hfS : tsupport f ⊆ Metric.closedBall t R :=
    closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (coefficient_cutoff_eq_zero hR h ξ))
      Metric.isClosed_closedBall
  have hbound : ∀ p ≤ N, ∀ z, ‖iteratedFDeriv ℝ p f z‖ ≤
      2 ^ N * B * (A * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
    intro p hp z
    rw [hf]
    refine (norm_iteratedFDeriv_smul_le hψt (c.contDiff_coefficient_slice ξ) z
      (mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i
          (fun z ↦ ψ (z - t)) z‖ * ‖iteratedFDeriv ℝ (p - i) (fun z ↦ c.coefficient (z, ξ)) z‖
        ≤ ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * B *
            (A * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [iteratedFDeriv_comp_sub]
          gcongr
          · exact hB i (hi'.trans hp) _
          · exact hA _ ((Nat.sub_le p i).trans hp) z ξ
      _ = 2 ^ p * B * (A * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
      _ ≤ _ := by gcongr; norm_num
  have hvol : volume.real (Metric.closedBall t R) = V₀ := by
    simp only [V₀, Measure.real, Measure.addHaar_closedBall_center]
  have h := one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset
    ((cutoff ψ hψ t c).contDiff_coefficient_slice ξ |>.of_le (mod_cast le_top))
    measurableSet_closedBall measure_closedBall_lt_top.ne hfS hbound θ
  rw [hvol] at h
  calc (1 + ‖θ‖) ^ N * ‖𝓕 f θ‖ ≤ 2 ^ N * (2 ^ N * B * (A * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) * V₀) := h
    _ = _ := by ring

/-- The loss `(1 + ‖θ‖) ^ |m|` is absorbed by `n + 1 + ⌈|m|⌉` powers of decay. -/
private theorem one_add_norm_rpow_abs_mul_inv_pow_le (m : ℝ) (θ : CoordinateSpace n) :
    (1 + ‖θ‖) ^ |m| * ((1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊))⁻¹ ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  have h1 : (0 : ℝ) < 1 + ‖θ‖ := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_neg h1.le, ← Real.rpow_add h1]
  refine Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (norm_nonneg θ)) ?_
  have := Nat.le_ceil |m|
  push_cast
  linarith

/-- The shifted Fourier slices of the cutoffs decay like `(1 + ‖θ‖) ^ (-(n + 1))`, uniformly in
the translation `t`. -/
private theorem exists_norm_fourier_cutoff_add_le (hψc : HasCompactSupport ψ) (hc : c.IsUniform) :
    ∃ K, 0 ≤ K ∧ ∀ t θ ξ : CoordinateSpace n,
      ‖𝓕 (fun z ↦ (cutoff ψ hψ t c).coefficient (z, ξ + (2 * π) • θ)) θ‖ ≤
        K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  set N := n + 1 + ⌈|m|⌉₊
  obtain ⟨K, hK0, hK⟩ := exists_one_add_norm_pow_mul_norm_fourier_cutoff_le (hψ := hψ) hψc hc N
  refine ⟨K * 2 ^ (|m| / 2) * (2 * π) ^ |m|, by positivity, fun t θ ξ ↦ ?_⟩
  have hN := one_add_norm_rpow_abs_mul_inv_pow_le m θ
  have hpeetre : (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (m / 2) ≤
      2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * ((2 * π) ^ |m| * (1 + ‖θ‖) ^ |m|) := by
    refine (one_add_norm_add_sq_rpow_le_mul m ξ ((2 * π) • θ)).trans ?_
    gcongr
    have h := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) |m| θ
    rw [abs_abs] at h
    exact h.trans (by gcongr; exact one_add_norm_sq_rpow_le_one_add_norm_rpow θ (abs_nonneg m))
  have hF : ‖𝓕 (fun z ↦ (cutoff ψ hψ t c).coefficient (z, ξ + (2 * π) • θ)) θ‖ ≤
      K * (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (m / 2) / (1 + ‖θ‖) ^ N :=
    (le_div_iff₀' (by positivity)).2 (hK t θ _)
  calc _ ≤ K * (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (m / 2) / (1 + ‖θ‖) ^ N := hF
    _ ≤ K * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * ((2 * π) ^ |m| * (1 + ‖θ‖) ^ |m|)) /
          (1 + ‖θ‖) ^ N := by gcongr
    _ = K * 2 ^ (|m| / 2) * (2 * π) ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖θ‖) ^ |m| * ((1 + ‖θ‖) ^ N)⁻¹) := by ring
    _ ≤ _ := by gcongr

/-- The left symbol of the right quantization of a cutoff `ψ(y - t) c(y, ξ)`. -/
private def cutoffLeft (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (t : CoordinateSpace n) (c : Symbol n V W m) : Symbol n V W m :=
  ofRight (cutoff ψ hψ t c) (hasCompactSpatialSupport_cutoff hψc)

/-- **The cut-off left symbols are bounded uniformly in the translation.** -/
private theorem exists_norm_coefficient_cutoffLeft_le (hψc : HasCompactSupport ψ)
    (hc : c.IsUniform) : ∃ C, 0 ≤ C ∧ ∀ t x ξ : CoordinateSpace n,
      ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_fourier_cutoff_add_le (hψ := hψ) hψc hc
  refine ⟨K * ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1)),
    mul_nonneg hK0 (integral_nonneg fun θ ↦ by positivity), fun t x ξ ↦ ?_⟩
  rw [cutoffLeft, coefficient_ofRight]
  calc _ ≤ ∫ θ : CoordinateSpace n, K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) :=
        norm_integral_le_of_norm_le (integrable_one_add_norm_rpow_neg_add_one.const_mul _)
          (.of_forall fun θ ↦ by rw [norm_smul, Circle.norm_coe, one_mul]; exact hK t θ ξ)
    _ = _ := by rw [integral_const_mul]; ring

private theorem frequencyDeriv_cutoffLeft (hψc : HasCompactSupport ψ) (t : CoordinateSpace n)
    (j : Fin n) :
    frequencyDeriv j (cutoffLeft ψ hψ hψc t c) = cutoffLeft ψ hψ hψc t (frequencyDeriv j c) := by
  unfold cutoffLeft
  rw [frequencyDeriv_ofRight]
  congr 1
  exact frequencyDeriv_cutoff j

private theorem hasCompactSupport_coordinateDeriv (hψc : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (coordinateDeriv [j] ψ) := by
  convert hψc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1) using 1
  funext x
  rw [coordinateDeriv_cons, coordinateDeriv_nil]

private theorem spatialDeriv_cutoffLeft (hψc : HasCompactSupport ψ) (t : CoordinateSpace n)
    (j : Fin n) :
    spatialDeriv j (cutoffLeft ψ hψ hψc t c) =
      cutoffLeft (coordinateDeriv [j] ψ) (hψ.coordinateDeriv [j])
          (hasCompactSupport_coordinateDeriv hψc j) t c +
        cutoffLeft ψ hψ hψc t (spatialDeriv j c) := by
  rw [cutoffLeft, spatialDeriv_ofRight]
  unfold cutoffLeft
  rw [← ofRight_add]
  congr 1
  exact spatialDeriv_cutoff j

private theorem contDiff_coord_mul (hψ : ContDiff ℝ ∞ ψ) (i : Fin n) :
    ContDiff ℝ ∞ fun z : CoordinateSpace n ↦ z i * ψ z :=
  (EuclideanSpace.proj i : CoordinateSpace n →L[ℝ] ℝ).contDiff.mul hψ

private theorem hasCompactSupport_coord_mul (hψc : HasCompactSupport ψ) (i : Fin n) :
    HasCompactSupport fun z : CoordinateSpace n ↦ z i * ψ z :=
  hψc.mul_left (f := fun z : CoordinateSpace n ↦ z i)

end Bounds

/-! ### Decay away from the cutoff -/

section Decay

variable [CompleteSpace V] [CompleteSpace W] {ψ : CoordinateSpace n → ℝ} {hψ : ContDiff ℝ ∞ ψ}
  {c : Symbol n V W m}

/-- **Multiplying by a coordinate of `x - t`.** The left symbol `b` of the right quantization of
`ψ(y - t) c(y, ξ)` satisfies `(x - t)ᵢ b = b₁ + i b₂`, where `b₁` and `b₂` are the left symbols of
`(y - t)ᵢ ψ(y - t) c(y, ξ)` and of `ψ(y - t) ∂_{ξᵢ} c(y, ξ)`. -/
private theorem coord_sub_smul_coefficient_cutoffLeft (hψc : HasCompactSupport ψ) (i : Fin n)
    (t x ξ : CoordinateSpace n) :
    ((x i - t i : ℝ) : ℂ) • (cutoffLeft ψ hψ hψc t c).coefficient (x, ξ) =
      (cutoffLeft _ (contDiff_coord_mul hψ i) (hasCompactSupport_coord_mul hψc i) t c).coefficient
          (x, ξ) +
        Complex.I • (cutoffLeft ψ hψ hψc t (frequencyDeriv i c)).coefficient (x, ξ) := by
  set b := cutoffLeft ψ hψ hψc t c
  set b₁ := cutoffLeft _ (contDiff_coord_mul hψ i) (hasCompactSupport_coord_mul hψc i) t c
  set b₂ := cutoffLeft ψ hψ hψc t (frequencyDeriv i c)
  set r : ℂ := ((x i - t i : ℝ) : ℂ)
  set S : Symbol n V W m := b₁ + Complex.I • inclusion (sub_le_self m zero_le_one) b₂
  have hS : S.coefficient = b₁.coefficient + Complex.I • b₂.coefficient := by
    simp [S, coefficient_add, coefficient_smul, coefficient_inclusion]
  obtain ⟨Ca, -, hCa⟩ := (r • b).exists_bound_coefficient_slice x
  obtain ⟨CS, -, hCS⟩ := S.exists_bound_coefficient_slice x
  obtain ⟨Cb, -, hCb⟩ := b.exists_bound_coefficient_slice x
  obtain ⟨C₁, -, hC₁⟩ := b₁.exists_bound_coefficient_slice x
  obtain ⟨C₂, -, hC₂⟩ :=
    (Complex.I • inclusion (sub_le_self m zero_le_one) b₂).exists_bound_coefficient_slice x
  have htg₁ : (fun y : CoordinateSpace n ↦ (x - y) i).HasTemperateGrowth :=
    (EuclideanSpace.proj i).hasTemperateGrowth.comp (by fun_prop : (x - ·).HasTemperateGrowth)
  have htg₂ : (fun y : CoordinateSpace n ↦ (y - t) i).HasTemperateGrowth :=
    (EuclideanSpace.proj i).hasTemperateGrowth.comp (by fun_prop : (· - t).HasTemperateGrowth)
  have key := eq_of_forall_quantizeSchwartzValue_eq ((r • b).continuous_coefficient_slice x)
    (S.continuous_coefficient_slice x) hCa hCS (fun u _ ↦ ?_) ξ
  · simpa [coefficient_smul, hS] using key
  -- Split `r u = (x - y)ᵢ u + (y - t)ᵢ u`.
  have hu : r • u = SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) i) u +
      SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (y - t) i) u := by
    ext y
    rw [add_apply, SchwartzMap.smulLeftCLM_apply_apply htg₁,
      SchwartzMap.smulLeftCLM_apply_apply htg₂, ← add_smul, smul_apply, Complex.coe_smul]
    congr 1
    simp only [PiLp.sub_apply]
    ring
  -- The second term is the right quantization of `(y - t)ᵢ ψ(y - t) c(y, ξ)`.
  have h₂ : quantizeSchwartzValue b.coefficient
      (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (y - t) i) u) x =
        quantizeSchwartzValue b₁.coefficient u x := by
    simp only [b, b₁, cutoffLeft, quantizeSchwartzValue_ofRight]
    refine congrArg (fun F ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • F ζ)
      (funext fun ζ ↦ congrArg (fun g : CoordinateSpace n → W ↦ 𝓕 g ζ) (funext fun y ↦ ?_))
    rw [coefficient_cutoff, coefficient_cutoff, SchwartzMap.smulLeftCLM_apply_apply htg₂,
      FunLike.coe_smul, Pi.smul_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.map_smul_of_tower, smul_smul, mul_comm]
  have hb₂ : (frequencyDeriv i b).coefficient = b₂.coefficient := by
    rw [frequencyDeriv_cutoffLeft]
  rw [coefficient_smul, quantizeSchwartzValue_smul_left, ← quantizeSchwartzValue_smul_right, hu,
    quantizeSchwartzValue_add_right (b.continuous_coefficient_slice x).aestronglyMeasurable hCb,
    quantizeSchwartzValue_smulLeftCLM_coord_sub, hb₂, h₂, coefficient_add,
    quantizeSchwartzValue_add_left (b₁.continuous_coefficient_slice x).aestronglyMeasurable hC₁
      ((Complex.I • inclusion (sub_le_self m zero_le_one) b₂).continuous_coefficient_slice
        x).aestronglyMeasurable hC₂,
    coefficient_smul, quantizeSchwartzValue_smul_left, coefficient_inclusion, add_comm]

/-- The norm form of `coord_sub_smul_coefficient_cutoffLeft`. -/
private theorem abs_coord_sub_mul_norm_coefficient_cutoffLeft_le (hψc : HasCompactSupport ψ)
    (i : Fin n) (t x ξ : CoordinateSpace n) :
    |x i - t i| * ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖ ≤
      ‖(cutoffLeft _ (contDiff_coord_mul hψ i) (hasCompactSupport_coord_mul hψc i) t
          c).coefficient (x, ξ)‖ +
        ‖(cutoffLeft ψ hψ hψc t (frequencyDeriv i c)).coefficient (x, ξ)‖ := by
  have h := congrArg norm (coord_sub_smul_coefficient_cutoffLeft (hψ := hψ) (c := c) hψc i t x ξ)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  rw [h]
  exact (norm_add_le _ _).trans (by rw [norm_smul, Complex.norm_I, one_mul])

/-- **Decay in the position.** The left symbol of the right quantization of `ψ(y - t) c(y, ξ)`,
multiplied by `∏_{i ∈ S} (1 + (x - t)ᵢ²)`, is bounded by `C ⟨ξ⟩ ^ m` uniformly in `t`. -/
private theorem exists_prod_mul_norm_coefficient_cutoffLeft_le (S : Finset (Fin n)) :
    ∀ {m : ℝ} {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      {c : Symbol n V W m}, c.IsUniform → ∃ C, 0 ≤ C ∧ ∀ t x ξ : CoordinateSpace n,
        (∏ i ∈ S, (1 + (x i - t i) ^ 2)) * ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro m ψ hψ hψc c hc
    simpa using exists_norm_coefficient_cutoffLeft_le (hψ := hψ) hψc hc
  | insert i S hi ih =>
    intro m ψ hψ hψc c hc
    have hψ₁ := contDiff_coord_mul hψ i
    have hψc₁ := hasCompactSupport_coord_mul hψc i
    obtain ⟨C₀, hC₀, h₀⟩ := ih hψ hψc hc
    obtain ⟨C₁, hC₁, h₁⟩ := ih (contDiff_coord_mul hψ₁ i) (hasCompactSupport_coord_mul hψc₁ i) hc
    obtain ⟨C₂, hC₂, h₂⟩ := ih hψ₁ hψc₁ (hc.frequencyDeriv i)
    obtain ⟨C₃, hC₃, h₃⟩ := ih hψ hψc ((hc.frequencyDeriv i).frequencyDeriv i)
    refine ⟨C₀ + C₁ + 2 * C₂ + C₃, by positivity, fun t x ξ ↦ ?_⟩
    set P := ∏ j ∈ S, (1 + (x j - t j) ^ 2)
    set z := x i - t i
    have e := abs_coord_sub_mul_norm_coefficient_cutoffLeft_le (hψ := hψ) (c := c) hψc i t x ξ
    have e₁ := abs_coord_sub_mul_norm_coefficient_cutoffLeft_le (hψ := hψ₁) (c := c) hψc₁ i t x ξ
    have e₂ := abs_coord_sub_mul_norm_coefficient_cutoffLeft_le (hψ := hψ) (c := frequencyDeriv i c)
      hψc i t x ξ
    have w₁ := rpow_weight_le_rpow_weight ξ (sub_le_self m zero_le_one)
    have w₂ := rpow_weight_le_rpow_weight ξ ((sub_le_self (m - 1) zero_le_one).trans
      (sub_le_self m zero_le_one))
    rw [Finset.prod_insert hi]
    calc (1 + z ^ 2) * P * ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖
        = P * ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖ +
            P * (|z| * (|z| * ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖)) := by
          rw [← sq_abs z]
          ring
      _ ≤ P * ‖(cutoffLeft ψ hψ hψc t c).coefficient (x, ξ)‖ +
            P * (‖(cutoffLeft _ (contDiff_coord_mul hψ₁ i) (hasCompactSupport_coord_mul hψc₁ i) t
                c).coefficient (x, ξ)‖ +
              ‖(cutoffLeft _ hψ₁ hψc₁ t (frequencyDeriv i c)).coefficient (x, ξ)‖ +
              (‖(cutoffLeft _ hψ₁ hψc₁ t (frequencyDeriv i c)).coefficient (x, ξ)‖ +
                ‖(cutoffLeft ψ hψ hψc t (frequencyDeriv i (frequencyDeriv i c))).coefficient
                  (x, ξ)‖)) := by
          gcongr
          refine (mul_le_mul_of_nonneg_left e (abs_nonneg z)).trans ?_
          rw [mul_add]
          exact add_le_add e₁ e₂
      _ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) + (C₁ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) +
            C₂ * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) + (C₂ * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) +
              C₃ * (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - 1) / 2))) := by
          simp only [mul_add]
          exact add_le_add (h₀ t x ξ) (add_le_add (add_le_add (h₁ t x ξ) (h₂ t x ξ))
            (add_le_add (h₂ t x ξ) (h₃ t x ξ)))
      _ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) + (C₁ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) +
            C₂ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) + (C₂ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) +
              C₃ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) := by gcongr
      _ = _ := by ring

/-- **Decay of all derivatives in the position.** Every mixed derivative `∂_x^α ∂_ξ^β` of the left
symbol of the right quantization of `ψ(y - t) c(y, ξ)`, multiplied by `∏ᵢ (1 + (x - t)ᵢ²)`, is
bounded by `C ⟨ξ⟩ ^ (m - |β|)` uniformly in `t`. -/
private theorem exists_prod_mul_norm_mixedDeriv_cutoffLeft_le (α β : List (Fin n)) :
    ∀ {m : ℝ} {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      {c : Symbol n V W m}, c.IsUniform → ∃ C, 0 ≤ C ∧ ∀ t x ξ : CoordinateSpace n,
        (∏ i, (1 + (x i - t i) ^ 2)) *
            ‖mixedDeriv α β (cutoffLeft ψ hψ hψc t c).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  induction β using List.reverseRecOn with
  | nil =>
    induction α using List.reverseRecOn with
    | nil =>
      intro m ψ hψ hψc c hc
      simpa [mixedDeriv_nil_nil] using
        exists_prod_mul_norm_coefficient_cutoffLeft_le Finset.univ hψ hψc hc
    | append_singleton α j ih =>
      intro m ψ hψ hψc c hc
      obtain ⟨C₁, hC₁, h₁⟩ :=
        ih (hψ.coordinateDeriv [j]) (hasCompactSupport_coordinateDeriv hψc j) hc
      obtain ⟨C₂, hC₂, h₂⟩ := ih hψ hψc (hc.spatialDeriv j)
      refine ⟨C₁ + C₂, by positivity, fun t x ξ ↦ ?_⟩
      rw [← mixedDeriv_spatialDeriv, spatialDeriv_cutoffLeft, coefficient_add,
        mixedDeriv_add (Symbol.contDiff_coefficient _) (Symbol.contDiff_coefficient _)]
      calc _ ≤ (∏ i, (1 + (x i - t i) ^ 2)) * ‖mixedDeriv α [] (cutoffLeft _ _
            (hasCompactSupport_coordinateDeriv hψc j) t c).coefficient x ξ‖ +
            (∏ i, (1 + (x i - t i) ^ 2)) *
              ‖mixedDeriv α [] (cutoffLeft ψ hψ hψc t (spatialDeriv j c)).coefficient x ξ‖ := by
            rw [← mul_add]
            gcongr
            exact norm_add_le _ _
        _ ≤ _ := by
            rw [add_mul]
            exact add_le_add (h₁ t x ξ) (h₂ t x ξ)
  | append_singleton β j ih =>
    intro m ψ hψ hψc c hc
    obtain ⟨C, hC, h⟩ := ih hψ hψc (hc.frequencyDeriv j)
    refine ⟨C, hC, fun t x ξ ↦ ?_⟩
    rw [← mixedDeriv_frequencyDeriv, frequencyDeriv_cutoffLeft, ← order_sub_one_sub_length]
    exact h t x ξ

end Decay

/-! ### Summing over the lattice -/

section Lattice

variable [CompleteSpace V] [CompleteSpace W] {c : Symbol n V W m}

/-- The left symbol of the right quantization of `χ(y - j) c(y, ξ)`, for the lattice partition of
unity `∑_{j ∈ ℤⁿ} χ(y - j) = 1` by translates of `χ = TauCeti.latticeBump n`. -/
private def latticeLeft (c : Symbol n V W m) (j : Fin n → ℤ) : Symbol n V W m :=
  cutoffLeft (latticeBump n) (contDiff_latticeBump (k := ⊤)) hasCompactSupport_latticeBump
    (latticePoint j) c

/-- The pieces decay like `∏ᵢ (1 + (x - j)ᵢ²)⁻¹` away from the lattice point `j`. -/
private theorem IsUniform.exists_norm_mixedDeriv_latticeLeft_le (hc : c.IsUniform)
    (α β : List (Fin n)) : ∃ C, 0 ≤ C ∧ ∀ j x ξ,
      ‖mixedDeriv α β (latticeLeft c j).coefficient x ξ‖ ≤
        C * (∏ i, (1 + (x i - j i) ^ 2))⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_prod_mul_norm_mixedDeriv_cutoffLeft_le α β
    (contDiff_latticeBump (k := ⊤)) hasCompactSupport_latticeBump hc
  refine ⟨C, hC0, fun j x ξ ↦ ?_⟩
  have h := hC (latticePoint j) x ξ
  simp only [latticePoint_apply] at h
  have hpos : 0 < ∏ i, (1 + (x i - j i) ^ 2) := Finset.prod_pos fun i _ ↦ by positivity
  rw [mul_comm C, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm]
  exact h

/-- The pieces have locally summable mixed derivatives. -/
private theorem IsUniform.locallySummableMixedDeriv_latticeLeft (hc : c.IsUniform) :
    LocallySummableMixedDeriv fun j ↦ (latticeLeft c j).coefficient := by
  refine ⟨fun j ↦ (latticeLeft c j).contDiff_coefficient, fun α β p₀ ↦ ?_⟩
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_mixedDeriv_latticeLeft_le α β
  set μ := m - β.length
  refine ⟨fun j ↦ C * (4 ^ n * (∏ i, (1 + (p₀.1 i - j i) ^ 2))⁻¹) *
      (2 ^ (|μ| / 2) * 2 ^ (|μ| / 2) * (1 + ‖p₀.2‖ ^ 2) ^ (μ / 2)),
    ((summable_prod_inv fun i ↦ p₀.1 i).mul_left _ |>.mul_left C |>.mul_right _),
    fun j p hp ↦ ?_⟩
  have hp' : ‖p - p₀‖ < 1 := by rwa [← dist_eq_norm]
  have hx : ∀ i, |p.1 i - p₀.1 i| ≤ 1 := fun i ↦ by
    rw [← Real.norm_eq_abs, ← PiLp.sub_apply]
    exact ((PiLp.norm_apply_le _ i).trans ((norm_fst_le (p - p₀)).trans hp'.le))
  have hξ : (1 + ‖p.2‖ ^ 2) ^ (μ / 2) ≤
      2 ^ (|μ| / 2) * 2 ^ (|μ| / 2) * (1 + ‖p₀.2‖ ^ 2) ^ (μ / 2) := by
    have h1 : ‖p.2 - p₀.2‖ ≤ 1 := (norm_snd_le (p - p₀)).trans hp'.le
    have h2 : (1 + ‖p.2 - p₀.2‖ ^ 2) ^ (|μ| / 2) ≤ 2 ^ (|μ| / 2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg (p.2 - p₀.2)])
        (by positivity)
    refine (one_add_norm_sq_rpow_le_mul_sub μ p.2 p₀.2).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity))
      (by positivity)
  calc ‖mixedDeriv α β (latticeLeft c j).coefficient p.1 p.2‖
      ≤ C * (∏ i, (1 + (p.1 i - j i) ^ 2))⁻¹ * (1 + ‖p.2‖ ^ 2) ^ (μ / 2) := hC j p.1 p.2
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left
        (prod_inv_le_four_pow_mul hx fun i ↦ (j i : ℝ)) hC0) hξ (by positivity)
        (mul_nonneg hC0 (by positivity))

/-- The mixed derivatives of the lattice sum satisfy the uniform symbol estimates. -/
private theorem IsUniform.exists_norm_mixedDeriv_tsum_latticeLeft_le (hc : c.IsUniform)
    (α β : List (Fin n)) : ∃ C, 0 ≤ C ∧ ∀ x ξ,
      ‖mixedDeriv α β (fun p ↦ ∑' j, (latticeLeft c j).coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_mixedDeriv_latticeLeft_le α β
  set W₀ := ∑' k : Fin n → ℤ, (∏ i, (1 + ((k i : ℤ) : ℝ) ^ 2))⁻¹
  refine ⟨C * (4 ^ n * W₀), mul_nonneg hC0 (mul_nonneg (by positivity)
    (tsum_nonneg fun k ↦ by positivity)), fun x ξ ↦ ?_⟩
  have hs : Summable fun j : Fin n → ℤ ↦
      C * (∏ i, (1 + (x i - j i) ^ 2))⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) :=
    ((summable_prod_inv fun i ↦ x i).mul_left C).mul_right _
  rw [mixedDeriv_tsum_of_locallySummableMixedDeriv hc.locallySummableMixedDeriv_latticeLeft]
  calc _ ≤ ∑' j : Fin n → ℤ,
        C * (∏ i, (1 + (x i - j i) ^ 2))⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) :=
        tsum_of_norm_bounded hs.hasSum fun j ↦ hC j x ξ
    _ = C * (∑' j : Fin n → ℤ, (∏ i, (1 + (x i - j i) ^ 2))⁻¹) *
          (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ _ := by
        gcongr
        exact tsum_prod_inv_le fun i ↦ x i

end Lattice

/-! ### The left symbol of a uniform right quantization -/

section OfRightUniform

variable [CompleteSpace V] [CompleteSpace W] {c : Symbol n V W m}

/-- **The left symbol of the right quantization of a uniform symbol.** For a symbol `c` of order
`m` whose estimates hold uniformly in the position, the left symbol `b` of its right quantization
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ`: a symbol of order `m` with estimates uniform in
the position (`TauCeti.Symbol.isUniform_ofRightUniform`) whose left quantization is the right
quantization of `c` (`TauCeti.Symbol.quantizeSchwartzValue_ofRightUniform`). It is
`∑_{j ∈ ℤⁿ} b_j` for the left symbols `b_j` (`TauCeti.Symbol.ofRight`) of the compactly
supported pieces `χ(y - j) c(y, ξ)` of `c`, and for `c` with compact spatial support it agrees
with `TauCeti.Symbol.ofRight` (`TauCeti.Symbol.ofRightUniform_eq_ofRight`). -/
def ofRightUniform (c : Symbol n V W m) (hc : c.IsUniform) : Symbol n V W m where
  coefficient p := ∑' j, (latticeLeft c j).coefficient p
  contDiff_coefficient :=
    contDiff_tsum_of_locallySummableMixedDeriv hc.locallySummableMixedDeriv_latticeLeft
  exists_bound _ _ α β := by
    obtain ⟨C, hC0, hC⟩ := hc.exists_norm_mixedDeriv_tsum_latticeLeft_le α β
    exact ⟨C, hC0, fun x _ ξ ↦ hC x ξ⟩

/-- The left symbol of a uniform right quantization satisfies its estimates uniformly in the
position. -/
@[simp]
theorem isUniform_ofRightUniform (hc : c.IsUniform) : (c.ofRightUniform hc).IsUniform :=
  isUniform_iff.2 hc.exists_norm_mixedDeriv_tsum_latticeLeft_le


private theorem coefficient_ofRightUniform_eq (hc : c.IsUniform)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (c.ofRightUniform hc).coefficient p = ∑' j, (latticeLeft c j).coefficient p :=
  (rfl)

/-! ### The quantization of the left symbol -/

/-- The quantization of the left symbol of `χ(y - j) c(y, ξ)` is the right quantization of that
cutoff. -/
private theorem quantizeSchwartzValue_latticeLeft (v : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) (j : Fin n → ℤ) :
    quantizeSchwartzValue (latticeLeft c j).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ latticeBump n (y - latticePoint j) •
        c.coefficient (y, (2 * π) • ζ) (v y)) ζ := by
  simp only [latticeLeft, cutoffLeft, quantizeSchwartzValue_ofRight, coefficient_cutoff,
    FunLike.coe_smul, Pi.smul_apply]

/-- **Step 1.** The quantization of the lattice sum is the sum of the quantizations of the
pieces. -/
private theorem IsUniform.hasSum_quantizeSchwartzValue_latticeLeft (hc : c.IsUniform)
    (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    HasSum (fun j ↦ quantizeSchwartzValue (latticeLeft c j).coefficient v x)
      (quantizeSchwartzValue (c.ofRightUniform hc).coefficient v x) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_mixedDeriv_latticeLeft_le [] []
  simp only [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero] at hC
  set F : (Fin n → ℤ) → CoordinateSpace n → W :=
    fun j ζ ↦ 𝐞 ⟪ζ, x⟫ • (latticeLeft c j).coefficient (x, (2 * π) • ζ) (𝓕 v ζ)
  set g : CoordinateSpace n → ℝ := fun ζ ↦ (2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 v ζ‖)
  have hg : Integrable g := ((𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _
  have hF (j : Fin n → ℤ) (ζ : CoordinateSpace n) :
      ‖F j ζ‖ ≤ C * (∏ i, (1 + (x i - j i) ^ 2))⁻¹ * g ζ := by
    simp only [F, g, Circle.norm_smul]
    calc ‖(latticeLeft c j).coefficient (x, (2 * π) • ζ) (𝓕 v ζ)‖
        ≤ ‖(latticeLeft c j).coefficient (x, (2 * π) • ζ)‖ * ‖𝓕 v ζ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (∏ i, (1 + (x i - j i) ^ 2))⁻¹ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) *
            ‖𝓕 v ζ‖ := by
          gcongr
          refine (hC j x _).trans ?_
          gcongr
          exact one_add_norm_smul_sq_rpow_le (by linarith [Real.two_le_pi]) m ζ
      _ = _ := by ring
  have hFi (j : Fin n → ℤ) : Integrable (F j) := by
    obtain ⟨C', -, hC'⟩ := (latticeLeft c j).exists_bound_coefficient_slice x
    exact integrable_quantizeSchwartzValue_integrand
      ((latticeLeft c j).continuous_coefficient_slice x).aestronglyMeasurable hC' (𝓕 v)
  have hsum : Summable fun j ↦ ∫ ζ, ‖F j ζ‖ := by
    refine (((summable_prod_inv fun i ↦ x i).mul_left C).mul_right (∫ ζ, g ζ)).of_nonneg_of_le
      (fun j ↦ integral_nonneg fun ζ ↦ norm_nonneg _) fun j ↦ ?_
    calc ∫ ζ, ‖F j ζ‖ ≤ ∫ ζ, C * (∏ i, (1 + (x i - j i) ^ 2))⁻¹ * g ζ :=
          integral_mono (hFi j).norm (hg.const_mul _) (hF j)
      _ = _ := integral_const_mul _ _
  convert hasSum_integral_of_summable_integral_norm hFi hsum using 1
  · funext j
    rw [quantizeSchwartzValue_def]
  rw [quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hb := (hc.locallySummableMixedDeriv_latticeLeft.summable (x, (2 * π) • ζ)).hasSum
  rw [← coefficient_ofRightUniform_eq hc] at hb
  have h := ((hb.mapL (ContinuousLinearMap.apply ℂ W (𝓕 v ζ))).const_smul
    (𝐞 ⟪ζ, x⟫ : ℂ)).tsum_eq
  simp only [ContinuousLinearMap.apply_apply] at h
  simp only [F, Circle.smul_def]
  exact h.symm


omit [CompleteSpace W] in
/-- The Fourier transforms of the lattice pieces `χ(y - j) h(y)` of an integrable function sum to
its Fourier transform. -/
private theorem hasSum_fourier_latticeBump_smul {h : CoordinateSpace n → W} (hh : Integrable h)
    (ζ : CoordinateSpace n) :
    HasSum (fun j : Fin n → ℤ ↦ 𝓕 (fun y ↦ latticeBump n (y - latticePoint j) • h y) ζ)
      (𝓕 h ζ) := by
  set G : (Fin n → ℤ) → CoordinateSpace n → W :=
    fun j y ↦ 𝐞 (-⟪y, ζ⟫) • latticeBump n (y - latticePoint j) • h y
  have hχ : Continuous (latticeBump n) := (contDiff_latticeBump (k := ⊤)).continuous
  have hG (j : Fin n → ℤ) (y : CoordinateSpace n) :
      ‖G j y‖ = latticeBump n (y - latticePoint j) * ‖h y‖ := by
    rw [Circle.norm_smul, norm_smul, Real.norm_of_nonneg (latticeBump_nonneg _)]
  have hGi (j : Fin n → ℤ) : Integrable (G j) := by
    refine (Real.fourierIntegral_convergent_iff ζ).2 ?_
    exact hh.bdd_smul (φ := fun y ↦ latticeBump n (y - latticePoint j)) 1
      (hχ.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (latticeBump_nonneg _)]
        exact latticeBump_le_one _)
  have hsum : Summable fun j ↦ ∫ y, ‖G j y‖ := by
    refine summable_of_sum_le (c := ∫ y, ‖h y‖) (fun j ↦ integral_nonneg fun y ↦ norm_nonneg _)
      fun s ↦ ?_
    rw [← integral_finsetSum _ fun j _ ↦ (hGi j).norm]
    refine integral_mono (integrable_finsetSum _ fun j _ ↦ (hGi j).norm) hh.norm fun y ↦ ?_
    simp only [hG, ← Finset.sum_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (sum_le_hasSum s (fun j _ ↦ latticeBump_nonneg _) (hasSum_latticeBump_sub y))
  convert hasSum_integral_of_summable_integral_norm hGi hsum using 1
  · funext j
    rw [Real.fourier_eq]
  rw [Real.fourier_eq]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  have h₁ := ((hasSum_latticeBump_sub y).smul_const (h y)).const_smul (𝐞 (-⟪y, ζ⟫) : ℂ)
  rw [one_smul] at h₁
  simp only [G, Circle.smul_def]
  exact h₁.tsum_eq.symm


omit [CompleteSpace V] in
/-- A Schwartz function and its derivatives of order at most `N` decay like
`∏ᵢ (1 + yᵢ²)⁻¹`. -/
private theorem exists_norm_iteratedFDeriv_schwartz_le (v : 𝓢(CoordinateSpace n, V)) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ k ≤ N, ∀ y : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k v y‖ ≤ C * (∏ i, (1 + (y i - 0) ^ 2))⁻¹ := by
  refine ⟨2 ^ (2 * n) * (Finset.Iic (2 * n, N)).sup (fun q ↦ SchwartzMap.seminorm ℂ q.1 q.2) v,
    mul_nonneg (by positivity) (apply_nonneg _ _), fun k hk y ↦ ?_⟩
  have hpos : 0 < ∏ i, (1 + (y i - 0) ^ 2) := Finset.prod_pos fun i _ ↦ by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  refine le_trans ?_
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (2 * n, N)) le_rfl hk v y)
  gcongr
  calc ∏ i, (1 + (y i - 0) ^ 2) ≤ ∏ _i : Fin n, (1 + ‖y‖) ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ by
          have h := PiLp.norm_apply_le y i
          rw [Real.norm_eq_abs] at h
          rw [sub_zero, ← sq_abs]
          nlinarith [abs_nonneg (y i), norm_nonneg y]
    _ = (1 + ‖y‖) ^ (2 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- The application `(T, u) ↦ T u` of `ℂ`-linear maps, a continuous real bilinear map of norm at
most `1`. -/
private def applyBilin (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] : (V →L[ℂ] W) →L[ℝ] V →L[ℝ] W :=
  (ContinuousLinearMap.apply ℂ W).flip.bilinearRestrictScalars ℝ

omit [CompleteSpace V] [CompleteSpace W] in
private theorem applyBilin_apply (T : V →L[ℂ] W) (u : V) : applyBilin V W T u = T u := by
  simp [applyBilin]

omit [CompleteSpace V] [CompleteSpace W] in
private theorem norm_applyBilin_le : ‖applyBilin V W‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun T u ↦ by
    simpa [applyBilin_apply] using T.le_opNorm u

omit [CompleteSpace V] [CompleteSpace W] in
private theorem coefficient_apply_eq_applyBilin (c : Symbol n V W m)
    (v : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    (fun y ↦ c.coefficient (y, ξ) (v y)) = fun y ↦ applyBilin V W (c.coefficient (y, ξ)) (v y) :=
  funext fun _ ↦ (applyBilin_apply _ _).symm

omit [CompleteSpace V] [CompleteSpace W] in
private theorem contDiff_coefficient_apply (c : Symbol n V W m) (v : 𝓢(CoordinateSpace n, V))
    (ξ : CoordinateSpace n) : ContDiff ℝ ∞ fun y ↦ c.coefficient (y, ξ) (v y) := by
  rw [coefficient_apply_eq_applyBilin]
  exact (applyBilin V W).isBoundedBilinearMap.contDiff.comp
    ((c.contDiff_coefficient_slice ξ).prodMk (v.smooth ⊤))

omit [CompleteSpace V] [CompleteSpace W] in
/-- The derivatives of `y ↦ c(y, ξ) v(y)` of order at most `N` are bounded by
`C ⟨ξ⟩ ^ m ∏ᵢ (1 + yᵢ²)⁻¹`. -/
private theorem IsUniform.exists_norm_iteratedFDeriv_coefficient_apply_le (hc : c.IsUniform)
    (v : 𝓢(CoordinateSpace n, V)) (N : ℕ) : ∃ C, 0 ≤ C ∧ ∀ q ≤ N, ∀ y ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ q (fun y ↦ c.coefficient (y, ξ) (v y)) y‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (∏ i, (1 + (y i - 0) ^ 2))⁻¹ := by
  obtain ⟨A, hA0, hA⟩ := hc.exists_norm_iteratedFDeriv_slice_le N
  obtain ⟨Cv, hCv0, hv⟩ := exists_norm_iteratedFDeriv_schwartz_le v N
  refine ⟨2 ^ N * A * Cv, by positivity, fun q hq y ξ ↦ ?_⟩
  set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  set ρ := (∏ i, (1 + (y i - 0) ^ 2))⁻¹
  rw [coefficient_apply_eq_applyBilin]
  refine ((applyBilin V W).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (c.contDiff_coefficient_slice ξ) (v.smooth ⊤) y (mod_cast le_top) norm_applyBilin_le).trans ?_
  calc ∑ r ∈ Finset.range (q + 1), (q.choose r : ℝ) *
        ‖iteratedFDeriv ℝ r (fun y ↦ c.coefficient (y, ξ)) y‖ * ‖iteratedFDeriv ℝ (q - r) v y‖
      ≤ ∑ r ∈ Finset.range (q + 1), (q.choose r : ℝ) * (A * w) * (Cv * ρ) := by
        refine Finset.sum_le_sum fun r hr ↦ ?_
        have hr' : r ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
        gcongr
        · exact hA r (hr'.trans hq) y ξ
        · exact hv _ ((Nat.sub_le q r).trans hq) y
    _ = 2 ^ q * A * Cv * w * ρ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ _ := by gcongr; norm_num

omit [CompleteSpace W] in
/-- A function cut off by `χ(y - j)` is supported where `y - j` is in the support of `χ`. -/
private theorem tsupport_latticeBump_sub_smul_subset (g : CoordinateSpace n → W)
    (j : Fin n → ℤ) :
    tsupport (fun y ↦ latticeBump n (y - latticePoint j) • g y) ⊆
      {y | y - latticePoint j ∈ tsupport (latticeBump n)} :=
  closure_minimal (fun _ hy ↦ subset_tsupport _ (left_ne_zero_of_smul hy))
    (isClosed_tsupport _ |>.preimage (continuous_id.sub continuous_const))

omit [CompleteSpace V] [CompleteSpace W] in
/-- The derivatives of the pieces `χ(y - j) c(y, ξ) v(y)` of order at most `N` are bounded by
`C ⟨ξ⟩ ^ m ∏ᵢ (1 + jᵢ²)⁻¹`, uniformly in the position. -/
private theorem IsUniform.exists_norm_iteratedFDeriv_latticeBump_smul_le (hc : c.IsUniform)
    (v : 𝓢(CoordinateSpace n, V)) (N : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (j : Fin n → ℤ), ∀ p ≤ N,
      ∀ y ξ : CoordinateSpace n, ‖iteratedFDeriv ℝ p
        (fun y ↦ latticeBump n (y - latticePoint j) • c.coefficient (y, ξ) (v y)) y‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (∏ i, (1 + ((j i : ℤ) : ℝ) ^ 2))⁻¹ := by
  have hχ : ContDiff ℝ ∞ (latticeBump n) := contDiff_latticeBump (k := ⊤)
  obtain ⟨Bχ, hBχ0, hBχ⟩ := hasCompactSupport_latticeBump.exists_bound_iteratedFDeriv hχ N
  obtain ⟨A, hA0, hA⟩ := hc.exists_norm_iteratedFDeriv_coefficient_apply_le v N
  set K := (2 * (1 + √n ^ 2)) ^ n
  refine ⟨2 ^ N * Bχ * A * K, by positivity, fun j p hp y ξ ↦ ?_⟩
  set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  set ρ := (∏ i, (1 + ((j i : ℤ) : ℝ) ^ 2))⁻¹
  have hχj : ContDiff ℝ ∞ fun y ↦ latticeBump n (y - latticePoint j) :=
    hχ.comp (contDiff_id.sub contDiff_const)
  have hHs := contDiff_coefficient_apply c v ξ
  by_cases hy : y - latticePoint j ∈ tsupport (latticeBump n)
  · -- Near `j` the weight at `y` is comparable to the weight at `j`.
    have hyj : ∀ i, |y i - ((j i : ℤ) : ℝ)| ≤ √n := fun i ↦ by
      have h := tsupport_latticeBump_subset hy
      rw [mem_closedBall_zero_iff] at h
      calc |y i - ((j i : ℤ) : ℝ)| = ‖(y - latticePoint j) i‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖y - latticePoint j‖ := PiLp.norm_apply_le _ _
        _ ≤ √n := h
    have hw : (∏ i, (1 + (y i - 0) ^ 2))⁻¹ ≤ K * ρ := by
      simpa only [sub_zero] using prod_inv_le_of_abs_sub_le hyj fun _ ↦ 0
    refine (norm_iteratedFDeriv_smul_le hχj hHs y (mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y ↦ latticeBump n (y - latticePoint j)) y‖ *
            ‖iteratedFDeriv ℝ (p - i) (fun y ↦ c.coefficient (y, ξ) (v y)) y‖
        ≤ ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * Bχ * (A * w * (K * ρ)) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [iteratedFDeriv_comp_sub]
          gcongr
          · exact hBχ i (hi'.trans hp) _
          · exact (hA _ ((Nat.sub_le p i).trans hp) y ξ).trans (by gcongr)
      _ = 2 ^ p * Bχ * A * K * w * ρ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
      _ ≤ _ := by gcongr; norm_num
  · -- Away from `j` all the derivatives of the piece vanish.
    rw [Function.notMem_support.1 fun h ↦ hy (tsupport_latticeBump_sub_smul_subset _ j
      (support_iteratedFDeriv_subset p h)), norm_zero]
    positivity

omit [CompleteSpace V] [CompleteSpace W] in
/-- The Fourier transforms of the pieces `χ(y - j) c(y, 2πζ) v(y)` of the right quantization
decay like `(1 + ‖ζ‖) ^ (-(n + 1))` in the frequency and like `∏ᵢ (1 + jᵢ²)⁻¹` in the lattice
point. -/
private theorem IsUniform.exists_norm_fourier_latticeBump_smul_le (hc : c.IsUniform)
    (v : 𝓢(CoordinateSpace n, V)) : ∃ D, 0 ≤ D ∧ ∀ (j : Fin n → ℤ) (ζ : CoordinateSpace n),
      ‖𝓕 (fun y ↦ latticeBump n (y - latticePoint j) • c.coefficient (y, (2 * π) • ζ) (v y)) ζ‖ ≤
        D * (∏ i, (1 + ((j i : ℤ) : ℝ) ^ 2))⁻¹ * (1 + ‖ζ‖) ^ (-((n : ℝ) + 1)) := by
  set N := n + 1 + ⌈|m|⌉₊
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_iteratedFDeriv_latticeBump_smul_le v N
  set V₀ := volume.real (Metric.closedBall (0 : CoordinateSpace n) √n)
  refine ⟨2 ^ N * C * V₀ * (2 * π) ^ |m|, by positivity, fun j ζ ↦ ?_⟩
  set f := fun y ↦ latticeBump n (y - latticePoint j) • c.coefficient (y, (2 * π) • ζ) (v y)
  set ρ := (∏ i, (1 + ((j i : ℤ) : ℝ) ^ 2))⁻¹
  set w := (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2)
  have hfS : tsupport f ⊆ Metric.closedBall (latticePoint j) √n := fun y hy ↦ by
    have h := tsupport_latticeBump_subset (tsupport_latticeBump_sub_smul_subset _ j hy)
    rwa [mem_closedBall_zero_iff, ← dist_eq_norm, ← Metric.mem_closedBall] at h
  have hvol : volume.real (Metric.closedBall (latticePoint j) √n) = V₀ := by
    simp only [V₀, Measure.real, Measure.addHaar_closedBall_center]
  have hf : ContDiff ℝ N f := (((contDiff_latticeBump (k := ⊤)).comp
    (contDiff_id.sub contDiff_const)).smul (contDiff_coefficient_apply c v _)).of_le
      (by exact_mod_cast le_top)
  have hdecay := one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset hf
    measurableSet_closedBall measure_closedBall_lt_top.ne hfS
    (fun p hp y ↦ hC j p hp y ((2 * π) • ζ)) ζ
  rw [hvol] at hdecay
  -- Absorb the growth `⟨2πζ⟩ ^ m ≤ (2π) ^ |m| (1 + ‖ζ‖) ^ |m|` of the symbol into the decay.
  have hwζ : w ≤ (2 * π) ^ |m| * (1 + ‖ζ‖) ^ |m| := by
    refine (one_add_norm_smul_sq_rpow_le (by linarith [Real.two_le_pi]) m ζ).trans ?_
    gcongr
    exact (rpow_weight_le_rpow_weight ζ (le_abs_self m)).trans
      (one_add_norm_sq_rpow_le_one_add_norm_rpow ζ (abs_nonneg m))
  calc ‖𝓕 f ζ‖ ≤ 2 ^ N * (C * w * ρ * V₀) / (1 + ‖ζ‖) ^ N :=
        (le_div_iff₀' (by positivity)).2 hdecay
    _ ≤ 2 ^ N * (C * ((2 * π) ^ |m| * (1 + ‖ζ‖) ^ |m|) * ρ * V₀) / (1 + ‖ζ‖) ^ N := by gcongr
    _ = 2 ^ N * C * V₀ * (2 * π) ^ |m| * ρ * ((1 + ‖ζ‖) ^ |m| * ((1 + ‖ζ‖) ^ N)⁻¹) := by ring
    _ ≤ _ := by gcongr; exact one_add_norm_rpow_abs_mul_inv_pow_le m ζ

/-- **Step 2.** The quantizations of the left symbols of the pieces sum to the right quantization
of `c`. -/
private theorem IsUniform.hasSum_quantizeSchwartzValue_latticeLeft_right (hc : c.IsUniform)
    (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    HasSum (fun j ↦ quantizeSchwartzValue (latticeLeft c j).coefficient v x)
      (∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ) := by
  obtain ⟨D, -, hD⟩ := hc.exists_norm_fourier_latticeBump_smul_le v
  obtain ⟨C, -, hC⟩ := isUniform_iff.1 hc [] []
  set G : (Fin n → ℤ) → CoordinateSpace n → W := fun j ζ ↦ 𝐞 ⟪ζ, x⟫ •
    𝓕 (fun y ↦ latticeBump n (y - latticePoint j) • c.coefficient (y, (2 * π) • ζ) (v y)) ζ
  have hGi (j : Fin n → ℤ) : Integrable (G j) := by
    have h := (hasCompactSpatialSupport_cutoff (hψ := contDiff_latticeBump (k := ⊤))
      (t := latticePoint j) (c := c)
      hasCompactSupport_latticeBump).integrable_fourier_coefficient_apply v
    simp only [coefficient_cutoff, FunLike.coe_smul, Pi.smul_apply] at h
    simp only [G, Circle.smul_def]
    exact h.norm.mono' ((by fun_prop : Continuous fun ζ : CoordinateSpace n ↦
      (𝐞 ⟪ζ, x⟫ : ℂ)).aestronglyMeasurable.smul h.aestronglyMeasurable)
      (.of_forall fun ζ ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  have hρ : Summable fun j : Fin n → ℤ ↦ (∏ i, (1 + ((j i : ℤ) : ℝ) ^ 2))⁻¹ := by
    simpa using summable_prod_inv fun _ : Fin n ↦ (0 : ℝ)
  set I := ∫ ζ : CoordinateSpace n, (1 + ‖ζ‖) ^ (-((n : ℝ) + 1))
  have hsum : Summable fun j ↦ ∫ ζ, ‖G j ζ‖ := by
    refine ((hρ.mul_left D).mul_right I).of_nonneg_of_le
      (fun j ↦ integral_nonneg fun ζ ↦ norm_nonneg _) fun j ↦ ?_
    calc ∫ ζ, ‖G j ζ‖ ≤ ∫ ζ, D * (∏ i, (1 + ((j i : ℤ) : ℝ) ^ 2))⁻¹ *
          (1 + ‖ζ‖) ^ (-((n : ℝ) + 1)) :=
          integral_mono (hGi j).norm (integrable_one_add_norm_rpow_neg_add_one.const_mul _)
            fun ζ ↦ by simpa only [G, Circle.norm_smul] using hD j ζ
      _ = _ := integral_const_mul _ _
  convert hasSum_integral_of_summable_integral_norm hGi hsum using 1
  · funext j
    exact quantizeSchwartzValue_latticeLeft v x j
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hint : Integrable fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y) := by
    refine (v.integrable.norm.const_mul (C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2))).mono'
      ((c.contDiff_coefficient_slice _).continuous.clm_apply v.continuous).aestronglyMeasurable
      (.of_forall fun y ↦ ?_)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    simpa [mixedDeriv_def, coordinateDeriv_nil] using hC y ((2 * π) • ζ)
  have h := (hasSum_fourier_latticeBump_smul hint ζ).const_smul (𝐞 ⟪ζ, x⟫ : ℂ)
  simp only [G, Circle.smul_def]
  exact h.tsum_eq.symm

/-- **The quantization of the left symbol is the right quantization.** For a symbol `c` whose
estimates are uniform in the position and a Schwartz function `v`,
`Op(c.ofRightUniform hc) v (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ) dζ`, which in
angular frequency is the right quantization `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) v(y) dy dξ`. -/
theorem quantizeSchwartzValue_ofRightUniform (hc : c.IsUniform) (v : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (c.ofRightUniform hc).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ :=
  (hc.hasSum_quantizeSchwartzValue_latticeLeft v x).unique
    (hc.hasSum_quantizeSchwartzValue_latticeLeft_right v x)

/-- For a symbol with compact spatial support, `ofRightUniform` is the left symbol
`TauCeti.Symbol.ofRight` of its right quantization. -/
theorem ofRightUniform_eq_ofRight (hc : c.HasCompactSpatialSupport) :
    c.ofRightUniform hc.isUniform = c.ofRight hc :=
  Symbol.ext <| coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦ funext fun x ↦ by
    rw [quantizeSchwartzValue_ofRightUniform, quantizeSchwartzValue_ofRight]

end OfRightUniform

end Symbol

end TauCeti
