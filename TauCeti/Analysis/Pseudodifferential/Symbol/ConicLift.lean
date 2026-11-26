/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.ExternalProduct
public import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import TauCeti.Analysis.Pseudodifferential.FourierSchur
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Lifting a symbol to a product, cut off near an axis

Let `p(x, ξ)` be a symbol of order `m` on a factor `ℝⁿ` of a product `ℝᴺ = ℝⁿ × ℝⁿ'`, and let
`P : ℝᴺ → ℝⁿ` be the projection onto that factor. The function `(x, ξ) ↦ p(P x, P ξ)` on the
product is not a symbol: a frequency derivative of `p` gains a power of `⟨P ξ⟩⁻¹`, which is not a
power of `⟨ξ⟩⁻¹` near the axis `P ξ = 0`. The remedy is to cut `p` off in a small cone around that
axis, keeping it unchanged at bounded frequencies. For a conic cutoff `χ` (`TauCeti.ConicCutoff`),
a frequency cutoff `φ` (`TauCeti.FrequencyCutoff`), `ε > 0` and `R ≥ 1`, put

`c(ξ) = 1 - φ(ξ / R) (1 - χ(‖P ξ‖² / (ε² ‖ξ‖²)))` (`TauCeti.conicLiftCutoff`).

It equals `1` for `‖ξ‖ ≤ R` and on the cone `‖P ξ‖² ≥ ε² ‖ξ‖² / 2`, and vanishes near every
frequency with `‖ξ‖ > 2 R` and `‖P ξ‖² < ε² ‖ξ‖² / 4`. It is a symbol of order `0`, and the lifted
symbol `c(ξ) p(P x, P ξ)` is a symbol of order `m` on `ℝᴺ` (`TauCeti.Symbol.conicLift`): on its
support away from bounded frequencies `⟨P ξ⟩` and `⟨ξ⟩` are comparable, so the estimates of `p`
in `P ξ` become estimates in `ξ`. Any linear `P` is allowed, for instance the projection onto
either factor.

The cutoff changes `p(P x, P ξ)` only where `‖ξ‖ > R` and `‖P ξ‖ < ε ‖ξ‖`, where
`⟨P ξ⟩ ≤ √2 ε ⟨ξ⟩` once `R ≥ ε⁻¹`. So for `m ≥ 0` the position derivatives of the difference are
`O(ε ^ m ⟨ξ⟩ ^ m)`, uniformly in `ε` and `R`
(`TauCeti.Symbol.exists_norm_mixedDeriv_sub_conicLift_le`). No frequency derivatives of the
difference are controlled, and none are claimed: the difference is not a symbol uniformly in `ε`.
These position bounds are what the weighted Fourier–Schur estimate needs, so after localization by
a compactly supported cutoff `ψ` the two quantizations are `O(ε ^ m)` apart as operators
`H^s → H^{s - m}`, for every real `s`
(`TauCeti.Symbol.exists_eLpNorm_smul_fourier_smul_quantizeSchwartzValue_sub_conicLift_le`);
for `m = 1` this is the bound `C ε` from `H¹` to `L²`.

The full symbols of the external product of two elliptic operators on the factors of a product
have entries of the form `p(P x, P ξ)`, singular along an axis; their lifts are symbols of order
`m` (in `S^m_{1,0}`) on the product, close to the original entries in the sense above. The lift
of a classical symbol is classical (`TauCeti.ClassicalSymbol.conicLift`, in
`TauCeti.Analysis.Pseudodifferential.Symbol.Classical.ConicLift`), and its homogeneous terms are
the homogeneous counterpart of the construction, `TauCeti.HomogeneousSymbol.conicLift`, with the
same `P`, `χ` and `ε`. The product-specific variant `TauCeti.HomogeneousSymbol.conicCutoffFst`
uses the ratio `‖ξ‖² / (‖ξ‖² + ‖η‖²)` instead.

## Main declarations

* `TauCeti.conicLiftCutoff`: the cutoff `c`, with `TauCeti.contDiff_conicLiftCutoff`, its values
  `TauCeti.conicLiftCutoff_eq_one_of_norm_le`, `TauCeti.conicLiftCutoff_eq_one_of_le`,
  `TauCeti.conicLiftCutoff_eventuallyEq_zero`, its angular form at large frequencies
  `TauCeti.conicLiftCutoff_eq_of_two_mul_le_norm`, the range `TauCeti.conicLiftCutoff_nonneg`,
  `TauCeti.conicLiftCutoff_le_one`, and the order-zero estimates
  `TauCeti.exists_norm_iteratedFDeriv_conicLiftCutoff_le`.
* `TauCeti.Symbol.conicLift`: the lifted symbol `c(ξ) p(P x, P ξ)` of order `m` on `ℝᴺ`, equal
  to `p(P x, P ξ)` on the cone and at bounded frequencies
  (`TauCeti.Symbol.coefficient_conicLift_of_le`,
  `TauCeti.Symbol.coefficient_conicLift_of_norm_le`), and vanishing near the axis at high
  frequencies (`TauCeti.Symbol.coefficient_conicLift_eventuallyEq_zero`).
* `TauCeti.Symbol.exists_norm_mixedDeriv_sub_conicLift_le`: the bound `C ε ^ m ⟨ξ⟩ ^ m` on the
  position derivatives of `p(P x, P ξ) - c(ξ) p(P x, P ξ)`, uniform in `ε` and `R ≥ max 1 ε⁻¹`.
* `TauCeti.Symbol.exists_eLpNorm_smul_fourier_smul_quantizeSchwartzValue_sub_conicLift_le`:
  the bound `‖ψ (Op(p ∘ P) u - Op(c p) u)‖_{H^{s - m}} ≤ C ε ^ m ‖u‖_{H^s}`, with the same
  uniformity.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968), §9,
  pp. 526–530 (the external product of elliptic operators on a product).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {N n : ℕ}

/-! ### The cutoff near the axis -/

section Cutoff

variable (P : CoordinateSpace N →L[ℝ] CoordinateSpace n) (χ : ConicCutoff)
  (φ : FrequencyCutoff (CoordinateSpace N)) (ε R : ℝ)

/-- The cutoff `c(ξ) = 1 - φ(ξ / R) (1 - χ(‖P ξ‖² / (ε² ‖ξ‖²)))` near the axis `P ξ = 0`. It
equals `1` for `‖ξ‖ ≤ R` and on the cone `‖P ξ‖² ≥ ε² ‖ξ‖² / 2`, and vanishes near the frequencies
with `‖ξ‖ > 2 R` and `‖P ξ‖² < ε² ‖ξ‖² / 4`. -/
def conicLiftCutoff (ξ : CoordinateSpace N) : ℝ :=
  1 - φ (R⁻¹ • ξ) * (1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2)))

theorem conicLiftCutoff_def (ξ : CoordinateSpace N) :
    conicLiftCutoff P χ φ ε R ξ = 1 - φ (R⁻¹ • ξ) * (1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))) :=
  (rfl)

theorem conicLiftCutoff_nonneg (ξ : CoordinateSpace N) : 0 ≤ conicLiftCutoff P χ φ ε R ξ := by
  have h₁ := φ.le_one (R⁻¹ • ξ)
  have h₂ := χ.nonneg (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))
  have h₃ := φ.nonneg (R⁻¹ • ξ)
  rw [conicLiftCutoff_def, sub_nonneg]
  nlinarith

theorem conicLiftCutoff_le_one (ξ : CoordinateSpace N) : conicLiftCutoff P χ φ ε R ξ ≤ 1 := by
  have h₁ := χ.le_one (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))
  have h₂ := φ.nonneg (R⁻¹ • ξ)
  rw [conicLiftCutoff_def, sub_le_self_iff]
  exact mul_nonneg h₂ (sub_nonneg.2 h₁)

variable {P χ φ ε R}

/-- The cutoff equals `1` at bounded frequencies. -/
theorem conicLiftCutoff_eq_one_of_norm_le (hR : 0 < R) {ξ : CoordinateSpace N} (hξ : ‖ξ‖ ≤ R) :
    conicLiftCutoff P χ φ ε R ξ = 1 := by
  rw [conicLiftCutoff_def, φ.apply_inv_smul_eq_zero hR hξ, zero_mul, sub_zero]

/-- The cutoff equals `1` on the cone `‖P ξ‖² ≥ ε² ‖ξ‖² / 2`. -/
theorem conicLiftCutoff_eq_one_of_le (hε : ε ≠ 0) {ξ : CoordinateSpace N}
    (hξ : ε ^ 2 * ‖ξ‖ ^ 2 / 2 ≤ ‖P ξ‖ ^ 2) : conicLiftCutoff P χ φ ε R ξ = 1 := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · simp [conicLiftCutoff_def]
  have hpos : 0 < ε ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [conicLiftCutoff_def, χ.apply_eq_one_of_one_div_two_le (by rw [le_div_iff₀ hpos]; linarith),
    sub_self, mul_zero, sub_zero]

/-- At frequencies `‖ξ‖ ≥ 2 R` the cutoff is the angular factor `χ(‖P ξ‖² / (ε² ‖ξ‖²))`, which is
positively homogeneous of degree `0`. -/
theorem conicLiftCutoff_eq_of_two_mul_le_norm (hR : 0 < R) {ξ : CoordinateSpace N}
    (hξ : 2 * R ≤ ‖ξ‖) : conicLiftCutoff P χ φ ε R ξ = χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2)) := by
  rw [conicLiftCutoff_def, φ.apply_inv_smul_eq_one hR hξ, one_mul, sub_sub_cancel]

/-- The cutoff vanishes near every frequency with `‖ξ‖ > 2 R` and `‖P ξ‖² < ε² ‖ξ‖² / 4`. -/
theorem conicLiftCutoff_eventuallyEq_zero (hε : ε ≠ 0) (hR : 0 < R) {ξ : CoordinateSpace N}
    (hξ : 2 * R < ‖ξ‖) (hPξ : ‖P ξ‖ ^ 2 < ε ^ 2 * ‖ξ‖ ^ 2 / 4) :
    conicLiftCutoff P χ φ ε R =ᶠ[𝓝 ξ] 0 := by
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
  have hden : ε ^ 2 * ‖ξ‖ ^ 2 ≠ 0 := by positivity
  -- The ratio `‖P η‖² / (ε² ‖η‖²)` is continuous at `ξ`, where it is below `1 / 4`.
  have hratio : ContinuousAt (fun η ↦ ‖P η‖ ^ 2 / (ε ^ 2 * ‖η‖ ^ 2)) ξ := by
    fun_prop (disch := exact hden)
  have hlt : ∀ᶠ η in 𝓝 ξ, ‖P η‖ ^ 2 / (ε ^ 2 * ‖η‖ ^ 2) < 1 / 4 :=
    hratio.eventually (gt_mem_nhds (by rw [div_lt_iff₀ (by positivity)]; linarith))
  have hfar : ∀ᶠ η in 𝓝 ξ, 2 * R < ‖η‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hξ)
  filter_upwards [hlt, hfar] with η hη hηR
  rw [conicLiftCutoff_def, φ.apply_inv_smul_eq_one hR hηR.le,
    χ.apply_eq_zero_of_le_one_div_four hη.le, Pi.zero_apply]
  ring

variable (P χ) in
/-- The angular factor `1 - χ(‖P ξ‖² / (ε² ‖ξ‖²))` is positively homogeneous of degree `0`. -/
private theorem angular_smul (ε : ℝ) {t : ℝ} (ht : 0 < t) (ξ : CoordinateSpace N) :
    1 - χ (‖P (t • ξ)‖ ^ 2 / (ε ^ 2 * ‖t • ξ‖ ^ 2)) = 1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2)) := by
  rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_pow, mul_pow,
    mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne')]

variable (P χ) in
/-- The angular factor is smooth away from `ξ = 0`. -/
private theorem contDiffOn_angular (hε : ε ≠ 0) :
    ContDiffOn ℝ ∞ (fun ξ : CoordinateSpace N ↦ 1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))) {0}ᶜ := by
  have hnum : ContDiff ℝ ∞ fun ξ : CoordinateSpace N ↦ ‖P ξ‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp P.contDiff
  have hden : ContDiff ℝ ∞ fun ξ : CoordinateSpace N ↦ ε ^ 2 * ‖ξ‖ ^ 2 :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  exact contDiffOn_const.sub (χ.contDiff.comp_contDiffOn
    (hnum.contDiffOn.div hden.contDiffOn fun ξ hξ ↦ by
      have : ξ ≠ 0 := Set.mem_compl_singleton_iff.1 hξ
      positivity))

/-- The cutoff is smooth: near bounded frequencies it is constant, and away from `ξ = 0` all its
factors are smooth. -/
theorem contDiff_conicLiftCutoff (hε : ε ≠ 0) (hR : 0 < R) :
    ContDiff ℝ ∞ (conicLiftCutoff P χ φ ε R) := by
  refine contDiff_iff_contDiffAt.2 fun ξ ↦ ?_
  rcases lt_or_ge ‖ξ‖ R with hξ | hξ
  · refine contDiffAt_const (c := (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hξ)] with η hη
    exact conicLiftCutoff_eq_one_of_norm_le hR hη.le
  · have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (hR.trans_le hξ)
    have hφ : ContDiff ℝ ∞ fun η : CoordinateSpace N ↦ φ (R⁻¹ • η) :=
      φ.contDiff.comp (contDiff_const_smul _)
    exact contDiffAt_const.sub (hφ.contDiffAt.mul
      ((contDiffOn_angular P χ hε).contDiffAt (isOpen_compl_singleton.mem_nhds hξ0)))

/-- **Estimates of the removed part away from bounded frequencies.** For `‖ξ‖ ≥ R ≥ 1`, the
Leibniz rule bounds the `k`-th derivative of `φ(ξ / R) g(ξ)`, with `g` the angular factor, by
`C ⟨ξ⟩ ^ (-k)`: the dilated cutoff has order-zero estimates, and `g`, homogeneous of degree `0`,
satisfies Mihlin's condition `‖D^j g(ξ)‖ ≤ A / ‖ξ‖ ^ j`. -/
private theorem exists_norm_iteratedFDeriv_removed_le (hε : ε ≠ 0) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ ξ : CoordinateSpace N, R ≤ ‖ξ‖ →
      ‖iteratedFDeriv ℝ k (fun ξ ↦ φ (R⁻¹ • ξ) * (1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2)))) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by
  set g : CoordinateSpace N → ℝ := fun ξ ↦ 1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))
  have hφ : ContDiff ℝ ∞ fun η : CoordinateSpace N ↦ φ (R⁻¹ • η) :=
    φ.contDiff.comp (contDiff_const_smul _)
  choose Cφ hCφ0 hCφ using fun i : ℕ ↦ φ.exists_norm_iteratedFDeriv_comp_inv_smul_le i
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq
    ((contDiffOn_angular P χ hε).of_le (mod_cast le_top) :
      ContDiffOn ℝ k g {0}ᶜ) fun t ht ξ ↦ angular_smul P χ ε ht ξ
  refine ⟨∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * Cφ i * (A * 2 ^ (((k - i : ℕ) : ℝ) / 2)),
    Finset.sum_nonneg fun i _ ↦ by have := hCφ0 i; positivity, fun ξ hξ ↦ ?_⟩
  have h1 : 1 ≤ ‖ξ‖ := hR.trans hξ
  -- The Leibniz rule on the open set `‖η‖ > 1 / 2`, where `g` is smooth.
  set U : Set (CoordinateSpace N) := {η | 1 / 2 < ‖η‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hξU : ξ ∈ U := by
    rw [Set.mem_ofPred_eq]
    linarith
  have hgU : ContDiffOn ℝ k g U :=
    ((contDiffOn_angular P χ hε).of_le (mod_cast le_top)).mono fun η hη ↦ by
      rw [Set.mem_ofPred_eq] at hη
      exact Set.mem_compl_singleton_iff.2 (norm_pos_iff.1 (by linarith))
  have hL := norm_iteratedFDerivWithin_mul_le (hφ.of_le (mod_cast le_top)).contDiffOn hgU
    hU.uniqueDiffOn hξU le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hU hξU] at hL
  refine hL.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_of_isOpen i hU hξU, iteratedFDerivWithin_of_isOpen (k - i) hU hξU]
  have hgk : ‖iteratedFDeriv ℝ (k - i) g ξ‖ ≤
      A * 2 ^ (((k - i : ℕ) : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (-((k - i : ℕ) : ℝ) / 2) := by
    refine (hA (k - i) (Nat.sub_le k i) ξ (norm_pos_iff.1 (one_pos.trans_le h1))).trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    gcongr
    have h := Real.abs_rpow_le_two_rpow_mul_one_add_sq_rpow (t := ‖ξ‖) (by rwa [abs_norm])
      (-((k - i : ℕ) : ℝ))
    rwa [abs_norm, abs_neg, Nat.abs_cast, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast] at h
  have hw : (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (-((k - i : ℕ) : ℝ) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_add (by positivity), Nat.cast_sub hik]
    ring_nf
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun η ↦ φ (R⁻¹ • η)) ξ‖ *
        ‖iteratedFDeriv ℝ (k - i) g ξ‖
      ≤ (k.choose i : ℝ) * (Cφ i * (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2)) *
          (A * 2 ^ (((k - i : ℕ) : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (-((k - i : ℕ) : ℝ) / 2)) := by
        gcongr
        exacts [by have := hCφ0 i; positivity, hCφ i R hR ξ]
    _ = (k.choose i : ℝ) * Cφ i * (A * 2 ^ (((k - i : ℕ) : ℝ) / 2)) *
          (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by
        rw [← hw]
        ring

/-- **The cutoff is a symbol of order `0`.** For `ε ≠ 0` and `R ≥ 1`, its derivatives satisfy
`‖D^k c(ξ)‖ ≤ C ⟨ξ⟩ ^ (-k)`. -/
theorem exists_norm_iteratedFDeriv_conicLiftCutoff_le (hε : ε ≠ 0) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k (conicLiftCutoff P χ φ ε R) ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by
  have hR0 : 0 < R := one_pos.trans_le hR
  rcases eq_or_ne k 0 with rfl | hk
  · refine ⟨1, fun ξ ↦ ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (conicLiftCutoff_nonneg P χ φ ε R ξ)]
    simpa using conicLiftCutoff_le_one P χ φ ε R ξ
  -- For `k ≥ 1` only the removed part `q`, with `c = 1 - q`, contributes.
  set q : CoordinateSpace N → ℝ :=
    fun ξ ↦ φ (R⁻¹ • ξ) * (1 - χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))) with hq_def
  have hcq : conicLiftCutoff P χ φ ε R = (fun _ ↦ (1 : ℝ)) - q :=
    funext (conicLiftCutoff_def P χ φ ε R)
  have hq : ContDiff ℝ ∞ q := by
    simpa [hcq] using (contDiff_const (c := (1 : ℝ))).sub
      (contDiff_conicLiftCutoff (P := P) (χ := χ) (φ := φ) hε hR0)
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_removed_le (P := P) (χ := χ) (φ := φ) hε hR k
  refine ⟨C, fun ξ ↦ ?_⟩
  rw [hcq, iteratedFDeriv_sub_apply contDiffAt_const (hq.contDiffAt.of_le (mod_cast le_top)),
    iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_sub, norm_neg]
  rcases lt_or_ge ‖ξ‖ R with hξ | hξ
  · -- Near bounded frequencies `q` vanishes identically.
    have hzero : q =ᶠ[𝓝 ξ] fun _ ↦ 0 := by
      filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hξ)] with η hη
      simp [hq_def, φ.apply_inv_smul_eq_zero hR0 hη.le]
    rw [(hzero.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity
  · exact hC ξ hξ

end Cutoff

/-! ### The lifted symbol -/

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} (P : CoordinateSpace N →L[ℝ] CoordinateSpace n)

/-- The symbol estimates of `p` at the positions `P x` bound the mixed derivatives of
`(x, ξ) ↦ p(P x, P ξ)` by `D ⟨P ξ⟩ ^ (m - |β|)`, for positions `x` in a compact set. -/
private theorem exists_bound_mixedDeriv_comp_prodMap_of_isCompact (p : Symbol n V W m)
    {K : Set (CoordinateSpace N)} (hK : IsCompact K) (α β : List (Fin N)) :
    ∃ D, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (p.coefficient ∘ P.prodMap P) x ξ‖ ≤
        D * (1 + ‖P ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  choose C _ hC using fun s t : List (Fin n) ↦ p.exists_bound (P '' K) (hK.image P.continuous) s t
  obtain ⟨B, hB, hB'⟩ := exists_bound_mixedDeriv_comp_prodMap (α := α) (β := β)
    (p.contDiff_coefficient.of_le (mod_cast le_top)) (norm_nonneg P) C m
  exact ⟨B, hB, fun x hx ξ ↦ hB' P P le_rfl le_rfl x (fun s t η ↦ hC s t (P x) ⟨x, hx, rfl⟩ η) ξ⟩

/-- **Estimates of a lifted symbol on a cone.** On the cone `δ ‖ξ‖ ≤ ‖P ξ‖`, where `⟨P ξ⟩` and
`⟨ξ⟩` are comparable, the symbol estimates of `p` give estimates of order `m` for
`(x, ξ) ↦ p(P x, P ξ)`, for positions `x` in a compact set. -/
private theorem exists_bound_mixedDeriv_comp_prodMap_of_cone (p : Symbol n V W m)
    {K : Set (CoordinateSpace N)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) (α β : List (Fin N)) :
    ∃ D, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ, δ * ‖ξ‖ ≤ ‖P ξ‖ →
      ‖mixedDeriv α β (p.coefficient ∘ P.prodMap P) x ξ‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_mixedDeriv_comp_prodMap_of_isCompact P p hK α β
  set c : ℝ := max 1 (max ‖P‖ δ⁻¹)
  have hc : 1 ≤ c := le_max_left _ _
  refine ⟨D * c ^ |m - β.length|, by positivity, fun x hx ξ hξ ↦ (hD x hx ξ).trans ?_⟩
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_le_of_norm_le_mul hc _ ?_ ?_) hD0
  · calc ‖P ξ‖ ≤ ‖P‖ * ‖ξ‖ := P.le_opNorm ξ
      _ ≤ c * ‖ξ‖ := by gcongr; exact le_max_of_le_right (le_max_left _ _)
  · calc ‖ξ‖ = δ⁻¹ * (δ * ‖ξ‖) := by field_simp
      _ ≤ c * ‖P ξ‖ := by gcongr; exact le_max_of_le_right (le_max_right _ _)

variable {χ : ConicCutoff} {φ : FrequencyCutoff (CoordinateSpace N)} {ε R : ℝ}

/-- Where the cutoff vanishes near `ξ`, the function `c(ξ) p(P x, P ξ)` vanishes near `(x, ξ)`. -/
private theorem conicLiftCutoff_smul_eventuallyEq_zero (hε : ε ≠ 0) (hR : 0 < R)
    (p : Symbol n V W m) (x : CoordinateSpace N) {ξ : CoordinateSpace N} (hξ : 2 * R < ‖ξ‖)
    (hPξ : ‖P ξ‖ ^ 2 < ε ^ 2 * ‖ξ‖ ^ 2 / 4) :
    (fun q : CoordinateSpace N × CoordinateSpace N ↦
      (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2)) =ᶠ[𝓝 (x, ξ)] 0 := by
  filter_upwards [continuous_snd.continuousAt.eventually
    (conicLiftCutoff_eventuallyEq_zero hε hR hξ hPξ)] with q hq
  have hq' : conicLiftCutoff P χ φ ε R q.2 = 0 := hq
  simp [hq']

/-- **Estimates of the lifted symbol on the cone.** On the cone `ε ‖ξ‖ ≤ 2 ‖P ξ‖` the lifted
symbol `c(ξ) p(P x, P ξ)` satisfies the estimates of order `m`, by the Leibniz rule for the
composition of `c(ξ) id` with `p(P x, P ξ)`: the first has order-zero estimates, the second
estimates of order `m` on the cone. -/
private theorem exists_bound_mixedDeriv_conicLift_of_cone (hε : ε ≠ 0) (hR : 1 ≤ R)
    (p : Symbol n V W m) {K : Set (CoordinateSpace N)} (hK : IsCompact K) (α β : List (Fin N)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, |ε| / 2 * ‖ξ‖ ≤ ‖P ξ‖ →
      ‖mixedDeriv α β
          (fun q ↦ (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  have hc : ContDiff ℝ ∞ (conicLiftCutoff P χ φ ε R) :=
    contDiff_conicLiftCutoff hε (one_pos.trans_le hR)
  -- The coefficient is the composition of `b(ξ) = c(ξ) id` with `g(x, ξ) = p(P x, P ξ)`.
  set L : ℝ →L[ℝ] W →L[ℂ] W := Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ W)
  set b : CoordinateSpace N → W →L[ℂ] W := fun ξ ↦ L (conicLiftCutoff P χ φ ε R ξ)
  have hb : ContDiff ℝ ∞ b := L.contDiff.comp hc
  have hfb : (fun q : CoordinateSpace N × CoordinateSpace N ↦
      (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2)) =
        fun q ↦ (b q.2).comp ((p.coefficient ∘ P.prodMap P) q) := by
    funext ⟨x, ξ⟩
    simp only [b, L, Function.comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]
  choose D hD0 hD using fun s t : List (Fin N) ↦
    exists_bound_mixedDeriv_comp_prodMap_of_cone P p hK (by positivity : 0 < |ε| / 2) s t
  choose E hE0 hE using fun s t : List (Fin N) ↦ exists_bound_mixedDeriv_comp_snd (m := 0)
    (hb.of_le (mod_cast le_top)) (by
      obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_conicLiftCutoff_le (P := P) (χ := χ) (φ := φ)
        hε hR t.length
      obtain ⟨C', hC'⟩ := L.exists_norm_iteratedFDeriv_comp_left_le
        (hc.of_le (mod_cast le_top)) ⟨C, hC⟩
      exact ⟨C', fun ξ ↦ by simpa [zero_sub, neg_div] using hC' ξ⟩) s
  refine ⟨(β.sublists'.revzip.map fun t ↦
    (α.sublists'.revzip.map fun s ↦ E s.1 t.1 * D s.2 t.2).sum).sum,
    List.sum_nonneg fun _ h ↦ ?_, fun x hx ξ hcone ↦ ?_⟩
  · obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
    exact List.sum_nonneg fun _ h' ↦ by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h'
      exact mul_nonneg (hE0 s.1 t.1) (hD0 s.2 t.2)
  rw [hfb]
  refine (norm_mixedDeriv_comp_le (m' := 0) (hb.comp contDiff_snd)
    (p.contDiff_coefficient.comp (P.prodMap P).contDiff) (fun s t ↦ hE s t x ξ)
    (fun s t ↦ hD s t x hx ξ hcone) α β).trans_eq ?_
  rw [zero_add]

/-- The symbol estimates of the lifted symbol `c(ξ) p(P x, P ξ)`: at bounded frequencies by
compactness, near the axis because the cutoff vanishes there, and on the remaining cone by
`exists_bound_mixedDeriv_conicLift_of_cone`. -/
private theorem exists_bound_conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (p : Symbol n V W m)
    {K : Set (CoordinateSpace N)} (hK : IsCompact K) (α β : List (Fin N)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β
          (fun q ↦ (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  have hR0 : 0 < R := one_pos.trans_le hR
  have hf : ContDiff ℝ ∞ fun q : CoordinateSpace N × CoordinateSpace N ↦
      (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2) :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_conicLiftCutoff hε hR0).comp contDiff_snd)).smul
      (p.contDiff_coefficient.comp (P.prodMap P).contDiff)
  obtain ⟨C₀, hC₀, h₀⟩ := (hf.of_le (mod_cast le_top) : ContDiff ℝ (α.length + β.length) _
    ).exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le hK (2 * R) (m - β.length)
  obtain ⟨C₁, -, h₁⟩ := exists_bound_mixedDeriv_conicLift_of_cone P hε hR p hK α β
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, fun x hx ξ ↦ ?_⟩
  rcases le_or_gt ‖ξ‖ (2 * R) with hξ | hξ
  · -- At bounded frequencies.
    refine (norm_mixedDeriv_le α β (hf.of_le (mod_cast le_top)) x ξ).trans
      ((h₀ x hx ξ hξ).trans ?_)
    gcongr
    exact le_max_left _ _
  rcases lt_or_ge (‖P ξ‖ ^ 2) (ε ^ 2 * ‖ξ‖ ^ 2 / 4) with hPξ | hPξ
  · -- Near the axis the cutoff, hence the function, vanishes.
    rw [((conicLiftCutoff_smul_eventuallyEq_zero P hε hR0 p x hξ hPξ).mixedDeriv_eq α β).trans
      (mixedDeriv_zero α β x ξ), norm_zero]
    positivity
  · -- On the cone.
    have hcone : |ε| / 2 * ‖ξ‖ ≤ ‖P ξ‖ :=
      (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1
        (by rw [mul_pow, div_pow, sq_abs]; linarith)
    refine (h₁ x hx ξ hcone).trans ?_
    gcongr
    exact le_max_right _ _

variable (χ φ)

/-- **The lift of a symbol to a product, cut off near an axis.** For a linear map
`P : ℝᴺ → ℝⁿ`, for instance the projection of a product onto a factor, a symbol `p` of order `m`
on `ℝⁿ` lifts to the symbol `c(ξ) p(P x, P ξ)` of order `m` on `ℝᴺ`, where `c` is the cutoff
`TauCeti.conicLiftCutoff P χ φ ε R` near the axis `P ξ = 0`, for `ε ≠ 0` and `R ≥ 1`. -/
def conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (p : Symbol n V W m) : Symbol N V W m where
  coefficient q := (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2)
  contDiff_coefficient :=
    (Complex.ofRealCLM.contDiff.comp
      ((contDiff_conicLiftCutoff hε (one_pos.trans_le hR)).comp contDiff_snd)).smul
      (p.contDiff_coefficient.comp (P.prodMap P).contDiff)
  exists_bound _ hK α β := exists_bound_conicLift P hε hR p hK α β

variable {χ φ}

@[simp]
theorem coefficient_conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (p : Symbol n V W m)
    (q : CoordinateSpace N × CoordinateSpace N) :
    (p.conicLift P χ φ hε hR).coefficient q =
      (conicLiftCutoff P χ φ ε R q.2 : ℂ) • p.coefficient (P q.1, P q.2) :=
  (rfl)

/-- On the cone `‖P ξ‖² ≥ ε² ‖ξ‖² / 2` the lifted symbol is `p(P x, P ξ)`. -/
theorem coefficient_conicLift_of_le (hε : ε ≠ 0) (hR : 1 ≤ R) (p : Symbol n V W m)
    (x : CoordinateSpace N) {ξ : CoordinateSpace N} (hξ : ε ^ 2 * ‖ξ‖ ^ 2 / 2 ≤ ‖P ξ‖ ^ 2) :
    (p.conicLift P χ φ hε hR).coefficient (x, ξ) = p.coefficient (P x, P ξ) := by
  rw [coefficient_conicLift, conicLiftCutoff_eq_one_of_le hε hξ, Complex.ofReal_one, one_smul]

/-- At frequencies `‖ξ‖ ≤ R` the lifted symbol is `p(P x, P ξ)`. -/
theorem coefficient_conicLift_of_norm_le (hε : ε ≠ 0) (hR : 1 ≤ R) (p : Symbol n V W m)
    (x : CoordinateSpace N) {ξ : CoordinateSpace N} (hξ : ‖ξ‖ ≤ R) :
    (p.conicLift P χ φ hε hR).coefficient (x, ξ) = p.coefficient (P x, P ξ) := by
  rw [coefficient_conicLift, conicLiftCutoff_eq_one_of_norm_le (one_pos.trans_le hR) hξ,
    Complex.ofReal_one, one_smul]

/-- Near every frequency with `‖ξ‖ > 2 R` and `‖P ξ‖² < ε² ‖ξ‖² / 4`, close to the axis, the
lifted symbol vanishes. -/
theorem coefficient_conicLift_eventuallyEq_zero (hε : ε ≠ 0) (hR : 1 ≤ R) (p : Symbol n V W m)
    (x : CoordinateSpace N) {ξ : CoordinateSpace N} (hξ : 2 * R < ‖ξ‖)
    (hPξ : ‖P ξ‖ ^ 2 < ε ^ 2 * ‖ξ‖ ^ 2 / 4) :
    (p.conicLift P χ φ hε hR).coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
  rw [show (p.conicLift P χ φ hε hR).coefficient = _ from
    funext (coefficient_conicLift P hε hR p)]
  exact conicLiftCutoff_smul_eventuallyEq_zero P hε (one_pos.trans_le hR) p x hξ hPξ

/-- Where `‖P ξ‖² < ε² ‖ξ‖² / 2` and `ε ‖ξ‖ ≥ 1`, the weight `⟨P ξ⟩ ^ m` of order `m ≥ 0` is at
most `2 ^ (m / 2) ε ^ m ⟨ξ⟩ ^ m`. -/
private theorem one_add_norm_sq_rpow_le_of_sq_lt (hm : 0 ≤ m) {ε : ℝ} (hε : 0 < ε)
    {ξ : CoordinateSpace N} (hεξ : 1 ≤ ε * ‖ξ‖) (hPξ : ‖P ξ‖ ^ 2 < ε ^ 2 * ‖ξ‖ ^ 2 / 2) :
    (1 + ‖P ξ‖ ^ 2) ^ (m / 2) ≤ 2 ^ (m / 2) * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  have hle : 1 + ‖P ξ‖ ^ 2 ≤ 2 * ε ^ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith
  calc (1 + ‖P ξ‖ ^ 2) ^ (m / 2) ≤ (2 * ε ^ 2 * (1 + ‖ξ‖ ^ 2)) ^ (m / 2) := by gcongr
    _ = 2 ^ (m / 2) * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast ε 2,
          ← Real.rpow_mul hε.le, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero]

/-- **The lift is close to `p(P x, P ξ)`.** For `m ≥ 0`, a compact set `K` of positions and a word
`α` of position derivatives there is a constant `C` such that for all `ε > 0` and `R ≥ 1` with
`R ≥ ε⁻¹`,

`‖∂_x^α (p(P x, P ξ) - c(ξ) p(P x, P ξ))‖ ≤ C ε ^ m ⟨ξ⟩ ^ m`

for `x ∈ K`. The constant does not depend on `ε`, `R` or the cutoffs: the difference is supported
where `‖ξ‖ > R` and `‖P ξ‖ < ε ‖ξ‖`, where `⟨P ξ⟩ ≤ √2 ε ⟨ξ⟩`. -/
theorem exists_norm_mixedDeriv_sub_conicLift_le (hm : 0 ≤ m) (p : Symbol n V W m)
    {K : Set (CoordinateSpace N)} (hK : IsCompact K) (α : List (Fin N)) :
    ∃ C, 0 ≤ C ∧ ∀ (χ : ConicCutoff) (φ : FrequencyCutoff (CoordinateSpace N)) {ε R : ℝ}
      (hε : 0 < ε) (hR₁ : 1 ≤ R), ε⁻¹ ≤ R → ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α [] (fun q ↦ p.coefficient (P q.1, P q.2) -
            (p.conicLift P χ φ hε.ne' hR₁).coefficient q) x ξ‖ ≤
          C * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_mixedDeriv_comp_prodMap_of_isCompact P p hK α []
  refine ⟨D * 2 ^ (m / 2), by positivity, fun χ φ ε R hε hR₁ hR x hx ξ ↦ ?_⟩
  set c := conicLiftCutoff P χ φ ε R
  have hc0 : 0 ≤ 1 - c ξ := sub_nonneg.2 (conicLiftCutoff_le_one P χ φ ε R ξ)
  -- The difference is `(1 - c(ξ)) p(P x, P ξ)`, and `1 - c(ξ)` does not depend on the position.
  have hdiff : mixedDeriv α [] (fun q ↦ p.coefficient (P q.1, P q.2) -
      (p.conicLift P χ φ hε.ne' hR₁).coefficient q) x ξ =
        ((1 - c ξ : ℝ) : ℂ) • mixedDeriv α [] (p.coefficient ∘ P.prodMap P) x ξ := by
    simp only [mixedDeriv_def, coordinateDeriv_nil, coefficient_conicLift]
    rw [← Pi.smul_apply (((1 - c ξ : ℝ) : ℂ)), ← coordinateDeriv_const_smul]
    congr 1
    funext y
    simp only [Pi.smul_apply, Function.comp_apply, ContinuousLinearMap.coe_prodMap',
      Prod.map_apply, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, c]
  rw [hdiff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
  -- Either `c(ξ) = 1`, or `‖ξ‖ > R ≥ ε⁻¹` and `‖P ξ‖² < ε² ‖ξ‖² / 2`.
  by_cases h1 : c ξ = 1
  · rw [h1, sub_self, zero_mul]
    positivity
  have hξR : R < ‖ξ‖ :=
    lt_of_not_ge fun h ↦ h1 (conicLiftCutoff_eq_one_of_norm_le (one_pos.trans_le hR₁) h)
  have hPξ : ‖P ξ‖ ^ 2 < ε ^ 2 * ‖ξ‖ ^ 2 / 2 :=
    lt_of_not_ge fun h ↦ h1 (conicLiftCutoff_eq_one_of_le hε.ne' h)
  have hεξ : 1 ≤ ε * ‖ξ‖ := by
    calc (1 : ℝ) = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
      _ ≤ ε * ‖ξ‖ := by gcongr; linarith
  have hDξ : ‖mixedDeriv α [] (p.coefficient ∘ P.prodMap P) x ξ‖ ≤
      D * (1 + ‖P ξ‖ ^ 2) ^ (m / 2) := by
    simpa using hD x hx ξ
  calc (1 - c ξ) * ‖mixedDeriv α [] (p.coefficient ∘ P.prodMap P) x ξ‖
      ≤ 1 * (D * (1 + ‖P ξ‖ ^ 2) ^ (m / 2)) := by
        gcongr
        exact sub_le_self _ (conicLiftCutoff_nonneg P χ φ ε R ξ)
    _ ≤ D * (2 ^ (m / 2) * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
        rw [one_mul]
        gcongr
        exact one_add_norm_sq_rpow_le_of_sq_lt P hm hε hεξ hPξ
    _ = D * 2 ^ (m / 2) * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

/-! ### The Sobolev estimate of the cutoff error -/

section Sobolev

open MeasureTheory FourierTransform
open scoped SchwartzMap

/-- For `m ≥ 0` the slices `ξ ↦ p(P x, P ξ)` of the uncut lift are bounded by `C ⟨ξ⟩ ^ m`. -/
private theorem exists_norm_coefficient_comp_prodMap_le (hm : 0 ≤ m) (p : Symbol n V W m)
    (x : CoordinateSpace N) :
    ∃ C, 0 ≤ C ∧ ∀ ξ, ‖p.coefficient (P x, P ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨D, hD0, hD⟩ :=
    exists_bound_mixedDeriv_comp_prodMap_of_isCompact P p isCompact_singleton [] []
  refine ⟨D * (1 + ‖P‖ ^ 2) ^ (m / 2), by positivity, fun ξ ↦ ?_⟩
  calc ‖p.coefficient (P x, P ξ)‖ ≤ D * (1 + ‖P ξ‖ ^ 2) ^ (m / 2) := by
        simpa using hD x rfl ξ
    _ ≤ D * ((1 + ‖P‖ ^ 2) ^ (m / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
        gcongr
        exact one_add_norm_sq_rpow_le_mul_of_norm_le_mul hm (P.le_opNorm ξ)
    _ = D * (1 + ‖P‖ ^ 2) ^ (m / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by rw [mul_assoc]

/-- The position slices of the cutoff error `p(P y, P ξ) - c(ξ) p(P y, P ξ)` are smooth. -/
private theorem contDiff_coefficient_comp_sub_conicLift (p : Symbol n V W m) (χ : ConicCutoff)
    (φ : FrequencyCutoff (CoordinateSpace N)) (hε : ε ≠ 0) (hR : 1 ≤ R) (ξ : CoordinateSpace N) :
    ContDiff ℝ ∞ fun y ↦
      p.coefficient (P y, P ξ) - (p.conicLift P χ φ hε hR).coefficient (y, ξ) :=
  (p.contDiff_coefficient.comp (P.contDiff.prodMk contDiff_const)).sub
    ((p.conicLift P χ φ hε hR).contDiff_coefficient.comp (contDiff_id.prodMk contDiff_const))

/-- **Position derivatives of the localized cutoff error.** For `m ≥ 0`, a smooth compactly
supported `ψ` and `L : ℕ` there is a constant `A` such that the position derivatives of order at
most `L` of `ψ(x) (p(P x, P ξ) - c(ξ) p(P x, P ξ))` are at most `A ε ^ m ⟨ξ⟩ ^ m` on the support
of `ψ`, uniformly in the cutoffs, `ε > 0` and `R ≥ max 1 ε⁻¹`. -/
private theorem exists_norm_iteratedFDeriv_smul_sub_conicLift_le (hm : 0 ≤ m)
    (p : Symbol n V W m) {ψ : CoordinateSpace N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (L : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ (χ : ConicCutoff) (φ : FrequencyCutoff (CoordinateSpace N)) {ε R : ℝ}
      (hε : 0 < ε) (hR₁ : 1 ≤ R), ε⁻¹ ≤ R → ∀ l ≤ L, ∀ x ∈ tsupport ψ, ∀ ξ,
        ‖iteratedFDeriv ℝ l (fun y ↦ ψ y • (p.coefficient (P y, P ξ) -
            (p.conicLift P χ φ hε.ne' hR₁).coefficient (y, ξ))) x‖ ≤
          A * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  -- Bounds for the derivatives of `ψ` and for the position derivatives of the cutoff error.
  choose B hB using fun i : ℕ ↦ (hψ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top))
    |>.bounded_above_of_compact_support (hψc.iteratedFDeriv i)
  have hB0 (i : ℕ) : 0 ≤ B i := (norm_nonneg _).trans (hB i 0)
  choose D hD0 hD using fun w : List (Fin N) ↦
    exists_norm_mixedDeriv_sub_conicLift_le P hm p (hψc : IsCompact (tsupport ψ)) w
  -- The Leibniz rule bounds the `l`-th derivative by `T l ε ^ m ⟨ξ⟩ ^ m`.
  set T : ℕ → ℝ := fun l ↦ ∑ i ∈ Finset.range (l + 1),
    (l.choose i : ℝ) * B i * ∑ w : Fin (l - i) → Fin N, D (List.ofFn w)
  have hT0 (l : ℕ) : 0 ≤ T l :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (by positivity) (hB0 i))
      (Finset.sum_nonneg fun w _ ↦ hD0 _)
  refine ⟨∑ l ∈ Finset.range (L + 1), T l, Finset.sum_nonneg fun l _ ↦ hT0 l,
    fun χ φ ε R hε hR₁ hR l hl x hx ξ ↦ ?_⟩
  have hg := contDiff_coefficient_comp_sub_conicLift P p χ φ hε.ne' hR₁ ξ
  refine (norm_iteratedFDeriv_smul_le hψ hg x (by exact_mod_cast le_top)).trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * B i *
        ∑ w : Fin (l - i) → Fin N, D (List.ofFn w) * ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        refine Finset.sum_le_sum fun i _ ↦ mul_le_mul
          (mul_le_mul_of_nonneg_left (hB i x) (by positivity)) ?_ (norm_nonneg _)
          (mul_nonneg (by positivity) (hB0 i))
        -- The derivatives of the error along words are its mixed position derivatives.
        refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (contDiff_infty.1 hg _) x).trans
          (Finset.sum_le_sum fun w _ ↦ ?_)
        simpa only [mixedDeriv_def, coordinateDeriv_nil] using
          hD (List.ofFn w) χ φ hε hR₁ hR x hx ξ
    _ = T l * (ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
        simp only [T, Finset.sum_mul, mul_assoc]
    _ ≤ (∑ l ∈ Finset.range (L + 1), T l) * (ε ^ m * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
        gcongr
        exact Finset.single_le_sum (fun l _ ↦ hT0 l) (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
    _ = _ := by ring

/-- **The Sobolev estimate of the cutoff error.** Let `p` be a symbol of order `m ≥ 0` on `ℝⁿ`,
`P : ℝᴺ → ℝⁿ` linear and `ψ` a smooth compactly supported function on `ℝᴺ`. For every real `s`
there is a constant `C` such that

`‖ψ (Op(p ∘ P) u - Op(c p) u)‖_{H^{s - m}} ≤ C ε ^ m ‖u‖_{H^s}`

for every Schwartz function `u`, every conic cutoff `χ`, every frequency cutoff `φ`, and all
`ε > 0` and `R ≥ max 1 ε⁻¹`, where `p ∘ P` is the uncut lift `(x, ξ) ↦ p(P x, P ξ)` and `c p` is
the lift `TauCeti.Symbol.conicLift` cut off near the axis `P ξ = 0`. The Sobolev norms are the
weighted `L²` norms of the Fourier transforms. So, after localization in the position, the
quantizations of the cut-off and the uncut lift are `O(ε ^ m)` apart in the operator norm
`H^s → H^{s - m}`. For `m > 0` the first converges to the second as `ε → 0`, at the rate `ε ^ m`;
for `m = 1` and `s = 1` this is the bound `C ε` from `H¹` to `L²`. -/
theorem exists_eLpNorm_smul_fourier_smul_quantizeSchwartzValue_sub_conicLift_le (hm : 0 ≤ m)
    (p : Symbol n V W m) {ψ : CoordinateSpace N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (χ : ConicCutoff) (φ : FrequencyCutoff (CoordinateSpace N)) {ε R : ℝ}
      (hε : 0 < ε) (hR₁ : 1 ≤ R), ε⁻¹ ≤ R → ∀ u : 𝓢(CoordinateSpace N, V),
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
            𝓕 (fun x ↦ ψ x • (quantizeSchwartzValue (p.coefficient ∘ P.prodMap P) u x -
              quantizeSchwartzValue (p.conicLift P χ φ hε.ne' hR₁).coefficient u x)) ξ)
            2 volume ≤
          ENNReal.ofReal (C * ε ^ m) *
            eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  -- The position derivatives of the localized error are `O(ε ^ m ⟨ξ⟩ ^ m)`, and the weighted
  -- Fourier–Schur estimate needs no frequency derivatives, which are not bounded uniformly in `ε`.
  obtain ⟨C₀, hC₀, hFS⟩ :=
    exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_norm_iteratedFDeriv_le
      (V := V) (W := W) (hψc : IsCompact (tsupport ψ)) m s
  obtain ⟨A, hA0, hA⟩ :=
    exists_norm_iteratedFDeriv_smul_sub_conicLift_le P hm p hψ hψc (⌈|s - m|⌉₊ + N + 1)
  refine ⟨C₀ * A, mul_nonneg hC₀ hA0, fun χ φ ε R hε hR₁ hR u ↦ ?_⟩
  set d : CoordinateSpace N × CoordinateSpace N → V →L[ℂ] W := fun q ↦
    ψ q.1 • (p.coefficient (P q.1, P q.2) - (p.conicLift P χ φ hε.ne' hR₁).coefficient q)
  have hd : Continuous d :=
    (hψ.continuous.comp continuous_fst).smul
      ((p.contDiff_coefficient.continuous.comp (P.prodMap P).continuous).sub
        (p.conicLift P χ φ hε.ne' hR₁).contDiff_coefficient.continuous)
  have hdsmooth (ξ : CoordinateSpace N) : ContDiff ℝ (⌈|s - m|⌉₊ + N + 1 : ℕ) fun x ↦ d (x, ξ) :=
    (hψ.smul (contDiff_coefficient_comp_sub_conicLift P p χ φ hε.ne' hR₁ ξ)).of_le
      (by exact_mod_cast le_top)
  have hdK (x : CoordinateSpace N) (hx : x ∉ tsupport ψ) (ξ : CoordinateSpace N) :
      d (x, ξ) = 0 := by
    simp [d, image_eq_zero_of_notMem_tsupport hx]
  -- Localizing the cutoff error localizes the difference of the two quantizations.
  have hOp : (fun x ↦ ψ x • (quantizeSchwartzValue (p.coefficient ∘ P.prodMap P) u x -
      quantizeSchwartzValue (p.conicLift P χ φ hε.ne' hR₁).coefficient u x)) =
        quantizeSchwartzValue d u := funext fun x ↦ by
    obtain ⟨C₁, -, hC₁⟩ := exists_norm_coefficient_comp_prodMap_le P hm p x
    obtain ⟨C₂, -, hC₂⟩ := (p.conicLift P χ φ hε.ne' hR₁).exists_bound_coefficient_slice x
    rw [eq_comm, quantizeSchwartzValue_congr_left (a := d) (b := fun q ↦ (ψ q.1 : ℂ) •
        (p.coefficient ∘ P.prodMap P - (p.conicLift P χ φ hε.ne' hR₁).coefficient) q)
        (fun ξ ↦ by simp [d, Complex.coe_smul]),
      quantizeSchwartzValue_comp_fst_smul_left (fun y ↦ (ψ y : ℂ)),
      quantizeSchwartzValue_sub_left (a := p.coefficient ∘ P.prodMap P)
        (p.contDiff_coefficient.continuous.comp
          ((P.prodMap P).continuous.comp (Continuous.prodMk_right x))).aestronglyMeasurable hC₁
        ((p.conicLift P χ φ hε.ne' hR₁).continuous_coefficient_slice x).aestronglyMeasurable hC₂,
      Complex.coe_smul]
  rw [hOp]
  refine (hFS d (A * ε ^ m) hd hdsmooth hdK (hA χ φ hε hR₁ hR) u).trans_eq ?_
  rw [mul_assoc]

end Sobolev

end Symbol

end TauCeti
