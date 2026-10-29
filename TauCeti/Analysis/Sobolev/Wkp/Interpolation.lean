/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import TauCeti.Analysis.Sobolev.Wkp.Zero
public import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The interpolation inequality for the gradient

The `Lᵖ` norm of the gradient of a function is controlled by the `Lᵖ` norms of the function and
of its Hessian: for every `ε > 0`,

`‖∇u‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `1 ≤ p ≤ ∞`, `n = dim E`.

The smooth and zero-boundary estimates include `p = ∞`. The statements for arbitrary
whole-space Sobolev functions and between balls retain `p < ∞` for the density and cutoff steps.

This is how a first-order term is absorbed into the left-hand side of a second-order estimate. In
the `W^{2,p}` theory of non-divergence-form operators with continuous coefficients, the
Calderón–Zygmund estimate is applied to `ζ u` for cutoffs `ζ` supported on small balls, and the
derivatives falling on `ζ` produce the terms `‖∇u‖_p` that this inequality absorbs.

* `ContDiff.eLpNorm_inv_smul_comp_add_smul_sub_half_le`: halving the step of a difference
  quotient `δ_s u = s⁻¹ (u(· + s h) - u)` costs at most `(|s| / 4) ‖h‖² ‖D²u‖_p`.
* `ContDiff.eLpNorm_fderiv_apply_le_eLpNorm_inv_smul_comp_add_smul_sub_add`: for `s ≠ 0`,
  `‖Du · h‖_p ≤ ‖δ_s u‖_p + (|s| / 2) ‖h‖² ‖D²u‖_p`.
* `ContDiff.eLpNorm_fderiv_apply_le`: for a `C²` function `u` and a direction `h`,
  `‖Du · h‖_p ≤ ε ‖h‖² ‖D²u‖_p + ε⁻¹ ‖u‖_p`.
* `ContDiff.eLpNorm_fderiv_le`: the same for the full derivative on a finite-dimensional inner
  product space, with constants `ε` and `n² / ε`.
* `TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule`: the inequality for
  `u ∈ W^{2,p}_0(Ω)`, on any open `Ω`, with the weak gradient and the weak Hessian.
* `TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le`: the inequality on all of `W^{2,p}(E)`.
* `TauCeti.Wkp.exists_lpNorm_gradient_ball_le`: the local form between concentric balls
  `B_s ⊆ B_t ⊆ Ω` for `u ∈ W^{2,p}(Ω)`, with the extra terms `(t - s)⁻¹ ‖∇u‖` and
  `(t - s)⁻² ‖u‖` on `B_t` produced by a cutoff.

## The argument

Write `δ_t u = t⁻¹ (u(· + t h) - u)` for the difference quotient. Halving the step changes it by a
second difference, `δ_{t/2} u - δ_t u = -t⁻¹ (u(· + t h) - 2 u(· + t h / 2) + u)`, whose `Lᵖ` norm
is at most `(t / 4) ‖h‖² ‖D²u‖_p` by the second-order translation estimate
`ContDiff.eLpNorm_comp_add_add_sub_sub_le_mul_eLpNorm_fderiv_fderiv`. Starting from
`‖δ_{2ε} u‖_p ≤ ε⁻¹ ‖u‖_p` (`MeasureTheory.eLpNorm_comp_add_sub_le_two_mul`) and summing over
the dyadic steps `2ε / 2ᵏ` gives `‖δ_{2ε/2ᵏ} u‖_p ≤ ε ‖h‖² ‖D²u‖_p + ε⁻¹ ‖u‖_p` for every `k`.
The difference quotients converge pointwise to `Du · h`, so Fatou's lemma bounds `‖Du · h‖_p` in
the same way. Summing over an orthonormal basis, `‖Du‖ ≤ ∑ᵢ |Du · eᵢ|` gives the gradient bound.
For `W^{2,p}_0(Ω)` both sides are continuous in the Sobolev norm, and the test functions are
dense. Between concentric balls, the `W^{2,p}_0` inequality is applied to the product of `u` with a
cutoff that is one on `B_s` and supported in `B_t`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.28.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology TopologicalSpace Module
open scoped ENNReal

section Smooth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
  [SFinite mu] [mu.IsAddRightInvariant] {u : E → F} {p : ℝ≥0∞}

/-- **Halving the step of a difference quotient.** For a `C²` function `u`, a direction `h` and a
step `s`, the difference quotients `δ_s u = s⁻¹ (u(· + s h) - u)` satisfy

`‖δ_{s/2} u‖_p ≤ ‖δ_s u‖_p + (|s| / 4) ‖h‖² ‖D²u‖_p`, `1 ≤ p ≤ ∞`. -/
theorem ContDiff.eLpNorm_inv_smul_comp_add_smul_sub_half_le (hu : ContDiff ℝ 2 u) (hp : 1 ≤ p)
    (h : E) (s : ℝ) :
    eLpNorm (fun x => (s / 2)⁻¹ • (u (x + (s / 2) • h) - u x)) p mu ≤
      eLpNorm (fun x => s⁻¹ • (u (x + s • h) - u x)) p mu +
        ENNReal.ofReal (|s| / 4) * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu := by
  set r := (s / 2) • h
  -- Halving the step changes the quotient by `s⁻¹` times a second difference with increments `r`.
  set D : E → F := fun x => u (x + r + r) - u (x + r) - (u (x + r) - u x)
  have hrr : s • h = r + r := by rw [← add_smul, add_halves]
  have hQ : (fun x => (s / 2)⁻¹ • (u (x + r) - u x)) =
      (fun x => s⁻¹ • (u (x + s • h) - u x)) - s⁻¹ • D := by
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, D, hrr, ← add_assoc, inv_div]
    module
  have hcoef : ‖s⁻¹‖ₑ * (‖r‖ₑ * ‖r‖ₑ) = ENNReal.ofReal (|s| / 4) * ‖h‖ₑ ^ 2 := by
    have hreal : ‖s⁻¹‖ * (‖r‖ * ‖r‖) = |s| / 4 * ‖h‖ ^ 2 := by
      rcases eq_or_ne s 0 with rfl | hs
      · simp
      · simp only [r, norm_smul, norm_inv, Real.norm_eq_abs, abs_div, abs_two]
        field_simp
        ring
    rw [← ofReal_norm h, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ← hreal, ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [ofReal_norm]
  calc eLpNorm (fun x => (s / 2)⁻¹ • (u (x + r) - u x)) p mu
      ≤ eLpNorm (fun x => s⁻¹ • (u (x + s • h) - u x)) p mu + eLpNorm (s⁻¹ • D) p mu := by
        rw [hQ]
        exact eLpNorm_sub_le hp
    _ ≤ eLpNorm (fun x => s⁻¹ • (u (x + s • h) - u x)) p mu +
          ‖s⁻¹‖ₑ * (‖r‖ₑ * ‖r‖ₑ * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu) := by
        rw [eLpNorm_const_smul]
        gcongr
        exact hu.eLpNorm_comp_add_add_sub_sub_le_mul_eLpNorm_fderiv_fderiv hp r r
    _ = _ := by rw [← mul_assoc, hcoef]

/-- **A directional derivative is controlled by a single difference quotient.** For a `C²`
function `u`, a direction `h` and a step `s ≠ 0`,

`‖Du · h‖_p ≤ ‖δ_s u‖_p + (|s| / 2) ‖h‖² ‖D²u‖_p`, `1 ≤ p ≤ ∞`,

where `δ_s u = s⁻¹ (u(· + s h) - u)`. -/
theorem ContDiff.eLpNorm_fderiv_apply_le_eLpNorm_inv_smul_comp_add_smul_sub_add
    (hu : ContDiff ℝ 2 u) (hp : 1 ≤ p) (h : E) {s : ℝ} (hs : s ≠ 0) :
    eLpNorm (fun x => fderiv ℝ u x h) p mu ≤
      eLpNorm (fun x => s⁻¹ • (u (x + s • h) - u x)) p mu +
        ENNReal.ofReal (|s| / 2) * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu := by
  set C := ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu
  -- `t k = s / 2ᵏ` is the `k`-th dyadic step and `Q k` the difference quotient with that step.
  set t : ℕ → ℝ := fun k => s / 2 ^ k with ht_def
  set Q : ℕ → E → F := fun k x => (t k)⁻¹ • (u (x + t k • h) - u x) with hQ_def
  have ht (k : ℕ) : t (k + 1) = t k / 2 := by simp only [ht_def, pow_succ, div_div]
  -- Summing the halving estimates over the dyadic steps bounds every `Q k`.
  have hQ (k : ℕ) : eLpNorm (Q k) p mu + ENNReal.ofReal (|t k| / 2) * C ≤
      eLpNorm (Q 0) p mu + ENNReal.ofReal (|s| / 2) * C := by
    induction k with
    | zero => simp [ht_def]
    | succ k ih =>
        calc eLpNorm (Q (k + 1)) p mu + ENNReal.ofReal (|t (k + 1)| / 2) * C
            ≤ eLpNorm (Q k) p mu + ENNReal.ofReal (|t k| / 4) * C +
                ENNReal.ofReal (|t k| / 4) * C := by
              have hdiv : |t (k + 1)| / 2 = |t k| / 4 := by
                rw [ht, abs_div, abs_two]
                ring
              rw [hdiv]
              gcongr
              simpa only [hQ_def, ht, mul_assoc] using
                hu.eLpNorm_inv_smul_comp_add_smul_sub_half_le hp h (t k)
          _ = eLpNorm (Q k) p mu + ENNReal.ofReal (|t k| / 2) * C := by
              rw [add_assoc, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
              ring_nf
          _ ≤ eLpNorm (Q 0) p mu + ENNReal.ofReal (|s| / 2) * C := ih
  -- The difference quotients converge pointwise to `Du · h`; conclude by Fatou's lemma.
  have hlim (x : E) : Tendsto (fun k => Q k x) atTop (𝓝 (fderiv ℝ u x h)) := by
    have hc : Tendsto (fun k => ‖(t k)⁻¹‖) atTop atTop := by
      simp only [ht_def, inv_div, norm_div, norm_pow, Real.norm_ofNat]
      exact (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_div_const (norm_pos_iff.2 hs)
    simpa only [hQ_def, inv_inv] using
      ((hu.differentiable (by norm_num)) x).hasFDerivAt.lim h hc
  have hQcont (k : ℕ) : Continuous (Q k) := by
    simp only [hQ_def]
    have := hu.continuous
    fun_prop
  calc eLpNorm (fun x => fderiv ℝ u x h) p mu
      ≤ atTop.liminf fun k => eLpNorm (Q k) p mu :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => (hQcont k).aestronglyMeasurable) _
          ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
          (ae_of_all _ hlim)
    _ ≤ eLpNorm (Q 0) p mu + ENNReal.ofReal (|s| / 2) * C :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun k => le_self_add.trans (hQ k))
    _ = _ := by simp [hQ_def, ht_def, C, mul_assoc]

/-- **The interpolation inequality for a directional derivative.** For a `C²` function `u`, a
direction `h` and `ε > 0`,

`‖Du · h‖_p ≤ ε ‖h‖² ‖D²u‖_p + ε⁻¹ ‖u‖_p`, `1 ≤ p ≤ ∞`.

No support, integrability or boundedness hypothesis is needed. -/
theorem ContDiff.eLpNorm_fderiv_apply_le (hu : ContDiff ℝ 2 u) (hp : 1 ≤ p)
    (h : E) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun x => fderiv ℝ u x h) p mu ≤
      ENNReal.ofReal ε * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu +
        ENNReal.ofReal ε⁻¹ * eLpNorm u p mu := by
  -- Compare with the difference quotient of step `2ε`, which is at most `ε⁻¹ ‖u‖_p`.
  have hQ : ‖(2 * ε)⁻¹‖ₑ * (2 * eLpNorm u p mu) = ENNReal.ofReal ε⁻¹ * eLpNorm u p mu := by
    have hreal : ε⁻¹ = ‖(2 * ε)⁻¹‖ * 2 := by
      rw [norm_inv, Real.norm_of_nonneg (by positivity)]
      field_simp
    rw [← mul_assoc, hreal, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
      ENNReal.ofReal_ofNat]
  calc eLpNorm (fun x => fderiv ℝ u x h) p mu
      ≤ eLpNorm (fun x => (2 * ε)⁻¹ • (u (x + (2 * ε) • h) - u x)) p mu +
          ENNReal.ofReal (|2 * ε| / 2) * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu :=
        hu.eLpNorm_fderiv_apply_le_eLpNorm_inv_smul_comp_add_smul_sub_add hp h (by positivity)
    _ ≤ ENNReal.ofReal ε⁻¹ * eLpNorm u p mu +
          ENNReal.ofReal ε * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu := by
        rw [abs_of_pos (by positivity), mul_div_cancel_left₀ _ two_ne_zero, ← hQ]
        gcongr
        exact (eLpNorm_const_smul _ (fun x => u (x + (2 * ε) • h) - u x) _ _).trans_le
          (by grw [eLpNorm_comp_add_sub_le_two_mul hu.continuous.aestronglyMeasurable hp])
    _ = _ := add_comm _ _

end Smooth

section InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
  [SFinite mu] [mu.IsAddRightInvariant] {u : E → F} {p : ℝ≥0∞}

/-- **The interpolation inequality for the derivative.** For a `C²` function `u` on a real inner
product space `E` of dimension `n` and `ε > 0`,

`‖Du‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `1 ≤ p ≤ ∞`.

No support, integrability or boundedness hypothesis is needed. -/
theorem ContDiff.eLpNorm_fderiv_le (hu : ContDiff ℝ 2 u) (hp : 1 ≤ p) {ε : ℝ}
    (hε : 0 < ε) :
    eLpNorm (fderiv ℝ u) p mu ≤
      ENNReal.ofReal ε * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu +
        ENNReal.ofReal ((finrank ℝ E) ^ 2 / ε) * eLpNorm u p mu := by
  set n := finrank ℝ E
  set b := stdOrthonormalBasis ℝ E
  set A := eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu
  set U := eLpNorm u p mu
  have hmeas (i : Fin n) : AEStronglyMeasurable (fun x => fderiv ℝ u x (b i)) mu :=
    ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
  -- Each partial derivative obeys the directional inequality with `ε / n` in place of `ε`.
  have hpartial (i : Fin n) : eLpNorm (fun x => fderiv ℝ u x (b i)) p mu ≤
      ENNReal.ofReal (ε / n) * A + ENNReal.ofReal (n / ε) * U := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i)
    have h := hu.eLpNorm_fderiv_apply_le (mu := mu) hp (b i) (div_pos hε hn)
    rwa [← ofReal_norm, b.orthonormal.1 i, ENNReal.ofReal_one, one_pow, mul_one,
      inv_div] at h
  calc eLpNorm (fderiv ℝ u) p mu
      ≤ eLpNorm (∑ i, fun x => ‖fderiv ℝ u x (b i)‖) p mu :=
        eLpNorm_mono_real (hu.continuous_fderiv (by norm_num)).aestronglyMeasurable fun x => by
          rw [Finset.sum_apply]
          exact (fderiv ℝ u x).opNorm_le_sum_norm_apply_orthonormalBasis b
    _ ≤ ∑ i, eLpNorm (fun x => ‖fderiv ℝ u x (b i)‖) p mu := eLpNorm_sum_le hp
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ u x (b i)) p mu :=
        Finset.sum_congr rfl fun i _ => eLpNorm_norm _ (hmeas i)
    _ ≤ ∑ _i : Fin n, (ENNReal.ofReal (ε / n) * A + ENNReal.ofReal (n / ε) * U) :=
        Finset.sum_le_sum fun i _ => hpartial i
    _ = ENNReal.ofReal (n * (ε / n)) * A + ENNReal.ofReal (n * (n / ε)) * U := by
        simp [ENNReal.ofReal_mul, mul_assoc]
    _ ≤ ENNReal.ofReal ε * A + ENNReal.ofReal (n ^ 2 / ε) * U := by
        gcongr
        · rcases eq_or_ne (n : ℝ) 0 with hn | hn
          · rw [hn, zero_mul]
            exact hε.le
          · rw [mul_div_cancel₀ _ hn]
        · rw [mul_div_assoc', sq]

end InnerProductSpace

namespace TauCeti

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The interpolation inequality in `W^{2,p}_0(Ω)`.** Let `Ω ⊆ E` be open, `1 ≤ p ≤ ∞` and
`ε > 0`. Every `u ∈ W^{2,p}_0(Ω)` satisfies

`‖∇u‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `n = dim E`,

where `∇u` is the weak gradient `TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)` and
`D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No boundedness or boundary
regularity of `Ω` is needed. -/
theorem Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule
    {u : Wkp mu Omega p 2} (hu : u ∈ wkp0Submodule mu Omega p 2) {ε : ℝ} (hε : 0 < ε) :
    ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ ≤
      ε * ‖Wkp.iteratedGradient 1 u‖ + (finrank ℝ E) ^ 2 / ε * ‖Wkp.value 2 u‖ := by
  -- Both sides are continuous on `W^{2,p}(Ω)`, so it suffices to treat test functions.
  refine wkp0Submodule_subset_of_isClosed 2
    (s := {v | ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ ≤
      ε * ‖Wkp.iteratedGradient 1 v‖ + (finrank ℝ E) ^ 2 / ε * ‖Wkp.value 2 v‖})
    (isClosed_le ?_ ?_) (fun φ => ?_) hu
  · simp only [← Wkp.iteratedGradientL_apply, ← Wkp.lowerOrderL_apply]
    exact ((Wkp.iteratedGradientL 0).continuous.comp (Wkp.lowerOrderL 1).continuous).norm
  · simp only [← Wkp.iteratedGradientL_apply, ← Wkp.valueL_apply]
    exact (continuous_const.mul (Wkp.iteratedGradientL 1).continuous.norm).add
      (continuous_const.mul (Wkp.valueL 2).continuous.norm)
  -- For a test function `φ`, the three norms are the `Lᵖ` norms of `Dφ`, `D²φ` and `φ` on all of
  -- `E`.
  have hφ : ContDiff ℝ 2 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
  have hE1 : eLpNorm (iteratedFDeriv ℝ 1 (φ : E → ℝ)) p mu = eLpNorm (fderiv ℝ (φ : E → ℝ)) p mu :=
    eLpNorm_congr_norm_ae (hφ.continuous_iteratedFDeriv (by norm_num)).aestronglyMeasurable
      (hφ.continuous_fderiv (by norm_num)).aestronglyMeasurable
      (ae_of_all _ fun _ => norm_iteratedFDeriv_one _)
  have hE2 : eLpNorm (iteratedFDeriv ℝ 2 (φ : E → ℝ)) p mu =
      eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu :=
    eLpNorm_congr_norm_ae (hφ.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
      ((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
        (by norm_num)).aestronglyMeasurable
      (ae_of_all _ fun _ => (norm_iteratedFDeriv_fderiv (n := 1)).symm.trans
        (norm_iteratedFDeriv_one _))
  have hD : ‖Wkp.iteratedGradient 0 (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1 φ)‖ₑ =
      eLpNorm (fderiv ℝ (φ : E → ℝ)) p mu :=
    (Wkp.enorm_iteratedGradient_ofTestFunctionₗ 0 φ).trans hE1
  have hD2 := (Wkp.enorm_iteratedGradient_ofTestFunctionₗ (mu := mu) (p := p) 1 φ).trans hE2
  have hV := Wkp.enorm_value_ofTestFunctionₗ (mu := mu) (p := p) 2 φ
  have hA : eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu ≠ ∞ := hD2 ▸ enorm_ne_top
  have hU : eLpNorm (φ : E → ℝ) p mu ≠ ∞ := hV ▸ enorm_ne_top
  -- The smooth inequality, read in `ℝ`: all three seminorms are finite.
  rw [Set.mem_ofPred_eq, Wkp.lowerOrder_ofTestFunctionₗ, ← toReal_enorm, ← toReal_enorm,
    ← toReal_enorm, hD, hD2, hV]
  calc (eLpNorm (fderiv ℝ (φ : E → ℝ)) p mu).toReal
      ≤ (ENNReal.ofReal ε * eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu +
          ENNReal.ofReal ((finrank ℝ E) ^ 2 / ε) * eLpNorm (φ : E → ℝ) p mu).toReal :=
        ENNReal.toReal_mono (by finiteness) (hφ.eLpNorm_fderiv_le Fact.out hε)
    _ = ε * (eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu).toReal +
          (finrank ℝ E) ^ 2 / ε * (eLpNorm (φ : E → ℝ) p mu).toReal := by
        rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal (by positivity)]

/-- **The interpolation inequality in `W^{2,p}(E)`.** Let `1 ≤ p < ∞` and `ε > 0`. Every
`u ∈ W^{2,p}(E)` satisfies

`‖∇u‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `n = dim E`,

where `∇u` is the weak gradient `TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)` and
`D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. -/
theorem Wkp.norm_iteratedGradient_lowerOrder_le (hp : p ≠ ∞) (u : Wkp mu ⊤ p 2) {ε : ℝ}
    (hε : 0 < ε) :
    ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ ≤
      ε * ‖Wkp.iteratedGradient 1 u‖ + (finrank ℝ E) ^ 2 / ε * ‖Wkp.value 2 u‖ :=
  Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule
    (by rw [wkp0Submodule_top_eq_top hp]; trivial) hε

open Metric in
/-- **Interpolation between concentric balls.** There is a universal constant `c` such that, for
`1 ≤ p < ∞`, every `u ∈ W^{2,p}(Ω)`, every pair of radii `0 < s < t` with `B(x₀, t) ⊆ Ω`, and every
`ε > 0`,

`‖∇u‖_{Lᵖ(B_s)} ≤ ε (‖D²u‖_{Lᵖ(B_t)} + c (t - s)⁻¹ ‖∇u‖_{Lᵖ(B_t)} + c (t - s)⁻² ‖u‖_{Lᵖ(B_t)})
  + (n² / ε) ‖u‖_{Lᵖ(B_t)}`, `n = dim E`.

This is `TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule` applied to a cutoff
of `u` between the two balls; the terms with `c` come from the derivatives of the cutoff. -/
theorem Wkp.exists_lpNorm_gradient_ball_le (hp_top : p ≠ ⊤) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Omega : Opens E} (u : Wkp mu Omega p 2) {x₀ : E} {s t : ℝ}, 0 < s →
      s < t → ball x₀ t ⊆ Omega → ∀ {ε : ℝ}, 0 < ε →
        lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ s)) ≤
          ε * (lpNorm (Wkp.iteratedGradient 1 u) p (mu.restrict (ball x₀ t)) +
            c / (t - s) *
              lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ t)) +
            c / (t - s) ^ 2 * lpNorm (Wkp.value 2 u) p (mu.restrict (ball x₀ t))) +
          finrank ℝ E ^ 2 / ε * lpNorm (Wkp.value 2 u) p (mu.restrict (ball x₀ t)) := by
  obtain ⟨c, hc0, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := E)
  refine ⟨4 * c, by positivity, fun {Omega} u x₀ s t hs hst ht ε hε => ?_⟩
  set m := (s + t) / 2 with hm
  obtain ⟨η, hη, hηr, hη1, hηts, hηg, hηh⟩ := hcut x₀ hs.le (show s < m by linarith)
  set U : Opens E := ⟨ball x₀ t, isOpen_ball⟩
  have hU : U ≤ Omega := fun x hx => ht hx
  have hsU : ball x₀ s ⊆ U := ball_subset_ball hst.le
  set v := Wkp.restrictL hU 2 u with hv
  have hcpt : HasCompactSupport η :=
    (isCompact_closedBall x₀ m).of_isClosed_subset (isClosed_tsupport η) hηts
  have hηU : tsupport η ⊆ U := hηts.trans (closedBall_subset_ball (by linarith))
  obtain ⟨w, hw0, hwv⟩ := Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul hp_top hη hcpt hηU 2 v
  have hint := Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule hw0 hε
  have hηabs : ∀ x, |η x| ≤ 1 := fun x =>
    abs_le.2 ⟨by linarith [(hηr ⟨x, rfl⟩).1], (hηr ⟨x, rfl⟩).2⟩
  -- The restriction `v` of `u` to `B_t` has the same value and weak derivatives there.
  have hvg : (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v) : E → E) =ᵐ[mu.restrict U]
      Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) := by
    rw [hv, Wkp.lowerOrder_restrictL]
    exact Wkp.iteratedGradient_restrictL_ae hU 0 (Wkp.lowerOrder 1 u)
  have hnv : ‖Wkp.value 2 v‖ = lpNorm (Wkp.value 2 u) p (mu.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Wkp.value_restrictL_ae hU 2 u), toReal_eLpNorm]
    rfl
  have hngv : ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ =
      lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae hvg, toReal_eLpNorm]
    rfl
  have hnHv : ‖Wkp.iteratedGradient 1 v‖ =
      lpNorm (Wkp.iteratedGradient 1 u) p (mu.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Wkp.iteratedGradient_restrictL_ae hU 1 u), toReal_eLpNorm]
    rfl
  -- On `B_s` the cutoff is one, so `∇w = ∇u` there.
  have hwg := Wkp.iteratedGradient_zero_ae_eq_of_value_ae_eq_mul (u := Wkp.lowerOrder 1 v)
    (w := Wkp.lowerOrder 1 w) hη (by simpa only [Wkp.value_succ] using hwv)
  have hgs : (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) : E → E) =ᵐ[mu.restrict (ball x₀ s)]
      Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsU hvg,
      ae_restrict_of_ae_restrict_of_subset hsU hwg, ae_restrict_mem measurableSet_ball]
      with x h1 h2 hx
    have hev : η =ᶠ[nhds x] fun _ => 1 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy =>
        hη1 (ball_subset_closedBall hy)
    rw [h2, hη1 (ball_subset_closedBall hx), hev.gradient_eq, gradient_fun_const, h1]
    simp
  have hstep1 : lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ s)) ≤
      ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w)‖ := by
    rw [← toReal_eLpNorm, eLpNorm_congr_ae hgs, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsU le_rfl))
  -- The weak Hessian of `w = η v` is `η D²v` plus the Leibniz remainder.
  set M₁ := c / (m - s)
  set M₂ := c / (m - s) ^ 2
  have hM₁0 : 0 ≤ M₁ := div_nonneg hc0 (by linarith)
  have hM₂0 : 0 ≤ M₂ := div_nonneg hc0 (by positivity)
  have hD := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hη hwv
  have hηH : MemLp (fun x => η x • Wkp.iteratedGradient 1 v x) p (mu.restrict U) :=
    (hη.continuous.memLp_top_of_hasCompactSupport hcpt (mu.restrict U)).smul (Lp.memLp _)
  set TL := Wkp.iteratedGradient 1 w - hηH.toLp _ with hTL_def
  have hTL : ‖TL‖ ≤ 2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ +
      M₂ * ‖Wkp.value 2 v‖ := by
    refine TauCeti.Lp.norm_le_add_of_ae_norm_le (by positivity) hM₂0 ?_
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 w) (hηH.toLp _), hD,
      hηH.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, add_assoc, add_assoc, add_sub_cancel_left, ← add_assoc]
    refine (norm_leibnizRemainder_le η _ _ x).trans ?_
    gcongr
    · exact hηg x
    · exact hηh x
  have hηHn : ‖hηH.toLp _‖ ≤ ‖Wkp.iteratedGradient 1 v‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hηH.coeFn_toLp] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηabs x)
  have hstep2 : ‖Wkp.iteratedGradient 1 w‖ ≤ ‖Wkp.iteratedGradient 1 v‖ +
      (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ + M₂ * ‖Wkp.value 2 v‖) := by
    rw [show Wkp.iteratedGradient 1 w = hηH.toLp _ + TL by rw [hTL_def, add_sub_cancel]]
    exact (norm_add_le _ _).trans (add_le_add hηHn hTL)
  have hstep3 : ‖Wkp.value 2 w‖ ≤ ‖Wkp.value 2 v‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hwv] with x hx
    rw [hx, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηabs x)
  have hms : m - s = (t - s) / 2 := by rw [hm]; ring
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  have hm1 : 2 * M₁ = 4 * c / (t - s) := by
    simp only [M₁, hms]
    field_simp
    ring
  have hm2 : M₂ = 4 * c / (t - s) ^ 2 := by
    simp only [M₂, hms]
    field_simp
    ring
  rw [hm1, hm2, hngv, hnv, hnHv] at hstep2
  rw [hnv] at hstep3
  calc _ ≤ _ := hstep1
    _ ≤ _ := hint
    _ ≤ _ := by
        gcongr
        linarith

end Sobolev

end TauCeti
