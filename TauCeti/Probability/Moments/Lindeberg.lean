/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Basic
public import TauCeti.MeasureTheory.Integral.Pi
public import TauCeti.MeasureTheory.Integral.Prod

/-!
# Lindeberg replacement

Finite-dimensional Lindeberg replacement: swapping the independent coordinates of a product of
probability measures on `ℝ` one at a time, for a test function that is `C^(r+1)` in each
coordinate, when the first `r` moments agree. The one-variable replacement bound also holds for
finite measures.

## Main results

* `TauCeti.abs_sub_taylorWithinEval_le`: if `g` is `C^(r+1)` and its `(r+1)`st derivative is
  bounded by `M`, then `g x` differs from its degree-`r` Taylor evaluation by at most
  `M * |x| ^ (r + 1) / (r + 1)!`.
* `TauCeti.Probability.abs_integral_sub_integral_le`: the one-variable replacement bound.
* `TauCeti.Probability.abs_integral_prod_sub_integral_prod_le`: the one-coordinate replacement
  bound with an arbitrary background measure.
* `TauCeti.Probability.abs_integral_pi_sub_integral_pi_le`: the replacement inequality for product
  measures on a finite product of copies of `ℝ`, assuming integrability under the hybrid
  product measures.
* `TauCeti.Probability.abs_integral_pi_sub_integral_pi_le_of_bounded`: the bounded-continuous
  specialization.

## References

* J. W. Lindeberg, “Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung,” *Mathematische Zeitschrift* 15 (1922), 211–225.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American
  Mathematical Society, 2012, §2.2.
-/

public section

open Finset Nat

namespace TauCeti.Probability

open MeasureTheory

/-- Two finite measures on `ℝ` with the same moments up to order `r` and a finite absolute
moment of order `r + 1` give expectations of a `C^(r+1)` function that differ by at most the
`(r+1)`st derivative bound times the two absolute moments over `(r+1)!`. -/
theorem abs_integral_sub_integral_le {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {g : ℝ → ℝ} {r : ℕ} (hg : ContDiff ℝ (r + 1) g) {M : ℝ}
    (hM : ∀ t, |iteratedDeriv (r + 1) g t| ≤ M)
    (hμ : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) μ)
    (hν : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ν)
    (hmom : ∀ k ≤ r, ∫ t, t ^ k ∂μ = ∫ t, t ^ k ∂ν) :
    |∫ t, g t ∂μ - ∫ t, g t ∂ν| ≤
      M / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ + ∫ t, |t| ^ (r + 1) ∂ν) := by
  let T : ℝ → ℝ := fun t ↦ taylorWithinEval g r Set.univ 0 t
  have hPc : Continuous T := by
    simp only [T, taylor_within_apply, iteratedDerivWithin_univ]
    fun_prop
  have hRc : Continuous fun t ↦ g t - T t := hg.continuous.sub hPc
  have hRb : ∀ t, ‖g t - T t‖ ≤ M / (r + 1)! * |t| ^ (r + 1) := fun t ↦ by
    rw [Real.norm_eq_abs, div_mul_eq_mul_div]
    simpa [T, sub_zero] using
      abs_sub_taylorWithinEval_le (x₀ := 0) (fun t _ ↦ hg.contDiffAt) fun s _ ↦ hM s
  have hPterm : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ →
      ∀ k ∈ range (r + 1),
        Integrable
          (fun t : ℝ ↦ ((k ! : ℝ)⁻¹ * (t - 0) ^ k) • iteratedDeriv k g 0) ρ := by
    intro ρ _ h k hk
    have hklt : k < r + 1 := Finset.mem_range.mp hk
    have hkle : k ≤ r + 1 := (Nat.le_of_lt_succ hklt).trans (Nat.le_succ r)
    have hpow : Integrable (fun t : ℝ ↦ ‖t‖ ^ (r + 1)) ρ := by
      simpa [Real.norm_eq_abs] using h
    have hlow : Integrable (fun t : ℝ ↦ ‖t‖ ^ k) ρ :=
      integrable_norm_pow_of_le aestronglyMeasurable_id hkle hpow
    have hpoly : Integrable (fun t : ℝ ↦ t ^ k) ρ := by
      apply (integrable_norm_iff
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ t ^ k) ρ)).1
      simpa only [norm_pow] using hlow
    have hterm := (hpoly.const_mul (iteratedDeriv k g 0)).div_const (k !)
    simpa [smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hterm
  have hPint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ → Integrable T ρ := by
    intro ρ _ h
    dsimp [T]
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    exact integrable_finsetSum _ fun k hk ↦ hPterm ρ h k hk
  have hRint : ∀ (ρ : Measure ℝ), Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ →
      Integrable (fun t ↦ g t - T t) ρ := fun ρ h ↦
    Integrable.mono' (h.const_mul _) hRc.aestronglyMeasurable (Filter.Eventually.of_forall hRb)
  have hPeq : ∫ t, T t ∂μ = ∫ t, T t ∂ν := by
    dsimp only [T]
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    rw [integral_finsetSum _ fun k hk ↦ hPterm μ hμ k hk,
      integral_finsetSum _ fun k hk ↦ hPterm ν hν k hk]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hterm :
        (fun t : ℝ ↦ ((k ! : ℝ)⁻¹ * (t - 0) ^ k) • iteratedDeriv k g 0) =
          fun t ↦ (k ! : ℝ)⁻¹ * iteratedDeriv k g 0 * t ^ k := by
      funext t
      simp only [smul_eq_mul, sub_zero]
      ring
    rw [hterm, integral_const_mul, integral_const_mul,
      hmom k (by have := Finset.mem_range.mp hk; omega)]
  have hgμ : Integrable g μ :=
    ((hRint μ hμ).add (hPint μ hμ)).congr (Filter.Eventually.of_forall fun t ↦ by simp)
  have hgν : Integrable g ν :=
    ((hRint ν hν).add (hPint ν hν)).congr (Filter.Eventually.of_forall fun t ↦ by simp)
  have hsplit : ∫ t, g t ∂μ - ∫ t, g t ∂ν =
      (∫ t, (g t - T t) ∂μ) - ∫ t, (g t - T t) ∂ν := by
    rw [integral_sub hgμ (hPint μ hμ), integral_sub hgν (hPint ν hν), hPeq]
    ring
  have hb : ∀ (ρ : Measure ℝ), Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ρ →
      |∫ t, (g t - T t) ∂ρ| ≤ M / (r + 1)! * ∫ t, |t| ^ (r + 1) ∂ρ :=
    fun ρ h ↦ by
      have := norm_integral_le_of_norm_le (h.const_mul (M / (r + 1)!))
        (Filter.Eventually.of_forall hRb)
      rwa [integral_const_mul, Real.norm_eq_abs] at this
  rw [hsplit]
  calc _ ≤ |∫ t, (g t - T t) ∂μ| + |∫ t, (g t - T t) ∂ν| :=
        abs_sub _ _
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hb μ hμ) (hb ν hν)

/-- Replacing one coordinate of a product of finite measures with matching moments, against a
probability background measure, is controlled by the one-variable replacement bound. The
assumptions allow the background space and test function to be arbitrary, including unbounded
test functions. -/
theorem abs_integral_prod_sub_integral_prod_le {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {β : Type*} [MeasurableSpace β]
    (κ : Measure β) [IsProbabilityMeasure κ] {r : ℕ} {g : ℝ × β → ℝ} (M : ℝ)
    (hμg : Integrable g (μ.prod κ)) (hνg : Integrable g (ν.prod κ))
    (hμ : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) μ)
    (hν : Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) ν)
    (hmom : ∀ k ≤ r, ∫ t, t ^ k ∂μ = ∫ t, t ^ k ∂ν)
    (hsm : ∀ w, ContDiff ℝ (r + 1) fun t ↦ g (t, w))
    (hM : ∀ w t, |iteratedDeriv (r + 1) (fun s ↦ g (s, w)) t| ≤ M) :
    |∫ p, g p ∂(μ.prod κ) - ∫ p, g p ∂(ν.prod κ)| ≤
      M / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ + ∫ t, |t| ^ (r + 1) ∂ν) := by
  rw [← Real.norm_eq_abs, ← integral_prod_swap (μ := μ) g, ← integral_prod_swap (μ := ν) g]
  have hslice := ae_of_all κ fun w ↦
    (Real.norm_eq_abs _).trans_le (abs_integral_sub_integral_le (hsm w) (hM w) hμ hν hmom)
  simpa only [probReal_univ, mul_one, Function.comp_apply] using
    norm_integral_prod_sub_integral_prod_le_of_ae hμg.swap hνg.swap hslice

/-- **Lindeberg replacement.** Let `μ i` and `ν i` be probability measures on `ℝ` with finite
absolute moments of order `r + 1` and the same moments up to order `r`. If `f` is integrable under
every hybrid product measure that chooses each coordinate from either `μ` or `ν`, and is
`C^(r+1)` in each coordinate with `(r+1)`st derivative in coordinate `i` bounded by `M i`, then
replacing `Measure.pi μ` by `Measure.pi ν` changes the expectation of `f` by at most
`∑ i, M i / (r + 1)! * (∫ |t| ^ (r + 1) ∂μ i + ∫ |t| ^ (r + 1) ∂ν i)`.

This is the finite-dimensional Lindeberg swapping argument; see the references above. -/
theorem abs_integral_pi_sub_integral_pi_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (μ i))
    (hν : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (ν i))
    (hmom : ∀ i, ∀ k ≤ r, ∫ t, t ^ k ∂μ i = ∫ t, t ^ k ∂ν i)
    {f : (ι → ℝ) → ℝ}
    (hfi : ∀ s : Finset ι,
      Integrable f (Measure.pi fun i ↦ if i ∈ s then ν i else μ i))
    {M : ι → ℝ}
    (hsm : ∀ z i, ContDiff ℝ (r + 1) fun t ↦ f (Function.update z i t))
    (hM : ∀ z i t, |iteratedDeriv (r + 1) (fun s ↦ f (Function.update z i s)) t| ≤ M i) :
    |∫ z, f z ∂Measure.pi μ - ∫ z, f z ∂Measure.pi ν| ≤
      ∑ i, M i / (r + 1)! * (∫ t, |t| ^ (r + 1) ∂μ i + ∫ t, |t| ^ (r + 1) ∂ν i) := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_pi_sub_integral_pi_le_of_ae_slice_le (α := fun _ ↦ ℝ) μ ν
    hfi _ (fun _ i _ ↦ ae_of_all _ fun x ↦ ?_)
  let w := (MeasurableEquiv.piSplitAt i (fun _ : ι ↦ ℝ)).symm (0, x)
  have hslice (t : ℝ) :
      (MeasurableEquiv.piSplitAt i (fun _ : ι ↦ ℝ)).symm (t, x) = Function.update w i t := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hj]
      simp only [w, MeasurableEquiv.piSplitAt_symm_apply_ne i _ j hj]
  simp only [hslice]
  simpa only [← Real.norm_eq_abs] using
    abs_integral_sub_integral_le (hsm w i) (hM w i) (hμ i) (hν i) (hmom i)

/-- The Lindeberg replacement inequality for bounded continuous test functions. Boundedness and
continuity imply the integrability hypothesis of `abs_integral_pi_sub_integral_pi_le`. -/
theorem abs_integral_pi_sub_integral_pi_le_of_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (μ i))
    (hν : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (ν i))
    (hmom : ∀ i, ∀ k ≤ r, ∫ t, t ^ k ∂μ i = ∫ t, t ^ k ∂ν i)
    {f : (ι → ℝ) → ℝ} (hf : Continuous f) {C : ℝ} (hfb : ∀ z, |f z| ≤ C)
    {M : ι → ℝ}
    (hsm : ∀ z i, ContDiff ℝ (r + 1) fun t ↦ f (Function.update z i t))
    (hM : ∀ z i t, |iteratedDeriv (r + 1) (fun s ↦ f (Function.update z i s)) t| ≤ M i) :
    |∫ z, f z ∂Measure.pi μ - ∫ z, f z ∂Measure.pi ν| ≤
      ∑ i, M i / (r + 1)! *
        (∫ t, |t| ^ (r + 1) ∂μ i + ∫ t, |t| ^ (r + 1) ∂ν i) := by
  apply abs_integral_pi_sub_integral_pi_le μ ν hμ hν hmom
    (f := f) (M := M) (hsm := hsm) (hM := hM)
  intro s
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z ↦ by
      simpa [Real.norm_eq_abs] using hfb z)

end TauCeti.Probability
