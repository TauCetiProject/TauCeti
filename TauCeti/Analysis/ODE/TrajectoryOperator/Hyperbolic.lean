/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.ODE.LyapunovPerron.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.Density
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# The trajectory operator of a constant hyperbolic coefficient

Let `A` be a bounded operator on a real Banach space `X` whose flow `exp (t A)` has an exponential
dichotomy: for a bounded operator `P` commuting with `A`, constants `K` and `α > 0`,

`‖exp (t A) (P v)‖ ≤ K exp (-α t) ‖v‖` for `t ≥ 0`, and
`‖exp (t A) (v - P v)‖ ≤ K exp (α t) ‖v‖` for `t ≤ 0`.

These are the hypotheses of the Lyapunov--Perron construction in
`TauCeti.Analysis.ODE.LyapunovPerron.Basic`. Classically, on a finite-dimensional space they hold
for the spectral projection `P` onto the generalized eigenspaces of eigenvalues of negative real
part whenever `A` has no eigenvalue on the imaginary axis; that existence statement is not proved
here, and the results below take the estimates as hypotheses. The projection `P` need not be
idempotent for any of them.

The *Green integral* (`ContinuousLinearMap.greenIntegral`)

`G g (t) = ∫_{s ≤ t} exp ((t - s) A) (P (g s)) ds - ∫_{s > t} exp ((t - s) A) (g s - P (g s)) ds`

propagates the `P`-part of a forcing term forward from `-∞` and the remaining part backward from
`+∞`. Its kernel is bounded by `K exp (-α |t - s|)`, which has integral `2 K / α`, so Schur's test
bounds it on every `Lᵖ` (`ContinuousLinearMap.eLpNorm_greenIntegral_le`). For a bounded continuous
forcing term it solves `u' = A u + g` (`ContinuousLinearMap.hasDerivAt_greenIntegral`), and it
recovers every compactly supported `C¹` path `u` from `u' - A u`
(`ContinuousLinearMap.greenIntegral_deriv_sub_eq`).

For a finite-dimensional `X` and `1 ≤ p < ∞` this shows that the trajectory operator
`d/ds - A : W^{1,p}(ℝ, X) → Lᵖ(ℝ, X)` (`TauCeti.WeakDerivStep.trajectoryOperator` of the
constant coefficient `-A`) is bijective. The representation formula gives the estimate
`‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - A u‖_{Lᵖ}` on smooth compactly supported paths, which extends to
`W^{1,p}(ℝ, X)` by density, so the operator is injective with closed range; its range contains
every smooth compactly supported path, hence is dense. In particular it is Fredholm of index zero.
This is the constant-coefficient, whole-line case of the Fredholm theory of `d/ds - A(s)` with
hyperbolic limits; neither symmetry of `A` nor an inner product is used.

## Main declarations

* `ContinuousLinearMap.greenIntegral`: the whole-line Green integral of a dichotomy.
* `ContinuousLinearMap.eLpNorm_greenIntegral_le`: the bound `‖G g‖_{Lᵖ} ≤ 2 K / α ‖g‖_{Lᵖ}`.
* `ContinuousLinearMap.hasDerivAt_greenIntegral`: `G g` solves `u' = A u + g`.
* `ContinuousLinearMap.greenIntegral_deriv_sub_eq`: `G (u' - A u) = u` for compactly supported
  `C¹` paths `u`.
* `TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_dichotomy`: the a priori
  estimate `‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - A u‖_{Lᵖ}` on `W^{1,p}(ℝ, X)`.
* `TauCeti.WeakDerivStep.bijective_trajectoryOperator_of_dichotomy`: `d/ds - A` is bijective.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_dichotomy` and
  `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_zero_of_dichotomy`: it is Fredholm of index
  zero.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer (1978) (exponential dichotomies and the Green function of `u' = A u + g`).
* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256 (the operator `u ↦ u' - A(t) u` under exponential
  dichotomies, and its Fredholm property).
-/

public section

noncomputable section

open Filter MeasureTheory NormedSpace Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The whole-line Green integral of the forcing term `g`:

`∫_{s ≤ t} exp ((t - s) A) (P (g s)) ds - ∫_{s > t} exp ((t - s) A) (g s - P (g s)) ds`.

The first integral propagates the part `P (g s)` of the forcing forward from `-∞`; the second
propagates the remaining part `g s - P (g s)` backward from `+∞`. Under an exponential dichotomy
for `exp (t A)` with projection `P`, it is the bounded solution of `u' = A u + g`. -/
def greenIntegral (A P : X →L[ℝ] X) (g : ℝ → X) (t : ℝ) : X :=
  (∫ s in Iic t, exp ((t - s) • A) (P (g s))) - ∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))

theorem greenIntegral_def (A P : X →L[ℝ] X) (g : ℝ → X) (t : ℝ) :
    greenIntegral A P g t = (∫ s in Iic t, exp ((t - s) • A) (P (g s))) -
      ∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s)) := (rfl)

variable [CompleteSpace X] {A P : X →L[ℝ] X} {K α : ℝ≥0} {M : ℝ} {g : ℝ → X}

/-! ### The Green integral solves `u' = A u + g` -/

/-- Under the forward exponential estimate, the stable integrand `exp (-s A) (P (g s))` of a
continuous forcing term bounded by `M` is integrable on every half-line `(-∞, c]`. -/
private theorem integrableOn_exp_neg_smul_apply_Iic
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (c : ℝ) :
    IntegrableOn (fun s ↦ exp ((-s) • A) (P (g s))) (Iic c) := by
  have hα' : (0 : ℝ) < α := hα
  have hcont : Continuous fun s ↦ exp ((-s) • A) (P (g s)) :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply
      (P.continuous.comp hg)
  -- On `(-∞, 0]` the integrand decays like `exp (α s)`.
  have h₀ : IntegrableOn (fun s ↦ exp ((-s) • A) (P (g s))) (Iic 0) := by
    refine ((integrableOn_exp_mul_Iic hα' 0).const_mul (K * M)).mono'
      (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs0
    calc ‖exp ((-s) • A) (P (g s))‖ ≤ K * Real.exp (-α * -s) * ‖g s‖ :=
          hs _ (neg_nonneg.2 hs0) _
      _ ≤ K * Real.exp (-α * -s) * M := by gcongr; exact hgM s
      _ = K * M * Real.exp (α * s) := by ring_nf
  exact (h₀.union (hcont.integrableOn_Icc (a := 0) (b := c))).mono_set fun s hs' ↦
    (le_or_gt s 0).elim Or.inl fun h ↦ Or.inr ⟨h.le, hs'⟩

/-- The Green integral differs from the Lyapunov--Perron integral by the free solution
`exp (t A) c` with `c = ∫_{s ≤ 0} exp (-s A) (P (g s)) ds`. -/
private theorem greenIntegral_eq_lyapunovPerronIntegral_add
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) :
    greenIntegral A P g t = lyapunovPerronIntegral A P g t +
      exp (t • A) (∫ s in Iic 0, exp ((-s) • A) (P (g s))) := by
  set h : ℝ → X := fun s ↦ exp ((-s) • A) (P (g s)) with h_def
  have hint := integrableOn_exp_neg_smul_apply_Iic hs hα hg hgM
  have hpull (s : ℝ) : exp ((t - s) • A) (P (g s)) = exp (t • A) (h s) := by
    simp only [h_def, ← ContinuousLinearMap.exp_add_smul_apply, sub_eq_add_neg]
  have hIic : (∫ s in Iic t, exp ((t - s) • A) (P (g s))) =
      exp (t • A) (∫ s in Iic t, h s) := by
    simp only [hpull]
    exact (exp (t • A)).integral_comp_comm (hint t)
  have hIcc : (∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))) =
      exp (t • A) (∫ s in (0 : ℝ)..t, h s) := by
    simp only [hpull]
    exact (exp (t • A)).intervalIntegral_comp_comm
      (((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply
        (P.continuous.comp hg) |>.intervalIntegrable _ _)
  have hsplit : (∫ s in Iic t, h s) = (∫ s in Iic 0, h s) + ∫ s in (0 : ℝ)..t, h s := by
    rw [← intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint t), add_sub_cancel]
  rw [greenIntegral_def, lyapunovPerronIntegral_def, hIic, hIcc, hsplit, map_add]
  abel

/-- **The Green integral solves the forced equation.** Under an exponential dichotomy, for a
continuous bounded forcing term `g`, the Green integral solves `u' = A u + g`. -/
theorem hasDerivAt_greenIntegral
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) :
    HasDerivAt (greenIntegral A P g) (A (greenIntegral A P g t) + g t) t := by
  set c := ∫ s in Iic 0, exp ((-s) • A) (P (g s))
  have hfun : greenIntegral A P g = fun t ↦ lyapunovPerronIntegral A P g t + exp (t • A) c :=
    funext (greenIntegral_eq_lyapunovPerronIntegral_add hs hα hg hgM)
  have hfree : HasDerivAt (fun t ↦ exp (t • A) c) (A (exp (t • A) c)) t := by
    simpa using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t c)
  rw [hfun]
  refine ((hasDerivAt_lyapunovPerronIntegral hu hα hg hgM t).add hfree).congr_deriv ?_
  rw [map_add]
  abel

/-- Under an exponential dichotomy, the Green integral of a continuous bounded forcing term is
continuous. -/
theorem continuous_greenIntegral
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) :
    Continuous (greenIntegral A P g) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_greenIntegral hs hu hα hg hgM t).continuousAt

/-! ### Pointwise and `Lᵖ` bounds -/

section Bounds

variable (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
include hs hu

omit [CompleteSpace X] in
/-- Under an exponential dichotomy, the Green integral is bounded pointwise by the integral of
`‖g‖` against the kernel `K exp (-α |t - s|)`. No integrability of `g` is needed. -/
theorem enorm_greenIntegral_le (g : ℝ → X) (t : ℝ) :
    ‖greenIntegral A P g t‖ₑ ≤
      ∫⁻ s, ENNReal.ofReal (K * Real.exp (-(α * |t - s|))) * ‖g s‖ₑ := by
  set k : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (K * Real.exp (-(α * |t - s|))) * ‖g s‖ₑ
  have h₁ : ‖∫ s in Iic t, exp ((t - s) • A) (P (g s))‖ₑ ≤ ∫⁻ s in Iic t, k s := by
    refine (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono_ae ((ae_restrict_mem measurableSet_Iic).mono fun s hst ↦ ?_))
    have hts : 0 ≤ t - s := sub_nonneg.2 hst
    calc ‖exp ((t - s) • A) (P (g s))‖ₑ = ENNReal.ofReal ‖exp ((t - s) • A) (P (g s))‖ := by
          rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (K * Real.exp (-(α * |t - s|)) * ‖g s‖) :=
          ENNReal.ofReal_le_ofReal ((hs _ hts _).trans_eq (by rw [abs_of_nonneg hts, neg_mul]))
      _ = k s := by rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
  have h₂ : ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ₑ ≤ ∫⁻ s in Ioi t, k s := by
    refine (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun s hst ↦ ?_))
    have hts : t - s < 0 := sub_neg.2 hst
    calc ‖exp ((t - s) • A) (g s - P (g s))‖ₑ =
          ENNReal.ofReal ‖exp ((t - s) • A) (g s - P (g s))‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (K * Real.exp (-(α * |t - s|)) * ‖g s‖) :=
          ENNReal.ofReal_le_ofReal
            ((hu _ hts.le _).trans_eq (by rw [abs_of_neg hts, mul_neg, neg_neg]))
      _ = k s := by rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
  calc ‖greenIntegral A P g t‖ₑ
      ≤ ‖∫ s in Iic t, exp ((t - s) • A) (P (g s))‖ₑ +
          ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ₑ := enorm_sub_le
    _ ≤ (∫⁻ s in Iic t, k s) + ∫⁻ s in Ioi t, k s := add_le_add h₁ h₂
    _ = ∫⁻ s, k s := by rw [← compl_Iic, lintegral_add_compl _ measurableSet_Iic]

omit hs hu in
/-- The kernel `K exp (-α |x|)` has integral `2 K / α`. -/
private theorem lintegral_ofReal_mul_exp_neg_mul_abs (hα : 0 < α) :
    ∫⁻ x : ℝ, ENNReal.ofReal (K * Real.exp (-(α * |x|))) = ENNReal.ofReal (2 * K / α) := by
  have hα' : (0 : ℝ) < α := hα
  have hIic : ∫⁻ x in Iic 0, ENNReal.ofReal (K * Real.exp (-(α * |x|))) =
      ENNReal.ofReal (K / α) := by
    have hint : IntegrableOn (fun x : ℝ ↦ K * Real.exp (α * x)) (Iic 0) :=
      (integrableOn_exp_mul_Iic hα' 0).const_mul _
    rw [setLIntegral_congr_fun measurableSet_Iic (g := fun x ↦ ENNReal.ofReal
        (K * Real.exp (α * x))) fun x hx ↦ by simp only [abs_of_nonpos hx, mul_neg, neg_neg],
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ by positivity),
      integral_const_mul, integral_exp_mul_Iic hα', mul_zero, Real.exp_zero, mul_one_div]
  have hIoi : ∫⁻ x in Ioi 0, ENNReal.ofReal (K * Real.exp (-(α * |x|))) =
      ENNReal.ofReal (K / α) := by
    have hint : IntegrableOn (fun x : ℝ ↦ K * Real.exp (-α * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hα') 0).const_mul _
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun x ↦ ENNReal.ofReal
        (K * Real.exp (-α * x))) fun x hx ↦ by simp only [abs_of_pos hx, neg_mul],
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ by positivity),
      integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hα'), mul_zero, Real.exp_zero,
      neg_div_neg_eq, mul_one_div]
  rw [← lintegral_add_compl _ measurableSet_Iic, compl_Iic, hIic, hIoi,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

/-- **The Green integral is bounded on `Lᵖ`.** Under an exponential dichotomy with constant `K`
and rate `α > 0`, `‖G g‖_{Lᵖ} ≤ 2 K / α ‖g‖_{Lᵖ}` for every continuous bounded `g` and every
`1 ≤ p ≤ ∞`. This is Schur's test for
the kernel `K exp (-α |t - s|)`, whose row and column integrals are `2 K / α`. -/
theorem eLpNorm_greenIntegral_le (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (greenIntegral A P g) p volume ≤ ENNReal.ofReal (2 * K / α) * eLpNorm g p volume := by
  set k : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ ENNReal.ofReal (K * Real.exp (-(α * |t - s|)))
  have hk : AEMeasurable (Function.uncurry k) (volume.prod volume) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.sub continuous_snd).abs).neg))).measurable.aemeasurable
  have hrow (t : ℝ) : ∫⁻ s, k t s ≤ ENNReal.ofReal (2 * K / α) :=
    (lintegral_sub_left_eq_self (fun x ↦ ENNReal.ofReal (K * Real.exp (-(α * |x|)))) t).trans
      (lintegral_ofReal_mul_exp_neg_mul_abs hα) |>.le
  have hcol (s : ℝ) : ∫⁻ t, k t s ≤ ENNReal.ofReal (2 * K / α) :=
    (lintegral_sub_right_eq_self (fun x ↦ ENNReal.ofReal (K * Real.exp (-(α * |x|)))) s).trans
      (lintegral_ofReal_mul_exp_neg_mul_abs hα) |>.le
  have hexp : (1 - p.toReal⁻¹) + p.toReal⁻¹ = 1 := sub_add_cancel _ _
  calc eLpNorm (greenIntegral A P g) p volume
      ≤ eLpNorm (fun t ↦ ∫⁻ s, k t s * ‖g s‖ₑ) p volume :=
        eLpNorm_mono_enorm (continuous_greenIntegral hs hu hα hg hgM).aestronglyMeasurable
          fun t ↦ by simpa only [enorm_eq_self] using enorm_greenIntegral_le hs hu g t
    _ ≤ ENNReal.ofReal (2 * K / α) ^ (1 - p.toReal⁻¹) *
          ENNReal.ofReal (2 * K / α) ^ p.toReal⁻¹ * eLpNorm (fun s ↦ ‖g s‖ₑ) p volume :=
        TauCeti.eLpNorm_lintegral_mul_le hk hg.aestronglyMeasurable.enorm hp (ae_of_all _ hrow)
          (ae_of_all _ hcol)
    _ = ENNReal.ofReal (2 * K / α) * eLpNorm g p volume := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (TauCeti.one_sub_toReal_inv_nonneg hp)
        (inv_nonneg.2 ENNReal.toReal_nonneg), hexp, ENNReal.rpow_one,
        eLpNorm_enorm _ hg.aestronglyMeasurable]

end Bounds

/-- **The Green integral inverts `d/ds - A` on compactly supported paths.** If `P` commutes with
`A`, then every compactly supported `C¹` path `u` is the Green integral of `u' - A u`. No
dichotomy estimate is needed: both half-line integrals are integrals of derivatives of
compactly supported paths. -/
theorem greenIntegral_deriv_sub_eq (hAP : Commute A P) {u : ℝ → X}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (t : ℝ) :
    greenIntegral A P (fun s ↦ deriv u s - A (u s)) t = u t := by
  set g : ℝ → X := fun s ↦ deriv u s - A (u s) with g_def
  have hgc : Continuous g := (hu.continuous_deriv le_rfl).sub (A.continuous.comp hu.continuous)
  have hgs : HasCompactSupport g := huc.deriv.sub (huc.comp_left (map_zero A))
  -- `exp (r A)` commutes with `A` and with `P`.
  have hcA (r : ℝ) (v : X) : exp (r • A) (A v) = A (exp (r • A) v) := by
    rw [← mul_apply_eq_comp, ((Commute.refl A).smul_right r).exp_right.eq.symm,
      mul_apply_eq_comp]
  have hexp (s : ℝ) : HasDerivAt (fun s ↦ exp ((t - s) • A)) (-(A * exp ((t - s) • A))) s := by
    simpa [Function.comp_def] using
      (hasDerivAt_exp_smul_const' A (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
  -- Each half-line integrand is the derivative of a compactly supported path.
  have hcont (L : X →L[ℝ] X) : Continuous fun s ↦ exp ((t - s) • A) (L (g s)) :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_const.sub continuous_id)).clm_apply (L.continuous.comp hgc)
  have hsupp (L : X →L[ℝ] X) {w : ℝ → X} (hw : HasCompactSupport w) :
      HasCompactSupport fun s ↦ exp ((t - s) • A) (L (w s)) :=
    hw.mono fun s hs hw0 ↦ hs (by simp [hw0])
  have htendsto (L : X →L[ℝ] X) (l : Filter ℝ) (hl : l ≤ Filter.cocompact ℝ) :
      Tendsto (fun s ↦ exp ((t - s) • A) (L (u s))) l (𝓝 0) := by
    have h := hsupp L huc
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h
    exact (h.filter_mono hl).tendsto
  have hderiv (L : X →L[ℝ] X) (hL : Commute A L) (s : ℝ) :
      HasDerivAt (fun s ↦ exp ((t - s) • A) (L (u s))) (exp ((t - s) • A) (L (g s))) s := by
    refine ((hexp s).clm_apply (L.hasFDerivAt.comp_hasDerivAt s
      ((hu.differentiable one_ne_zero s).hasDerivAt))).congr_deriv ?_
    rw [g_def, map_sub, map_sub, ← mul_apply_eq_comp L A, ← hL.eq, mul_apply_eq_comp, hcA]
    simp only [neg_apply, mul_apply_eq_comp, Function.comp_apply]
    abel
  have hstable : (∫ s in Iic t, exp ((t - s) • A) (P (g s))) = P (u t) := by
    rw [integral_Iic_of_hasDerivAt_of_tendsto' (a := t) (fun s _ ↦ hderiv P hAP s)
      ((hcont P).integrable_of_hasCompactSupport (hsupp P hgs)).integrableOn
      (htendsto P atBot atBot_le_cocompact)]
    simp
  have hunstable : (∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))) = -(u t - P (u t)) := by
    have hL : Commute A (1 - P) := (Commute.one_right A).sub_right hAP
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := t) (fun s _ ↦ hderiv (1 - P) hL s)
      ((hcont (1 - P)).integrable_of_hasCompactSupport (hsupp (1 - P) hgs)).integrableOn
      (htendsto (1 - P) atTop atTop_le_cocompact)
    simpa using h
  rw [greenIntegral_def, hstable, hunstable]
  abel

end ContinuousLinearMap

/-! ### The trajectory operator `d/ds - A` on `W^{1,p}(ℝ, X)` -/

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {A P : E →L[ℝ] E} {K α : ℝ≥0}
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

section Dichotomy

variable (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α)
  (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun _ ↦ -A)
include hs hu hα hAL

/-- **The a priori estimate for `d/ds - A`.** Under an exponential dichotomy for `exp (t A)` with
constant `K` and rate `α > 0`, and `1 ≤ p < ∞`, every `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - A u‖_{Lᵖ}`. The coefficient of the trajectory operator is any `L∞`
class `AL` of the constant `-A`. -/
theorem norm_prev_le_mul_norm_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖prev _ u‖ ≤ 2 * K / α * ‖trajectoryOperator AL u‖ := by
  -- Abstract the base map before introducing `u`, so that the closed set below and the density
  -- statement are stated over the same graph space.
  revert u
  set base := ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
  intro u
  -- The estimate is a closed condition, so it suffices to prove it on smooth compactly supported
  -- paths, where it is the `Lᵖ` bound for the Green integral.
  have hclosed : IsClosed {u : WeakDerivStep volume ⊤ p base |
      ‖prev base u‖ ≤ 2 * K / α * ‖trajectoryOperator AL u‖} :=
    isClosed_le ((prevL base).continuous.congr fun u ↦ prevL_apply base u).norm
      (continuous_const.mul (trajectoryOperator AL).continuous.norm)
  refine hclosed.closure_subset_iff.mpr ?_ (dense_setOf_exists_contDiff_hasCompactSupport hp u)
  rintro u ⟨φ, hφ, hφc, huφ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  set g : ℝ → E := fun s ↦ deriv φ s - A (φ s) with g_def
  have hgc : Continuous g := (hφ1.continuous_deriv le_rfl).sub (A.continuous.comp hφ1.continuous)
  have hgs : HasCompactSupport g := hφc.deriv.sub (hφc.comp_left (map_zero A))
  have hgp : MemLp g p volume := hgc.memLp_of_hasCompactSupport hgs
  have hTu : trajectoryOperator AL u =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g := by
    filter_upwards [trajectoryOperator_apply_ae_eq_deriv_add AL u huφ
      ((hφ1.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      (fun s _ ↦ hφ1.differentiable one_ne_zero s), hAL] with s hs' hAs
    rw [hs', hAs, neg_apply, ← sub_eq_add_neg]
  have hG : ContinuousLinearMap.greenIntegral A P g = φ :=
    funext (ContinuousLinearMap.greenIntegral_deriv_sub_eq hAP hφ1 hφc)
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  have key := ContinuousLinearMap.eLpNorm_greenIntegral_le hs hu hα hgc hM (p := p) Fact.out
  rw [hG] at key
  rw [Set.mem_ofPred_eq, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae huφ, eLpNorm_congr_ae hTu]
  simp only [Opens.coe_top, Measure.restrict_univ]
  calc (eLpNorm φ p volume).toReal
      ≤ (ENNReal.ofReal (2 * K / α) * eLpNorm g p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgp.eLpNorm_ne_top) key
    _ = 2 * K / α * (eLpNorm g p volume).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- **The graph-norm estimate for `d/ds - A`.** Under an exponential dichotomy for `exp (t A)`
with constant `K` and rate `α > 0`, and `1 ≤ p < ∞`, every `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖ ≤ (1 + (1 + ‖AL‖) 2 K / α) ‖u' - A u‖_{Lᵖ}`, where `AL` is the `L∞` class of `-A`. -/
theorem norm_le_mul_norm_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖u‖ ≤ (1 + (1 + ‖AL‖) * (2 * K / α)) * ‖trajectoryOperator AL u‖ := by
  have hprev := norm_prev_le_mul_norm_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP u
  have hweak := norm_weakFDeriv_le_norm_trajectoryOperator_add AL u
  have hsum : ‖u‖ ≤ ‖prev _ u‖ + ‖weakFDeriv _ u‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero).mp ?_
    rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
    nlinarith [norm_nonneg (prev _ u), norm_nonneg (weakFDeriv _ u)]
  have hAL0 := norm_nonneg AL
  calc ‖u‖ ≤ ‖trajectoryOperator AL u‖ + (1 + ‖AL‖) * ‖prev _ u‖ := by linarith
    _ ≤ ‖trajectoryOperator AL u‖ + (1 + ‖AL‖) * (2 * K / α * ‖trajectoryOperator AL u‖) := by
      gcongr
    _ = (1 + (1 + ‖AL‖) * (2 * K / α)) * ‖trajectoryOperator AL u‖ := by ring

/-- **`d/ds - A` is injective.** Under an exponential dichotomy for `exp (t A)` and `1 ≤ p < ∞`,
`u' = A u` has no nonzero solution in `W^{1,p}(ℝ, E)`. -/
theorem injective_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    Function.Injective (trajectoryOperator (p := p) AL) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu0 ↦ norm_le_zero_iff.1 ?_
  simpa [hu0] using norm_le_mul_norm_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP u

/-- **The Green integral is a `W^{1,p}` solution.** Under an exponential dichotomy for
`exp (t A)`, for every continuous compactly supported `f` and `1 ≤ p ≤ ∞`, some
`u ∈ W^{1,p}(ℝ, E)` represented by the Green integral of `f` solves `u' - A u = f`. -/
theorem exists_prev_ae_eq_greenIntegral_and_trajectoryOperator_ae_eq {f : ℝ → E}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ u : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          ContinuousLinearMap.greenIntegral A P f ∧
        ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  set v := ContinuousLinearMap.greenIntegral A P f
  have hv (s : ℝ) : HasDerivAt v (A (v s) + f s) s :=
    ContinuousLinearMap.hasDerivAt_greenIntegral hs hu hα hf hM s
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun s ↦ (hv s).continuousAt
  have hfp : MemLp f p volume := hf.memLp_of_hasCompactSupport hfc
  have hvp : MemLp v p volume :=
    (ContinuousLinearMap.eLpNorm_greenIntegral_le hs hu hα hf hM Fact.out).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp.eLpNorm_lt_top)
  have hvp' : MemLp v p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by simpa using hvp
  have hfp' : MemLp f p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by simpa using hfp
  have hx := hvp'.coeFn_toLp
  have hy := hfp'.coeFn_toLp
  have h : HasWeakLineDerivOn volume ⊤ v (fun s ↦ A (v s) + f s) 1 :=
    hasWeakLineDerivOn_of_hasLineDerivAt ((hvp.locallyIntegrable Fact.out).locallyIntegrableOn _)
      (((A.continuous.comp hvc).add hf).locallyIntegrable.locallyIntegrableOn _)
      fun s _ ↦ by simpa using (hv s).hasFDerivAt.hasLineDerivAt 1
  -- In the form `u' = f - AL u` used by the trajectory operator.
  have hd : (fun s ↦ A (v s) + f s) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hfp'.toLp f s - AL s (hvp'.toLp v s) := by
    filter_upwards [hAL, hx, hy] with s hAs hxs hys
    rw [hAs, hxs, hys, neg_apply, sub_neg_eq_add, add_comm]
  obtain ⟨u, hux, hu'⟩ := exists_prev_eq_and_trajectoryOperator_eq_of_hasWeakLineDerivOn AL
    ((h.congr_ae hx.symm).congr_ae_deriv hd)
  exact ⟨u, by rw [hux]; exact hx, by rw [hu']; exact hy⟩

/-- **`d/ds - A` is surjective.** Under an exponential dichotomy for `exp (t A)` and
`1 ≤ p < ∞`, the equation `u' - A u = f` has a solution `u ∈ W^{1,p}(ℝ, E)` for every
`f ∈ Lᵖ(ℝ, E)`. -/
theorem surjective_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    Function.Surjective (trajectoryOperator (p := p) AL) := by
  set C : ℝ≥0 := ⟨1 + (1 + ‖AL‖) * (2 * K / α), by positivity⟩
  have hanti : AntilipschitzWith C (trajectoryOperator (p := p) AL) :=
    (trajectoryOperator (p := p) AL).antilipschitz_of_bound
      (norm_le_mul_norm_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP)
  have hclosed : IsClosed (range (trajectoryOperator (p := p) AL)) :=
    hanti.isClosed_range (trajectoryOperator (p := p) AL).uniformContinuous
  -- The range contains every smooth compactly supported path, and these are dense in `Lᵖ`.
  have hdense : Dense (range (trajectoryOperator (p := p) AL)) := by
    refine (Lp.dense_hasCompactSupport_contDiff hp).mono ?_
    rintro f ⟨g, hfg, hgc, hg⟩
    obtain ⟨u, -, hTu⟩ := exists_prev_ae_eq_greenIntegral_and_trajectoryOperator_ae_eq
      (p := p) (P := P) hs hu hα hAL hg.continuous hgc
    exact ⟨u, Lp.ext (hTu.trans hfg.symm)⟩
  exact range_eq_univ.mp (hclosed.closure_eq.symm.trans hdense.closure_eq)

/-- **`d/ds - A` is bijective.** Under an exponential dichotomy for `exp (t A)` and
`1 ≤ p < ∞`, the trajectory operator `u ↦ u' - A u` is a bijection from `W^{1,p}(ℝ, E)` onto
`Lᵖ(ℝ, E)`. -/
theorem bijective_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    Function.Bijective (trajectoryOperator (p := p) AL) :=
  ⟨injective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP,
    surjective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP⟩

/-- **`d/ds - A` is Fredholm.** Under an exponential dichotomy for `exp (t A)` and `1 ≤ p < ∞`,
the trajectory operator `u ↦ u' - A u` from `W^{1,p}(ℝ, E)` to `Lᵖ(ℝ, E)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    (trajectoryOperator (p := p) AL).IsFredholm :=
  .of_bijective (bijective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP)

/-- **`d/ds - A` has index zero.** Under an exponential dichotomy for `exp (t A)` and
`1 ≤ p < ∞`, the trajectory operator `u ↦ u' - A u` from `W^{1,p}(ℝ, E)` to `Lᵖ(ℝ, E)` has
Fredholm index zero. -/
theorem index_trajectoryOperator_eq_zero_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    (trajectoryOperator (p := p) AL).index = 0 :=
  ContinuousLinearMap.index_eq_zero_of_bijective _
    (bijective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP)

end Dichotomy

end TauCeti.WeakDerivStep
