/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Sobolev.Wkp.Classical

/-!
# Derivative-form averaged Taylor evaluation on Sobolev spaces

Integrating by parts the cutoff-weighted Taylor polynomial of a Sobolev function `u ∈ W^{m,p}(Ω)`
against a weight `φ : E → ℝ` replaces classical derivatives by weak iterated gradients:

`∑_{j ≤ m} (j!)⁻¹ ∫_{y ∈ Ω} φ y * ⟨D^j u(y), (x - y)^{⊗ j}⟩ dμ`,

where the directional pairing of the weak derivative field is given basis-freely by
`TauCeti.IteratedGradient.fullContractL`. This file defines the resulting recursive integral
expression `TauCeti.Wkp.averagedTaylorEval φ m u x` for general `1 ≤ p ≤ ∞` (which defines a
polynomial in `x` of degree at most `m`, order `m + 1` in Brenner–Scott, when `φ` is measurable,
bounded, and compactly supported) and establishes its analytical properties under cutoff hypotheses
on `φ`:

* when `support φ ⊆ closedBall x R` (`0 ≤ R`) and `‖φ y‖ ≤ M`, the cutoff-weighted contraction
  `φ y * IteratedGradient.fullContractL m (x - y) v` has norm at most `M * R ^ (m + 1) * ‖v‖`
  (`TauCeti.norm_mul_fullContractL_le_of_support_subset_closedBall`), making each weak-derivative
  integrand integrable on `Ω` whenever `φ` is measurable, bounded, and compactly supported;
* `TauCeti.Wkp.averagedTaylorEval` is homogeneous for every weight `φ`, additive when `φ` is
  measurable, bounded, and compactly supported, and invariant under lowering the Sobolev exponent
  (`TauCeti.Wkp.averagedTaylorEval_ofExponentLEL`);
* for a measurable, bounded cutoff `φ` with compact support in `Ω` (`tsupport φ ⊆ Ω`),
  `TauCeti.Wkp.averagedTaylorEval` agrees with the classical averaged Taylor integral
  `∫_{y ∈ Ω} φ y * T^m_y f(x) dμ` on any `C^m` representative `f` of `u`;
* for a measurable, bounded, compactly supported cutoff `φ`, `u ↦ averagedTaylorEval φ m u x` is
  continuous on `W^{m,1}(Ω)` (`TauCeti.Wkp.continuous_averagedTaylorEval_one`).

## Main declarations

* `TauCeti.norm_mul_fullContractL_le_of_support_subset_closedBall`: uniform bound on a
  cutoff-weighted full contraction `φ y * IteratedGradient.fullContractL m (x - y) v` when
  `support φ ⊆ closedBall x R`.
* `TauCeti.Wkp.averagedTaylorEval`: recursive derivative-form integral expression for a Sobolev
  function `u ∈ W^{m,p}(Ω)` at `x` (defining the averaged Taylor polynomial of degree at most `m`
  when `φ` is measurable, bounded, and compactly supported).
* `TauCeti.Wkp.averagedTaylorEval_smul`, `TauCeti.Wkp.averagedTaylorEval_add`: linearity in `u`.
* `TauCeti.Wkp.averagedTaylorEval_ofExponentLEL`: invariance under `TauCeti.Wkp.ofExponentLEL`.
* `TauCeti.Wkp.averagedTaylorEval_eq_setIntegral_sum_iteratedFDeriv`: agreement with the classical
  Taylor sum integral on `C^m` representatives.
* `TauCeti.Wkp.continuous_averagedTaylorEval_one`: continuity of `u ↦ averagedTaylorEval φ m u x`
  on `W^{m,1}(Ω)`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.1, pp. 93–95.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Cutoff-weighted contraction bound -/

section CutoffBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `support φ ⊆ closedBall x R` (`0 ≤ R`) and `‖φ y‖ ≤ M`, then the cutoff-weighted full
contraction `φ y * IteratedGradient.fullContractL m (x - y) v` has norm at most
`M * R ^ (m + 1) * ‖v‖`. -/
theorem norm_mul_fullContractL_le_of_support_subset_closedBall {φ : E → ℝ} {x y : E} {R M : ℝ}
    (hR : 0 ≤ R) (hsupp : Function.support φ ⊆ closedBall x R) (hφ : ‖φ y‖ ≤ M) (m : ℕ)
    (v : IteratedGradient E m) :
    ‖φ y * IteratedGradient.fullContractL m (x - y) v‖ ≤ M * R ^ (m + 1) * ‖v‖ := by
  have hM : 0 ≤ M := (norm_nonneg (φ y)).trans hφ
  by_cases hy : y ∈ Function.support φ
  · have hxy : ‖x - y‖ ≤ R := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact mem_closedBall.1 (hsupp hy)
    rw [norm_mul]
    refine (mul_le_mul hφ
      ((IteratedGradient.norm_fullContractL_apply_le m (x - y) v).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxy (m + 1))
          (norm_nonneg v))) (norm_nonneg _) hM).trans_eq ?_
    ring
  · rw [Function.notMem_support.1 hy, zero_mul, norm_zero]
    positivity

end CutoffBound

/-! ### Recursive averaged Taylor evaluation on `W^{m,p}(Ω)` -/

section AveragedTaylor

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Recursive derivative-form integral expression for a Sobolev function `u ∈ W^{m,p}(Ω)` with
respect to an arbitrary weight `φ : E → ℝ`, evaluated at `x : E`:
`∑_{j ≤ m} (j!)⁻¹ ∫_{y ∈ Ω} φ y * ⟨D^j u(y), (x - y)^{⊗ j}⟩ dμ`.
When `φ` is measurable, bounded, and compactly supported, each integrand is integrable on `Ω` and
`x ↦ averagedTaylorEval φ m u x` defines a polynomial of degree at most `m` (order `m + 1` in
Brenner–Scott), the averaged Taylor polynomial of `u`. -/
def averagedTaylorEval (φ : E → ℝ) : (m : ℕ) → Wkp mu Omega p m → E → ℝ
  | 0, u, _ => ∫ y in Omega, φ y * u y ∂mu
  | m + 1, u, x =>
    averagedTaylorEval φ m (lowerOrder m u) x +
      ((m + 1).factorial : ℝ)⁻¹ *
        ∫ y in Omega, φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu

@[simp]
theorem averagedTaylorEval_zero (φ : E → ℝ) (u : Wkp mu Omega p 0) (x : E) :
    averagedTaylorEval φ 0 u x = ∫ y in Omega, φ y * u y ∂mu :=
  (rfl)

@[simp]
theorem averagedTaylorEval_succ (φ : E → ℝ) (m : ℕ) (u : Wkp mu Omega p (m + 1)) (x : E) :
    averagedTaylorEval φ (m + 1) u x =
      averagedTaylorEval φ m (lowerOrder m u) x +
        ((m + 1).factorial : ℝ)⁻¹ *
          ∫ y in Omega,
            φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu :=
  (rfl)

@[simp]
theorem averagedTaylorEval_zero_weight (m : ℕ) (u : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval (0 : E → ℝ) m u x = 0 := by
  induction m with
  | zero => simp [averagedTaylorEval]
  | succ m ih => simp [averagedTaylorEval_succ, ih]

/-- Scalar multiplication commutes with `averagedTaylorEval` for every `1 ≤ p ≤ ∞`. -/
theorem averagedTaylorEval_smul (φ : E → ℝ) (m : ℕ) (c : ℝ) (u : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval φ m (c • u) x = c * averagedTaylorEval φ m u x := by
  induction m with
  | zero =>
    rw [averagedTaylorEval_zero, averagedTaylorEval_zero, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c u] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  | succ m ih =>
    have htop : (∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m (c • u) y) ∂mu) =
        c * ∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu := by
      rw [← iteratedGradientL_apply m (c • u), map_smul, iteratedGradientL_apply m u,
        ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c (iteratedGradient m u)] with y hy
      rw [hy, Pi.smul_apply, map_smul, smul_eq_mul, mul_left_comm]
    rw [averagedTaylorEval_succ, averagedTaylorEval_succ, ← lowerOrderL_apply m (c • u), map_smul,
      lowerOrderL_apply m u, ih, htop]
    ring

@[simp]
theorem averagedTaylorEval_zero_right (φ : E → ℝ) (m : ℕ) (x : E) :
    averagedTaylorEval φ m (0 : Wkp mu Omega p m) x = 0 := by
  simpa using averagedTaylorEval_smul φ m 0 (0 : Wkp mu Omega p m) x

/-- Compact support and boundedness of `φ` ensure integrability of `φ y * ⟨g y, (x - y)^{⊗ m+1}⟩`
on `Ω` for any `g ∈ Lᵖ(Ω; IteratedGradient E m)` (`1 ≤ p ≤ ∞`). -/
private theorem integrableOn_mul_fullContractL_Lp {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    (g : Lp (IteratedGradient E m) p (mu.restrict Omega)) (x : E) :
    IntegrableOn
      (fun y ↦ φ y * IteratedGradient.fullContractL m (x - y) (g y)) Omega mu := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure (ν.restrict (tsupport φ)) := isFiniteMeasure_restrict.2
    ((Measure.restrict_apply_le _ _).trans_lt hcpt.measure_lt_top).ne
  obtain ⟨R, hR, hR_sub⟩ := hcpt.isBounded.subset_closedBall_lt 0 x
  have hsupp : Function.support φ ⊆ closedBall x R := (subset_tsupport φ).trans hR_sub
  have hg_int : Integrable g (ν.restrict (tsupport φ)) :=
    ((Lp.memLp g).restrict (tsupport φ)).integrable Fact.out
  have hmeas : AEStronglyMeasurable
      (fun y ↦ φ y * IteratedGradient.fullContractL m (x - y) (g y)) (ν.restrict (tsupport φ)) :=
    (hφ_meas.aestronglyMeasurable.mul
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((((IteratedGradient.continuous_fullContractL m).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable).prodMk
          (Lp.aestronglyMeasurable g)))).restrict
  refine (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left φ _).trans (subset_tsupport φ))).1 ?_
  exact (hg_int.norm.const_mul (M * R ^ (m + 1))).mono' hmeas (Eventually.of_forall fun y ↦
    norm_mul_fullContractL_le_of_support_subset_closedBall hR.le hsupp (hφ_bound y) m (g y))

/-- Addition commutes with `averagedTaylorEval` for every `1 ≤ p ≤ ∞` whenever `φ` is measurable,
bounded, and compactly supported. -/
theorem averagedTaylorEval_add {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (u v : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval φ m (u + v) x =
      averagedTaylorEval φ m u x + averagedTaylorEval φ m v x := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure (ν.restrict (tsupport φ)) := isFiniteMeasure_restrict.2
    ((Measure.restrict_apply_le _ _).trans_lt hcpt.measure_lt_top).ne
  induction m with
  | zero =>
    have hint : ∀ w : Wkp mu Omega p 0, Integrable (fun y ↦ φ y * w y) ν := fun w ↦
      (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_left φ w).trans (subset_tsupport φ))).1
        ((((Lp.memLp w).restrict (tsupport φ)).integrable Fact.out).bdd_mul
          hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))
    rw [averagedTaylorEval_zero, averagedTaylorEval_zero, averagedTaylorEval_zero,
      ← integral_add (hint u) (hint v)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u v] with y hy
    rw [hy, Pi.add_apply, mul_add]
  | succ m ih =>
    have htop : (∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m (u + v) y) ∂mu) =
        (∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu) +
        ∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m v y) ∂mu := by
      rw [← iteratedGradientL_apply m (u + v), map_add, iteratedGradientL_apply m u,
        iteratedGradientL_apply m v, ← integral_add
          (integrableOn_mul_fullContractL_Lp hφ_meas hcpt hφ_bound (iteratedGradient m u) x)
          (integrableOn_mul_fullContractL_Lp hφ_meas hcpt hφ_bound (iteratedGradient m v) x)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (iteratedGradient m u) (iteratedGradient m v)] with y hy
      rw [hy, Pi.add_apply, map_add, mul_add]
    rw [averagedTaylorEval_succ, averagedTaylorEval_succ, averagedTaylorEval_succ,
      ← lowerOrderL_apply m (u + v), map_add, lowerOrderL_apply m u, lowerOrderL_apply m v,
      ih (lowerOrder m u) (lowerOrder m v), htop]
    ring

/-- Lowering the Sobolev integrability exponent does not change `averagedTaylorEval`. -/
theorem averagedTaylorEval_ofExponentLEL [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) (φ : E → ℝ) (m : ℕ) (u : Wkp mu Omega q m) (x : E) :
    averagedTaylorEval φ m (ofExponentLEL hpq m u) x = averagedTaylorEval φ m u x := by
  induction m with
  | zero =>
    refine integral_congr_ae ?_
    filter_upwards [value_ofExponentLEL_ae hpq 0 u] with y hy
    simp only [value_zero] at hy
    rw [hy]
  | succ m ih =>
    rw [averagedTaylorEval_succ, averagedTaylorEval_succ, lowerOrder_ofExponentLEL, ih]
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [iteratedGradient_ofExponentLEL_ae hpq m u] with y hy
    rw [hy]

/-- On a `C^m` representative `f` of `u ∈ W^{m,p}(Ω)`, for a measurable, bounded cutoff `φ` with
compact support in `Ω` (`tsupport φ ⊆ Ω`), `averagedTaylorEval φ m u x` agrees with the classical
averaged Taylor integral `∫_{y ∈ Ω} φ y * T^m_y f(x) dμ`. -/
theorem averagedTaylorEval_eq_setIntegral_sum_iteratedFDeriv {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) {M : ℝ}
    (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (u : Wkp mu Omega p m) {f : E → ℝ}
    (hf : ContDiffOn ℝ m f Omega) (hu : (value m u : E → ℝ) =ᵐ[mu.restrict Omega] f) (x : E) :
    averagedTaylorEval φ m u x =
      ∫ y in Omega, φ y * (∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) ∂mu := by
  have hint_on : ∀ ψ : E → ℝ, ContinuousOn ψ Omega → IntegrableOn (fun y ↦ φ y * ψ y) Omega mu :=
    fun ψ hψ ↦ ((integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left φ ψ).trans (subset_tsupport φ))).1
        (((hψ.mono hφ_supp).integrableOn_compact hcpt).bdd_mul
          hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))).integrableOn
  induction m with
  | zero =>
    refine integral_congr_ae ?_
    filter_upwards [hu] with y hy
    simp only [value_zero] at hy
    simp [hy]
  | succ m ih =>
    have hlow : (value m (lowerOrder m u) : E → ℝ) =ᵐ[mu.restrict Omega] f := by
      simpa only [value_succ] using hu
    have hf_m : ContDiffOn ℝ m f Omega := hf.of_le (by simp)
    rw [averagedTaylorEval_succ, ih (lowerOrder m u) hf_m hlow]
    have hgrad_ae := iteratedGradient_ae_eq_of_contDiffOn m u hf hu
    have htop_eq : ((m + 1).factorial : ℝ)⁻¹ *
        (∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu) =
        ∫ y in Omega, φ y * (((m + 1).factorial : ℝ)⁻¹ *
          iteratedFDeriv ℝ (m + 1) f y (fun _ ↦ x - y)) ∂mu := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hgrad_ae] with y hy
      rw [hy, fullContractL_iteratedGradientChain]
      ring
    have hsum_cont : ContinuousOn (fun y ↦ ∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) Omega := by
      simpa only [smul_eq_mul] using continuousOn_sum_iteratedFDeriv Omega.isOpen hf_m x
    have htop_cont : ContinuousOn (fun y ↦ ((m + 1).factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (m + 1) f y (fun _ ↦ x - y)) Omega :=
      continuousOn_const.mul (continuous_eval.comp_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv (k := m + 1) hf Omega.isOpen (by simp)).prodMk
          (continuous_pi fun _ ↦ continuous_const.sub continuous_id).continuousOn))
    rw [htop_eq, ← integral_add (hint_on _ hsum_cont) (hint_on _ htop_cont)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [Finset.sum_range_succ _ (m + 1), mul_add]

/-- Operator-norm bound on `W^{m,1}(Ω)` for `u ↦ averagedTaylorEval φ m u x` when `φ` is measurable,
bounded, and compactly supported. -/
private theorem exists_norm_averagedTaylorEval_one_le {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    ∃ C : ℝ, ∀ u : Wkp mu Omega 1 m, ‖averagedTaylorEval φ m u x‖ ≤ C * ‖u‖ := by
  let ν : Measure E := mu.restrict Omega
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hφ_bound 0)
  induction m with
  | zero =>
    refine ⟨M, fun u ↦ (norm_integral_le_integral_norm _).trans ?_⟩
    have hint : Integrable (fun y ↦ φ y * u y) ν := (L1.integrable_coeFn u).bdd_mul
      hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound)
    refine (integral_mono hint.norm ((L1.integrable_coeFn u).norm.const_mul M)
      fun y ↦ ?_).trans_eq (by rw [integral_const_mul, L1.norm_eq_integral_norm])
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hφ_bound y) (norm_nonneg _)
  | succ m ih =>
    obtain ⟨C₀, hC₀⟩ := ih
    obtain ⟨R, hR, hR_sub⟩ := hcpt.isBounded.subset_closedBall_lt 0 x
    have hsupp : Function.support φ ⊆ closedBall x R := (subset_tsupport φ).trans hR_sub
    set A := max C₀ 0
    set B := M * R ^ (m + 1)
    let L_low := lowerOrderL (mu := mu) (Omega := Omega) (p := 1) m
    let L_grad := iteratedGradientL (mu := mu) (Omega := Omega) (p := 1) m
    refine ⟨A * ‖L_low‖ + ((m + 1).factorial : ℝ)⁻¹ * (B * ‖L_grad‖), fun u ↦ ?_⟩
    have hlow_le : ‖averagedTaylorEval φ m (lowerOrder m u) x‖ ≤ A * (‖L_low‖ * ‖u‖) :=
      (hC₀ _).trans <| (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _)).trans <| by
        rw [← lowerOrderL_apply]
        exact mul_le_mul_of_nonneg_left (L_low.le_opNorm u) (le_max_right C₀ 0)
    have htop_le : ‖∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu‖ ≤
        B * (‖L_grad‖ * ‖u‖) :=
      (norm_integral_le_integral_norm _).trans <| (integral_mono
        (integrableOn_mul_fullContractL_Lp hφ_meas hcpt hφ_bound (iteratedGradient m u) x).norm
        ((L1.integrable_coeFn (iteratedGradient m u)).norm.const_mul B) fun y ↦
          norm_mul_fullContractL_le_of_support_subset_closedBall hR.le hsupp (hφ_bound y) m
            (iteratedGradient m u y)).trans
        (by rw [integral_const_mul, ← L1.norm_eq_integral_norm, ← iteratedGradientL_apply]
            exact mul_le_mul_of_nonneg_left (L_grad.le_opNorm u) (by positivity))
    rw [averagedTaylorEval_succ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    exact (add_le_add hlow_le
      (mul_le_mul_of_nonneg_left htop_le (by positivity))).trans_eq (by ring)

/-- For a bounded measurable cutoff `φ` with compact support, `u ↦ averagedTaylorEval φ m u x` is
continuous on `W^{m,1}(Ω)`. -/
theorem continuous_averagedTaylorEval_one {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    Continuous fun u : Wkp mu Omega 1 m ↦ averagedTaylorEval φ m u x := by
  obtain ⟨C, hC⟩ := exists_norm_averagedTaylorEval_one_le (mu := mu) (Omega := Omega)
    hφ_meas hcpt hφ_bound m x
  exact (LinearMap.mkContinuous
    ({ toFun := fun u ↦ averagedTaylorEval φ m u x
       map_add' := fun u v ↦ averagedTaylorEval_add hφ_meas hcpt hφ_bound m u v x
       map_smul' := fun c u ↦ averagedTaylorEval_smul φ m c u x } :
      Wkp mu Omega 1 m →ₗ[ℝ] ℝ) C hC).continuous

end Wkp

end AveragedTaylor

end TauCeti
