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
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Derivative-form averaged Taylor evaluation on Sobolev spaces

Replacing the classical derivatives in the cutoff-weighted Taylor polynomial of a Sobolev function
`u ∈ W^{m,p}(Ω)` against a weight `φ : E → ℝ` by weak iterated gradients gives the derivative-form
expression

`∑_{j ≤ m} (j!)⁻¹ ∫_{y ∈ Ω} φ y * ⟨D^j u(y), (x - y)^{⊗ j}⟩ dμ`,

where the directional pairing of the weak derivative field is given basis-freely by
`TauCeti.IteratedGradient.fullContractL`. This file defines the resulting recursive integral
expression `TauCeti.Wkp.averagedTaylorEval φ m u x` for general `1 ≤ p ≤ ∞` (which defines a
polynomial in `x` of degree at most `m`, order `m + 1` in Brenner–Scott, when `φ` is measurable,
bounded, and compactly supported), bundles it as a continuous linear functional
`TauCeti.Wkp.averagedTaylorEvalL`, and establishes its analytical properties under cutoff hypotheses
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
* when `support φ ⊆ closedBall x R` and `‖φ y‖ ≤ M`, `TauCeti.Wkp.averagedTaylorEval φ m u x`
  satisfies an explicit operator-norm bound on `W^{m,p}(Ω)` for every `1 ≤ p ≤ ∞`
  (`TauCeti.Wkp.norm_averagedTaylorEval_le_of_support_subset_closedBall`), yielding the bundled
  continuous linear functional `TauCeti.Wkp.averagedTaylorEvalL` and continuity
  `TauCeti.Wkp.continuous_averagedTaylorEval`.

## Main declarations

* `TauCeti.norm_mul_fullContractL_le_of_support_subset_closedBall`: uniform bound on a
  cutoff-weighted full contraction `φ y * IteratedGradient.fullContractL m (x - y) v` when
  `support φ ⊆ closedBall x R`.
* `TauCeti.integrable_mul_sum_iteratedFDeriv`: integrability of a cutoff-weighted classical Taylor
  sum for `f ∈ C^m(Ω)` when `tsupport φ ⊆ Ω` is compact.
* `TauCeti.Wkp.averagedTaylorEval`, `TauCeti.Wkp.averagedTaylorEvalL`: recursive derivative-form
  integral expression for `u ∈ W^{m,p}(Ω)` at `x` and its bundled continuous linear functional
  `Wkp mu Omega p m →L[ℝ] ℝ`.
* `TauCeti.Wkp.averagedTaylorEval_smul`, `TauCeti.Wkp.averagedTaylorEval_add`: linearity in `u`.
* `TauCeti.Wkp.averagedTaylorEval_ofExponentLEL`: invariance under `TauCeti.Wkp.ofExponentLEL`.
* `TauCeti.Wkp.averagedTaylorEval_eq_setIntegral_sum_iteratedFDeriv`: agreement with the classical
  Taylor sum integral on `C^m` representatives.
* `TauCeti.Wkp.norm_averagedTaylorEval_le_of_support_subset_closedBall`,
  `TauCeti.Wkp.norm_averagedTaylorEvalL_le_of_support_subset_closedBall`,
  `TauCeti.Wkp.exists_norm_averagedTaylorEval_le`, `TauCeti.Wkp.continuous_averagedTaylorEval`:
  explicit and existential operator-norm bounds and continuity on `W^{m,p}(Ω)` (`1 ≤ p ≤ ∞`).

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.1, pp. 93–95.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Cutoff-weighted contraction and Taylor-sum integrability -/

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

private theorem integrable_mul_of_continuousOn {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [T2Space X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Ω : Set X}
    {φ ψ : X → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Ω)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hψ : ContinuousOn ψ Ω) :
    Integrable (fun y ↦ φ y * ψ y) μ :=
  (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left φ ψ).trans (subset_tsupport φ))).1
    (((hψ.mono hφ_supp).integrableOn_compact hcpt).bdd_mul
      hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))

/-- For a `C^m` function `f` on an open set `Ω` and a bounded measurable cutoff `φ` with compact
support contained in `Ω`, the cutoff-weighted classical Taylor sum at `x` is integrable. -/
theorem integrable_mul_sum_iteratedFDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [OpensMeasurableSpace F] {μ : Measure F} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set F} (hΩ : IsOpen Ω) {φ : F → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ Ω) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {f : F → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m f Ω) (x : F) :
    Integrable (fun y ↦ φ y * ∑ j ∈ Finset.range (m + 1),
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) μ :=
  integrable_mul_of_continuousOn hφ_meas hcpt hφ_supp hφ_bound
    (by simpa only [smul_eq_mul] using continuousOn_sum_iteratedFDeriv hΩ hf x)

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem integrableOn_of_support_subset_tsupport_Lp {F : Type*} [NormedAddCommGroup F]
    {φ : E → ℝ} (hcpt : HasCompactSupport φ) (g : Lp F p (mu.restrict Omega)) {h : E → ℝ}
    (hh_meas : AEStronglyMeasurable h (mu.restrict Omega))
    (hh_supp : Function.support h ⊆ tsupport φ) {K : ℝ} (hh_le : ∀ y, ‖h y‖ ≤ K * ‖g y‖) :
    IntegrableOn h Omega mu := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure (ν.restrict (tsupport φ)) := isFiniteMeasure_restrict.2
    ((Measure.restrict_apply_le _ _).trans_lt hcpt.measure_lt_top).ne
  refine (integrableOn_iff_integrable_of_support_subset hh_supp).1 ?_
  exact ((((Lp.memLp g).restrict (tsupport φ)).integrable Fact.out).norm.const_mul K).mono'
    hh_meas.restrict (Eventually.of_forall hh_le)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem norm_setIntegral_le_of_support_subset_tsupport_Lp {F : Type*}
    [NormedAddCommGroup F] {φ : E → ℝ} (hcpt : HasCompactSupport φ)
    (g : Lp F p (mu.restrict Omega)) {h : E → ℝ} (hh_supp : Function.support h ⊆ tsupport φ)
    {K : ℝ} (hK : 0 ≤ K) (hh_le : ∀ y, ‖h y‖ ≤ K * ‖g y‖) :
    ‖∫ y in Omega, h y ∂mu‖ ≤
      K * ((mu.restrict Omega) (tsupport φ) ^ (1 - 1 / p.toReal)).toReal * ‖g‖ := by
  let ν : Measure E := mu.restrict Omega
  let S : Set E := tsupport φ
  have : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2
    ((Measure.restrict_apply_le _ _).trans_lt hcpt.measure_lt_top).ne
  have hgS : MemLp g p (ν.restrict S) := (Lp.memLp g).restrict S
  have hnorm_le : ‖hgS.toLp g‖ ≤ ‖g‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
      (eLpNorm_mono_measure g Measure.restrict_le_self)
  have hsub : ∫ y, h y ∂ν = ∫ y in S, h y ∂ν :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      Function.notMem_support.1 fun hmem ↦ hy (hh_supp hmem)).symm
  rw [hsub]
  refine (Lp.norm_integral_le_of_ae_norm_le_mul (K := K) (hgS.toLp g) ?_).trans ?_
  · filter_upwards [hgS.coeFn_toLp] with y hy
    rw [hy]
    exact hh_le y
  · rw [Measure.restrict_apply_univ]
    exact mul_le_mul_of_nonneg_left hnorm_le (mul_nonneg hK ENNReal.toReal_nonneg)

/-- Compact support and boundedness of `φ` ensure integrability of `φ y * ⟨g y, (x - y)^{⊗ m+1}⟩`
on `Ω` for any `g ∈ Lᵖ(Ω; IteratedGradient E m)` (`1 ≤ p ≤ ∞`). -/
private theorem integrableOn_mul_fullContractL_Lp {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    (g : Lp (IteratedGradient E m) p (mu.restrict Omega)) (x : E) :
    IntegrableOn
      (fun y ↦ φ y * IteratedGradient.fullContractL m (x - y) (g y)) Omega mu := by
  obtain ⟨R, hR, hR_sub⟩ := hcpt.isBounded.subset_closedBall_lt 0 x
  have hsupp : Function.support φ ⊆ closedBall x R := (subset_tsupport φ).trans hR_sub
  refine integrableOn_of_support_subset_tsupport_Lp hcpt g ?_
    ((Function.support_mul_subset_left φ _).trans (subset_tsupport φ)) fun y ↦
      norm_mul_fullContractL_le_of_support_subset_closedBall hR.le hsupp (hφ_bound y) m (g y)
  exact hφ_meas.aestronglyMeasurable.mul
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((((IteratedGradient.continuous_fullContractL m).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable).prodMk
        (Lp.aestronglyMeasurable g)))

/-- Addition commutes with `averagedTaylorEval` for every `1 ≤ p ≤ ∞` whenever `φ` is measurable,
bounded, and compactly supported. -/
theorem averagedTaylorEval_add {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (u v : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval φ m (u + v) x =
      averagedTaylorEval φ m u x + averagedTaylorEval φ m v x := by
  induction m with
  | zero =>
    have hint : ∀ w : Wkp mu Omega p 0, IntegrableOn (fun y ↦ φ y * w y) Omega mu := fun w ↦
      integrableOn_of_support_subset_tsupport_Lp hcpt w
        (hφ_meas.aestronglyMeasurable.mul (Lp.aestronglyMeasurable w))
        ((Function.support_mul_subset_left φ w).trans (subset_tsupport φ)) fun y ↦ by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hφ_bound y) (norm_nonneg _)
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
    have hsum_m : IntegrableOn (fun y ↦ φ y * ∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) Omega mu :=
      (integrable_mul_sum_iteratedFDeriv Omega.isOpen hφ_meas hcpt hφ_supp hφ_bound hf_m
        x).integrableOn
    have hsum_m1 : IntegrableOn (fun y ↦ φ y * ∑ j ∈ Finset.range (m + 1 + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) Omega mu :=
      (integrable_mul_sum_iteratedFDeriv Omega.isOpen hφ_meas hcpt hφ_supp hφ_bound hf
        x).integrableOn
    have htop_int : IntegrableOn (fun y ↦ φ y * (((m + 1).factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (m + 1) f y (fun _ ↦ x - y))) Omega mu :=
      (hsum_m1.sub hsum_m).congr_fun
        (fun y _ ↦ by rw [Pi.sub_apply, Finset.sum_range_succ _ (m + 1), mul_add,
          add_sub_cancel_left])
        Omega.isOpen.measurableSet
    rw [htop_eq, ← integral_add hsum_m htop_int]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [Finset.sum_range_succ _ (m + 1), mul_add]

/-- Quantitative bound on `W^{m,p}(Ω)` (`1 ≤ p ≤ ∞`) for `averagedTaylorEval φ m u x` when
`support φ ⊆ closedBall x R` (`0 ≤ R`) and `‖φ y‖ ≤ M`, without measurability assumptions on `φ`
or boundedness of `Ω`. -/
theorem norm_averagedTaylorEval_le_of_support_subset_closedBall {φ : E → ℝ} {x : E} {R M : ℝ}
    (hR : 0 ≤ R) (hsupp : Function.support φ ⊆ closedBall x R) (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    (m : ℕ) (u : Wkp mu Omega p m) :
    ‖averagedTaylorEval φ m u x‖ ≤
      M * ((mu.restrict Omega) (tsupport φ) ^ (1 - 1 / p.toReal)).toReal *
        (∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ * R ^ j) * ‖u‖ := by
  have hcpt : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x R) hsupp
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hφ_bound 0)
  set c := ((mu.restrict Omega) (tsupport φ) ^ (1 - 1 / p.toReal)).toReal
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  induction m with
  | zero =>
    rw [averagedTaylorEval_zero, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
      pow_zero, mul_one, mul_one]
    exact norm_setIntegral_le_of_support_subset_tsupport_Lp hcpt u
      ((Function.support_mul_subset_left φ u).trans (subset_tsupport φ)) hM0 fun y ↦ by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hφ_bound y) (norm_nonneg _)
  | succ m ih =>
    have hlow : ‖averagedTaylorEval φ m (lowerOrder m u) x‖ ≤
        M * c * (∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ * R ^ j) * ‖u‖ :=
      (ih (lowerOrder m u)).trans (mul_le_mul_of_nonneg_left (norm_lowerOrder_le m u)
        (mul_nonneg (mul_nonneg hM0 hc0) (Finset.sum_nonneg fun _ _ ↦ by positivity)))
    have htop : ‖∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu‖ ≤
        M * R ^ (m + 1) * c * ‖u‖ :=
      (norm_setIntegral_le_of_support_subset_tsupport_Lp hcpt (iteratedGradient m u)
        ((Function.support_mul_subset_left φ _).trans (subset_tsupport φ)) (by positivity)
        fun y ↦ norm_mul_fullContractL_le_of_support_subset_closedBall hR hsupp (hφ_bound y) m
          (iteratedGradient m u y)).trans
        (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le m u) (by positivity))
    rw [averagedTaylorEval_succ, Finset.sum_range_succ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    exact (add_le_add hlow
      (mul_le_mul_of_nonneg_left htop (by positivity))).trans_eq (by ring)

/-- Operator-norm bound on `W^{m,p}(Ω)` (`1 ≤ p ≤ ∞`) for `u ↦ averagedTaylorEval φ m u x` when `φ`
is bounded and compactly supported. -/
theorem exists_norm_averagedTaylorEval_le {φ : E → ℝ} (hcpt : HasCompactSupport φ) {M : ℝ}
    (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    ∃ C : ℝ, ∀ u : Wkp mu Omega p m, ‖averagedTaylorEval φ m u x‖ ≤ C * ‖u‖ := by
  obtain ⟨R, hR, hR_sub⟩ := hcpt.isBounded.subset_closedBall_lt 0 x
  exact ⟨_, norm_averagedTaylorEval_le_of_support_subset_closedBall hR.le
    ((subset_tsupport φ).trans hR_sub) hφ_bound m⟩

/-- Bundled continuous linear functional `u ↦ averagedTaylorEval φ m u x` on `W^{m,p}(Ω)`
(`1 ≤ p ≤ ∞`) for a measurable, bounded, compactly supported cutoff `φ`. -/
def averagedTaylorEvalL {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    Wkp mu Omega p m →L[ℝ] ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u ↦ averagedTaylorEval φ m u x
      map_add' := fun u v ↦ averagedTaylorEval_add hφ_meas hcpt hφ_bound m u v x
      map_smul' := fun c u ↦ averagedTaylorEval_smul φ m c u x }
    (exists_norm_averagedTaylorEval_le hcpt hφ_bound m x)

@[simp]
theorem averagedTaylorEvalL_apply {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E)
    (u : Wkp mu Omega p m) :
    averagedTaylorEvalL hφ_meas hcpt hφ_bound m x u = averagedTaylorEval φ m u x :=
  (rfl)

/-- Explicit operator-norm bound for `averagedTaylorEvalL` when `support φ ⊆ closedBall x R`. -/
theorem norm_averagedTaylorEvalL_le_of_support_subset_closedBall {φ : E → ℝ}
    (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ) {x : E} {R M : ℝ} (hR : 0 ≤ R)
    (hsupp : Function.support φ ⊆ closedBall x R) (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) :
    ‖averagedTaylorEvalL (mu := mu) (Omega := Omega) (p := p) hφ_meas hcpt hφ_bound m x‖ ≤
      M * ((mu.restrict Omega) (tsupport φ) ^ (1 - 1 / p.toReal)).toReal *
        (∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ * R ^ j) := by
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hφ_bound 0)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hM0 ENNReal.toReal_nonneg)
      (Finset.sum_nonneg fun _ _ ↦ by positivity)) fun u ↦ ?_
  exact norm_averagedTaylorEval_le_of_support_subset_closedBall hR hsupp hφ_bound m u

/-- For a bounded measurable cutoff `φ` with compact support, `u ↦ averagedTaylorEval φ m u x` is
continuous on `W^{m,p}(Ω)` (`1 ≤ p ≤ ∞`). -/
theorem continuous_averagedTaylorEval {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    Continuous fun u : Wkp mu Omega p m ↦ averagedTaylorEval φ m u x :=
  (averagedTaylorEvalL hφ_meas hcpt hφ_bound m x).continuous

end Wkp

end AveragedTaylor

end TauCeti
