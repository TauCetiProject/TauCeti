/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.Sobolev.Poincare.W1p0
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Comparison and uniqueness for quasilinear divergence-form equations

On an open set `Ω ⊆ ℝⁿ` consider the quasilinear divergence-form operator

`Q u = -∂ᵢ(Aⁱʲ(x, u) ∂ⱼu)`,

whose coefficient matrix depends on the solution itself. Its weak form against a test function
`φ` is the energy form of the linear operator with the frozen coefficient `a(x) = A(x, u(x))`,

`Q(u, φ) = ∫_Ω ⟨A(x, u) ∇u, ∇φ⟩`,

which is `TauCeti.PDE.energyFormH1 (fun x ↦ A x (u x)) 0 0 u φ`. Suppose that `A(·, s)` is
uniformly elliptic with constants `λ, Λ` for every `s`, and that `A` is Lipschitz in its second
variable, uniformly in `x`:

`|ηᵀ (A(x, s) - A(x, t)) ξ| ≤ L |s - t| ‖η‖ ‖ξ‖`.

No continuity in `x` is assumed. If `Ω` carries a Poincaré inequality on `W^{1,2}_0(Ω)`, for
instance when `Ω` is bounded, this file proves the **comparison principle**
(`TauCeti.PDE.value_le_of_energyFormH1_quasilinear_le`): if `u` is a weak subsolution and `v` a
weak supersolution of the same equation, in the sense that `Q(u, φ) ≤ Q(v, φ)` for every
nonnegative `φ ∈ W^{1,2}_0(Ω)`, and `u ≤ v` on `∂Ω` in the sense that `(u - v)⁺ ∈ W^{1,2}_0(Ω)`,
then `u ≤ v` almost everywhere. In particular the weak Dirichlet problem `Q u = ℓ`, `u = g` on
`∂Ω`, has at most one solution in `W^{1,2}(Ω)`
(`TauCeti.PDE.eq_of_forall_energyFormH1_quasilinear_eq`), whatever the right-hand side `ℓ`, and
this applies to every bounded open `Ω ⊆ ℝⁿ⁺¹`
(`TauCeti.PDE.eq_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`).

The operator is not monotone in general, so testing with `u - v` does not work. The Lipschitz
dependence on `u` is used only at small values of `u - v`, through truncation.

## The argument

This is the truncation argument of Chipot and Michaille. Let `w = u - v`, fix `ε > 0`, and test
with the truncation `φ_ε = min(w⁺, ε) = w⁺ - (w - ε)⁺`, which lies in `W^{1,2}_0(Ω)`, is
nonnegative, and has gradient `1_{S_ε} ∇w` on `S_ε = {0 < w ≤ ε}`. Writing
`A(u) ∇u - A(v) ∇v = A(u) ∇w + (A(u) - A(v)) ∇v` and using `|A(u) - A(v)| ≤ L w ≤ L ε` on `S_ε`,

`λ ∫_{S_ε} |∇w|² ≤ ∫_{S_ε} ⟨A(u) ∇w, ∇w⟩ ≤ L ε ∫_{S_ε} |∇v| |∇w|`,

so that `‖∇φ_ε‖₂ ≤ (L ε / λ) ‖∇v‖_{L²(S_ε)}`. By the Poincaré inequality the same bound, with the
factor `P`, holds for `‖φ_ε‖₂`. For `ε ≤ δ`, `φ_ε = ε` on `{w > δ}`, so dividing by `ε`,

`|{w > δ}|^{1/2} ≤ (P L / λ) ‖∇v‖_{L²(S_ε)}`.

As `ε → 0` the sets `S_ε` decrease to the empty set, so the right-hand side tends to `0`. Hence
`{w > δ}` is null for every `δ > 0`, and `w ≤ 0` almost everywhere. The factor `ε` gained from the
Lipschitz bound exactly compensates the division by `ε`.

## Main declarations

* `TauCeti.PDE.value_le_of_energyFormH1_quasilinear_le`: the comparison principle.
* `TauCeti.PDE.eq_of_forall_energyFormH1_quasilinear_eq`: uniqueness for the Dirichlet problem.
* `TauCeti.PDE.eq_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`: uniqueness on a bounded
  domain.

## References

* M. Chipot and G. Michaille, *Uniqueness results and monotonicity properties for strongly
  nonlinear elliptic variational inequalities*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **16**
  (1989), 137–166.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped Matrix

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

/-! ### Truncation between the levels `0` and `ε` -/

/-- The truncation `min(w⁺, ε) = w⁺ - (w - ε)⁺` of a Sobolev function between the levels `0`
and `ε`. -/
private def truncation {ε : ℝ} (hε : 0 ≤ ε) (w : W1p mu Omega 2) : W1p mu Omega 2 :=
  W1p.posPart (by norm_num) w - W1p.posPartAbove (by norm_num) hε w

/-- The set `{0 < w ≤ ε}` on which the truncation has nonzero gradient is measurable. -/
private theorem measurableSet_truncationSet (w : W1p mu Omega 2) (ε : ℝ) :
    MeasurableSet {x | 0 < W1p.value w x ∧ W1p.value w x ≤ ε} := by
  have hmeas := (Lp.stronglyMeasurable (W1p.value w)).measurable
  simpa only [ofPred_and] using
    (measurableSet_lt measurable_const hmeas).inter (measurableSet_le hmeas measurable_const)

/-- The truncation of a function whose positive part has zero boundary values has zero boundary
values. -/
private theorem truncation_mem_w1p0Submodule {ε : ℝ} (hε : 0 ≤ ε) {w : W1p mu Omega 2}
    (hw : W1p.posPart (by norm_num) w ∈ w1p0Submodule mu Omega 2) :
    truncation hε w ∈ w1p0Submodule mu Omega 2 := by
  have h0 : W1p.posPartAbove (by norm_num) (le_refl (0 : ℝ)) w ∈ w1p0Submodule mu Omega 2 := by
    rwa [W1p.posPartAbove_zero]
  exact Submodule.sub_mem _ hw
    (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) (le_refl 0) hε h0)

/-- The value of the truncation is `w⁺ - (w - ε)⁺` almost everywhere. -/
private theorem value_truncation_ae {ε : ℝ} (hε : 0 ≤ ε) (w : W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (truncation hε w) x =
      max (W1p.value w x) 0 - max (W1p.value w x - ε) 0 := by
  filter_upwards [W1p.value_sub_ae (W1p.posPart (by norm_num) w)
      (W1p.posPartAbove (by norm_num) hε w), Lp.coeFn_posPart (W1p.value w),
    W1p.value_posPartAbove_ae (by norm_num) hε w] with x h₁ h₂ h₃
  rw [truncation, h₁, Pi.sub_apply, W1p.value_posPart, h₂, h₃]

/-- The weak gradient of the truncation is `1_{0 < w ≤ ε} ∇w` almost everywhere. -/
private theorem gradient_truncation_ae {ε : ℝ} (hε : 0 ≤ ε) (w : W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.gradient (truncation hε w) x =
      {x | 0 < W1p.value w x ∧ W1p.value w x ≤ ε}.indicator (W1p.gradient w) x := by
  filter_upwards [Lp.coeFn_sub (W1p.gradient (W1p.posPart (by norm_num) w))
      (W1p.gradient (W1p.posPartAbove (by norm_num) hε w)),
    W1p.gradient_posPart_ae (by norm_num) w,
    W1p.gradient_posPartAbove_ae (by norm_num) hε w] with x h₁ h₂ h₃
  rw [truncation, W1p.gradient_sub, h₁, Pi.sub_apply, h₂, h₃]
  by_cases h0 : 0 < W1p.value w x
  · by_cases hεx : ε < W1p.value w x
    · simp [indicator, h0, hεx, not_le.2 hεx]
    · simp [indicator, h0, hεx, le_of_not_gt hεx]
  · have hεx : ¬ε < W1p.value w x := fun h ↦ h0 (hε.trans_lt h)
    simp [indicator, h0, hεx]

/-- The truncation is nonnegative. -/
private theorem value_truncation_nonneg_ae {ε : ℝ} (hε : 0 ≤ ε) (w : W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (truncation hε w) x := by
  filter_upwards [value_truncation_ae hε w] with x hx
  rw [hx, sub_nonneg]
  exact max_le_max (by linarith) le_rfl

/-! ### The truncation argument -/

/-- **The level-set bound.** If `w⁺ ∈ W^{1,2}_0(Ω)`, `Ω` carries a Poincaré inequality with
constant `P`, and the truncation `φ_ε = min(w⁺, ε)` satisfies
`‖∇φ_ε‖² ≤ (K ε)² ∫_{0 < w ≤ ε} g`, then for every `δ ≥ ε` the measure of `{w > δ}` is at most
`(P K)² ∫_{0 < w ≤ ε} g`: on `{w > δ}` the truncation equals `ε`, and the factor `ε²` cancels. -/
private theorem measureReal_lt_value_le_of_norm_gradient_truncation_sq_le {P K δ ε : ℝ}
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤ P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    {w : W1p mu Omega 2} (hw : W1p.posPart (by norm_num) w ∈ w1p0Submodule mu Omega 2)
    {g : EuclideanSpace ℝ ι → ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hbound : ‖W1p.gradient (truncation hε.le w)‖ ^ 2 ≤
      (K * ε) ^ 2 * ∫ x in {x | 0 < W1p.value w x ∧ W1p.value w x ≤ ε}, g x ∂mu.restrict Omega) :
    (mu.restrict Omega).real {x | δ < W1p.value w x} ≤
      (P * K) ^ 2 * ∫ x in {x | 0 < W1p.value w x ∧ W1p.value w x ≤ ε}, g x ∂mu.restrict Omega := by
  set φ := truncation hε.le w
  have hT : MeasurableSet {x | δ < W1p.value w x} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value w)).measurable
  have hval : (mu.restrict Omega).real {x | δ < W1p.value w x} * ε ^ 2 ≤ ‖W1p.value φ‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq, ← smul_eq_mul, ← setIntegral_const]
    calc ∫ _ in {x | δ < W1p.value w x}, ε ^ 2 ∂mu.restrict Omega
        = ∫ x in {x | δ < W1p.value w x}, ‖W1p.value φ x‖ ^ 2 ∂mu.restrict Omega := by
          refine setIntegral_congr_ae hT ?_
          filter_upwards [value_truncation_ae hε.le w] with x hx hxT
          have hδx : δ < W1p.value w x := hxT
          rw [hx, max_eq_left (by linarith [hδx]), max_eq_left (by linarith [hδx]),
            Real.norm_eq_abs, sq_abs]
          ring
      _ ≤ _ := setIntegral_le_integral (Lp.integrable_sq_norm _)
          (Eventually.of_forall fun _ ↦ sq_nonneg _)
  have hP : ‖W1p.value φ‖ ^ 2 ≤ P ^ 2 * ‖W1p.gradient φ‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpoincare ⟨φ, truncation_mem_w1p0Submodule hε.le hw⟩) 2
  set I := ∫ x in {x | 0 < W1p.value w x ∧ W1p.value w x ≤ ε}, g x ∂mu.restrict Omega
  have := (hval.trans hP).trans (mul_le_mul_of_nonneg_left hbound (sq_nonneg P))
  rw [show P ^ 2 * ((K * ε) ^ 2 * I) = (P * K) ^ 2 * I * ε ^ 2 by ring] at this
  exact le_of_mul_le_mul_right this (by positivity)

/-- The integrals of an integrable `g` over the sets `{0 < w ≤ δ / (k + 1)}` tend to `0`: the sets
decrease to the empty set. -/
private theorem tendsto_setIntegral_truncationSet (w : W1p mu Omega 2)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : Integrable g (mu.restrict Omega)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ ↦ ∫ x in {x | 0 < W1p.value w x ∧ W1p.value w x ≤ δ / (k + 1)}, g x
      ∂mu.restrict Omega) atTop (𝓝 0) := by
  set S : ℕ → Set (EuclideanSpace ℝ ι) :=
    fun k ↦ {x | 0 < W1p.value w x ∧ W1p.value w x ≤ δ / (k + 1)}
  have hanti : Antitone S := fun k l hkl x hx ↦
    ⟨hx.1, hx.2.trans (div_le_div_of_nonneg_left hδ.le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hkl))⟩
  have hempty : ⋂ k, S k = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (mem_iInter.1 hx 0).1 hδ)
    have h := (mem_iInter.1 hx k).2
    rw [div_lt_div_iff₀ (by positivity) hδ] at hk
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have := tendsto_setIntegral_of_antitone (μ := mu.restrict Omega) (f := g) (s := S)
    (fun k ↦ measurableSet_truncationSet w _) hanti ⟨0, hg.integrableOn⟩
  rwa [hempty, Measure.restrict_empty, integral_zero_measure] at this

/-- **The truncation argument.** Let `w ∈ W^{1,2}(Ω)` have `w⁺ ∈ W^{1,2}_0(Ω)`, let `Ω` carry a
Poincaré inequality with constant `P`, and let `g` be integrable. If for every `ε > 0` the
truncation `φ_ε = min(w⁺, ε)` satisfies `‖∇φ_ε‖² ≤ (K ε)² ∫_{0 < w ≤ ε} g`, then `w ≤ 0` almost
everywhere. -/
private theorem value_nonpos_of_norm_gradient_truncation_sq_le {P K : ℝ}
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤ P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    {w : W1p mu Omega 2} (hw : W1p.posPart (by norm_num) w ∈ w1p0Submodule mu Omega 2)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : Integrable g (mu.restrict Omega))
    (hbound : ∀ ε (hε : 0 < ε), ‖W1p.gradient (truncation hε.le w)‖ ^ 2 ≤
      (K * ε) ^ 2 * ∫ x in {x | 0 < W1p.value w x ∧ W1p.value w x ≤ ε}, g x ∂mu.restrict Omega) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value w x ≤ 0 := by
  -- `{w > δ}` is null for every `δ > 0`: its measure is at most `(P K)² ∫_{0 < w ≤ ε} g` for every
  -- `ε ≤ δ`, and this tends to `0` with `ε`. It has finite measure, since `w ∈ L²`.
  have hnull {δ : ℝ} (hδ : 0 < δ) : mu.restrict Omega {x | δ < W1p.value w x} = 0 := by
    have hreal : (mu.restrict Omega).real {x | δ < W1p.value w x} ≤ 0 := by
      refine le_of_tendsto_of_tendsto' tendsto_const_nhds
        (by simpa using (tendsto_setIntegral_truncationSet w hg hδ).const_mul ((P * K) ^ 2))
        fun k ↦ measureReal_lt_value_le_of_norm_gradient_truncation_sq_le hpoincare hw
          (by positivity) (div_le_self hδ.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
          (hbound _ (by positivity))
    exact (measureReal_eq_zero_iff ((Lp.memLp (W1p.value w)).measure_gt_lt_top two_ne_zero
      ENNReal.ofNat_ne_top hδ).ne).1 (le_antisymm hreal measureReal_nonneg)
  -- Hence `{w > 0} = ⋃ₖ {w > 1 / (k + 1)}` is null.
  have hunion : {x | 0 < W1p.value w x} = ⋃ k : ℕ, {x | 1 / ((k : ℝ) + 1) < W1p.value w x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun hx ↦ exists_nat_one_div_lt hx, fun ⟨k, hk⟩ ↦ (by positivity : (0 : ℝ) < _).trans hk⟩
  have h0 : mu.restrict Omega {x | 0 < W1p.value w x} = 0 := by
    rw [hunion]
    exact measure_iUnion_null fun k ↦ hnull (by positivity)
  exact ae_iff.2 (by simpa only [not_le] using h0)

/-! ### The energy estimate for the truncation -/

variable [DecidableEq ι]


/-- The pointwise inequality behind the energy estimate: if `M` is elliptic with constant `λ` and
`|gᵀ (M - N) h| ≤ L |d| ‖g‖ ‖h‖` with `|d| ≤ ε`, then
`gᵀ M (g + h) - gᵀ N h ≥ (λ / 2) ‖g‖² - ((L ε)² / (2 λ)) ‖h‖²`. -/
private theorem le_matrixBilinearForm_add_sub {M N : Matrix ι ι ℝ}
    {g h : EuclideanSpace ℝ ι} {lam L d ε : ℝ} (hlam : 0 < lam)
    (hM : lam * ‖g‖ ^ 2 ≤ M.toQuadraticForm' g)
    (hMN : |g ⬝ᵥ ((M - N) *ᵥ h)| ≤ L * |d| * ‖g‖ * ‖h‖) (hd : |d| ≤ ε) :
    lam / 2 * ‖g‖ ^ 2 - (L * ε) ^ 2 / (2 * lam) * ‖h‖ ^ 2 ≤
      matrixBilinearForm M g (g + h) - matrixBilinearForm N g h := by
  have hsplit : matrixBilinearForm M g (g + h) - matrixBilinearForm N g h =
      M.toQuadraticForm' g + g ⬝ᵥ ((M - N) *ᵥ h) := by
    rw [map_add, ← matrixBilinearForm_self]
    simp only [matrixBilinearForm_apply, Matrix.sub_mulVec, dotProduct_sub]
    ring
  -- `L |d| ‖g‖ ‖h‖ ≤ (λ / 2) ‖g‖² + (L |d| ‖h‖)² / (2 λ) ≤ (λ / 2) ‖g‖² + (L ε)² ‖h‖² / (2 λ)`.
  have hsq : (L * |d|) ^ 2 ≤ (L * ε) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg d) hd 2) (sq_nonneg L)
  have hamgm : L * |d| * ‖g‖ * ‖h‖ ≤
      lam / 2 * ‖g‖ ^ 2 + (L * ε) ^ 2 / (2 * lam) * ‖h‖ ^ 2 := by
    rw [← sub_nonneg]
    have key : 0 ≤ (lam * ‖g‖ - L * |d| * ‖h‖) ^ 2 + ((L * ε) ^ 2 - (L * |d|) ^ 2) * ‖h‖ ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.2 hsq) (sq_nonneg _))
    have : lam / 2 * ‖g‖ ^ 2 + (L * ε) ^ 2 / (2 * lam) * ‖h‖ ^ 2 - L * |d| * ‖g‖ * ‖h‖ =
        ((lam * ‖g‖ - L * |d| * ‖h‖) ^ 2 + ((L * ε) ^ 2 - (L * |d|) ^ 2) * ‖h‖ ^ 2) /
          (2 * lam) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg key (by positivity)
  rw [hsplit]
  linarith [neg_abs_le (g ⬝ᵥ ((M - N) *ᵥ h))]

variable {A : EuclideanSpace ℝ ι → ℝ → Matrix ι ι ℝ} {lam Lam L : ℝ}

/-- The pointwise form of the energy estimate: on `S_ε = {0 < u - v ≤ ε}` the difference of the
two energy densities tested against the truncation `φ_ε` is at least
`(λ / 2) ‖∇(u - v)‖² - ((L ε)² / (2 λ)) ‖∇v‖²`, and off `S_ε` it vanishes. -/
private theorem ae_indicator_le_matrixBilinearForm_sub
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (u v : W1p mu Omega 2) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ x ∂mu.restrict Omega,
      {x | 0 < W1p.value (u - v) x ∧ W1p.value (u - v) x ≤ ε}.indicator
          (fun x ↦ lam / 2 * ‖W1p.gradient (u - v) x‖ ^ 2 -
            (L * ε) ^ 2 / (2 * lam) * ‖W1p.gradient v x‖ ^ 2) x ≤
        matrixBilinearForm (A x (W1p.value u x)) (W1p.gradient (truncation hε (u - v)) x)
            (W1p.gradient u x) -
          matrixBilinearForm (A x (W1p.value v x)) (W1p.gradient (truncation hε (u - v)) x)
            (W1p.gradient v x) := by
  filter_upwards [gradient_truncation_ae hε (u - v), W1p.value_sub_ae u v,
    Lp.coeFn_sub (W1p.gradient u) (W1p.gradient v), ae_restrict_mem Omega.isOpen.measurableSet]
    with x hφ hw hgw hxΩ
  rw [hφ]
  by_cases hx : x ∈ {x | 0 < W1p.value (u - v) x ∧ W1p.value (u - v) x ≤ ε}
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    have hu : W1p.gradient u x = W1p.gradient (u - v) x + W1p.gradient v x := by
      rw [W1p.gradient_sub, hgw, Pi.sub_apply, sub_add_cancel]
    rw [hu]
    refine le_matrixBilinearForm_add_sub (hA 0).pos ((hA _).lower_bound hxΩ _)
      (hlip x hxΩ _ _ _ _) ?_
    rw [← Pi.sub_apply, ← hw]
    exact (abs_of_pos hx.1).le.trans hx.2
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    simp

/-- **The energy estimate for the truncation.** If `u` is a subsolution and `v` a supersolution
of the quasilinear equation, tested against the truncation `φ_ε = min((u - v)⁺, ε)`, then
`‖∇φ_ε‖² ≤ (L ε / λ)² ∫_{S_ε} ‖∇v‖²` with `S_ε = {0 < u - v ≤ ε}`. -/
private theorem norm_gradient_truncation_sq_le
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    {u v : W1p mu Omega 2}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (mu.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (mu.restrict Omega))
    {ε : ℝ} (hε : 0 ≤ ε)
    (huv : energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u (truncation hε (u - v)) ≤
      energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v (truncation hε (u - v))) :
    ‖W1p.gradient (truncation hε (u - v))‖ ^ 2 ≤
      (L * ε / lam) ^ 2 * ∫ x in {x | 0 < W1p.value (u - v) x ∧ W1p.value (u - v) x ≤ ε},
        ‖W1p.gradient v x‖ ^ 2 ∂mu.restrict Omega := by
  set S := {x | 0 < W1p.value (u - v) x ∧ W1p.value (u - v) x ≤ ε}
  have hlam := (hA 0).pos
  have hS : MeasurableSet S := measurableSet_truncationSet (u - v) ε
  -- Freezing the coefficient at `z` gives a uniformly elliptic matrix field.
  have hint (z : W1p mu Omega 2)
      (hz : AEStronglyMeasurable (fun x ↦ A x (W1p.value z x)) (mu.restrict Omega)) :
      Integrable (fun x ↦ matrixBilinearForm (A x (W1p.value z x))
        (W1p.gradient (truncation hε (u - v)) x) (W1p.gradient z x)) (mu.restrict Omega) := by
    have hz' : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι))
        (fun x ↦ A x (W1p.value z x)) lam Lam :=
      uniformlyEllipticOn_iff.2 ⟨hlam, (hA 0).le, fun x hx ↦
        ⟨(hA (W1p.value z x)).lower_bound hx, (hA (W1p.value z x)).upper_bound hx⟩⟩
    exact hz'.integrable_matrixBilinearForm_gradient hz z (truncation hε (u - v))
  -- Testing both inequalities with `φ_ε`, the difference of the two energy densities has
  -- nonpositive integral, and it dominates `1_S ((λ / 2) ‖∇w‖² - ((L ε)² / (2 λ)) ‖∇v‖²)`.
  rw [energyFormH1_zero_zero_eq_setIntegral, energyFormH1_zero_zero_eq_setIntegral] at huv
  have hind : Integrable (S.indicator fun x ↦ lam / 2 * ‖W1p.gradient (u - v) x‖ ^ 2 -
      (L * ε) ^ 2 / (2 * lam) * ‖W1p.gradient v x‖ ^ 2) (mu.restrict Omega) :=
    (((Lp.integrable_sq_norm _).const_mul _).sub
      ((Lp.integrable_sq_norm _).const_mul _)).indicator hS
  have hmono := integral_mono_ae hind ((hint u hAu).sub (hint v hAv))
    (ae_indicator_le_matrixBilinearForm_sub hA hlip u v hε)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hint u hAu) (hint v hAv), integral_indicator hS,
    integral_sub ((Lp.integrable_sq_norm _).const_mul _).integrableOn
      ((Lp.integrable_sq_norm _).const_mul _).integrableOn,
    integral_const_mul, integral_const_mul] at hmono
  -- The squared norm of `∇φ_ε = 1_S ∇w` is `∫_S ‖∇w‖²`.
  have hnorm : ‖W1p.gradient (truncation hε (u - v))‖ ^ 2 =
      ∫ x in S, ‖W1p.gradient (u - v) x‖ ^ 2 ∂mu.restrict Omega := by
    rw [← Lp.integral_norm_sq_eq_norm_sq, ← integral_indicator hS]
    refine integral_congr_ae ?_
    filter_upwards [gradient_truncation_ae hε (u - v)] with x hx
    by_cases hxS : x ∈ S
    · rw [hx, indicator_of_mem hxS, indicator_of_mem hxS]
    · rw [hx, indicator_of_notMem hxS, indicator_of_notMem hxS, norm_zero, zero_pow two_ne_zero]
  set Iw := ∫ x in S, ‖W1p.gradient (u - v) x‖ ^ 2 ∂mu.restrict Omega
  set Iv := ∫ x in S, ‖W1p.gradient v x‖ ^ 2 ∂mu.restrict Omega
  have h : lam / 2 * Iw ≤ (L * ε) ^ 2 / (2 * lam) * Iv := by linarith
  rw [hnorm, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc Iw * lam ^ 2 = 2 * lam * (lam / 2 * Iw) := by ring
    _ ≤ 2 * lam * ((L * ε) ^ 2 / (2 * lam) * Iv) := by gcongr
    _ = (L * ε) ^ 2 * Iv := by field_simp

/-! ### The comparison principle and uniqueness -/

/-- **The comparison principle for quasilinear divergence-form equations.** Let `A(x, s)` be
uniformly elliptic with constants `λ, Λ` on `Ω` for every `s`, and Lipschitz in `s` with constant
`L`, uniformly in `x ∈ Ω`, and let `Ω` carry a Poincaré inequality on `W^{1,2}_0(Ω)`. Let
`u, v ∈ W^{1,2}(Ω)`, with `x ↦ A(x, u(x))` and `x ↦ A(x, v(x))` measurable, satisfy

`∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ ≤ ∫_Ω ⟨A(x, v) ∇v, ∇φ⟩` for every nonnegative `φ ∈ W^{1,2}_0(Ω)`,

that is `-div(A(x, u) ∇u) ≤ -div(A(x, v) ∇v)` weakly, and `u ≤ v` on `∂Ω` in the sense that
`(u - v)⁺ ∈ W^{1,2}_0(Ω)`. Then `u ≤ v` almost everywhere in `Ω`. -/
theorem value_le_of_energyFormH1_quasilinear_le {P : ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤ P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    {u v : W1p mu Omega 2}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (mu.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u w ≤
          energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v w) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hw := value_nonpos_of_norm_gradient_truncation_sq_le (K := L / lam) hpoincare hboundary
    (Lp.integrable_sq_norm (W1p.gradient v)) fun ε hε ↦ by
    have := norm_gradient_truncation_sq_le hA hlip hAu hAv hε.le
      (huv ⟨_, truncation_mem_w1p0Submodule hε.le hboundary⟩
        (value_truncation_nonneg_ae hε.le (u - v)))
    convert this using 2
    ring
  filter_upwards [hw, W1p.value_sub_ae u v] with x hx hsub
  rw [hsub, Pi.sub_apply] at hx
  exact sub_nonpos.1 hx

/-- **Uniqueness for the quasilinear Dirichlet problem.** Under the hypotheses of
`TauCeti.PDE.value_le_of_energyFormH1_quasilinear_le` on `A` and `Ω`, if `u, v ∈ W^{1,2}(Ω)` have
the same boundary values, `u - v ∈ W^{1,2}_0(Ω)`, and are weak solutions of the same equation,

`∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω ⟨A(x, v) ∇v, ∇φ⟩` for every `φ ∈ W^{1,2}_0(Ω)`,

then `u = v`. -/
theorem eq_of_forall_energyFormH1_quasilinear_eq {P : ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤ P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    {u v : W1p mu Omega 2}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (mu.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (mu.restrict Omega))
    (hboundary : u - v ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u w =
        energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v w) :
    u = v := by
  have hvu : v - u ∈ w1p0Submodule mu Omega 2 := by
    simpa using (w1p0Submodule mu Omega 2).neg_mem hboundary
  have h₁ := value_le_of_energyFormH1_quasilinear_le hA hlip hpoincare hAu hAv
    (W1p.posPart_mem_w1p0Submodule (by norm_num) hboundary) fun w _ ↦ (huv w).le
  have h₂ := value_le_of_energyFormH1_quasilinear_le hA hlip hpoincare hAv hAu
    (W1p.posPart_mem_w1p0Submodule (by norm_num) hvu) fun w _ ↦ (huv w).ge
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact le_antisymm hx₁ hx₂

/-- **Uniqueness for the quasilinear Dirichlet problem on a bounded domain.** Let
`Ω ⊆ B(z, R) ⊆ ℝⁿ⁺¹`, let `A(x, s)` be uniformly elliptic with constants `λ, Λ` on `Ω` for every
`s`, and Lipschitz in `s` with constant `L`, uniformly in `x ∈ Ω`. Two weak solutions
`u, v ∈ W^{1,2}(Ω)` of `-div(A(x, u) ∇u) = -div(A(x, v) ∇v)` with `u - v ∈ W^{1,2}_0(Ω)`, and with
`x ↦ A(x, u(x))` and `x ↦ A(x, v(x))` measurable, are equal. -/
theorem eq_of_forall_energyFormH1_quasilinear_eq_of_subset_ball {n : ℕ}
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x ↦ A x s) lam Lam)
    (hlip : ∀ x ∈ Omega, ∀ s t : ℝ, ∀ η ξ : EuclideanSpace ℝ (Fin (n + 1)),
      |η ⬝ᵥ ((A x s - A x t) *ᵥ ξ)| ≤ L * |s - t| * ‖η‖ * ‖ξ‖)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {u v : W1p volume Omega 2}
    (hAu : AEStronglyMeasurable (fun x ↦ A x (W1p.value u x)) (volume.restrict Omega))
    (hAv : AEStronglyMeasurable (fun x ↦ A x (W1p.value v x)) (volume.restrict Omega))
    (hboundary : u - v ∈ w1p0Submodule volume Omega 2)
    (huv : ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u w =
        energyFormH1 (fun x ↦ A x (W1p.value v x)) 0 0 v w) :
    u = v :=
  eq_of_forall_energyFormH1_quasilinear_eq hA hlip
    (fun w ↦ W1p.norm_value_le_mul_norm_gradient_of_subset_ball hOmega w.property) hAu hAv
    hboundary huv

end TauCeti.PDE
