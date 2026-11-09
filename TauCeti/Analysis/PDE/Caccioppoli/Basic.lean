/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The Caccioppoli inequality for weak solutions

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, with `f ∈ L²(Ω)`,

meaning `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`; no boundary condition is imposed on
`u`. If the coefficient `a` is measurable and uniformly elliptic with constants `0 < λ ≤ Λ`,
then for every smooth cutoff `ζ` compactly supported in `Ω`,

`∫_Ω ζ² ‖∇u‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ζ‖² u² + (2/λ) ∫_Ω ζ² f u`.

This is the **Caccioppoli inequality** (the reverse Poincaré, or interior energy, inequality):
the gradient of a solution on the region where `ζ = 1` is controlled by the solution itself on
the support of `ζ`. The constants depend only on the ellipticity constants `λ` and `Λ`, and not
on `Ω`, on the dimension, or on any regularity of the coefficients beyond measurability. It is
the basic interior estimate of elliptic regularity theory: it is an ingredient in
difference-quotient proofs of interior `H²` regularity under additional coefficient regularity,
and its variant for the truncations `(u - k)⁺` of subsolutions, not proved here, is the starting
point of De Giorgi's iteration.

The proof tests the equation against `ζ² u`, which lies in `H¹₀(Ω)` because `ζ` is compactly
supported in `Ω`, and whose gradient is `ζ² ∇u + 2ζu ∇ζ`. Ellipticity bounds the first term of
`⟨a ∇u, ∇(ζ² u)⟩` below by `λζ²‖∇u‖²`, and Young's inequality absorbs half of it into the cross
term `2ζu ⟨a ∇u, ∇ζ⟩`.

## Main declarations

* `TauCeti.PDE.W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise`: the common
  integration and absorption step for Caccioppoli inequalities.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff`,
  `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_of_cutoff`: the common localization
  of a cutoff Caccioppoli inequality to concentric balls, with a nonnegative datum density or
  with a zeroth-order term.
* `TauCeti.PDE.UniformlyEllipticOn.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1`:
  the common testing step against `ψ² u`, for any right-hand side.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le`: the Caccioppoli
  inequality.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1 (the energy estimate in the proof of
  Theorem 1, interior `H²` regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.2 and §8.6.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 4.4.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- Integrate a pointwise Caccioppoli estimate and absorb half of its energy term. This is
the common measure-theoretic step for the solution and subsolution forms of the inequality;
the caller supplies the energy density and its comparison with the forcing term. -/
theorem W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise (hlam : 0 < lam)
    (w : W1p mu Omega 2) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hψM : ∀ x, |ψ x| ≤ M) (hgradM : ∀ x, ‖∇ ψ x‖ ≤ M)
    {e force : EuclideanSpace ℝ ι → ℝ} (he : Integrable e (mu.restrict Omega))
    (hpointwise : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ≤
        e x + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2))
    (hforce : ∫ x in Omega, e x ∂mu ≤ ∫ x in Omega, force x ∂mu) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + 2 / lam * ∫ x in Omega, force x ∂mu := by
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hgrad2 : AEStronglyMeasurable (fun x => ‖∇ ψ x‖ ^ 2) (mu.restrict Omega) :=
    ((ContDiff.continuous_gradient hψ).norm.pow 2).aestronglyMeasurable
  have hI1 : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_sq w).bdd_mul hψ2 (c := M ^ 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2)
  have hI2 : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value w)).integrable_sq.bdd_mul hgrad2 (c := M ^ 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgradM x) 2)
  have hint : ∫ x in Omega, lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ∂mu ≤
      ∫ x in Omega, (e x + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
        + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2)) ∂mu :=
    integral_mono_ae (hI1.const_mul lam) ((he.add (hI1.const_mul _)).add (hI2.const_mul _))
      hpointwise
  rw [integral_const_mul, integral_add, integral_add, integral_const_mul,
    integral_const_mul] at hint
  rotate_left
  · exact he
  · exact hI1.const_mul _
  · exact he.add (hI1.const_mul _)
  · exact hI2.const_mul _
  set X := ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
  set F := ∫ x in Omega, force x ∂mu
  have _ : lam * X ≤ F + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
    calc
      lam * X ≤ (∫ x in Omega, e x ∂mu) + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
        simpa [X, Y] using hint
      _ ≤ F + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
        gcongr
  have hX : X = 2 / lam * (lam / 2 * X) := by field_simp
  rw [hX]
  calc
    2 / lam * (lam / 2 * X) ≤ 2 / lam * (F + 2 * Lam ^ 2 / lam * Y) := by
      gcongr
      linarith
    _ = (2 * Lam / lam) ^ 2 * Y + 2 / lam * F := by
      field_simp
      ring

/-- Bound the cutoff-gradient term by the squared gradient bound and an integral over a set
containing the support of the cutoff. The comparison function may dominate the Sobolev value only
almost everywhere. -/
theorem W1p.setIntegral_norm_gradient_sq_mul_value_sq_le (w : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) {G : ℝ}
    (hG : ∀ x, ‖∇ ψ x‖ ≤ G) {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S)
    (hts : tsupport ψ ⊆ S) {g : EuclideanSpace ℝ ι → ℝ}
    (hg : Integrable g (mu.restrict Omega))
    (hwg : ∀ᵐ x ∂mu.restrict Omega, W1p.value w x ^ 2 ≤ g x) :
    ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      G ^ 2 * ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ S, g x ∂mu := by
  have hleft : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2)
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.value w)).integrable_sq.bdd_mul
      ((ContDiff.continuous_gradient hψ).norm.pow 2).aestronglyMeasurable (c := G ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hG x) 2)
  have hright : Integrable (S.indicator g) (mu.restrict Omega) := hg.indicator hS
  calc
    ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
        ∫ x in Omega, G ^ 2 * S.indicator g x ∂mu :=
      integral_mono_ae hleft (hright.const_mul _) (by
        filter_upwards [hwg] with x hx
        by_cases hxS : x ∈ S
        · rw [indicator_of_mem hxS]
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hG x) 2) hx
            (sq_nonneg _) (sq_nonneg _)
        · have hfd : fderiv ℝ ψ x = 0 := Function.notMem_support.1 fun hx' =>
            hxS (hts (support_fderiv_subset ℝ hx'))
          simp [indicator_of_notMem hxS, _root_.gradient, hfd])
    _ = G ^ 2 * ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ S, g x ∂mu := by
      rw [integral_const_mul, setIntegral_indicator hS]

/-- Bound the zeroth-order term of a Caccioppoli inequality by an integral over a set containing
the support of a cutoff with `ψ² ≤ 1`. The comparison function may dominate the Sobolev value only
almost everywhere. -/
theorem W1p.setIntegral_sq_mul_value_sq_le (w : W1p mu Omega 2) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : AEStronglyMeasurable ψ (mu.restrict Omega)) (hψ1 : ∀ x, ψ x ^ 2 ≤ 1)
    {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S) (hts : tsupport ψ ⊆ S)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : Integrable g (mu.restrict Omega))
    (hwg : ∀ᵐ x ∂mu.restrict Omega, W1p.value w x ^ 2 ≤ g x) :
    ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ S, g x ∂mu := by
  rw [← setIntegral_indicator hS]
  refine integral_mono_ae ((Lp.memLp (W1p.value w)).integrable_sq.bdd_mul (hψ.pow 2) (c := 1)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hψ1 x)) (hg.indicator hS) ?_
  filter_upwards [hwg] with x hx
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
    exact (mul_le_of_le_one_left (sq_nonneg _) (hψ1 x)).trans hx
  · rw [indicator_of_notMem hxS, image_eq_zero_of_notMem_tsupport fun hx' => hxS (hts hx')]
    simp

open Filter Metric in
/-- **Localizing a cutoff Caccioppoli inequality with a datum to concentric balls.** There is a
constant `C > 0`, depending only on the dimension, such that the following holds for every additive
Haar measure `μ`. Let `w ∈ H¹(Ω)`, `A ≥ 0`, and let `g` be integrable and almost everywhere
nonnegative on `Ω`, and suppose that every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + ∫_Ω ψ² g`.

Then for every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `0 < r < R`,

`∫_{B(x₀, r)} ‖∇w‖² ≤ A (C / (R - r))² ∫_{B(x₀, R)} w² + ∫_{B(x₀, R)} g`.

The cutoff is one on `B(x₀, r)`, takes values in `[0, 1]`, is supported in `B(x₀, R)`, and has
gradient at most `C / (R - r)`. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} (w : W1p mu Omega 2) {A : ℝ}
      {g : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      0 ≤ A → Integrable g (mu.restrict Omega) → (∀ᵐ x ∂mu.restrict Omega, 0 ≤ g x) → 0 < r →
      r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
          A * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
            + ∫ x in Omega, ψ x ^ 2 * g x ∂mu) →
      ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
        A * (C / (R - r)) ^ 2 * ∫ x in ball x₀ R, W1p.value w x ^ 2 ∂mu
          + ∫ x in ball x₀ R, g x ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨2 * (C + 1), by positivity, ?_⟩
  intro mu _ Omega w A g x₀ r R hA hg hg0 hr hrR hball hcacc
  -- A cutoff equal to one on `ball x₀ r` and supported in
  -- `closedBall x₀ ((r + R) / 2) ⊆ ball x₀ R`.
  obtain ⟨ψ, hψ, hrange, hone, hts, hgrad, -⟩ := hC x₀ hr.le (by linarith : r < (r + R) / 2)
  have htsR : tsupport ψ ⊆ ball x₀ R :=
    hts.trans (closedBall_subset_ball (by linarith))
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ((r + R) / 2)).of_isClosed_subset (isClosed_tsupport ψ) hts
  set G : ℝ := 2 * (C + 1) / (R - r)
  have hG : ∀ x, ‖∇ ψ x‖ ≤ G := fun x => (hgrad x).trans (by
    rw [(by ring : (r + R) / 2 - r = (R - r) / 2), div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith))
  have hψ1 : ∀ x, ψ x ^ 2 ≤ 1 := fun x => by
    obtain ⟨h0, h1⟩ := hrange (mem_range_self x)
    exact pow_le_one₀ h0 h1
  -- On `B(x₀, r)` the cutoff is one.
  have hleft : ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu :=
    MeasureTheory.setIntegral_le_setIntegral_sq_mul_of_eqOn (W1p.integrable_norm_gradient_sq w)
      (ae_of_all _ fun x => sq_nonneg _) hψ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => hrange (mem_range_self x)) measurableSet_ball
      (hone.mono ball_subset_closedBall) ((ball_subset_ball hrR.le).trans hball)
  -- `∇ψ` vanishes off `B(x₀, R)`, where it is bounded by `G`.
  have hright : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      G ^ 2 * ∫ x in ball x₀ R, W1p.value w x ^ 2 ∂mu :=
    (W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hG measurableSet_ball htsR
      (Lp.memLp (W1p.value w)).integrable_sq (Eventually.of_forall fun x => le_rfl)).trans_eq
      (by rw [inter_eq_right.2 hball])
  -- `ψ² ≤ 1` on `B(x₀, R)`, `ψ` vanishes off it, and `g ≥ 0`.
  have hdatum : ∫ x in Omega, ψ x ^ 2 * g x ∂mu ≤ ∫ x in ball x₀ R, g x ∂mu := by
    rw [← inter_eq_right.2 hball, ← setIntegral_indicator measurableSet_ball]
    refine integral_mono_ae (hg.bdd_mul (hψ.continuous.pow 2).aestronglyMeasurable (c := 1)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hψ1 x)) (hg.indicator measurableSet_ball) ?_
    filter_upwards [hg0] with x hx
    by_cases hxR : x ∈ ball x₀ R
    · rw [indicator_of_mem hxR]
      exact mul_le_of_le_one_left hx (hψ1 x)
    · rw [indicator_of_notMem hxR, image_eq_zero_of_notMem_tsupport fun hx' => hxR (htsR hx')]
      simp
  calc ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu
      ≤ A * (G ^ 2 * ∫ x in ball x₀ R, W1p.value w x ^ 2 ∂mu) + ∫ x in ball x₀ R, g x ∂mu :=
        (hleft.trans (hcacc ψ hψ hcpt (htsR.trans hball))).trans (by gcongr)
    _ = _ := by ring

open Filter Metric in
/-- **Localizing a cutoff Caccioppoli inequality to concentric balls.** There is a constant
`C > 0`, depending only on the dimension, such that the following holds for every additive Haar
measure `μ`. Let `w ∈ H¹(Ω)` and `A, B ≥ 0`, and suppose that every smooth `ψ` compactly
supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + B ∫_Ω ψ² w²`.

Then for every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `0 < r < R`,

`∫_{B(x₀, r)} ‖∇w‖² ≤ (A (C / (R - r))² + B) ∫_{B(x₀, R)} w²`.

This is `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff` with
the datum `g = B w²`. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_of_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} (w : W1p mu Omega 2) {A B : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      0 ≤ A → 0 ≤ B → 0 < r → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
          A * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
            + B * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu) →
      ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
        (A * (C / (R - r)) ^ 2 + B) * ∫ x in ball x₀ R, W1p.value w x ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff
    (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega w A B x₀ r R hA hB hr hrR hball hcacc
  have hloc := hC w (g := fun x => B * W1p.value w x ^ 2) hA
    ((Lp.memLp (W1p.value w)).integrable_sq.const_mul B)
    (Eventually.of_forall fun x => by positivity) hr hrR hball fun ψ hψ hcpt hts => by
      simp_rw [mul_left_comm (ψ _ ^ 2), integral_const_mul]
      exact hcacc ψ hψ hcpt hts
  rw [integral_const_mul] at hloc
  linarith

variable [DecidableEq ι]

/-- **The testing step of the Caccioppoli inequality**, for any right-hand side. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `u ∈ H¹(Ω)`, and let `ψ` be
smooth and compactly supported in `Ω`. The test function `v = ψ² u` lies in `H¹₀(Ω)`, has
`∇v = ψ (ψ ∇u + u ∇ψ) + ψ u ∇ψ` almost everywhere, and

`∫_Ω ψ² ‖∇u‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² u² + (2/λ) a(u, v)`.

The caller evaluates `a(u, v)` through the weak form of its equation. -/
theorem UniformlyEllipticOn.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (u : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, W1p.value (v : W1p mu Omega 2) x = ψ x ^ 2 * W1p.value u x) ∧
      (∀ᵐ x ∂mu.restrict Omega, W1p.gradient (v : W1p mu Omega 2) x =
        ψ x • (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) + (ψ x * W1p.value u x) • ∇ ψ x) ∧
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
          + 2 / lam * energyFormH1 a 0 0 u (v : W1p mu Omega 2) := by
  have hlam := h.pos
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- The test function `ψ² u = ψ (ψ u)`, which lies in `H¹₀(Ω)`.
  set w := W1p.contDiffSMul ψ hψ hM hψM' hgradM' u
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM' hgradM' hcpt
      hts w
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0) (gamma := 0)
    ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u v
  -- The pointwise estimate, almost everywhere on `Ω`.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2) ≤
        energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x)
          + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2) := by
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' u,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' u] with x hx hgv hgw hvw
    have key := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam (ψ x)
      (W1p.value u x) (W1p.gradient u x) (∇ ψ x)
      (h.lower_bound hx (W1p.gradient u x))
      (h.upper_bound hx (∇ ψ x) (W1p.gradient u x))
    rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgw, hvw]
    simpa [driftForm_apply, massForm_apply, smul_eq_mul] using key
  refine ⟨⟨v, hv⟩, ?_, ?_, ?_⟩
  · filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' u] with x hvv hvw
    rw [hvv, hvw, smul_eq_mul, smul_eq_mul]
    ring
  · filter_upwards [W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' u,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' u] with x hgv hgw hvw
    rw [hgv, hgw, hvw, smul_eq_mul]
  · rw [energyFormH1_def]
    exact W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise hlam u hψ hψM hgradM hE hpt
      le_rfl

/-- **The Caccioppoli inequality.** Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, in
the sense that `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`.
Then for every smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² ‖∇u‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² u² + (2/λ) ∫_Ω ψ² f u`.

For `f = 0` the last term vanishes, and the gradient of `u` where `ψ = 1` is bounded by `u`
itself on the support of `ψ`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
        + 2 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
  obtain ⟨v, hvalue, -, hstep⟩ :=
    h.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1 ha u hψ hcpt hts
  -- The energy is `∫_Ω ψ² f u`, by the weak equation.
  have hF : energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
    rw [hu v]
    refine integral_congr_ae ?_
    filter_upwards [hvalue] with x hx
    rw [hx]
    ring
  rwa [hF] at hstep

end PDE

end TauCeti
