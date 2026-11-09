/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Topology.MetricSpace.Holder

/-!
# Campanato's characterization of Hölder continuity

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E` of dimension
`n`, and let `0 < α`. For a locally integrable `f : E → F`, write `f_{x,r}` for its average over
`closedBall x r`, and call `⨍_{closedBall x r} ‖f - f_{x,r}‖` its *mean oscillation* on that
ball. **Campanato's theorem** says that `f` agrees almost everywhere with an `α`-Hölder function
exactly when its mean oscillation on balls of radius `r` is `O(r^α)`. The Hölder representative
is the precise representative `TauCeti.MeasureTheory.preciseRepresentative μ f`, the limit of the
averages `f_{x,r}` as `r → 0`.

The hypothesis controls an integral average rather than an essential supremum, so it is much
weaker than the oscillation bound behind `TauCeti.MeasureTheory.holderOnWith_preciseRepresentative`.
This is the form in which energy estimates deliver regularity: Poincaré's inequality turns a
growth bound on `∫_{closedBall x r} ‖∇u‖ᵖ` (Morrey's Dirichlet growth condition) into such a mean
oscillation bound, and the Campanato approach to the Schauder estimates compares a solution with
solutions of a constant-coefficient problem in the same integral norms.

## Campanato's theorem on a domain

Estimates up to the boundary of a domain `Ω ⊆ E` only control the mean oscillation of `f` on the
pieces `closedBall x r ∩ Ω` with `x ∈ Ω`, and the averages `f_{x,r}` are then taken over these
pieces. The theorem persists when `Ω` satisfies the **measure density condition**: there are
`A > 0` and `D > 0` with `A μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)` for all `x ∈ Ω` and
`0 < r ≤ D`, so that `Ω` fills a fixed proportion of every small ball centred in it. Bounded
convex open sets and bounded Lipschitz domains have this property, while a domain with an outward
cusp does not. If moreover any two
points of `Ω` are at distance at most `D / 2`, and the mean oscillation of `f ∈ L¹(Ω)` on
`closedBall x r ∩ Ω` is at most `M r^α` for `x ∈ Ω` and `0 < r ≤ D`, then the precise
representative of `f` with respect to `μ.restrict Ω` is `α`-Hölder on `Ω`, with constant
`2 · 2^α · 2ⁿ / (A (1 - 2^(-α))) · M`, and agrees with `f` almost everywhere on `Ω`. Conversely,
an `α`-Hölder function on `Ω` has mean oscillation at most `K (2 r)^α` on every such piece
(`TauCeti.setAverage_norm_sub_setAverage_le_of_holderOnWith`). In
the language of Campanato spaces, the same conclusion follows from the `Lᵖ` bound
`∫_{closedBall x r ∩ Ω} ‖f - f_{x,r}‖ᵖ ≤ M r^λ`, `p ≥ 1`, with `α = (λ - n) / p > 0`, by Hölder's
inequality: `𝓛^{p,λ}(Ω) ⊆ C^{0,α}(Ω)`. The statements on the whole space are the case `Ω = E`,
`A = 1`.

## The proof

The proof is a telescoping argument. If `closedBall y ε ⊆ closedBall x r` with `r ≤ 2 ε`, then
comparing the averages over `closedBall x r ∩ Ω` and `closedBall y ε ∩ Ω` costs at most
`2ⁿ / A · M r^α`: the factor is a bound for the ratio of the measures of the two pieces, the
measure density condition reducing it to the ratio `2ⁿ` of the measures of the two balls (by
`TauCeti.norm_setAverage_sub_le_of_subset` and
`MeasureTheory.Measure.addHaar_real_closedBall_div_le`).
Summing over dyadic radii shows that the averages `f_{x,r}` converge as `r → 0`, with
`‖f_{x,r} - f*(x)‖ ≤ 2ⁿ / (A (1 - 2^(-α))) · M r^α`, and comparing the averages over
`closedBall y d ∩ Ω ⊆ closedBall x (2 d) ∩ Ω`, `d = dist x y`, then gives the Hölder bound. The
limit agrees with `f` almost everywhere on `Ω` by the Lebesgue differentiation theorem for the
restricted measure `μ.restrict Ω`, which holds by the Besicovitch covering theorem although that
measure is not doubling.

## Main declarations

All declarations are in the `TauCeti.MeasureTheory` namespace.

* `norm_setAverage_closedBall_inter_sub_preciseRepresentative_restrict_le`: mean oscillation on
  the pieces `closedBall x r ∩ Ω` decaying like `r^α` makes their averages converge at `x`, at
  rate `r^α`.
* `dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le`: the local Hölder estimate
  on a domain, between two points, from mean oscillation bounds on pieces of radius comparable to
  their distance.
* `holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le`: **Campanato's theorem**
  on a bounded domain satisfying the measure density condition.
* `exists_holderOnWith_ae_eq_iff_forall_setAverage_norm_sub_le`: on such a domain, an integrable
  function agrees almost everywhere with an `α`-Hölder function on `Ω` if and only if its mean
  oscillation on the pieces `closedBall x r ∩ Ω` is `O(r^α)`.
* `setAverage_norm_sub_le_of_setLIntegral_enorm_sub_rpow_le`: an `Lᵖ` bound on the oscillation
  on a single piece `closedBall x r ∩ Ω` of growth `r^(n + p α)` bounds the mean oscillation there
  by a multiple of `r^α`.
* `holderOnWith_preciseRepresentative_restrict_of_setLIntegral_enorm_sub_rpow_le`: Campanato's
  theorem on such a domain from an `Lᵖ` bound on the oscillation, `𝓛^{p,λ}(Ω) ⊆ C^{0,α}(Ω)`.
* `tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le` and
  `norm_setAverage_closedBall_sub_preciseRepresentative_le`: on the whole space, the averages
  converge at `x`, at rate `r^α`.
* `dist_preciseRepresentative_le_of_setAverage_norm_sub_le`: the local Hölder estimate on the
  whole space.
* `holderWith_preciseRepresentative_of_setAverage_norm_sub_le`: **Campanato's theorem** on the
  whole space.
* `exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le`: a locally integrable function
  agrees almost everywhere with an `α`-Hölder function if and only if its mean oscillation on
  balls of radius `r` is `O(r^α)`.

## References

* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 5.5.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Theorem 3.1.
-/

public section

noncomputable section

open Filter Metric Set Topology MeasureTheory Module
open scoped NNReal

namespace TauCeti

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x : E} {M α ρ : ℝ}
  {Ω : Set E} {A : ℝ≥0}

/-- For `α > 0`, `1 - 2^(-α)` is positive: the dyadic series of ratio `2^(-α)` converges. -/
private lemma one_sub_two_rpow_neg_pos (hα : 0 < α) : 0 < 1 - (2 : ℝ) ^ (-α) :=
  sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα))

/-- Comparing the averages over `closedBall y ε ∩ Ω ⊆ closedBall x r ∩ Ω` for `r ≤ 2 ε` costs at
most `2ⁿ / A` times the mean oscillation on `closedBall x r ∩ Ω`, when `Ω` fills at least the
proportion `A` of `closedBall y ε`. -/
private lemma norm_setAverage_closedBall_inter_sub_le_of_le_two_mul {y : E} {ε r : ℝ}
    (hA : 0 < A) (hε : 0 < ε) (hsub : closedBall y ε ⊆ closedBall x r) (hrε : r ≤ 2 * ε)
    (hdens : A * μ (closedBall y ε) ≤ μ (closedBall y ε ∩ Ω))
    (hf : IntegrableOn f (closedBall x r ∩ Ω) μ)
    (hosc : ⨍ z in closedBall x r ∩ Ω, ‖f z - ⨍ w in closedBall x r ∩ Ω, f w ∂μ‖ ∂μ ≤
      M * r ^ α) :
    ‖(⨍ z in closedBall y ε ∩ Ω, f z ∂μ) - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ≤
      2 ^ finrank ℝ E / A * (M * r ^ α) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.1 (hsub (mem_closedBall_self hε.le)))
  have hyε : 0 < μ.real (closedBall y ε) :=
    ENNReal.toReal_pos (measure_closedBall_pos μ y hε).ne' measure_closedBall_lt_top.ne
  -- The measure density condition turns the doubling of `μ` into a bound for the ratio of the
  -- measures of the two pieces of `Ω`.
  have hratio : μ.real (closedBall x r ∩ Ω) / μ.real (closedBall y ε ∩ Ω) ≤
      2 ^ finrank ℝ E / A :=
    calc μ.real (closedBall x r ∩ Ω) / μ.real (closedBall y ε ∩ Ω)
        ≤ μ.real (closedBall x r) / (A * μ.real (closedBall y ε)) :=
          div_le_div₀ measureReal_nonneg
            (measureReal_mono inter_subset_left measure_closedBall_lt_top.ne)
            (mul_pos (by exact_mod_cast hA) hyε) (mul_measureReal_closedBall_le hdens)
      _ = μ.real (closedBall x r) / μ.real (closedBall y ε) / A := by
          rw [div_div, mul_comm (A : ℝ)]
      _ ≤ 2 ^ finrank ℝ E / A := by
          gcongr
          simpa using μ.addHaar_real_closedBall_div_le x y hε hr hrε
  exact (norm_setAverage_sub_le_of_subset (inter_subset_inter_left Ω hsub)
    (measure_closedBall_inter_ne_zero hA hε hdens)
    (measure_ne_top_of_subset inter_subset_left measure_closedBall_lt_top.ne) hf _).trans <|
    mul_le_mul hratio hosc (average_nonneg fun _ ↦ norm_nonneg _) (by positivity)

/-- **Telescoping over dyadic radii.** If `Ω` fills at least the proportion `A` of
`closedBall x r` and the mean oscillation of `f` on `closedBall x r ∩ Ω` is at most `M r^α` for
`0 < r ≤ ρ`, then the averages over `closedBall x ε ∩ Ω` and `closedBall x r ∩ Ω`,
`0 < ε ≤ r ≤ ρ`, differ by at most `2ⁿ / (A (1 - 2^(-α))) · M r^α`. -/
private lemma norm_setAverage_closedBall_inter_sub_le (hα : 0 < α) (hA : 0 < A)
    (hdens : ∀ r, 0 < r → r ≤ ρ → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hf : IntegrableOn f (closedBall x ρ ∩ Ω) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {ε r : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x ε ∩ Ω, f y ∂μ) - ⨍ y in closedBall x r ∩ Ω, f y ∂μ‖ ≤
      2 ^ finrank ℝ E / A / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  set c : ℝ := 2 ^ finrank ℝ E / A
  set C : ℝ := c / (1 - 2 ^ (-α))
  have hq := one_sub_two_rpow_neg_pos hα
  have hC : c ≤ C :=
    le_div_self (by positivity) hq (sub_le_self _ (Real.rpow_pos_of_pos two_pos _).le)
  have hCq : C * 2 ^ (-α) + c = C := by
    simp only [C]
    field_simp [hq.ne']
    ring
  have hM : ∀ r, 0 < r → r ≤ ρ → 0 ≤ M * r ^ α := fun r hr hrρ ↦
    (average_nonneg fun _ ↦ norm_nonneg _).trans (hosc r hr hrρ)
  have hint : ∀ r ≤ ρ, IntegrableOn f (closedBall x r ∩ Ω) μ := fun r hrρ ↦
    hf.mono_set (inter_subset_inter_left Ω (closedBall_subset_closedBall hrρ))
  -- By induction on `k`, the bound holds for `r / 2 ^ k ≤ ε ≤ r`: either `ε ≥ r / 2`, and one
  -- step suffices, or `ε < r / 2`, and we pass through the average over
  -- `closedBall x (r / 2) ∩ Ω`, the identity `C 2^(-α) + c = C` absorbing the extra step.
  have key : ∀ k : ℕ, ∀ r, 0 < r → r ≤ ρ → ∀ ε, r / 2 ^ k ≤ ε → ε ≤ r →
      ‖(⨍ y in closedBall x ε ∩ Ω, f y ∂μ) - ⨍ y in closedBall x r ∩ Ω, f y ∂μ‖ ≤
        C * (M * r ^ α) := by
    intro k
    induction k with
    | zero =>
      intro r hr hrρ ε h₁ h₂
      obtain rfl : ε = r := le_antisymm h₂ (by simpa using h₁)
      simpa using mul_nonneg ((by positivity : (0 : ℝ) ≤ c).trans hC) (hM ε hr hrρ)
    | succ k ih =>
      intro r hr hrρ ε h₁ h₂
      have hε : 0 < ε := (by positivity : 0 < r / 2 ^ (k + 1)).trans_le h₁
      rcases le_or_gt (r / 2) ε with h | h
      · exact (norm_setAverage_closedBall_inter_sub_le_of_le_two_mul hA hε
          (closedBall_subset_closedBall h₂) (by linarith) (hdens ε hε (h₂.trans hrρ))
          (hint r hrρ) (hosc r hr hrρ)).trans (mul_le_mul_of_nonneg_right hC (hM r hr hrρ))
      have h₃ := ih (r / 2) (by positivity) (by linarith) ε
        (by rwa [div_div, ← pow_succ']) h.le
      have h₄ := norm_setAverage_closedBall_inter_sub_le_of_le_two_mul hA (half_pos hr)
        (closedBall_subset_closedBall (half_le_self hr.le)) (by linarith)
        (hdens (r / 2) (half_pos hr) (by linarith)) (hint r hrρ) (hosc r hr hrρ)
      calc ‖(⨍ y in closedBall x ε ∩ Ω, f y ∂μ) - ⨍ y in closedBall x r ∩ Ω, f y ∂μ‖
          ≤ ‖(⨍ y in closedBall x ε ∩ Ω, f y ∂μ) - ⨍ y in closedBall x (r / 2) ∩ Ω, f y ∂μ‖ +
            ‖(⨍ y in closedBall x (r / 2) ∩ Ω, f y ∂μ) -
              ⨍ y in closedBall x r ∩ Ω, f y ∂μ‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C * (M * (r / 2) ^ α) + c * (M * r ^ α) := add_le_add h₃ h₄
        _ = (C * 2 ^ (-α) + c) * (M * r ^ α) := by
            rw [Real.div_rpow hr.le zero_le_two, Real.rpow_neg zero_le_two]
            ring
        _ = C * (M * r ^ α) := by rw [hCq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε (hε.trans_le hεr)) one_half_lt_one
  refine key k r (hε.trans_le hεr) hrρ ε ?_ hεr
  calc r / 2 ^ k = (1 / 2) ^ k * r := by rw [one_div_pow]; ring
    _ ≤ ε := ((lt_div_iff₀ (hε.trans_le hεr)).1 hk).le

/-- **Mean oscillation decay gives convergence of the averages on a domain.** Let `α > 0` and
`ρ > 0`. If `Ω` fills at least the proportion `A > 0` of `closedBall x r`, `f` is integrable on
`closedBall x ρ ∩ Ω` and its mean oscillation on `closedBall x r ∩ Ω` is at most `M r^α` for
`0 < r ≤ ρ`, then the averages of `f` over the sets `closedBall x ε ∩ Ω` converge, as `ε → 0`, to
the precise representative of `f` at `x` with respect to `μ.restrict Ω`. -/
theorem tendsto_setAverage_closedBall_inter_preciseRepresentative_restrict_of_setAverage_norm_sub_le
    (hα : 0 < α) (hρ : 0 < ρ) (hA : 0 < A)
    (hdens : ∀ r, 0 < r → r ≤ ρ → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hf : IntegrableOn f (closedBall x ρ ∩ Ω) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ∂μ ≤ M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε ∩ Ω, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative (μ.restrict Ω) f x)) := by
  set C : ℝ := 2 ^ finrank ℝ E / A / (1 - 2 ^ (-α))
  -- The averages form a Cauchy filter: those of radius at most `τ` lie within `C M τ^α` of the
  -- average of radius `τ`.
  have hcauchy : Cauchy (map (fun ε ↦ ⨍ y in closedBall x ε ∩ Ω, f y ∂μ) (𝓝[>] (0 : ℝ))) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun δ hδ ↦ ?_⟩
    have h0 : Tendsto (fun r : ℝ ↦ C * (M * r ^ α)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuous_rpow_const hα.le).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow hα.ne'] using (h.const_mul M).const_mul C
    obtain ⟨τ, hτ, hτρ⟩ := ((h0.eventually (gt_mem_nhds (half_pos hδ))).and
      (Ioc_mem_nhdsGT hρ)).exists
    refine ⟨(fun ε ↦ ⨍ y in closedBall x ε ∩ Ω, f y ∂μ) '' Ioc 0 τ,
      image_mem_map (Ioc_mem_nhdsGT hτρ.1), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    calc dist (⨍ y in closedBall x a ∩ Ω, f y ∂μ) (⨍ y in closedBall x b ∩ Ω, f y ∂μ)
        ≤ dist (⨍ y in closedBall x a ∩ Ω, f y ∂μ) (⨍ y in closedBall x τ ∩ Ω, f y ∂μ) +
          dist (⨍ y in closedBall x b ∩ Ω, f y ∂μ) (⨍ y in closedBall x τ ∩ Ω, f y ∂μ) :=
          dist_triangle_right _ _ _
      _ ≤ C * (M * τ ^ α) + C * (M * τ ^ α) := by
          rw [dist_eq_norm, dist_eq_norm]
          exact add_le_add
            (norm_setAverage_closedBall_inter_sub_le hα hA hdens hf hosc ha.1 ha.2 hτρ.2)
            (norm_setAverage_closedBall_inter_sub_le hα hA hdens hf hosc hb.1 hb.2 hτρ.2)
      _ < δ := by linarith
  obtain ⟨v, hv⟩ := CompleteSpace.complete hcauchy
  have hv' : Tendsto (fun ε ↦ ⨍ y in closedBall x ε ∩ Ω, f y ∂μ) (𝓝[>] 0) (𝓝 v) := hv
  -- With respect to `μ.restrict Ω`, the average over `closedBall x ε` is the one over
  -- `closedBall x ε ∩ Ω`.
  rwa [preciseRepresentative_eq_of_tendsto
    (by simpa only [Measure.restrict_restrict measurableSet_closedBall] using hv')]

/-- **The rate of convergence of the averages on a domain.** Let `α > 0` and `A > 0`. If `Ω` fills
at least the proportion `A` of `closedBall x r`, `f` is integrable on `closedBall x ρ ∩ Ω` and its
mean oscillation on `closedBall x r ∩ Ω` is at most `M r^α` for `0 < r ≤ ρ`, then for
`0 < r ≤ ρ` the average of `f` over `closedBall x r ∩ Ω` lies within
`2ⁿ / (A (1 - 2^(-α))) · M r^α` of the precise representative of `f` at `x` with respect to
`μ.restrict Ω`, where `n` is the dimension. -/
theorem norm_setAverage_closedBall_inter_sub_preciseRepresentative_restrict_le (hα : 0 < α)
    (hA : 0 < A)
    (hdens : ∀ r, 0 < r → r ≤ ρ → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hf : IntegrableOn f (closedBall x ρ ∩ Ω) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x r ∩ Ω, f y ∂μ) - preciseRepresentative (μ.restrict Ω) f x‖ ≤
      2 ^ finrank ℝ E / A / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  have ht :=
    tendsto_setAverage_closedBall_inter_preciseRepresentative_restrict_of_setAverage_norm_sub_le
      hα (hr.trans_le hrρ) hA hdens hf hosc
  refine le_of_tendsto (tendsto_const_nhds.sub ht).norm ?_
  filter_upwards [Ioc_mem_nhdsGT hr] with ε hε
  rw [norm_sub_rev]
  exact norm_setAverage_closedBall_inter_sub_le hα hA hdens hf hosc hε.1 hε.2 hrρ

/-- **The local Campanato estimate on a domain.** Let `α > 0`, `A > 0` and `d = dist x y`. Suppose
that `Ω` fills at least the proportion `A` of `closedBall x r` for `0 < r ≤ 2 d` and of
`closedBall y r` for `0 < r ≤ d`, that `f` is integrable on `closedBall x (2 d) ∩ Ω`, and that the
mean oscillation of `f` is at most `M r^α` on `closedBall x r ∩ Ω` for `0 < r ≤ 2 d` and on
`closedBall y r ∩ Ω` for `0 < r ≤ d`. Then the precise representatives of `f` with respect to
`μ.restrict Ω` at `x` and `y` differ by at most `2 · 2^α · 2ⁿ / (A (1 - 2^(-α))) · M d^α`, where
`n` is the dimension. -/
theorem dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le {y : E}
    (hα : 0 < α) (hA : 0 < A)
    (hdensx : ∀ r, 0 < r → r ≤ 2 * dist x y → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hdensy : ∀ r, 0 < r → r ≤ dist x y → A * μ (closedBall y r) ≤ μ (closedBall y r ∩ Ω))
    (hf : IntegrableOn f (closedBall x (2 * dist x y) ∩ Ω) μ)
    (hoscx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ⨍ z in closedBall x r ∩ Ω, ‖f z - ⨍ w in closedBall x r ∩ Ω, f w ∂μ‖ ∂μ ≤ M * r ^ α)
    (hoscy : ∀ r, 0 < r → r ≤ dist x y →
      ⨍ z in closedBall y r ∩ Ω, ‖f z - ⨍ w in closedBall y r ∩ Ω, f w ∂μ‖ ∂μ ≤ M * r ^ α) :
    dist (preciseRepresentative (μ.restrict Ω) f x) (preciseRepresentative (μ.restrict Ω) f y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / A / (1 - 2 ^ (-α))) * (M * dist x y ^ α) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp [Real.zero_rpow hα.ne']
  set d := dist x y
  set c : ℝ := 2 ^ finrank ℝ E / A
  set C : ℝ := c / (1 - 2 ^ (-α))
  have hd : 0 < d := dist_pos.2 hxy
  -- Pass from `x` to `y` through the averages over
  -- `closedBall x (2 d) ∩ Ω ⊇ closedBall y d ∩ Ω`.
  have hsub : closedBall y d ⊆ closedBall x (2 * d) :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  have h₁ := norm_setAverage_closedBall_inter_sub_preciseRepresentative_restrict_le hα hA hdensx
    hf hoscx (by positivity) le_rfl
  have h₂ := norm_setAverage_closedBall_inter_sub_preciseRepresentative_restrict_le hα hA hdensy
    (hf.mono_set (inter_subset_inter_left Ω hsub)) hoscy hd le_rfl
  have h₃ : ‖(⨍ z in closedBall y d ∩ Ω, f z ∂μ) - ⨍ z in closedBall x (2 * d) ∩ Ω, f z ∂μ‖ ≤
      c * (M * (2 * d) ^ α) :=
    norm_setAverage_closedBall_inter_sub_le_of_le_two_mul hA hd hsub le_rfl
      (hdensy d hd le_rfl) hf (hoscx _ (by positivity) le_rfl)
  have hCq : 2 ^ α * c = C * (2 ^ α - 1) := by
    simp only [C]
    field_simp [(one_sub_two_rpow_neg_pos hα).ne']
    rw [Real.rpow_neg zero_le_two]
    field_simp
  rw [dist_eq_norm]
  calc ‖preciseRepresentative (μ.restrict Ω) f x - preciseRepresentative (μ.restrict Ω) f y‖
      ≤ ‖preciseRepresentative (μ.restrict Ω) f x - ⨍ z in closedBall x (2 * d) ∩ Ω, f z ∂μ‖ +
        ‖(⨍ z in closedBall x (2 * d) ∩ Ω, f z ∂μ) - ⨍ z in closedBall y d ∩ Ω, f z ∂μ‖ +
        ‖(⨍ z in closedBall y d ∩ Ω, f z ∂μ) - preciseRepresentative (μ.restrict Ω) f y‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ (⨍ z in closedBall y d ∩ Ω, f z ∂μ) _).trans
          (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ C * (M * (2 * d) ^ α) + c * (M * (2 * d) ^ α) + C * (M * d ^ α) := by
        refine add_le_add (add_le_add ?_ ?_) h₂ <;> rw [norm_sub_rev]
        exacts [h₁, h₃]
    _ = (2 ^ α * C + 2 ^ α * c + C) * (M * d ^ α) := by
        rw [Real.mul_rpow zero_le_two hd.le]
        ring
    _ = 2 * 2 ^ α * C * (M * d ^ α) := by
        rw [hCq]
        ring

/-- **Campanato's theorem on a domain.** Let `α > 0` and `A > 0`, and let `Ω` satisfy the measure
density condition `A μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)` for `x ∈ Ω` and `0 < r ≤ D`,
where any two points of `Ω` are at distance at most `D / 2`. If `f` is integrable on `Ω` and its
mean oscillation on `closedBall x r ∩ Ω` is at most `M r^α` for `x ∈ Ω` and `0 < r ≤ D`, then the
precise representative of `f` with respect to `μ.restrict Ω` is `α`-Hölder continuous on `Ω`, with
constant `2 · 2^α · 2ⁿ / (A (1 - 2^(-α))) · M`, where `n` is the dimension. It agrees with `f`
almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_preciseRepresentative_of_hasBesicovitchCovering`). -/
theorem holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le
    {α M : ℝ≥0} {D : ℝ} (hα : 0 < α) (hA : 0 < A) (hf : IntegrableOn f Ω μ)
    (hD : ∀ x ∈ Ω, ∀ y ∈ Ω, 2 * dist x y ≤ D)
    (hdens : ∀ x ∈ Ω, ∀ r, 0 < r → r ≤ D → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ x ∈ Ω, ∀ r, 0 < r → r ≤ D →
      ⨍ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ∂μ ≤
        M * r ^ (α : ℝ)) :
    HolderOnWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / A / (1 - 2 ^ (-(α : ℝ))))) * M) α
      (preciseRepresentative (μ.restrict Ω) f) Ω := by
  have hα' : (0 : ℝ) < α := hα
  have hC : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / A / (1 - 2 ^ (-(α : ℝ)))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (one_sub_two_rpow_neg_pos hα').le)
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  have hxy := hD x hx y hy
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hC, mul_assoc]
  exact dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le hα' hA
    (fun r hr hr' ↦ hdens x hx r hr (hr'.trans hxy))
    (fun r hr hr' ↦ hdens y hy r hr (by linarith [dist_nonneg (x := x) (y := y)]))
    (hf.mono_set inter_subset_right) (fun r hr hr' ↦ hosc x hx r hr (hr'.trans hxy))
    (fun r hr hr' ↦ hosc y hy r hr (by linarith [dist_nonneg (x := x) (y := y)]))

/-- **Campanato's characterization of Hölder continuity on a domain.** Let `α > 0` and `A > 0`, and
let `Ω` satisfy the measure density condition `A μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)` for
`x ∈ Ω` and `0 < r ≤ D`, where any two points of `Ω` are at distance at most `D / 2`. A function
integrable on `Ω` agrees almost everywhere on `Ω` with a function that is `α`-Hölder continuous on
`Ω` if and only if its mean oscillation on `closedBall x r ∩ Ω` is at most `M r^α` for `x ∈ Ω`,
`0 < r ≤ D` and some constant `M`. Here `Ω` is null-measurable, for instance open. -/
theorem exists_holderOnWith_ae_eq_iff_forall_setAverage_norm_sub_le {α : ℝ≥0} {D : ℝ}
    (hα : 0 < α) (hA : 0 < A) (hΩ : NullMeasurableSet Ω μ) (hf : IntegrableOn f Ω μ)
    (hD : ∀ x ∈ Ω, ∀ y ∈ Ω, 2 * dist x y ≤ D)
    (hdens : ∀ x ∈ Ω, ∀ r, 0 < r → r ≤ D → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)) :
    (∃ (K : ℝ≥0) (g : E → F), HolderOnWith K α g Ω ∧ f =ᵐ[μ.restrict Ω] g) ↔
      ∃ M : ℝ≥0, ∀ x ∈ Ω, ∀ r, 0 < r → r ≤ D →
        ⨍ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ∂μ ≤
          M * r ^ (α : ℝ) := by
  constructor
  · rintro ⟨K, g, hg, hfg⟩
    refine ⟨K * 2 ^ (α : ℝ), fun x hx r hr hrD ↦ ?_⟩
    -- On `closedBall x r ∩ Ω` the functions `f` and `g` agree almost everywhere, so they have
    -- the same averages there.
    have hfg' : f =ᵐ[μ.restrict (closedBall x r ∩ Ω)] g :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hfg
    rw [average_congr hfg', average_congr (hfg'.mono fun y hy ↦ by rw [hy])]
    refine (setAverage_norm_sub_setAverage_le_of_holderOnWith
      (measurableSet_closedBall.nullMeasurableSet.inter hΩ) inter_subset_left
      (measure_closedBall_inter_ne_zero hA hr (hdens x hx r hr hrD))
      (measure_ne_top_of_subset inter_subset_left measure_closedBall_lt_top.ne)
      (hg.mono inter_subset_right)
      ((hf.mono_set inter_subset_right).congr_fun_ae hfg')).trans_eq ?_
    push_cast
    rw [Real.mul_rpow zero_le_two hr.le]
    ring
  · rintro ⟨M, hM⟩
    exact ⟨_, _, holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le hα hA hf
      hD hdens hM,
      ae_eq_preciseRepresentative_of_hasBesicovitchCovering hf.integrable.locallyIntegrable⟩

omit [CompleteSpace F] in
/-- An `Lᵖ` bound `∫_{closedBall x r ∩ Ω} ‖f - f_{x,r}‖ᵖ ≤ M r^(n + p α)` on the oscillation of `f`
gives the bound `(M / (A |closedBall 0 1|))^(1/p) r^α` on its mean oscillation, when `Ω` fills
at least the proportion `A` of `closedBall x r`. Here `n` is the dimension and `p ≥ 1`. -/
theorem setAverage_norm_sub_le_of_setLIntegral_enorm_sub_rpow_le {p r : ℝ} (hp : 1 ≤ p)
    (hA : 0 < A) (hM : 0 ≤ M) (hr : 0 < r)
    (hdens : A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∫⁻ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal (M * r ^ (finrank ℝ E + p * α))) :
    ⨍ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ ∂μ ≤
      (M / (A * μ.real (closedBall (0 : E) 1))) ^ p⁻¹ * r ^ α := by
  set s := closedBall x r ∩ Ω
  set a := ⨍ y in s, ‖f y - ⨍ z in s, f z ∂μ‖ ∂μ
  have hp0 : 0 < p := one_pos.trans_le hp
  have ha : 0 ≤ a := average_nonneg fun _ ↦ norm_nonneg _
  have hs0 : μ s ≠ 0 := measure_closedBall_inter_ne_zero hA hr hdens
  have hAB : 0 < (A : ℝ) * μ.real (closedBall x r) := mul_pos (by exact_mod_cast hA)
    (ENNReal.toReal_pos (measure_closedBall_pos μ x hr).ne' measure_closedBall_lt_top.ne)
  have hB : 0 < μ.real (closedBall (0 : E) 1) :=
    ENNReal.toReal_pos (measure_closedBall_pos μ 0 one_pos).ne' measure_closedBall_lt_top.ne
  -- Hölder's inequality bounds the `p`-th power of the mean oscillation by the average of
  -- `‖f - f_{x,r}‖ᵖ`, and the measure density condition bounds the measure of `s` from below.
  have h₁ : ‖a‖ₑ ^ p ≤ (μ s)⁻¹ * ENNReal.ofReal (M * r ^ (finrank ℝ E + p * α)) := by
    refine (enorm_setAverage_rpow_le (f := fun y ↦ ‖f y - ⨍ z in s, f z ∂μ‖) hp).trans ?_
    simp only [enorm_norm]
    gcongr
  have h₂ := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hs0) ENNReal.ofReal_ne_top) h₁
  rw [← ENNReal.toReal_rpow, toReal_enorm, Real.norm_of_nonneg ha, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), ← measureReal_def] at h₂
  have hpow : a ^ p ≤ M / (A * μ.real (closedBall (0 : E) 1)) * r ^ (p * α) :=
    calc a ^ p ≤ (μ.real s)⁻¹ * (M * r ^ (finrank ℝ E + p * α)) := h₂
      _ ≤ ((A : ℝ) * μ.real (closedBall x r))⁻¹ * (M * r ^ (finrank ℝ E + p * α)) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hAB (mul_measureReal_closedBall_le hdens))
            (by positivity)
      _ = M / (A * μ.real (closedBall (0 : E) 1)) * r ^ (p * α) := by
          rw [μ.addHaar_real_closedBall' x hr.le, Real.rpow_add hr, Real.rpow_natCast]
          field_simp
  calc a = (a ^ p) ^ p⁻¹ := (Real.rpow_rpow_inv ha hp0.ne').symm
    _ ≤ (M / (A * μ.real (closedBall (0 : E) 1)) * r ^ (p * α)) ^ p⁻¹ :=
        Real.rpow_le_rpow (by positivity) hpow (inv_nonneg.2 hp0.le)
    _ = (M / (A * μ.real (closedBall (0 : E) 1))) ^ p⁻¹ * r ^ α := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr.le,
          mul_comm p, mul_inv_cancel_right₀ hp0.ne']

/-- **Campanato's theorem on a domain, in `Lᵖ` form.** Let `α > 0`, `p ≥ 1` and `A > 0`, and let
`Ω` satisfy the measure density condition `A μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)` for
`x ∈ Ω` and `0 < r ≤ D`, where any two points of `Ω` are at distance at most `D / 2`. If `f` is
integrable on `Ω` and `∫_{closedBall x r ∩ Ω} ‖f - f_{x,r}‖ᵖ ≤ M r^λ` for `x ∈ Ω` and
`0 < r ≤ D`, where `λ = n + p α` and `n` is the dimension, then the precise representative of `f`
with respect to `μ.restrict Ω` is `α`-Hölder continuous on `Ω`. In the language of Campanato
spaces, `𝓛^{p,λ}(Ω) ⊆ C^{0,α}(Ω)` for `λ > n`, with `α = (λ - n) / p`. The Hölder constant is
`2 · 2^α · 2ⁿ / (A (1 - 2^(-α))) · (M / (A |closedBall 0 1|))^(1/p)`. -/
theorem holderOnWith_preciseRepresentative_restrict_of_setLIntegral_enorm_sub_rpow_le
    {α M : ℝ≥0} {p D : ℝ} (hα : 0 < α) (hp : 1 ≤ p) (hA : 0 < A) (hf : IntegrableOn f Ω μ)
    (hD : ∀ x ∈ Ω, ∀ y ∈ Ω, 2 * dist x y ≤ D)
    (hdens : ∀ x ∈ Ω, ∀ r, 0 < r → r ≤ D → A * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ x ∈ Ω, ∀ r, 0 < r → r ≤ D →
      ∫⁻ y in closedBall x r ∩ Ω, ‖f y - ⨍ z in closedBall x r ∩ Ω, f z ∂μ‖ₑ ^ p ∂μ ≤
        ENNReal.ofReal (M * r ^ (finrank ℝ E + p * α))) :
    HolderOnWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / A / (1 - 2 ^ (-(α : ℝ))))) *
      Real.toNNReal ((M / (A * μ.real (closedBall (0 : E) 1))) ^ p⁻¹)) α
      (preciseRepresentative (μ.restrict Ω) f) Ω := by
  refine holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le hα hA hf hD hdens
    fun x hx r hr hrD ↦ ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  exact setAverage_norm_sub_le_of_setLIntegral_enorm_sub_rpow_le hp hA M.coe_nonneg hr
    (hdens x hx r hr hrD) (hosc x hx r hr hrD)

/-! ### Campanato's theorem on the whole space

These are the statements on a domain for `Ω = univ`, which satisfies the measure density condition
with `A = 1` at every radius. -/

/-- **Mean oscillation decay gives convergence of the averages.** Let `α > 0` and `ρ > 0`. If `f`
is integrable on `closedBall x ρ` and its mean oscillation on `closedBall x r` is at most `M r^α`
for `0 < r ≤ ρ`, then the averages of `f` over the closed balls around `x` converge to the
precise representative of `f` at `x`. -/
theorem tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le
    (hα : 0 < α) (hρ : 0 < ρ) (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := by
  simpa only [inter_univ, Measure.restrict_univ] using
    tendsto_setAverage_closedBall_inter_preciseRepresentative_restrict_of_setAverage_norm_sub_le
      (Ω := univ) hα hρ one_pos (fun _ _ _ ↦ by simp)
      (by rwa [inter_univ]) (by simpa only [inter_univ] using hosc)

/-- **The rate of convergence of the averages.** Let `α > 0`. If `f` is integrable on
`closedBall x ρ` and its mean oscillation on `closedBall x r` is at most `M r^α` for
`0 < r ≤ ρ`, then for `0 < r ≤ ρ` the average of `f` over `closedBall x r` lies within
`2ⁿ / (1 - 2^(-α)) · M r^α` of the precise representative of `f` at `x`, where `n` is the
dimension. -/
theorem norm_setAverage_closedBall_sub_preciseRepresentative_le (hα : 0 < α)
    (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x r, f y ∂μ) - preciseRepresentative μ f x‖ ≤
      2 ^ finrank ℝ E / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  simpa only [inter_univ, Measure.restrict_univ, NNReal.coe_one, div_one] using
    norm_setAverage_closedBall_inter_sub_preciseRepresentative_restrict_le (Ω := univ) hα one_pos
      (fun _ _ _ ↦ by simp) (by rwa [inter_univ])
      (by simpa only [inter_univ] using hosc) hr hrρ

/-- **The local Campanato estimate.** Let `α > 0` and `d = dist x y`. If `f` has mean oscillation
at most `M r^α` on `closedBall x r` for `0 < r ≤ 2 d` and on `closedBall y r` for `0 < r ≤ d`,
and is integrable on `closedBall x (2 d)`, then the precise representatives of `f` at `x`
and `y` differ by at most `2 · 2^α · 2ⁿ / (1 - 2^(-α)) · M d^α`, where `n` is the dimension. -/
theorem dist_preciseRepresentative_le_of_setAverage_norm_sub_le {y : E}
    (hα : 0 < α) (hf : IntegrableOn f (closedBall x (2 * dist x y)) μ)
    (hoscx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w ∂μ‖ ∂μ ≤ M * r ^ α)
    (hoscy : ∀ r, 0 < r → r ≤ dist x y →
      ⨍ z in closedBall y r, ‖f z - ⨍ w in closedBall y r, f w ∂μ‖ ∂μ ≤ M * r ^ α) :
    dist (preciseRepresentative μ f x) (preciseRepresentative μ f y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / (1 - 2 ^ (-α))) * (M * dist x y ^ α) := by
  simpa only [inter_univ, Measure.restrict_univ, NNReal.coe_one, div_one] using
    dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le (Ω := univ) hα one_pos
      (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp) (by rwa [inter_univ])
      (by simpa only [inter_univ] using hoscx) (by simpa only [inter_univ] using hoscy)

/-- **Campanato's theorem.** Let `α > 0`, and let `f` be locally integrable, with mean oscillation
on every closed ball of radius `r > 0` at most `M r^α`. Then the precise representative of `f`
is `α`-Hölder continuous, with constant `2 · 2^α · 2ⁿ / (1 - 2^(-α)) · M`, where `n` is the
dimension. It agrees with `f` almost everywhere
(`TauCeti.MeasureTheory.ae_eq_preciseRepresentative`). -/
theorem holderWith_preciseRepresentative_of_setAverage_norm_sub_le
    {α M : ℝ≥0} (hα : 0 < α) (hf : LocallyIntegrable f μ)
    (hosc : ∀ x r, 0 < r →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ)) :
    HolderWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ))))) * M) α (preciseRepresentative μ f) := by
  have hα' : (0 : ℝ) < α := hα
  have hC : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ)))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (one_sub_two_rpow_neg_pos hα').le)
  refine holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hC, mul_assoc]
  exact dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα'
    (hf.integrableOn_isCompact (isCompact_closedBall _ _)) (fun r hr _ ↦ hosc x r hr)
    (fun r hr _ ↦ hosc y r hr)

/-- **Campanato's characterization of Hölder continuity.** Let `α > 0`. A locally integrable
function agrees almost everywhere with an `α`-Hölder continuous function if and only if its mean
oscillation on closed balls of radius `r > 0` is at most `M r^α` for some constant `M`. -/
theorem exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le {α : ℝ≥0}
    (hα : 0 < α) (hf : LocallyIntegrable f μ) :
    (∃ (K : ℝ≥0) (g : E → F), HolderWith K α g ∧ f =ᵐ[μ] g) ↔
      ∃ M : ℝ≥0, ∀ x r, 0 < r →
        ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ) := by
  constructor
  · rintro ⟨K, g, hg, hfg⟩
    refine ⟨K * 2 ^ (α : ℝ), fun x r hr ↦ ?_⟩
    -- The averages of `f` and `g` over every ball agree.
    have havg : ⨍ z in closedBall x r, f z ∂μ = ⨍ z in closedBall x r, g z ∂μ :=
      average_congr (ae_restrict_of_ae hfg)
    rw [havg, average_congr (ae_restrict_of_ae (hfg.mono fun y hy ↦ by rw [hy]))]
    refine (setAverage_norm_sub_setAverage_le_of_holderOnWith
      measurableSet_closedBall.nullMeasurableSet subset_rfl
      (measure_closedBall_pos μ x hr).ne' measure_closedBall_lt_top.ne (hg.holderOnWith _)
      ((hf.integrableOn_isCompact (isCompact_closedBall x r)).congr_fun_ae
        (ae_restrict_of_ae hfg))).trans_eq ?_
    push_cast
    rw [Real.mul_rpow zero_le_two hr.le]
    ring
  · rintro ⟨M, hM⟩
    exact ⟨_, _, holderWith_preciseRepresentative_of_setAverage_norm_sub_le hα hf hM,
      ae_eq_preciseRepresentative hf⟩

end MeasureTheory

end TauCeti
