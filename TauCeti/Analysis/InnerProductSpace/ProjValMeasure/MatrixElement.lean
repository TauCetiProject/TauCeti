/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Variation
public import TauCeti.MeasureTheory.VectorMeasure.WithDensity
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity

/-!
# Matrix elements of the integral against a projection-valued measure

Let `P` be a projection-valued measure on `X` acting on a complex Hilbert space `H`. For vectors
`ψ ξ : H`, the polarized complex measure `μ_(ψ,ξ) = P.polarizedComplexMeasure ψ ξ` takes the value
`⟪ψ, P(B) ξ⟫` on a measurable set `B`, and has finite variation. This file identifies the matrix
elements of the operator integral `P.integral f = ∫ f dP` of a bounded Borel symbol `f` with
Mathlib's integral against this complex measure, through the multiplication pairing `ℂ × ℂ → ℂ`:

`⟪ψ, (∫ f dP) ξ⟫ = ∫ᵛ x, f x ∂[mul ℝ ℂ; μ_(ψ,ξ)]`.

So the operator integral is determined by scalar integration against the polarized measures, and
the scalar integration theory of complex measures applies to its matrix elements.

Acting on `ξ` or `ψ` by a bounded operator integral multiplies the polarized and diagonal measures
by the corresponding symbol density (`polarizedComplexMeasure_integral_right`,
`polarizedComplexMeasure_integral_left`, `diag_integral`), and combining this with the sharp
total-variation bound gives the Cauchy–Schwarz inequality for Lebesgue integration
against `|μ_(ψ,ξ)|` (`lintegral_mul_polarizedComplexMeasure_variation_sq_le`).

On the diagonal, the variation of the polarized measure `μ_(ξ,ξ)` is the finite positive measure
`P.diag ξ` (`variation_polarizedComplexMeasure_self`), and integrating any complex function
against `μ_(ξ,ξ)` gives the Bochner integral against `P.diag ξ`.

## Main declarations

* `ProjValMeasure.integral_polarizedComplexMeasure_eq_inner_integral`: the matrix element
  `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against `μ_(ψ,ξ)`.
* `ProjValMeasure.integral_polarizedComplexMeasure_self`: integration of any `f : X → ℂ` against
  `μ_(ξ,ξ)` is the Bochner integral against `P.diag ξ`.
* `ProjValMeasure.diag_integral`, `ProjValMeasure.polarizedComplexMeasure_integral_right`,
  `ProjValMeasure.polarizedComplexMeasure_integral_left`,
  `ProjValMeasure.polarizedComplexMeasure_integral_integral`: densities of diagonal and polarized
  measures after applying bounded spectral integrals.
* `ProjValMeasure.lintegral_mul_polarizedComplexMeasure_variation_sq_le` and
  `ProjValMeasure.lintegral_polarizedComplexMeasure_variation_sq_le`: Cauchy–Schwarz inequalities
  bounding integrals against `|μ_(ψ,ξ)|` by `L²` integrals against `P.diag ψ` and `P.diag ξ`.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 12.21.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The matrix element of the integral of a simple symbol is its integral against the polarized
measure. -/
private theorem integral_polarizedComplexMeasure_ofSimpleFunc (P : ProjValMeasure X H)
    (s : SimpleFunc X ℂ) (ψ ξ : H) :
    ∫ᵛ x, s x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ] =
      ⟪ψ, P.integral (BoundedBorelFunction.ofSimpleFunc s) ξ⟫_ℂ := by
  induction s using SimpleFunc.induction with
  | @const c B hB =>
    have hs : ⇑(SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        B.indicator fun _ => c := by
      ext x
      by_cases hx : x ∈ B <;> simp [SimpleFunc.piecewise_apply, hx]
    have h : BoundedBorelFunction.ofSimpleFunc
        (SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
          c • BoundedBorelFunction.indicator B hB 1 := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [hs, VectorMeasure.integral_indicator_const _ hB, h]
    simp [integral_indicator, inner_smul_right, polarizedComplexMeasure_apply _ _ _ _ hB]
  | @add s t _ hs ht =>
    rw [FunLike.coe_add, VectorMeasure.integral_add (SimpleFunc.integrable_of_isFiniteMeasure s)
      (SimpleFunc.integrable_of_isFiniteMeasure t), hs, ht]
    simp [inner_add_right]

/-- **Matrix elements of the integral against a projection-valued measure.** For a bounded Borel
symbol `f`, `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against the polarized complex measure
`μ_(ψ,ξ)`, whose value on a measurable set `B` is `⟪ψ, P(B) ξ⟫`, through the multiplication
pairing. -/
theorem integral_polarizedComplexMeasure_eq_inner_integral (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) (ψ ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ] =
      ⟪ψ, P.integral f ξ⟫_ℂ := by
  obtain ⟨s, hs_le, hs⟩ := BoundedBorelFunction.exists_seq_tendsto_ofSimpleFunc f
  have hcont : Continuous fun g => ⟪ψ, P.integral g ξ⟫_ℂ :=
    continuous_const.inner ((ContinuousLinearMap.apply ℂ H ξ).continuous.comp
      P.continuous_integral)
  refine tendsto_nhds_unique (l := atTop)
    (f := fun n => ∫ᵛ x, s n x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ])
    ?_ (((hcont.tendsto f).comp hs).congr fun n => ?_)
  · -- Dominated convergence, with the constant bound `‖f‖` and pointwise convergence.
    refine VectorMeasure.tendsto_integral_filter_of_norm_le_const
      (Eventually.of_forall fun n => (s n).aestronglyMeasurable)
      ⟨‖f‖, Eventually.of_forall fun n => Eventually.of_forall (hs_le n)⟩
      (Eventually.of_forall fun x => ?_)
    rw [BoundedBorelFunction.tendsto_iff_tendstoUniformly] at hs
    simpa using hs.tendsto_at x
  · exact (P.integral_polarizedComplexMeasure_ofSimpleFunc (s n) ψ ξ).symm

/-- Integration of a complex function against the diagonal polarized measure through the
multiplication pairing is the Bochner integral against the diagonal measure. Both sides vanish
when `f` is not integrable, since the variation of the polarized measure is the diagonal
measure. -/
@[simp]
theorem integral_polarizedComplexMeasure_self (P : ProjValMeasure X H) (f : X → ℂ) (ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ξ ξ] =
      ∫ x, f x ∂(P.diag ξ) := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ, VectorMeasure.integral_mul_withDensityᵥ_one]

/-- Applying `P.integral g` to `ξ` weights its diagonal measure by `‖g x‖ₑ ^ 2`. -/
theorem diag_integral (P : ProjValMeasure X H) (g : BoundedBorelFunction X) (ξ : H) :
    P.diag (P.integral g ξ) = (P.diag ξ).withDensity fun x => ‖g x‖ₑ ^ 2 := by
  ext B hB
  have hmul : BoundedBorelFunction.indicator B hB 1 * g =
      BoundedBorelFunction.indicator B hB g := by
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hind : P.proj B hB (P.integral g ξ) =
      P.integral (BoundedBorelFunction.indicator B hB g) ξ := by
    rw [← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul, hmul]
  have hint : Integrable (fun x => ‖g x‖ ^ 2) (P.diag ξ) :=
    .of_bound (g.measurable.norm.pow_const 2).aestronglyMeasurable (‖g‖ ^ 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (g.norm_coe_le_norm x) 2)
  have hnorm_ind : (fun x => ‖(BoundedBorelFunction.indicator B hB g) x‖ ^ 2) =
      B.indicator fun x => ‖g x‖ ^ 2 := by
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [← P.enorm_sq_proj_apply B hB, hind, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    P.norm_sq_integral_apply, hnorm_ind, MeasureTheory.integral_indicator hB,
    ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _),
    withDensity_apply _ hB]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Applying `P.integral g` in the right slot of `P.polarizedComplexMeasure` weights the polarized
complex measure by `g`. -/
theorem polarizedComplexMeasure_integral_right (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure ψ (P.integral g ξ) =
      (P.polarizedComplexMeasure ψ ξ).withDensity g (ContinuousLinearMap.mul ℝ ℂ) := by
  have hg : (P.polarizedComplexMeasure ψ ξ).Integrable g := g.integrable _
  ext B hB
  have hmul : BoundedBorelFunction.indicator B hB 1 * g =
      BoundedBorelFunction.indicator B hB g := by
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [P.polarizedComplexMeasure_apply _ _ B hB, ← P.integral_indicator hB,
    ← mul_apply_eq_comp, ← map_mul, hmul,
    ← P.integral_polarizedComplexMeasure_eq_inner_integral,
    VectorMeasure.withDensity_apply hg, BoundedBorelFunction.coe_indicator,
    VectorMeasure.integral_indicator hB]

/-- Applying `P.integral g` in the left slot of `P.polarizedComplexMeasure` weights the polarized
complex measure by `star g`, reflecting conjugate linearity in the first slot. -/
theorem polarizedComplexMeasure_integral_left (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure (P.integral g ψ) ξ =
      (P.polarizedComplexMeasure ψ ξ).withDensity (star g) (ContinuousLinearMap.mul ℝ ℂ) := by
  ext B hB
  have hadj : ⟪P.integral g ψ, P.proj B hB ξ⟫_ℂ =
      ⟪ψ, P.proj B hB (P.integral (star g) ξ)⟫_ℂ := by
    calc
      ⟪P.integral g ψ, P.proj B hB ξ⟫_ℂ
          = ⟪ψ, (P.integral g).adjoint
              (P.integral (BoundedBorelFunction.indicator B hB 1) ξ)⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_right, P.integral_indicator hB]
      _ = ⟪ψ, P.proj B hB (P.integral (star g) ξ)⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← mul_apply_eq_comp,
          ← map_mul, mul_comm, map_mul, mul_apply_eq_comp, P.integral_indicator hB]
  rw [P.polarizedComplexMeasure_apply _ _ B hB, hadj,
    ← P.polarizedComplexMeasure_apply _ _ B hB,
    P.polarizedComplexMeasure_integral_right (star g) ψ ξ, BoundedBorelFunction.coe_star]

/-- Applying `P.integral g` on the left and `P.integral h` on the right weights
`P.polarizedComplexMeasure ψ ξ` by `star g * h`. -/
theorem polarizedComplexMeasure_integral_integral (P : ProjValMeasure X H)
    (g h : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure (P.integral g ψ) (P.integral h ξ) =
      (P.polarizedComplexMeasure ψ ξ).withDensity (star g * h) (ContinuousLinearMap.mul ℝ ℂ) := by
  rw [P.polarizedComplexMeasure_integral_left, P.polarizedComplexMeasure_integral_right,
    VectorMeasure.withDensity_withDensity_mul (h.integrable _)]
  rfl

/-- **Cauchy–Schwarz inequality** for Lebesgue integration against the variation of a polarized
spectral measure: for measurable `g, h : X → ℝ≥0∞`,
`(∫⁻ x, g x * h x ∂|μ_(ψ,ξ)|) ^ 2 ≤ (∫⁻ x, g x ^ 2 ∂(P.diag ψ)) * (∫⁻ x, h x ^ 2 ∂(P.diag ξ))`. -/
theorem lintegral_mul_polarizedComplexMeasure_variation_sq_le (P : ProjValMeasure X H) (ψ ξ : H)
    {g h : X → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ x, g x * h x ∂(P.polarizedComplexMeasure ψ ξ).variation) ^ 2 ≤
      (∫⁻ x, g x ^ 2 ∂(P.diag ψ)) * (∫⁻ x, h x ^ 2 ∂(P.diag ξ)) := by
  -- Truncate `g` and `h` at height `n`, realize them as bounded Borel symbols, and apply the
  -- sharp total-variation bound to `P.integral (G n) ψ` and `P.integral (H n) ξ`.
  let G : ℕ → BoundedBorelFunction X := fun n =>
    BoundedBorelFunction.ofFunction (fun x => (((min (g x) n).toReal : ℝ) : ℂ))
      (Complex.continuous_ofReal.measurable.comp (hg.min measurable_const).ennreal_toReal)
      ⟨n, Nat.cast_nonneg n, fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg n)
          ((min_le_right _ _).trans_eq (ENNReal.ofReal_natCast n).symm)⟩
  let Hn : ℕ → BoundedBorelFunction X := fun n =>
    BoundedBorelFunction.ofFunction (fun x => (((min (h x) n).toReal : ℝ) : ℂ))
      (Complex.continuous_ofReal.measurable.comp (hh.min measurable_const).ennreal_toReal)
      ⟨n, Nat.cast_nonneg n, fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg n)
          ((min_le_right _ _).trans_eq (ENNReal.ofReal_natCast n).symm)⟩
  have hG_enorm (n : ℕ) (x : X) : ‖G n x‖ₑ = min (g x) n := by
    rw [← ofReal_norm, BoundedBorelFunction.ofFunction_apply, Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal ((min_le_right _ _).trans_lt (ENNReal.natCast_lt_top n)).ne
  have hH_enorm (n : ℕ) (x : X) : ‖Hn n x‖ₑ = min (h x) n := by
    rw [← ofReal_norm, BoundedBorelFunction.ofFunction_apply, Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal ((min_le_right _ _).trans_lt (ENNReal.natCast_lt_top n)).ne
  have hstep (n : ℕ) :
      (∫⁻ x, min (g x) n * min (h x) n ∂(P.polarizedComplexMeasure ψ ξ).variation) ^ 2 ≤
        (∫⁻ x, g x ^ 2 ∂(P.diag ψ)) * (∫⁻ x, h x ^ 2 ∂(P.diag ξ)) := by
    have hvar :
        ∫⁻ x, min (g x) n * min (h x) n ∂(P.polarizedComplexMeasure ψ ξ).variation =
          (P.polarizedComplexMeasure (P.integral (G n) ψ) (P.integral (Hn n) ξ)).variation
            Set.univ := by
      rw [P.polarizedComplexMeasure_integral_integral,
        VectorMeasure.variation_withDensity_mul ((star (G n) * Hn n).integrable _),
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine lintegral_congr fun x => ?_
      rw [BoundedBorelFunction.mul_apply, BoundedBorelFunction.star_apply, eNorm_mul,
        ← ofReal_norm, norm_star, ofReal_norm, hG_enorm, hH_enorm]
    have hle1 :
        (P.polarizedComplexMeasure (P.integral (G n) ψ) (P.integral (Hn n) ξ)).variation
            Set.univ ≤
          ‖P.integral (G n) ψ‖ₑ * ‖P.integral (Hn n) ξ‖ₑ := by
      refine (P.polarizedComplexMeasure_variation_univ_le _ _).trans_eq ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    have hnormG : ‖P.integral (G n) ψ‖ₑ ^ 2 = ∫⁻ x, (min (g x) n) ^ 2 ∂(P.diag ψ) := by
      rw [← P.diag_univ (P.integral (G n) ψ), P.diag_integral,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_congr fun x => by rw [hG_enorm]
    have hnormH : ‖P.integral (Hn n) ξ‖ₑ ^ 2 = ∫⁻ x, (min (h x) n) ^ 2 ∂(P.diag ξ) := by
      rw [← P.diag_univ (P.integral (Hn n) ξ), P.diag_integral,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_congr fun x => by rw [hH_enorm]
    calc
      (∫⁻ x, min (g x) n * min (h x) n ∂(P.polarizedComplexMeasure ψ ξ).variation) ^ 2
          ≤ (‖P.integral (G n) ψ‖ₑ * ‖P.integral (Hn n) ξ‖ₑ) ^ 2 := by
        rw [hvar]
        exact pow_le_pow_left' hle1 2
      _ = ‖P.integral (G n) ψ‖ₑ ^ 2 * ‖P.integral (Hn n) ξ‖ₑ ^ 2 := mul_pow _ _ 2
      _ = (∫⁻ x, (min (g x) n) ^ 2 ∂(P.diag ψ)) * (∫⁻ x, (min (h x) n) ^ 2 ∂(P.diag ξ)) := by
        rw [hnormG, hnormH]
      _ ≤ (∫⁻ x, g x ^ 2 ∂(P.diag ψ)) * (∫⁻ x, h x ^ 2 ∂(P.diag ξ)) :=
        mul_le_mul' (lintegral_mono fun x => pow_le_pow_left' (min_le_left _ _) 2)
          (lintegral_mono fun x => pow_le_pow_left' (min_le_left _ _) 2)
  have hmono : Monotone fun (n : ℕ) x => min (g x) n * min (h x) n := fun m n hmn x =>
    mul_le_mul' (min_le_min_left _ (Nat.cast_le.mpr hmn))
      (min_le_min_left _ (Nat.cast_le.mpr hmn))
  have hsup (x : X) : (⨆ n : ℕ, min (g x) n * min (h x) n) = g x * h x := by
    rcases eq_or_ne (g x) 0 with hgx | hgx
    · simp [hgx]
    rcases eq_or_ne (h x) 0 with hhx | hhx
    · simp [hhx]
    have htendG : Tendsto (fun n : ℕ => min (g x) n) atTop (𝓝 (g x)) := by
      rcases eq_or_ne (g x) ∞ with htop | htop
      · simpa [htop] using ENNReal.tendsto_nat_nhds_top
      · lift g x to ℝ≥0 using htop with gx
        obtain ⟨N, hN⟩ := exists_nat_ge gx
        exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn =>
          (min_eq_left (ENNReal.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn)))).symm⟩)
    have htendH : Tendsto (fun n : ℕ => min (h x) n) atTop (𝓝 (h x)) := by
      rcases eq_or_ne (h x) ∞ with htop | htop
      · simpa [htop] using ENNReal.tendsto_nat_nhds_top
      · lift h x to ℝ≥0 using htop with hx'
        obtain ⟨N, hN⟩ := exists_nat_ge hx'
        exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn =>
          (min_eq_left (ENNReal.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn)))).symm⟩)
    exact tendsto_nhds_unique
      (tendsto_atTop_iSup fun m n hmn => hmono hmn x)
      (ENNReal.Tendsto.mul htendG (Or.inl hgx) htendH (Or.inl hhx))
  have hmeas (n : ℕ) : Measurable fun x => min (g x) n * min (h x) n :=
    (hg.min measurable_const).mul (hh.min measurable_const)
  have hiSup : ∫⁻ x, g x * h x ∂(P.polarizedComplexMeasure ψ ξ).variation =
      ⨆ n : ℕ, ∫⁻ x, min (g x) n * min (h x) n ∂(P.polarizedComplexMeasure ψ ξ).variation := by
    rw [← lintegral_iSup hmeas hmono]
    exact lintegral_congr fun x => (hsup x).symm
  rcases eq_or_ne (∫⁻ x, g x * h x ∂(P.polarizedComplexMeasure ψ ξ).variation) 0 with h0 | h0
  · simp [h0]
  have htend₀ :
      Tendsto (fun n : ℕ =>
          ∫⁻ x, min (g x) n * min (h x) n ∂(P.polarizedComplexMeasure ψ ξ).variation)
        atTop (𝓝 (∫⁻ x, g x * h x ∂(P.polarizedComplexMeasure ψ ξ).variation)) := by
    rw [hiSup]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono (hmono hmn)
  have htend :
      Tendsto (fun n : ℕ =>
          (∫⁻ x, min (g x) n * min (h x) n ∂(P.polarizedComplexMeasure ψ ξ).variation) ^ 2)
        atTop (𝓝 ((∫⁻ x, g x * h x ∂(P.polarizedComplexMeasure ψ ξ).variation) ^ 2)) := by
    simpa only [sq] using ENNReal.Tendsto.mul htend₀ (Or.inl h0) htend₀ (Or.inl h0)
  exact le_of_tendsto' htend hstep

/-- One-vector **Cauchy–Schwarz inequality** for Lebesgue integration against the variation of a
polarized spectral measure:
`(∫⁻ x, h x ∂|μ_(ψ,ξ)|) ^ 2 ≤ ‖ψ‖ₑ ^ 2 * ∫⁻ x, h x ^ 2 ∂(P.diag ξ)`. -/
theorem lintegral_polarizedComplexMeasure_variation_sq_le (P : ProjValMeasure X H) (ψ ξ : H)
    {h : X → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ x, h x ∂(P.polarizedComplexMeasure ψ ξ).variation) ^ 2 ≤
      ‖ψ‖ₑ ^ 2 * ∫⁻ x, h x ^ 2 ∂(P.diag ξ) := by
  simpa [P.diag_univ ψ] using
    P.lintegral_mul_polarizedComplexMeasure_variation_sq_le ψ ξ
      (measurable_const : Measurable fun _ : X => (1 : ℝ≥0∞)) hh

end ProjValMeasure
end TauCeti
