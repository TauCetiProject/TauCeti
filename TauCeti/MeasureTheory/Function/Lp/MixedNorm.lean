/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Mixed norms of `L²`-valued functions

Let `Φ : β → L²(X, μ)` be a family of square integrable functions, for instance the orbit
`t ↦ U(t) f` of a unitary group. Its mixed norm `L^q_b L^r_x` is

`‖Φ‖_{L^q L^r} = ‖b ↦ ‖Φ b‖_{L^r(μ)}‖_{L^q(ρ)}`,

which is meaningful because `b ↦ ‖Φ b‖_{L^r(μ)}` is measurable
(`MeasureTheory.AEStronglyMeasurable.aemeasurable_eLpNorm_Lp`). For Hölder conjugate pairs
`(q, q')` and `(r, r')`, Hölder's inequality in `x` and then in `b` bounds the pairings
`∫ ⟪Φ b, G b⟫ dρ` by `‖Φ‖_{L^q L^r} ‖G‖_{L^{q'} L^{r'}}`.

This file proves the testing step of the converse bound
(`MeasureTheory.eLpNorm_le_of_enorm_rpow_le_re_inner`): for `f ∈ L^q(ρ)` with `q < ∞`, a test
function `G` with `‖f b‖ ^ q ≤ re ⟪Φ b, G b⟫` and `‖G b‖_{r'} ≤ ‖f b‖ ^ (q - 1)` turns a bound
`|∫ ⟪Φ b, G b⟫ dρ| ≤ M ‖G‖_{L^{q'} L^{r'}}` into `‖f‖_q ≤ M`. The converse bound itself, at all
exponents, is proved in `TauCeti.MeasureTheory.Function.Lp.MixedNorm.Bounded`.

The file also records four elementary properties of mixed norms of families of `Lᵖ` functions:
Minkowski's inequality `‖Φ + Ψ‖_{L^q L^r} ≤ ‖Φ‖_{L^q L^r} + ‖Ψ‖_{L^q L^r}` for `1 ≤ q, r`
(`MeasureTheory.eLpNorm_eLpNorm_add_le`), the bound `‖T ∘ Φ‖_{L^q L^s} ≤ K ‖Φ‖_{L^q L^r}` for a
continuous map `T` of `Lᵖ` spaces with `‖T f‖_s ≤ K ‖f‖_r`
(`MeasureTheory.eLpNorm_eLpNorm_apply_le`), the identity
`‖T ∘ (1_s Φ)‖_{L^q(ρ) L^r} = ‖T ∘ Φ‖_{L^q(ρ|_s) L^r}` for a map `T` with `T 0 = 0`
(`MeasureTheory.eLpNorm_eLpNorm_apply_indicator`), and invariance under the reflection `b ↦ -b` of
the parameter when `ρ` is invariant under negation (`ρ.IsNegInvariant`), as Lebesgue measure on the
time line is (`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_comp_neg`); the latter reverses
time in such estimates.

A family `u : β → Lᵖ(μ)` representing an element `Φ` of the Bochner space `L^q(ρ; L^r(μ))` has
mixed norm `‖u‖_{L^q L^r} = ‖Φ‖` (`MeasureTheory.eLpNorm_eLpNorm_eq_eNorm_of_ae_eq`), so bounds in
mixed norms of `L²`-valued families are bounds in the Bochner norm.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.14 (norming `Lᵖ` by test functions).
* A. Benedek and R. Panzone, *The space `Lᴾ`, with mixed norm*, Duke Math. J. 28 (1961), 301–324.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MeasureTheory

variable {β X 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {mβ : MeasurableSpace β} {ρ : Measure β} {mX : MeasurableSpace X} {μ : Measure X}

/-! ### The testing step -/

/-- **The testing step for mixed norms.** Let `f ∈ L^q(ρ)` with `q < ∞`, and let `G` be a test
function with integrable pairing such that `‖f b‖ ^ q ≤ re ⟪Φ b, G b⟫` almost everywhere and
`‖G b‖_{r'} ≤ ‖f b‖ ^ (q - 1)`. If `|∫ ⟪Φ b, G b⟫ dρ| ≤ M ‖G‖_{L^{q'} L^{r'}}`, then
`‖f‖_q ^ q ≤ M ‖f‖_q ^ (q - 1)`, so `‖f‖_q ≤ M`. -/
theorem eLpNorm_le_of_enorm_rpow_le_re_inner {q q' r' : ℝ≥0∞} [q.HolderConjugate q']
    (hq : q ≠ ∞) {Φ G : β → Lp E 2 μ} {M : ℝ≥0∞} {f : β → ℝ} (hf : MemLp f q ρ)
    (hG : AEStronglyMeasurable G ρ) (hpair : Integrable (fun b ↦ ⟪Φ b, G b⟫_𝕜) ρ)
    (hre : ∀ᵐ b ∂ρ, 0 ≤ RCLike.re ⟪Φ b, G b⟫_𝕜)
    (hle : ∀ᵐ b ∂ρ, ‖f b‖ₑ ^ q.toReal ≤ ENNReal.ofReal (RCLike.re ⟪Φ b, G b⟫_𝕜))
    (hGf : ∀ b, eLpNorm (G b) r' μ ≤ ‖‖f b‖ ^ (q.toReal - 1)‖ₑ)
    (hM : ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ) :
    eLpNorm f q ρ ≤ M := by
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q q'
  refine ENNReal.le_of_rpow_le_mul_rpow_sub_one (r := q.toReal) hf.eLpNorm_ne_top ?_
  calc eLpNorm f q ρ ^ q.toReal = ∫⁻ b, ‖f b‖ₑ ^ q.toReal ∂ρ :=
        (lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf.aestronglyMeasurable).symm
    _ ≤ ∫⁻ b, ENNReal.ofReal (RCLike.re ⟪Φ b, G b⟫_𝕜) ∂ρ := lintegral_mono_ae hle
    _ = ENNReal.ofReal (∫ b, RCLike.re ⟪Φ b, G b⟫_𝕜 ∂ρ) :=
        (ofReal_integral_eq_lintegral_ofReal hpair.re hre).symm
    _ ≤ ‖∫ b, ⟪Φ b, G b⟫_𝕜 ∂ρ‖ₑ := by
        rw [integral_re hpair, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
    _ ≤ M * eLpNorm (fun b ↦ eLpNorm (G b) r' μ) q' ρ := hM
    _ ≤ M * eLpNorm (fun b ↦ ‖f b‖ ^ (q.toReal - 1)) q' ρ := by
        gcongr
        exact eLpNorm_mono_eNorm
          (hG.aemeasurable_eLpNorm_Lp .rfl r').aestronglyMeasurable
          fun b ↦ by rw [eNorm_eq_self]; exact hGf b
    _ ≤ M * eLpNorm f q ρ ^ (q.toReal - 1) := by
        gcongr
        exact TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq
          (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
          (ae_of_all _ fun b ↦ (Real.norm_of_nonneg (by positivity)).le)

/-! ### Minkowski's inequality -/

section Elementary

variable {F : Type*} [NormedAddCommGroup F] {p q r : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Minkowski's inequality for mixed norms.** For `1 ≤ q` and `1 ≤ r`, the `L^q_b L^r_x` mixed
norm of the sum of two almost everywhere strongly measurable families of `Lᵖ` functions is at most
the sum of their mixed norms. -/
theorem eLpNorm_eLpNorm_add_le {u v : β → Lp F p μ} (hu : AEStronglyMeasurable u ρ)
    (hv : AEStronglyMeasurable v ρ) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    eLpNorm (fun b ↦ eLpNorm (u b + v b) r μ) q ρ ≤
      eLpNorm (fun b ↦ eLpNorm (u b) r μ) q ρ + eLpNorm (fun b ↦ eLpNorm (v b) r μ) q ρ :=
  calc _ ≤ eLpNorm (fun b ↦ eLpNorm (u b) r μ + eLpNorm (v b) r μ) q ρ :=
        eLpNorm_mono_eNorm ((hu.add hv).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun b ↦ by
            simp only [eNorm_eq_self, Pi.add_apply]
            rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
            exact eLpNorm_add_le hr
    _ ≤ _ := eLpNorm_add_le hq

/-! ### Bounded operators -/

/-- **Bounded operators in mixed norms.** A continuous map `T` from `Lᵖ(μ)` to `Lᵖ'(ν)` with
`‖T f‖_{L^s(ν)} ≤ K ‖f‖_{L^r(μ)}` costs at most the factor `K` in every mixed norm: for an almost
everywhere strongly measurable `u : β → Lᵖ(μ)`, `‖T ∘ u‖_{L^q_b L^s_y} ≤ K ‖u‖_{L^q_b L^r_x}`. -/
theorem eLpNorm_eLpNorm_apply_le {Y G : Type*} {mY : MeasurableSpace Y} {ν : Measure Y}
    [NormedAddCommGroup G] {p' : ℝ≥0∞} [Fact (1 ≤ p')] {T : Lp F p μ → Lp G p' ν}
    (hTc : Continuous T) {K s : ℝ≥0∞} (hT : ∀ f, eLpNorm (T f) s ν ≤ K * eLpNorm f r μ)
    {u : β → Lp F p μ} (hu : AEStronglyMeasurable u ρ) :
    eLpNorm (fun b ↦ eLpNorm (T (u b)) s ν) q ρ ≤
      K * eLpNorm (fun b ↦ eLpNorm (u b) r μ) q ρ := by
  have hTu := ((hTc.comp_aestronglyMeasurable hu).aemeasurable_eLpNorm_Lp .rfl
    s).aestronglyMeasurable
  rcases eq_or_ne q 0 with rfl | hq
  · simp [eLpNorm_exponent_zero hTu]
  calc _ ≤ eLpNorm (fun b ↦ K * eLpNorm (u b) r μ) q ρ :=
        eLpNorm_mono_eNorm hTu fun b ↦ by simpa only [eNorm_eq_self] using hT (u b)
    _ = _ := eLpNorm_const_mul_ennreal_of_pos (pos_iff_ne_zero.2 hq)

omit [Fact (1 ≤ p)] in
/-- **Cut-off families in mixed norms.** For a map `T` from `Lᵖ(μ)` to `Lᵖ'(ν)` with `T 0 = 0`,
such as a linear map, and a null measurable set `s`, the mixed norm `L^q_b L^r_y` of `T` applied
to `u : β → Lᵖ(μ)` cut off to `s` and extended by zero is the mixed norm of `T ∘ u` over `s`. -/
theorem eLpNorm_eLpNorm_apply_indicator {Y G : Type*} {mY : MeasurableSpace Y} {ν : Measure Y}
    [NormedAddCommGroup G] {p' : ℝ≥0∞} {T : Lp F p μ → Lp G p' ν} (hT : T 0 = 0) {s : Set β}
    (hs : NullMeasurableSet s ρ) (u : β → Lp F p μ) :
    eLpNorm (fun b ↦ eLpNorm (T (s.indicator u b)) r ν) q ρ =
      eLpNorm (fun b ↦ eLpNorm (T (u b)) r ν) q (ρ.restrict s) := by
  have hind : (fun b ↦ eLpNorm (T (s.indicator u b)) r ν) =
      s.indicator fun b ↦ eLpNorm (T (u b)) r ν := by
    funext b
    by_cases hb : b ∈ s
    · simp [hb]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, hT,
        eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
  rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict hs]

end Elementary

/-! ### Reflection of the parameter -/

/-- The mixed norm `‖b ↦ ‖F b‖_{L^r(μ)}‖_{L^q(ρ)}` of a family `F` of `Lᵖ` functions representing
an element `Φ` of the Bochner space `L^q(ρ; L^r(μ))`, `Φ(b) = F(b)` almost everywhere for almost
every `b`, is the norm of `Φ`. -/
theorem eLpNorm_eLpNorm_eq_eNorm_of_ae_eq {F : Type*} [NormedAddCommGroup F] {p q r : ℝ≥0∞}
    [Fact (1 ≤ r)] {Φ : Lp (Lp F r μ) q ρ} {u : β → Lp F p μ}
    (hΦu : ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] u b) :
    eLpNorm (fun b ↦ eLpNorm (u b) r μ) q ρ = ‖Φ‖ₑ := by
  rw [Lp.eNorm_def, ← eLpNorm_eNorm _ (Lp.aestronglyMeasurable Φ)]
  refine eLpNorm_congr_ae ?_
  filter_upwards [hΦu] with b hb
  rw [Lp.eNorm_def, eLpNorm_congr_ae hb]

/-- Reflecting the parameter, `b ↦ -b`, preserves mixed norms when the measure `ρ` is invariant
under negation, as Lebesgue measure on the time line is. -/
theorem AEStronglyMeasurable.eLpNorm_eLpNorm_comp_neg [InvolutiveNeg β] [MeasurableNeg β]
    [ρ.IsNegInvariant] {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Φ : β → Lp F p μ} (hΦ : AEStronglyMeasurable Φ ρ) {q r : ℝ≥0∞} :
    eLpNorm (fun b ↦ eLpNorm (Φ (-b)) r μ) q ρ = eLpNorm (fun b ↦ eLpNorm (Φ b) r μ) q ρ :=
  eLpNorm_comp_measurePreserving (g := fun b ↦ eLpNorm (Φ b) r μ)
    (hΦ.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable (Measure.measurePreserving_neg ρ)

end MeasureTheory
