/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# The Wasserstein distance under convolution and translation

Convolving two laws with a common probability law does not increase their Wasserstein distance:
on an additive monoid whose extended distance is invariant under right addition,

`W_p (μ ∗ η, ν ∗ η) ≤ W_p (μ, ν)`,

and symmetrically for left convolution under left-invariance. Both are instances of a single
estimate for a common *random isometry*: if `f (·, z)` is an isometry for every `z`, then pushing
`μ ⊗ η` and `ν ⊗ η` forward along `f` does not increase the Wasserstein distance. The proof runs a
coupling `π` of `μ` and `ν` alongside an independent sample `z ∼ η` and applies `f (·, z)` to both
coordinates; the displacement of each coupled pair is unchanged.

Translation is the Dirac case of convolution, and in a group it is an isometry of every
Wasserstein distance. Finally, on a real seminormed space, a law and its translate by `a` are at
`W_p` distance exactly `‖a‖ₑ` for every `1 ≤ p`, with no moment assumption. The upper bound is
the translation plan; the lower bound tests a coupling against bounded truncations of a norming
functional for `a` supplied by the Hahn–Banach theorem and passes to the limit by dominated
convergence. The restriction `1 ≤ p` cannot be dropped: for the uniform law on `[0, 1]` and
`a = 1 / 2`, moving the left half to `[1, 3 / 2]` has objective `(1 / 2) ^ (1 / p)`, which is below
`1 / 2` once `p < 1`.

## Main statements

* `TauCeti.IsCoupling.map_prod` — a coupling run alongside an independent sample, with measurable
  maps applied to both coordinates, couples the two pushed-forward products;
* `TauCeti.wassersteinEDist_map_prod_le` — a common random isometry does not increase the
  Wasserstein distance;
* `TauCeti.wassersteinEDist_conv_right_le` and `TauCeti.wassersteinEDist_conv_left_le` —
  convolution with a common probability law does not increase the Wasserstein distance;
* `TauCeti.wassersteinEDist_map_add_right` and `TauCeti.wassersteinEDist_map_add_left` — in a
  group with an invariant distance, translation preserves the Wasserstein distance;
* `TauCeti.wassersteinEDist_map_add_right_le_enorm` and
  `TauCeti.wassersteinEDist_map_add_right_eq_enorm` — the distance from a law to its translate by
  `a` is at most `‖a‖ₑ`, with equality on a real seminormed space for `1 ≤ p`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

universe u v w

section Coupling

variable {X X' Y Y' H : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace H] {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}

/-- **Running a coupling alongside an independent sample.** If `π` couples `μ` and `ν`, then
sampling `(x, y) ∼ π` and an independent `z ∼ η` and applying `f (·, z)` and `g (·, z)` to the two
coordinates couples the pushforwards of `μ ⊗ η` along `f` and of `ν ⊗ η` along `g`. -/
protected theorem IsCoupling.map_prod (hπ : IsCoupling π μ ν) [SFinite π] (η : Measure H)
    [SFinite η] {f : X × H → X'} {g : Y × H → Y'} (hf : Measurable f) (hg : Measurable g) :
    IsCoupling ((π.prod η).map fun w ↦ (f (w.1.1, w.2), g (w.1.2, w.2)))
      ((μ.prod η).map f) ((ν.prod η).map g) := by
  have hf' : Measurable fun w : (X × Y) × H ↦ f (w.1.1, w.2) := by fun_prop
  have hg' : Measurable fun w : (X × Y) × H ↦ g (w.1.2, w.2) := by fun_prop
  constructor
  · have hprod : (π.map Prod.fst).prod η = (π.prod η).map (Prod.map Prod.fst id) := by
      simpa only [Measure.map_id] using Measure.map_prod_map π η measurable_fst measurable_id
    rw [Measure.fst_map_prodMk hf' hg', ← hπ.fst_eq, Measure.fst, hprod,
      Measure.map_map hf (by fun_prop)]
    simp only [Function.comp_def, Prod.map_def, id]
  · have hprod : (π.map Prod.snd).prod η = (π.prod η).map (Prod.map Prod.snd id) := by
      simpa only [Measure.map_id] using Measure.map_prod_map π η measurable_snd measurable_id
    rw [Measure.snd_map_prodMk hf' hg', ← hπ.snd_eq, Measure.snd, hprod,
      Measure.map_map hg (by fun_prop)]
    simp only [Function.comp_def, Prod.map_def, id]

end Coupling

section RandomIsometry

variable {X : Type u} {Y : Type v} {H : Type w} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace H] [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {p : ℝ≥0∞}

/-- **A common random isometry does not increase the Wasserstein distance.** If every section
`f (·, z)` is an isometry and `η` is a probability law, then pushing `μ ⊗ η` and `ν ⊗ η` forward
along `f` does not increase the `p`-Wasserstein distance, for every exponent `p`.

The source `μ` is σ-finite so that every coupling of `μ` is σ-finite as well, which is what the
product with `η` needs; no finiteness is asked of `ν`. -/
theorem wassersteinEDist_map_prod_le (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2)
    {f : X × H → Y} (hf : Measurable f) (hfi : ∀ z, Isometry fun x ↦ f (x, z))
    (μ ν : Measure X) [SigmaFinite μ] (η : Measure H) [IsProbabilityMeasure η] :
    wassersteinEDist p ((μ.prod η).map f) ((ν.prod η).map f) ≤ wassersteinEDist p μ ν := by
  obtain ⟨z₀⟩ := nonempty_of_isProbabilityMeasure η
  -- The ground distance of `X` is the ground distance of `Y` read through the isometry `f (·, z₀)`.
  have hdX : Measurable fun z : X × X ↦ edist z.1 z.2 := by
    have hm : Measurable fun z : X × X ↦ (f (z.1, z₀), f (z.2, z₀)) := by fun_prop
    convert hdY.comp hm using 1
    exact funext fun z ↦ ((hfi z₀).edist_eq z.1 z.2).symm
  refine le_wassersteinEDist fun π hπ ↦ ?_
  -- A coupling of `μ` has `μ` as its first marginal, so it inherits σ-finiteness from `μ`.
  have : SigmaFinite π := SigmaFinite.of_map π measurable_fst.aemeasurable
    (by rw [← Measure.fst, hπ.fst_eq]; infer_instance)
  have hg : Measurable fun w : (X × X) × H ↦ (f (w.1.1, w.2), f (w.1.2, w.2)) := by fun_prop
  calc wassersteinEDist p ((μ.prod η).map f) ((ν.prod η).map f)
      ≤ eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p
          ((π.prod η).map fun w ↦ (f (w.1.1, w.2), f (w.1.2, w.2))) :=
        wassersteinEDist_le (hπ.map_prod η hf hf) p
    _ = eLpNorm (fun w : (X × X) × H ↦ edist w.1.1 w.1.2) p (π.prod η) := by
        rw [eLpNorm_map_measure hdY.aestronglyMeasurable hg.aemeasurable]
        exact eLpNorm_congr_ae (.of_forall fun w ↦ (hfi w.2).edist_eq w.1.1 w.1.2)
    _ = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π :=
        eLpNorm_comp_measurePreserving (g := fun z : X × X ↦ edist z.1 z.2) (f := Prod.fst)
          hdX.aestronglyMeasurable
          ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

end RandomIsometry

section Convolution

variable {G : Type u} [AddMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G] [PseudoEMetricSpace G]
  {p : ℝ≥0∞}

/-- **Convolution does not increase the Wasserstein distance.** Convolving on the right with a
common probability law does not increase the `p`-Wasserstein distance, when the ground distance is
invariant under right addition. -/
theorem wassersteinEDist_conv_right_le [IsIsometricVAdd Gᵃᵒᵖ G]
    (hd : Measurable fun z : G × G ↦ edist z.1 z.2) (μ ν : Measure G) [SigmaFinite μ]
    (η : Measure G) [IsProbabilityMeasure η] :
    wassersteinEDist p (μ ∗ η) (ν ∗ η) ≤ wassersteinEDist p μ ν :=
  wassersteinEDist_map_prod_le hd measurable_add (fun z ↦ isometry_add_right z) μ ν η

/-- **Convolution does not increase the Wasserstein distance.** Convolving on the left with a
common probability law does not increase the `p`-Wasserstein distance, when the ground distance is
invariant under left addition. -/
theorem wassersteinEDist_conv_left_le [IsIsometricVAdd G G]
    (hd : Measurable fun z : G × G ↦ edist z.1 z.2) (μ ν : Measure G) [SigmaFinite μ]
    [SFinite ν] (η : Measure G) [IsProbabilityMeasure η] :
    wassersteinEDist p (η ∗ μ) (η ∗ ν) ≤ wassersteinEDist p μ ν := by
  -- Rewrite `η ∗ μ` as the pushforward of `μ ⊗ η` along `(x, z) ↦ z + x`.
  have hswap : ∀ ρ : Measure G, SFinite ρ →
      η ∗ ρ = (ρ.prod η).map fun w : G × G ↦ w.2 + w.1 := fun ρ _ ↦ by
    rw [Measure.conv, ← Measure.prod_swap, Measure.map_map measurable_add measurable_swap]
    simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap]
  rw [hswap μ inferInstance, hswap ν inferInstance]
  exact wassersteinEDist_map_prod_le hd (measurable_snd.add measurable_fst)
    (fun z ↦ isometry_add_left z) μ ν η

end Convolution

section Translation

variable {G : Type u} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] [PseudoEMetricSpace G]
  {p : ℝ≥0∞}

/-- In a group whose ground distance is invariant under right addition, translating two laws by a
common element preserves their Wasserstein distance. -/
@[simp]
theorem wassersteinEDist_map_add_right [IsIsometricVAdd Gᵃᵒᵖ G]
    (hd : Measurable fun z : G × G ↦ edist z.1 z.2) (a : G) (μ ν : Measure G) :
    wassersteinEDist p (μ.map (· + a)) (ν.map (· + a)) = wassersteinEDist p μ ν :=
  wassersteinEDist_map_eq (e := MeasurableEquiv.addRight a) hd (isometry_add_right a) μ ν

/-- In a group whose ground distance is invariant under left addition, translating two laws by a
common element preserves their Wasserstein distance. -/
@[simp]
theorem wassersteinEDist_map_add_left [IsIsometricVAdd G G]
    (hd : Measurable fun z : G × G ↦ edist z.1 z.2) (a : G) (μ ν : Measure G) :
    wassersteinEDist p (μ.map (a + ·)) (ν.map (a + ·)) = wassersteinEDist p μ ν :=
  wassersteinEDist_map_eq (e := MeasurableEquiv.addLeft a) hd (isometry_add_left a) μ ν

end Translation

section Normed

variable {E : Type u} [SeminormedAddCommGroup E] [MeasurableSpace E] {p : ℝ≥0∞}

/-- The Wasserstein distance from a probability law to its translate by `a` is at most `‖a‖ₑ`,
for every exponent: the translation plan moves every point by exactly `‖a‖ₑ`. -/
theorem wassersteinEDist_map_add_right_le_enorm [MeasurableAdd E]
    (hd : Measurable fun z : E × E ↦ edist z.1 z.2) (μ : Measure E) [IsProbabilityMeasure μ]
    (a : E) : wassersteinEDist p μ (μ.map (· + a)) ≤ ‖a‖ₑ := by
  refine (wassersteinEDist_map_le hd (measurable_add_const a).aemeasurable p).trans ?_
  simp only [edist_eq_enorm_sub, sub_add_cancel_left, enorm_neg]
  simpa using eLpNorm_le_of_ae_enorm_bound (p := p) (μ := μ) (f := fun _ : E ↦ ‖a‖ₑ)
    (.of_forall fun _ ↦ le_rfl)

variable [NormedSpace ℝ E] [OpensMeasurableSpace E]

/-- **The Hahn–Banach lower bound.** On a real seminormed space, every coupling of a probability
law with its translate by `a` has mean displacement at least `‖a‖ₑ`. No moment of the law is
assumed. -/
theorem enorm_le_lintegral_edist_of_isCoupling_map_add_right [MeasurableAdd E] {μ : Measure E}
    [IsProbabilityMeasure μ] {a : E} {π : Measure (E × E)}
    (hπ : IsCoupling π μ (μ.map (· + a))) : ‖a‖ₑ ≤ ∫⁻ z, edist z.1 z.2 ∂π := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  obtain ⟨ℓ, hℓ, hℓa⟩ := exists_dual_vector'' ℝ a
  -- `F n` is the norming functional `ℓ` truncated at height `n`: bounded, and `1`-Lipschitz.
  set F : ℕ → E → ℝ := fun n x ↦ max (-n) (min n (ℓ x)) with hF
  have hFm (n : ℕ) : Measurable (F n) := by fun_prop
  have hFb (n : ℕ) (x : E) : ‖F n x‖ ≤ n := by
    rw [hF, Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (neg_le_self n.cast_nonneg) (min_le_left _ _)⟩
  have hFi (n : ℕ) {ρ : Measure E} [IsFiniteMeasure ρ] : Integrable (F n) ρ :=
    .of_bound (hFm n).aestronglyMeasurable n (.of_forall (hFb n))
  have hFl (n : ℕ) (x y : E) : |F n x - F n y| ≤ |ℓ x - ℓ y| :=
    (abs_max_sub_max_le_max _ _ _ _).trans <| max_le (by simp) <|
      (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)
  have ha : Measurable fun x : E ↦ x + a := measurable_add_const a
  -- Each truncation bounds the mean displacement from below.
  have hstep (n : ℕ) : ‖∫ x, (F n (x + a) - F n x) ∂μ‖ₑ ≤ ∫⁻ z, edist z.1 z.2 ∂π := by
    have hint : ∫ x, (F n (x + a) - F n x) ∂μ = ∫ z, (F n z.2 - F n z.1) ∂π := by
      have hFa : Integrable (fun x ↦ F n (x + a)) μ := (hFi n).comp_measurable ha
      rw [integral_sub hFa (hFi n),
        integral_sub (hπ.integrable_comp_snd (hFi n)) (hπ.integrable_comp_fst (hFi n)),
        hπ.integral_comp_snd (hFm n).aestronglyMeasurable,
        hπ.integral_comp_fst (hFm n).aestronglyMeasurable,
        integral_map ha.aemeasurable (hFm n).aestronglyMeasurable]
    rw [hint]
    refine enorm_integral_le_lintegral_enorm _ |>.trans (lintegral_mono fun z ↦ ?_)
    rw [edist_comm, edist_dist, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ((hFl n _ _).trans ?_)
    rw [← map_sub, dist_eq_norm]
    exact (ℓ.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hℓ (norm_nonneg _))
  -- As the truncation height grows, the integrals converge to `ℓ a = ‖a‖`.
  have hlim : Tendsto (fun n : ℕ ↦ ∫ x, (F n (x + a) - F n x) ∂μ) atTop (𝓝 ‖a‖) := by
    have hconst : ∫ _ : E, ℓ a ∂μ = ‖a‖ := by simp [hℓa]
    rw [← hconst]
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ |ℓ a|)
      (fun n ↦ ((hFm n).comp ha).sub (hFm n) |>.aestronglyMeasurable)
      (integrable_const _) (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
    · simpa [Real.norm_eq_abs] using hFl n (x + a) x
    · have hev (y : E) : ∀ᶠ n : ℕ in atTop, F n y = ℓ y := by
        filter_upwards [eventually_ge_atTop ⌈|ℓ y|⌉₊] with n hn
        have hy : |ℓ y| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        rw [abs_le] at hy
        simp only [hF, min_eq_right hy.2, max_eq_right hy.1]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev (x + a), hev x] with n h₁ h₂
      simp [h₁, h₂]
  have := (continuous_enorm.tendsto _).comp hlim
  simpa using le_of_tendsto' this hstep

/-- **The Wasserstein distance to a translate.** On a real seminormed space, a probability law and
its translate by `a` are at `p`-Wasserstein distance exactly `‖a‖ₑ` for every `1 ≤ p`. No moment
of the law is assumed. -/
theorem wassersteinEDist_map_add_right_eq_enorm [MeasurableAdd E]
    (hd : Measurable fun z : E × E ↦ edist z.1 z.2) (hp : 1 ≤ p) (μ : Measure E)
    [IsProbabilityMeasure μ] (a : E) : wassersteinEDist p μ (μ.map (· + a)) = ‖a‖ₑ := by
  refine le_antisymm (wassersteinEDist_map_add_right_le_enorm hd μ a)
    (le_wassersteinEDist fun π hπ ↦ ?_)
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  calc ‖a‖ₑ ≤ ∫⁻ z, edist z.1 z.2 ∂π := enorm_le_lintegral_edist_of_isCoupling_map_add_right hπ
    _ = eLpNorm (fun z : E × E ↦ edist z.1 z.2) 1 π := by
        simp [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ eLpNorm (fun z : E × E ↦ edist z.1 z.2) p π :=
        eLpNorm_le_eLpNorm_of_exponent_le hp hd.aestronglyMeasurable

end Normed

end TauCeti
