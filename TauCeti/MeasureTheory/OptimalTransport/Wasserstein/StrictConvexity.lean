/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Mixture
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Strict convexity of `W_p ^ p` and uniqueness of Wasserstein barycenters

For a fixed law `μ`, the map `ν ↦ W_p(μ, ν) ^ p` is convex along mixtures `a • ν₀ + b • ν₁`
(`TauCeti.wassersteinEDist_smul_add_smul_rpow_le`). It is *strictly* convex as soon as the optimal
plans out of `μ` are induced by maps: a mixture of optimal plans to `ν₀` and `ν₁` that is itself
optimal must then be a graph plan, which forces `ν₀ = ν₁`
(`TauCeti.transportCost_smul_add_smul_lt`). By Brenier's theorem this holds for the quadratic
cost on a finite-dimensional real inner product space whenever `μ` is absolutely continuous with
respect to an additive Haar measure, such as Lebesgue measure on `ℝⁿ`.

Strict convexity gives uniqueness of Wasserstein barycenters. If `ν₀` and `ν₁` are two Fréchet
barycenters of a law `P` on `P_p(X)`, the mixture `2⁻¹ • ν₀ + 2⁻¹ • ν₁` has Fréchet value at most
their common minimal value, so the convexity inequality is an equality for `P`-almost every input
law. If `P` gives positive mass to input laws whose optimal plans are induced by maps, one of
them sees a strict inequality unless `ν₀ = ν₁`. In the quadratic Euclidean case this is the
uniqueness half of Agueh and Carlier's theorem for finitely many input laws, one of them absolutely
continuous with a positive weight, and its population version, for laws `P` giving positive mass
to absolutely continuous measures.

## Main statements

* `TauCeti.wassersteinEDist_smul_add_smul_rpow_lt` — on a Polish metric space, if the optimal
  plans for `edist ^ p` from `μ` to the mixture `a • ν₀ + b • ν₁` of two distinct probability
  laws are induced by maps, then `W_p(μ, a • ν₀ + b • ν₁) ^ p` is strictly below
  `a * W_p(μ, ν₀) ^ p + b * W_p(μ, ν₁) ^ p`;
* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt` — strict convexity of `ν ↦ W₂(μ, ν) ^ 2`
  for an absolutely continuous `μ` on a finite-dimensional real inner product space;
* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters` — a law on `P_p(X)` that gives
  positive mass to input laws whose optimal plans are induced by maps has at most one Fréchet
  barycenter;
* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two` and
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac` — on a
  finite-dimensional real inner product space, there is at most one quadratic Wasserstein
  barycenter when the law of the input laws gives positive mass to absolutely continuous laws, in
  particular for finitely many input laws one of which is absolutely continuous and has a positive
  weight.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924, for uniqueness of finite quadratic barycenters.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields 168 (2017), 901--917, for the population version.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` is absolutely continuous.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

section Polish

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞}

/-- **Strict convexity of `W_p ^ p` in one argument.** On a Polish metric space, let `μ`, `ν₀`
and `ν₁` be probability laws with `ν₀ ≠ ν₁`, and let `a, b` be nonzero weights with `a + b = 1`.
If every optimal plan for the cost `edist ^ p` from `μ` to the mixture `a • ν₀ + b • ν₁` is the
graph plan of a map, then the `p`-th power of the Wasserstein distance from `μ` to the mixture is
strictly below the mixture of the `p`-th powers of the distances from `μ` to `ν₀` and to `ν₁`. -/
theorem wassersteinEDist_smul_add_smul_rpow_lt (hp0 : p ≠ 0) (hp : p ≠ ∞) {μ ν₀ ν₁ : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] {a b : ℝ≥0∞}
    (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgraph : ∀ π, IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) π μ
      (a • ν₀ + b • ν₁) → ∃ T : X → X, AEMeasurable T μ ∧ π = graphPlan T μ)
    (hne : ν₀ ≠ ν₁) :
    wassersteinEDist p μ (a • ν₀ + b • ν₁) ^ p.toReal
      < a * wassersteinEDist p μ ν₀ ^ p.toReal + b * wassersteinEDist p μ ν₁ ^ p.toReal := by
  obtain ⟨π₀, h₀⟩ := exists_isOptimalCoupling_edist_rpow μ ν₀ p.toReal
  obtain ⟨π₁, h₁⟩ := exists_isOptimalCoupling_edist_rpow μ ν₁ p.toReal
  simp only [wassersteinEDist_rpow_eq_transportCost measurable_edist hp0 hp]
  exact transportCost_smul_add_smul_lt hab ha hb h₀ h₁ hgraph hne

end Polish

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for an absolutely continuous `μ`.** On a
finite-dimensional real inner product space, let `μ` be a probability law absolutely continuous
with respect to an additive Haar measure, and let `ν₀ ≠ ν₁` be probability laws at finite `W₂`
distance from `μ`. For nonzero weights with `a + b = 1`,
`W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt {μ ν₀ ν₁ : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hμ : μ ≪ ρ) {a b : ℝ≥0∞}
    (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞)
    (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 := by
  have hle := wassersteinEDist_smul_add_smul_rpow_le measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top hab μ ν₀ ν₁
  have hlt := wassersteinEDist_smul_add_smul_rpow_lt two_ne_zero ENNReal.ofNat_ne_top hab ha hb
    (μ := μ) (fun π hπ ↦ ?_) hne
  · simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using hlt
  -- The mixture is at finite distance from `μ`, by convexity, so Brenier's theorem applies.
  have hfin : wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ≠ ∞ := by
    simp only [ENNReal.toReal_ofNat] at hle
    refine fun htop ↦ (ne_top_of_le_ne_top ?_ hle) (by simp [htop])
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add))
          (ENNReal.rpow_ne_top_of_nonneg zero_le_two h₀),
        ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self))
          (ENNReal.rpow_ne_top_of_nonneg zero_le_two h₁)⟩
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_absolutelyContinuous hμ hfin
  exact ⟨T, hT.aemeasurable, hπT⟩

end Euclidean

namespace WassersteinSpace

section Polish

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Uniqueness of Wasserstein barycenters.** On a Polish metric space and for `1 ≤ p < ∞`, let
`P` be a law on `P_p(X)` that gives positive mass to the input laws `m` out of which every optimal
plan for the cost `edist ^ p` to a law of `P_p(X)` is the graph plan of a map. Then `P` has at
most one `p`-Fréchet barycenter in `P_p(X)`. -/
theorem subsingleton_frechetBarycenters (hp : p ≠ ∞) {P : Measure (WassersteinSpace p X)}
    (hP : P {m : WassersteinSpace p X | ∀ (ν : WassersteinSpace p X) (π : Measure (X × X)),
      IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) π
        ((m : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) →
      ∃ T : X → X, AEMeasurable T ((m : ProbabilityMeasure X) : Measure X) ∧
        π = graphPlan T ((m : ProbabilityMeasure X) : Measure X)} ≠ 0) :
    (frechetBarycenters p P).Subsingleton := by
  have := borelSpace (X := X) (p := p) hp
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hm (z : WassersteinSpace p X) : Measurable fun y ↦ edist z y :=
    (continuous_const.edist continuous_id).measurable
  have hm' (z : WassersteinSpace p X) : Measurable fun y ↦ edist y z ^ p.toReal :=
    (continuous_id.edist continuous_const).measurable.pow_const _
  -- The Fréchet value of `z`, with the input law as the source of each transport problem.
  have hF (z : WassersteinSpace p X) :
      frechetPower p P z = ∫⁻ m, edist m z ^ p.toReal ∂P := by
    simp_rw [frechetPower_def, edist_comm z]
  intro ν₀ h₀ ν₁ h₁
  obtain ⟨hR₀, hmin₀⟩ := (isFrechetBarycenter_iff_forall_frechetPower_le hp0 hp
    (hm ν₀).aemeasurable fun z ↦ (hm z).aemeasurable).1 (mem_frechetBarycenters.1 h₀)
  obtain ⟨-, hmin₁⟩ := (isFrechetBarycenter_iff_forall_frechetPower_le hp0 hp
    (hm ν₁).aemeasurable fun z ↦ (hm z).aemeasurable).1 (mem_frechetBarycenters.1 h₁)
  have hF₀ : frechetPower p P ν₀ ≠ ∞ := by
    rw [← frechetRadius_rpow_eq_frechetPower hp0 hp (hm ν₀).aemeasurable]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hR₀
  set μ₀ := ((ν₀ : ProbabilityMeasure X) : Measure X)
  set μ₁ := ((ν₁ : ProbabilityMeasure X) : Measure X)
  -- The midpoint mixture of the two barycenters is again a law of `P_p(X)`.
  obtain ⟨ν, hν⟩ := exists_coe_eq_smul_add_smul hp0 hp ENNReal.inv_two_add_inv_two ν₀ ν₁
  -- Convexity: the cost of each input law to the mixture is at most the mean of its costs to the
  -- two barycenters, and integrating gives the minimal value, so `P`-almost everywhere equality.
  set g : WassersteinSpace p X → ℝ≥0∞ := fun m ↦ edist m ν ^ p.toReal
  set f : WassersteinSpace p X → ℝ≥0∞ :=
    fun m ↦ 2⁻¹ * edist m ν₀ ^ p.toReal + 2⁻¹ * edist m ν₁ ^ p.toReal
  have hgf (m : WassersteinSpace p X) : g m ≤ f m := by
    simp only [g, f, edist_def, hν]
    exact wassersteinEDist_smul_add_smul_rpow_le measurable_edist hp0 hp
      ENNReal.inv_two_add_inv_two _ _ _
  have hintf : ∫⁻ m, f m ∂P = frechetPower p P ν₀ := by
    rw [lintegral_add_left ((hm' ν₀).const_mul _), lintegral_const_mul _ (hm' ν₀),
      lintegral_const_mul _ (hm' ν₁), ← hF, ← hF, le_antisymm (hmin₁ ν₀) (hmin₀ ν₁), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]
  have hae : g =ᵐ[P] f := by
    refine ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hgf)
      (ne_top_of_le_ne_top (hintf ▸ hF₀) (lintegral_mono hgf))
      (((hm' ν₀).const_mul _).add ((hm' ν₁).const_mul _)).aemeasurable ?_
    rw [hintf, ← hF]
    exact hmin₀ ν
  -- An input law whose optimal plans are maps sees a strict inequality unless `ν₀ = ν₁`.
  by_contra hne
  have hne' : μ₀ ≠ μ₁ := fun h ↦ hne (ext (ProbabilityMeasure.toMeasure_injective h))
  refine hP (measure_mono_null (fun m hmS ↦ ?_) (ae_iff.1 hae))
  have hlt := wassersteinEDist_smul_add_smul_rpow_lt hp0 hp
    (μ := ((m : ProbabilityMeasure X) : Measure X)) ENNReal.inv_two_add_inv_two (by simp)
    (by simp) (fun π hπ ↦ hmS ν π (by rwa [hν])) hne'
  simp only [mem_ofPred_eq, g, f, edist_def, hν]
  exact hlt.ne

end Polish

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **Uniqueness of quadratic Wasserstein barycenters.** On a finite-dimensional real inner
product space, a law `P` on `P₂(E)` that gives positive mass to the laws absolutely continuous
with respect to an additive Haar measure has at most one quadratic Fréchet barycenter in
`P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters ENNReal.ofNat_ne_top fun h ↦
    hP (measure_mono_null ?_ h)
  intro m (hm : _ ≪ ρ) ν π hπ
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_absolutelyContinuous hm
    (wassersteinEDist_ne_top measurable_edist m ν)
  exact ⟨T, hT.aemeasurable, hπT⟩

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** (Agueh–Carlier). On
a finite-dimensional real inner product space, if one of finitely many laws `μ i` of `P₂(E)` is
absolutely continuous with respect to an additive Haar measure and has a nonzero weight, then the
law `∑ i, w i • δ_{μ i}` has at most one quadratic Fréchet barycenter in `P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac {ι : Type*} [Fintype ι]
    {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : ((μ j : ProbabilityMeasure E) : Measure E) ≪ ρ) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton := by
  set S := {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ}
  refine subsingleton_frechetBarycenters_two (ρ := ρ) (ne_of_gt ?_)
  calc (0 : ℝ≥0∞) < w j := ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hj)
    _ = (w j • Measure.dirac (μ j)) S := by
        simp [Measure.dirac_apply_of_mem (show μ j ∈ S from hμj)]
    _ ≤ ∑ i, (w i • Measure.dirac (μ i)) S :=
        Finset.single_le_sum (f := fun i ↦ (w i • Measure.dirac (μ i)) S)
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)
    _ = (∑ i, w i • Measure.dirac (μ i)) S := by rw [Measure.coe_finsetSum, Finset.sum_apply]

end Euclidean

end WassersteinSpace

end TauCeti
