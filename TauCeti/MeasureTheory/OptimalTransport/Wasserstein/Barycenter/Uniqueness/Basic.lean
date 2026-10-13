/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Mixture.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Uniqueness of Wasserstein barycenters

For a fixed law `μ`, the map `ν ↦ W_p(μ, ν) ^ p` is convex along mixtures `a • ν₀ + b • ν₁`
(`TauCeti.wassersteinEDist_smul_add_smul_rpow_le`), and *strictly* convex as soon as the optimal
plans out of `μ` are induced by maps (`TauCeti.wassersteinEDist_smul_add_smul_rpow_lt`).

Strict convexity gives uniqueness of Wasserstein barycenters. If `ν₀` and `ν₁` are two Fréchet
barycenters of a law `P` on `P_p(X)`, the mixture `2⁻¹ • ν₀ + 2⁻¹ • ν₁` has Fréchet value at most
their common minimal value, so the convexity inequality is an equality for `P`-almost every input
law. If `P` gives positive mass to input laws whose optimal plans are induced by maps, one of
them sees a strict inequality unless `ν₀ = ν₁`. The quadratic Euclidean case, where Brenier's
theorem supplies the maps for absolutely continuous input laws, is
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean`.

## Main statements

* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters` — on a Polish metric space and for
  `1 ≤ p < ∞`, a law on `P_p(X)` that gives positive mass to input laws whose optimal plans are
  induced by maps has at most one Fréchet barycenter.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924, for uniqueness of finite quadratic barycenters.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields 168 (2017), 901--917, for the population version.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

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
  obtain ⟨ν, hν⟩ := exists_coe_eq_smul_add_smul ENNReal.inv_two_add_inv_two ν₀ ν₁
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

end WassersteinSpace

end TauCeti
