/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.UniformIntegrable
public import TauCeti.MeasureTheory.OptimalTransport.Cost.WeakConvergence
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence

/-!
# Wasserstein convergence and convergence of moments

For a finite exponent `1 ≤ p < ∞`, convergence in the `p`-Wasserstein distance is weak convergence
of probability measures together with convergence of the `p`-moments. This file proves both
halves of this classical characterization and assembles them on the finite-moment Wasserstein
space `TauCeti.WassersteinSpace p X` over a separable Borel pseudometric space.

The moment of a law about a basepoint `x` is its Wasserstein distance from the Dirac law at `x`
(`TauCeti.wassersteinEDist_dirac_left`), so the triangle inequality makes it a continuous
function on the Wasserstein space; this holds for every exponent, including `p = ∞`, in its
`eLpNorm` form. Together with `TauCeti.WassersteinSpace.continuous_toProbabilityMeasure`, which
gives weak convergence, this is the necessity half. Uniform integrability of the tails then follows
from the general criterion `TauCeti.exists_setLIntegral_le_of_tendsto_lintegral` for integrals of
unbounded continuous functions along weakly convergent families.

For the sufficiency half, a displacement larger than `2 R` forces one of the two endpoints to lie
at distance at least `R` from the basepoint, and then the displacement is at most twice that
distance. The `p`-th power of the displacement is therefore at most its truncation at `2 R` plus
`2 ^ p` times the `p`-moment tails beyond `R` of the two marginals. The tails are uniformly small
by the uniform integrability just described, and the transport cost of the bounded truncated cost
tends to `0` along weak convergence by `TauCeti.tendsto_transportCost_of_tendsto`.

## Main statements

* `TauCeti.WassersteinSpace.continuous_eLpNorm_edist` — the `L^p` norm of the distance to a
  basepoint is continuous on the Wasserstein space;
* `TauCeti.WassersteinSpace.continuous_lintegral_edist_rpow` — for `p < ∞`, so is the `p`-moment
  `∫⁻ y, edist x y ^ p`;
* `TauCeti.exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral` — along a weakly convergent
  family whose `p`-moments converge to a finite limit, the `p`-moments have uniformly small tails;
* `TauCeti.WassersteinSpace.exists_setLIntegral_edist_rpow_le` — in particular, the `p`-moments
  have uniformly small tails along a `W_p`-convergent family;
* `TauCeti.tendsto_wassersteinEDist_of_tendsto_lintegral` — on a separable pseudometric space,
  weak convergence together with convergence of the `p`-moments to a finite limit gives
  convergence in the `p`-Wasserstein distance, for every finite exponent;
* `TauCeti.WassersteinSpace.tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral` — the
  characterization of convergence in the Wasserstein space.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 6.8
  and Theorem 6.9.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, Proposition 7.1.5.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Tails

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {p : ℝ≥0∞} {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

/-- **Uniformly small moment tails.** For a finite nonzero exponent `p`, along a weakly convergent
family of probability measures whose `p`-moments about a basepoint converge to the finite
`p`-moment of the limit, the `p`-moments have uniformly small tails: for every `ε > 0` there is a
radius `R` such that eventually the part of the `p`-moment coming from distance at least `R` is at
most `ε`. -/
theorem exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (h : Tendsto μs L (𝓝 μ)) (x : X) (hμ : ∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X) ≠ ∞)
    (hlim : Tendsto (fun i ↦ ∫⁻ y, edist x y ^ p.toReal ∂(μs i : Measure X)) L
      (𝓝 (∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X)))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂(μs i : Measure X) ≤ ε := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set g : X → ℝ≥0 := fun y ↦ nndist x y ^ p.toReal
  have hg : Continuous g :=
    (NNReal.continuous_rpow_const hq.le).comp (continuous_const.nndist continuous_id)
  have hcoe (y : X) : (g y : ℝ≥0∞) = edist x y ^ p.toReal := by
    rw [ENNReal.coe_rpow_of_nonneg _ hq.le, edist_nndist]
  obtain ⟨R, hR⟩ := exists_setLIntegral_le_of_tendsto_lintegral hg h (by simpa only [hcoe] using hμ)
    (by simpa only [hcoe] using hlim) hε
  refine ⟨R ^ p.toReal⁻¹, hR.mono fun i hi ↦ ?_⟩
  have hset : {y | R ^ p.toReal⁻¹ ≤ nndist x y} = {y | R ≤ g y} := by
    ext y
    exact NNReal.rpow_inv_le_iff hq
  simpa only [hset, hcoe] using hi

end Tails

namespace WassersteinSpace

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- The `L^p` norm of the distance to a basepoint, that is the `p`-th root of the `p`-moment
about that basepoint, is continuous on the Wasserstein space: it is the Wasserstein distance from
the Dirac law at the basepoint. -/
theorem continuous_eLpNorm_edist (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      eLpNorm (fun y ↦ edist x y) p ((μ : ProbabilityMeasure X) : Measure X) := by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun μ ν ↦ ?_
  rw [one_mul, edist_comm, edist_def, ← wassersteinEDist_dirac_left measurable_edist,
    ← wassersteinEDist_dirac_left measurable_edist]
  exact wassersteinEDist_triangle measurable_edist Fact.out _ _ _

/-- For a finite exponent `p`, the `p`-moment `∫⁻ y, edist x y ^ p` about a basepoint is a
continuous function on the `p`-Wasserstein space. -/
theorem continuous_lintegral_edist_rpow (hp : p ≠ ∞) (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      ∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) := by
  simp_rw [← eLpNorm_rpow_eq_lintegral (zero_lt_one.trans_le Fact.out).ne' hp]
  exact (ENNReal.continuous_rpow_const).comp (continuous_eLpNorm_edist x)

omit [SecondCountableTopology X] [StandardBorelSpace X] in
/-- The `p`-moment of a finite-moment law about any basepoint is finite. -/
private theorem lintegral_edist_rpow_ne_top (hp : p ≠ ∞) (μ : WassersteinSpace p X) (x : X) :
    ∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rw [← eLpNorm_rpow_eq_lintegral hp0 hp]
  exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    ((hasFiniteMoment μ).memLp measurable_edist_right.aestronglyMeasurable).eLpNorm_ne_top

/-- **Uniform integrability of moments along a `W_p`-convergent family.** For a finite exponent
`1 ≤ p < ∞`, along a family converging in the `p`-Wasserstein distance the `p`-moments about any
basepoint have uniformly small tails: for every `ε > 0` there is a radius `R` such that eventually
the part of the `p`-moment coming from distance at least `R` is at most `ε`. -/
theorem exists_setLIntegral_edist_rpow_le (hp : p ≠ ∞) {γ : Type*} {L : Filter γ}
    {μs : γ → WassersteinSpace p X} {μ : WassersteinSpace p X} (h : Tendsto μs L (𝓝 μ)) (x : X)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μs i : ProbabilityMeasure X) : Measure X) ≤ ε :=
  exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral (zero_lt_one.trans_le Fact.out).ne' hp
    ((continuous_toProbabilityMeasure.tendsto μ).comp h) x (lintegral_edist_rpow_ne_top hp μ x)
    (((continuous_lintegral_edist_rpow hp x).tendsto μ).comp h) hε

end WassersteinSpace

section Sufficiency

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {p : ℝ≥0∞} {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- A displacement larger than `2 R` is at most twice the distance from the basepoint `x` of an
endpoint lying at distance at least `R` from it. Hence the `p`-th power of the displacement is at
most its truncation at `2 R` plus `2 ^ p` times the tail parts, beyond `R`, of the `p`-th powers of
the distances of the two endpoints from `x`. -/
private theorem edist_rpow_le_min_add_indicator {q : ℝ} (hq : 0 < q) (x : X) (R : ℝ≥0)
    (y z : X) :
    edist y z ^ q ≤ min (edist y z) (2 * R) ^ q +
      2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) y +
      2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) z := by
  by_cases hd : edist y z ≤ 2 * R
  · rw [min_eq_left hd, add_assoc]
    exact le_self_add
  rw [not_le] at hd
  -- An endpoint `w` with `edist y z ≤ 2 * edist x w` lies at distance at least `R` from `x`.
  have hmem {w : X} (hw : edist y z ≤ 2 * edist x w) : w ∈ {w | R ≤ nndist x w} := by
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, ← edist_nndist]
    by_contra hlt
    exact (not_le.2 hd) (hw.trans (by gcongr; exact (not_le.1 hlt).le))
  have hbound {w : X} (hw : edist y z ≤ 2 * edist x w) :
      edist y z ^ q ≤ 2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) w := by
    rw [indicator_of_mem (hmem hw), ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    exact ENNReal.rpow_le_rpow hw hq.le
  have htri : edist y z ≤ edist x y + edist x z := edist_triangle_left y z x
  rcases le_total (edist x z) (edist x y) with hle | hle
  · refine (hbound ?_).trans (le_add_right (le_add_left le_rfl))
    exact htri.trans (by rw [two_mul]; gcongr)
  · refine (hbound ?_).trans (le_add_left le_rfl)
    exact htri.trans (by rw [two_mul]; gcongr)

/-- **Weak convergence and convergence of moments give Wasserstein convergence.** On a separable
pseudometric space, let probability measures `μᵢ` converge weakly to `μ`, and let their
`p`-moments about a basepoint `x` converge to the finite `p`-moment of `μ`. Then for every finite
exponent `p` the `p`-Wasserstein distance from `μᵢ` to `μ` tends to `0`. -/
theorem tendsto_wassersteinEDist_of_tendsto_lintegral [TopologicalSpace.SeparableSpace X]
    (hp : p ≠ ∞) (h : Tendsto μs L (𝓝 μ)) (x : X)
    (hμ : ∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X) ≠ ∞)
    (hlim : Tendsto (fun i ↦ ∫⁻ y, edist x y ^ p.toReal ∂(μs i : Measure X)) L
      (𝓝 (∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X)))) :
    Tendsto (fun i ↦ wassersteinEDist p (μs i : Measure X) (μ : Measure X)) L (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp_rw [wassersteinEDist_exponent_zero ⟨_, isCoupling_prod _ _⟩]
    exact tendsto_const_nhds
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- It suffices that the transport cost of `edist ^ p` tends to `0`.
  suffices hc : Tendsto (fun i ↦ transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal)
      (μs i : Measure X) (μ : Measure X)) L (𝓝 0) by
    simp_rw [wassersteinEDist_eq_transportCost_rpow hp0 hp]
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hq)] using
      ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hc
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have h2q : (2 : ℝ≥0∞) ^ p.toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofNat_ne_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- The tails beyond a common radius `R` are at most `τ` for the family and for the limit.
  obtain ⟨τ, hτ, hτε⟩ : ∃ τ > 0, 2 ^ p.toReal * τ + 2 ^ p.toReal * τ ≤ ε / 2 := by
    refine ⟨ε / 2 / 2 / 2 ^ p.toReal, ENNReal.div_pos (ENNReal.half_pos hε2.ne').ne' h2q, ?_⟩
    calc 2 ^ p.toReal * (ε / 2 / 2 / 2 ^ p.toReal) + 2 ^ p.toReal * (ε / 2 / 2 / 2 ^ p.toReal)
        ≤ ε / 2 / 2 + ε / 2 / 2 := add_le_add ENNReal.mul_div_le ENNReal.mul_div_le
      _ = ε / 2 := ENNReal.add_halves _
  obtain ⟨R₁, hR₁⟩ :=
    exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral hp0 hp h x hμ hlim hτ
  obtain ⟨R₂, hR₂⟩ :=
    exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral (L := (⊤ : Filter Unit))
    (μs := fun _ ↦ μ) hp0 hp tendsto_const_nhds x hμ tendsto_const_nhds hτ
  set R : ℝ≥0 := max R₁ R₂
  set S : Set X := {w | R ≤ nndist x w}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (continuous_const.nndist continuous_id).measurable
  have htail {ν : Measure X} {R' : ℝ≥0} (hR' : R' ≤ R)
      (hν : ∫⁻ y in {y | R' ≤ nndist x y}, edist x y ^ p.toReal ∂ν ≤ τ) :
      ∫⁻ y, 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) y ∂ν ≤ 2 ^ p.toReal * τ := by
    rw [lintegral_const_mul' _ _ h2q, lintegral_indicator hS]
    gcongr
    exact (lintegral_mono_set fun y (hy : R ≤ nndist x y) ↦ hR'.trans hy).trans hν
  have hf : Measurable fun w ↦ 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) w :=
    (((continuous_const.edist continuous_id).measurable.pow_const _).indicator hS).const_mul _
  -- The transport cost of the truncated cost tends to `0` along weak convergence.
  have hcore : Tendsto (fun i ↦ transportCost (fun z : X × X ↦ min (edist z.1 z.2) (2 * R) ^
      p.toReal) (μs i : Measure X) (μ : Measure X)) L (𝓝 0) := by
    refine tendsto_transportCost_of_tendsto (M := (2 * (R : ℝ≥0∞)) ^ p.toReal)
      (ENNReal.rpow_ne_top_of_nonneg hq.le (by finiteness))
      (fun z ↦ ENNReal.rpow_le_rpow (min_le_right _ _) hq.le) (fun η hη ↦ ?_) h
    have hpow : Tendsto (fun t : ℝ≥0∞ ↦ t ^ p.toReal) (𝓝 0) (𝓝 0) := by
      simpa [ENNReal.zero_rpow_of_pos hq] using
        (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0
    obtain ⟨δ, hδ, hδη⟩ :=
      ENNReal.nhds_zero_basis.eventually_iff.1 (hpow.eventually (ge_mem_nhds hη))
    exact ⟨δ, hδ, fun a b hab ↦
      (ENNReal.rpow_le_rpow (min_le_left _ _) hq.le).trans (hδη hab)⟩
  filter_upwards [hcore.eventually (ge_mem_nhds hε2), hR₁] with i hi hRi
  calc transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) (μs i : Measure X) μ
      ≤ transportCost (fun z : X × X ↦ min (edist z.1 z.2) (2 * R) ^ p.toReal +
          2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) z.1 +
          2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) z.2)
          (μs i : Measure X) μ :=
        transportCost_mono fun z ↦ edist_rpow_le_min_add_indicator hq x R z.1 z.2
    _ = transportCost (fun z : X × X ↦ min (edist z.1 z.2) (2 * R) ^ p.toReal)
          (μs i : Measure X) μ +
          ∫⁻ y, 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) y ∂(μs i : Measure X) +
          ∫⁻ y, 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) y ∂(μ : Measure X) :=
        transportCost_add_split hf hf
    _ ≤ ε / 2 + 2 ^ p.toReal * τ + 2 ^ p.toReal * τ :=
        add_le_add (add_le_add hi (htail (le_max_left _ _) hRi))
          (htail (le_max_right _ _) (eventually_top.1 hR₂ ()))
    _ ≤ ε / 2 + ε / 2 := by
        rw [add_assoc]
        exact add_le_add le_rfl hτε
    _ = ε := ENNReal.add_halves ε

end Sufficiency

namespace WassersteinSpace

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- **Convergence in the Wasserstein space.** For a finite exponent `1 ≤ p < ∞` and any
basepoint `x`, a family of finite-moment laws converges in the `p`-Wasserstein distance exactly
when it converges weakly and its `p`-moments about `x` converge to the `p`-moment of the limit. -/
theorem tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral (hp : p ≠ ∞) {γ : Type*}
    {L : Filter γ} {μs : γ → WassersteinSpace p X} {μ : WassersteinSpace p X} (x : X) :
    Tendsto μs L (𝓝 μ) ↔
      Tendsto (fun i ↦ (μs i : ProbabilityMeasure X)) L (𝓝 (μ : ProbabilityMeasure X)) ∧
        Tendsto (fun i ↦ ∫⁻ y, edist x y ^ p.toReal ∂((μs i : ProbabilityMeasure X) : Measure X))
          L (𝓝 (∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X))) := by
  refine ⟨fun h ↦ ⟨(continuous_toProbabilityMeasure.tendsto μ).comp h,
    ((continuous_lintegral_edist_rpow hp x).tendsto μ).comp h⟩, fun ⟨hw, hm⟩ ↦ ?_⟩
  rw [tendsto_iff_edist_tendsto_0]
  simpa only [edist_def] using
    tendsto_wassersteinEDist_of_tendsto_lintegral hp hw x (lintegral_edist_rpow_ne_top hp μ x) hm

end WassersteinSpace

end TauCeti
