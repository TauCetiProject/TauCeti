/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Moment

/-!
# Relatively compact sets of the Wasserstein space

For a finite exponent `1 ≤ p < ∞` and a complete separable metric ground space `X`, a set `S` of
laws with finite `p`-moment is relatively compact in the Wasserstein space
`TauCeti.WassersteinSpace p X` exactly when

* it is tight, and
* its `p`-moments about a basepoint `x` have uniformly small tails: for every `ε > 0` there is a
  radius `R` with `∫⁻ y in {y | R ≤ dist x y}, dist x y ^ p ∂μ ≤ ε` for every `μ ∈ S`.

It is compact exactly when it is moreover closed. This is the compactness half of the description
of the `W_p` topology as weak convergence together with uniform integrability of `p`-moments, whose
convergence half is
`TauCeti.WassersteinSpace.tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral`. The criterion
does not depend on the basepoint, since the equivalence holds for each one.

Both directions reduce to Prokhorov's theorem in Mathlib, which relates tightness to relative
compactness for the weak topology on `ProbabilityMeasure X`.

* Tightness of a relatively compact set is Mathlib's
  `MeasureTheory.isTightMeasureSet_of_isCompact_closure` applied to its weakly compact image, since
  the Wasserstein topology is finer than the weak one.
  Uniformly small tails follow by contradiction: a sequence with persistent tails beyond larger
  and larger radii has a `W_p`-convergent subsequence, along which the tails are uniformly small by
  `TauCeti.WassersteinSpace.exists_setLIntegral_edist_rpow_le`.
* Conversely, a tight set with uniformly small tails lies in the set `T` of laws in the weak closure
  of the set whose tails beyond the same radii, taken over open regions, obey the same bounds. An
  ultrafilter on `T` converges weakly by Prokhorov's theorem (Mathlib's
  `isCompact_closure_of_isTightMeasureSet`); the open-region tails are weakly lower
  semicontinuous, so the limit lies in `T` and has finite `p`-moment; and uniformly small tails give
  convergence of the `p`-moments by `TauCeti.tendsto_lintegral_of_tendsto_probabilityMeasure`, hence
  convergence in `W_p`. So `T` is compact. This direction needs neither completeness of `X` nor
  that of the Wasserstein space.

## Main statements

* `isCompact_closure_of_isTightMeasureSet_of_exists_setLIntegral_edist_rpow_le`
  — a tight set with uniformly small `p`-moment tails is relatively compact, on a separable metric
  space;
* `isTightMeasureSet_of_isCompact_closure` — a relatively compact set is
  tight, on a complete separable pseudometric space;
* `exists_setLIntegral_edist_rpow_le_of_isCompact_closure` — a relatively
  compact set has uniformly small `p`-moment tails about every basepoint;
* `isCompact_closure_iff_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le` and
  `isCompact_iff_isClosed_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le`
  — the resulting characterizations of relatively compact and of compact sets.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace WassersteinSpace

private theorem setOf_toMeasure_eq_image {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {p : ℝ≥0∞}
    (S : Set (WassersteinSpace p X)) :
    {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} =
      {((ν : ProbabilityMeasure X) : Measure X) |
        ν ∈ ((↑) '' S : Set (ProbabilityMeasure X))} := by
  ext
  simp

section Necessity

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- **A relatively compact set of the Wasserstein space is tight.** On a complete separable
pseudometric space, the laws of a relatively compact set of `P_p (X)` form a tight family. -/
theorem isTightMeasureSet_of_isCompact_closure [CompleteSpace X] {S : Set (WassersteinSpace p X)}
    (hS : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  have hS' : IsCompact (closure ((↑) '' S : Set (ProbabilityMeasure X))) :=
    (hS.image continuous_toProbabilityMeasure).closure_of_subset (image_mono subset_closure)
  rw [setOf_toMeasure_eq_image]
  exact MeasureTheory.isTightMeasureSet_of_isCompact_closure hS'

/-- **A relatively compact set of the Wasserstein space has uniformly integrable moments.** For a
finite exponent `1 ≤ p < ∞`, the `p`-moments about any basepoint of the laws of a relatively
compact set of `P_p (X)` have uniformly small tails: for every `ε > 0` there is a radius `R` such
that, for every law of the set, the part of its `p`-moment coming from distance at least `R` is at
most `ε`. -/
theorem exists_setLIntegral_edist_rpow_le_of_isCompact_closure (hp : p ≠ ∞)
    {S : Set (WassersteinSpace p X)} (hS : IsCompact (closure S)) (x : X) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε := by
  by_contra! h
  -- Laws of `S` whose tails beyond radius `n` exceed `ε` have a convergent subsequence, along
  -- which the tails beyond some fixed radius are eventually at most `ε`.
  choose μ hμS hμ using fun n : ℕ ↦ h n
  obtain ⟨ν, -, φ, hφ, hlim⟩ := hS.tendsto_subseq fun n ↦ subset_closure (hμS n)
  obtain ⟨R, hR⟩ := exists_setLIntegral_edist_rpow_le hp hlim x hε
  obtain ⟨n, hn, hRn⟩ := (hR.and (hφ.tendsto_atTop.eventually_ge_atTop ⌈R⌉₊)).exists
  refine (hμ (φ n)).not_ge ((lintegral_mono_set fun y hy ↦ ?_).trans hn)
  exact (Nat.le_ceil R).trans ((Nat.cast_le.2 hRn).trans hy)

end Necessity

section Sufficiency

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- **Tightness and uniformly integrable moments give relative compactness.** On a separable
metric space and for a finite exponent `1 ≤ p < ∞`, a set of laws of finite `p`-moment is
relatively compact in `P_p (X)` as soon as it is tight and its `p`-moments about a basepoint `x`
have uniformly small tails: for every `ε > 0` there is a radius `R` such that, for every law of the
set, the part of its `p`-moment coming from distance at least `R` is at most `ε`. -/
theorem isCompact_closure_of_isTightMeasureSet_of_exists_setLIntegral_edist_rpow_le
    (hp : p ≠ ∞) (x : X)
    {S : Set (WassersteinSpace p X)}
    (hT : IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S})
    (hU : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε) :
    IsCompact (closure S) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  choose R hR using hU
  have hK : IsCompact (closure ((↑) '' S : Set (ProbabilityMeasure X))) :=
    _root_.isCompact_closure_of_isTightMeasureSet <| by
    rw [← setOf_toMeasure_eq_image]
    exact hT
  set S' : Set (ProbabilityMeasure X) := (↑) '' S
  -- `S` lies in the set `T` of laws in the weak closure of `S` whose tails over the open regions
  -- beyond the radii `R ε` are at most `ε`; it suffices to show that `T` is compact.
  set T : Set (WassersteinSpace p X) := {μ | (μ : ProbabilityMeasure X) ∈ closure S' ∧
    ∀ ε (hε : 0 < ε), ∫⁻ y in {y | R ε hε < nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε}
  refine exists_isCompact_superset_iff.1 ⟨T, isCompact_iff_ultrafilter_le_nhds.2 fun F hF ↦ ?_,
    fun μ hμ ↦ ⟨subset_closure (mem_image_of_mem _ hμ), fun ε hε ↦
      (lintegral_mono_set fun y hy ↦ le_of_lt (α := ℝ≥0) hy).trans (hR ε hε μ hμ)⟩⟩
  have hFT : ∀ᶠ μ in (F : Filter (WassersteinSpace p X)), μ ∈ T := le_principal_iff.1 hF
  -- By Prokhorov's theorem the ultrafilter converges weakly, to a law whose tails obey the same
  -- bounds by lower semicontinuity.
  obtain ⟨ν, hνK, hν⟩ := hK.ultrafilter_le_nhds (F.map (↑)) <| by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact hFT.mono fun μ hμ ↦ hμ.1
  have hlim : Tendsto (fun μ : WassersteinSpace p X ↦ (μ : ProbabilityMeasure X)) F (𝓝 ν) := by
    rwa [Tendsto, ← Ultrafilter.coe_map]
  have hνT (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∫⁻ y in {y | R ε hε < nndist x y}, edist x y ^ p.toReal ∂(ν : Measure X) ≤ ε :=
    ((lowerSemicontinuous_setLIntegral_edist_rpow (q := p.toReal) x (R ε hε)).isClosed_preimage
      ε).mem_of_tendsto hlim (hFT.mono fun μ hμ ↦ hμ.2 ε hε)
  -- The limit has finite `p`-moment, so it is a point of the Wasserstein space.
  have hνmem : HasFiniteMoment p (ν : Measure X) := by
    apply (hasFiniteMoment_iff_lintegral_edist_rpow_ne_top hp0 hp x _).2
    exact (lintegral_edist_rpow_le_add (q := p.toReal) ENNReal.toReal_nonneg _ x
      (R 1 one_pos)).trans_lt
      (ENNReal.add_lt_top.2 ⟨by finiteness, (hνT 1 one_pos).trans_lt ENNReal.one_lt_top⟩) |>.ne
  refine ⟨mk ν hνmem, ⟨by simpa using hνK, fun ε hε ↦ by simpa using hνT ε hε⟩, ?_⟩
  -- Weak convergence and convergence of the `p`-moments give convergence in `W_p`.
  have hmoment := tendsto_lintegral_edist_rpow (q := p.toReal) (ENNReal.toReal_pos hp0 hp) hlim x
    fun ε hε ↦ ⟨R ε hε, hFT.mono fun μ hμ ↦ hμ.2 ε hε⟩
  exact Filter.tendsto_id'.1 <|
    (tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral hp x (μs := id)).2
      ⟨by simpa using hlim, by simpa using hmoment⟩

end Sufficiency

section Characterization

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [CompleteSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **Relatively compact sets of the Wasserstein space.** On a complete separable metric space and
for a finite exponent `1 ≤ p < ∞`, a set of laws of finite `p`-moment is relatively compact in
`P_p (X)` exactly when it is tight and its `p`-moments about a basepoint `x` have uniformly small
tails. -/
theorem isCompact_closure_iff_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le
    (hp : p ≠ ∞) (x : X)
    {S : Set (WassersteinSpace p X)} :
    IsCompact (closure S) ↔
      IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} ∧
        ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y},
          edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε :=
  ⟨fun h ↦ ⟨isTightMeasureSet_of_isCompact_closure h,
      fun _ hε ↦ exists_setLIntegral_edist_rpow_le_of_isCompact_closure hp h x hε⟩,
    fun h ↦ isCompact_closure_of_isTightMeasureSet_of_exists_setLIntegral_edist_rpow_le hp x h.1
      h.2⟩

/-- **Compact sets of the Wasserstein space.** On a complete separable metric space and for a
finite exponent `1 ≤ p < ∞`, a set of laws of finite `p`-moment is compact in `P_p (X)` exactly
when it is closed, tight, and its `p`-moments about a basepoint `x` have uniformly small tails. -/
theorem isCompact_iff_isClosed_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le
    (hp : p ≠ ∞) (x : X)
    {S : Set (WassersteinSpace p X)} :
    IsCompact S ↔ IsClosed S ∧
      IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} ∧
        ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y},
          edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε := by
  rw [← isCompact_closure_iff_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le hp x]
  exact ⟨fun h ↦ ⟨h.isClosed, h.closure⟩,
    fun ⟨hc, h⟩ ↦ hc.closure_eq ▸ h⟩

end Characterization

end WassersteinSpace

end TauCeti
