/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport

/-!
# Separability of the finite-moment Wasserstein space

For a finite exponent `1 ≤ p < ∞` the Wasserstein space `TauCeti.WassersteinSpace p X` of laws of
finite `p`-moment is separable when the ground space is second countable and its measurable
structure is standard Borel and induced by the metric topology. The countable dense family is the
expected one: the laws carried by finitely many terms of a dense sequence of `X`, each term
receiving a rational share of the total mass. Concretely it is the range of a map defined on
`Finset (ℕ × ℕ)`, a pair `(i, k)` contributing the multiplicity `k` to the `i`-th term of the
sequence and the resulting weights being normalised to total mass `1`.

Three approximations take an arbitrary law to a member of that family, each costing a quarter of
the prescribed accuracy, and all three are supplied by the imported finite-support module: the
finite-support approximation `TauCeti.exists_ae_mem_finset_wassersteinEDist_le`, then
`TauCeti.exists_map_range_wassersteinEDist_le`, which pushes the resulting finitely supported law
onto terms of the dense sequence, and finally the rational-weight approximation
`TauCeti.exists_nat_weights_wassersteinEDist_le`.

The exponent must be finite. Finitely supported laws are not `W_∞`-dense on a general separable
metric space, and indeed `P_∞ (X)` need not be separable.

## Main statements

* `TauCeti.WassersteinSpace.separableSpace` — separability of `P_p (X)` for `1 ≤ p < ∞`, with
  `TauCeti.WassersteinSpace.instSeparableSpace` its instance form.
* `TauCeti.WassersteinComponent.separableSpace_of_hasFiniteMoment` — separability of the component
  anchored at a law with finite `p`-moment.

## Implementation notes

The imported approximation estimates take the measurability of the ground distance explicitly,
and the separability theorem reads it off the Borel structure. Finiteness of the exponent cannot
be an instance argument, so `TauCeti.WassersteinSpace.separableSpace` takes it explicitly and the
instance reads it off a `Fact`, exactly as the metric structure of `TauCeti.WassersteinSpace`
reads `1 ≤ p` off `Fact (1 ≤ p)`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 6.18.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p : ℝ≥0∞}

/-- The probability measure with weights given by natural multiplicities `m x` on the points of a
finite set `S` is a probability measure when the total multiplicity is positive. -/
theorem isProbabilityMeasure_natWeights {S : Finset X} {m : X → ℕ} (hm : 0 < ∑ x ∈ S, m x) :
    IsProbabilityMeasure
      ((∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) := by
  refine ⟨?_⟩
  have hmsum : ∑ x ∈ S, ((m x : ℕ) : ℝ≥0∞) = ((∑ x ∈ S, m x : ℕ) : ℝ≥0∞) :=
    (Nat.cast_sum _ _).symm
  have hmass : (∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) univ
      = ((∑ x ∈ S, m x : ℕ) : ℝ≥0∞) := by
    rw [FunLike.coe_sum, Finset.sum_apply, ← hmsum]
    exact Finset.sum_congr rfl fun x _ ↦ by simp
  rw [_root_.smul_apply, hmass, smul_eq_mul, hmsum,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hm.ne') (ENNReal.natCast_ne_top _)]

/-- The measure with natural multiplicities `m x` on the points of a finite set `S` is carried
by `S`. -/
theorem natWeights_compl_eq_zero [MeasurableSingletonClass X] (S : Finset X) (m : X → ℕ) :
    ((∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x)
      ((S : Set X)ᶜ) = 0 := by
  have hzero : (∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) ((S : Set X)ᶜ) = 0 := by
    rw [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [_root_.smul_apply, Measure.dirac_apply' _ S.measurableSet.compl,
      Set.indicator_of_notMem (by simpa using hx), smul_zero]
  rw [_root_.smul_apply, hzero, smul_zero]

/-- The measure with natural multiplicities on a finite set of terms of a sequence `u` is of the
form `(∑ m)⁻¹ • ∑ m • δ_(u i)` for a finite set of pairs `(i, k)`, where `k` is the
multiplicity of the `i`-th term. -/
theorem exists_finset_prod_natWeights_eq {u : ℕ → X} {S : Finset X} (m : X → ℕ)
    (hS : ∀ x ∈ S, x ∈ Set.range u) :
    ∃ t : Finset (ℕ × ℕ), (∑ q ∈ t, (q.2 : ℝ≥0∞))⁻¹ •
        ∑ q ∈ t, (q.2 : ℝ≥0∞) • Measure.dirac (u q.1) =
      (∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x := by
  classical
  choose! i hi using hS
  have hinj : ∀ x ∈ S, ∀ y ∈ S, (i x, m x) = (i y, m y) → x = y := by
    intro x hx y hy hxy
    have hix : i x = i y := congrArg Prod.fst hxy
    rw [← hi x hx, ← hi y hy, hix]
  refine ⟨S.image fun x ↦ (i x, m x), ?_⟩
  rw [Finset.sum_image hinj, Finset.sum_image hinj]
  exact congrArg₂ _ rfl (Finset.sum_congr rfl fun x hx ↦ by rw [hi x hx])

namespace WassersteinSpace

/-- The Wasserstein space over an empty ground space is empty: there is no probability measure. -/
theorem isEmpty_of_isEmpty [PseudoEMetricSpace X] [IsEmpty X] :
    IsEmpty (WassersteinSpace p X) := by
  refine ⟨fun μ ↦ ?_⟩
  have h : ((μ : ProbabilityMeasure X) : Measure X) univ = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.2 ‹IsEmpty X›, measure_empty] at h
  exact zero_ne_one h

/-- Approximation by laws with rational weights on a dense sequence: a law of finite `p`-moment is
within `3 * δ` in `W_p` of a law with natural multiplicities on finitely many terms of the
dense sequence `u`, by the three imported approximation steps (finite support, moving the atoms
onto terms of `u`, rounding the weights) each costing `δ`. -/
theorem exists_natWeights_wassersteinEDist_le [PseudoMetricSpace X] [StandardBorelSpace X]
    [BorelSpace X] [SecondCountableTopology X] {u : ℕ → X} (hu : DenseRange u) (hp1 : 1 ≤ p)
    (hp_top : p ≠ ∞)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : HasFiniteMoment p μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset X) (m : X → ℕ), (∀ x ∈ S, x ∈ Set.range u) ∧ 0 < ∑ x ∈ S, m x ∧
      wassersteinEDist p μ
        ((∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x) ≤
        ENNReal.ofReal (3 * δ) := by
  classical
  have hδ' : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  -- step one: approximate by a law carried by a finite set
  obtain ⟨s, ν₁, hν₁, hnull₁, -, hle₁⟩ := exists_ae_mem_finset_wassersteinEDist_le hp1 hp_top hμ hδ'
  -- step two: move its atoms onto terms of the dense sequence
  have : IsProbabilityMeasure ν₁ := hν₁
  obtain ⟨T, hT, hTu, hle₂⟩ := exists_map_range_wassersteinEDist_le measurable_edist hu hδ ν₁ p
  have hν₂ : IsProbabilityMeasure (ν₁.map T) := inferInstance
  have hnull₂ : (ν₁.map T) ((↑(s.image T) : Set X)ᶜ) = 0 := by
    rw [Measure.map_apply hT (s.image T).measurableSet.compl]
    refine measure_mono_null (fun x hx ↦ ?_) hnull₁
    simp only [Finset.coe_image, mem_preimage, mem_compl_iff, mem_image, Finset.mem_coe,
      not_exists, not_and] at hx ⊢
    exact fun hxs ↦ hx x hxs rfl
  -- step three: round the weights to a common denominator
  obtain ⟨m, hmpos, hle₃⟩ :=
    exists_nat_weights_wassersteinEDist_le (ν := ν₁.map T) measurable_edist hp0 hp_top hnull₂ hδ'
  refine ⟨s.image T, m, fun x hx ↦ ?_, hmpos, ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hTu y
  · refine (wassersteinEDist_triangle measurable_edist hp1 μ ν₁ _).trans ?_
    refine (add_le_add hle₁ ((wassersteinEDist_triangle measurable_edist hp1 ν₁ (ν₁.map T) _).trans
      (add_le_add hle₂ hle₃))).trans_eq ?_
    rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add hδ.le (by positivity)]
    ring_nf


section Separable

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **`P_p (X)` is separable.** For a finite exponent `1 ≤ p < ∞`, the finite-moment Wasserstein
space over a second-countable ground space whose measurable structure is standard Borel and
induced by the metric topology is separable: the laws carried by finitely many terms of a dense
sequence and giving each of them a rational share of the mass form a countable dense set. -/
theorem separableSpace (hp_top : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (WassersteinSpace p X) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have := hX
    exact ⟨∅, Set.countable_empty, fun μ ↦ (isEmpty_of_isEmpty.false μ).elim⟩
  set u : ℕ → X := TopologicalSpace.denseSeq X
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  -- the countable family of laws with natural multiplicities on terms of the dense sequence
  set G : Finset (ℕ × ℕ) → Measure X := fun t ↦
    (∑ q ∈ t, (q.2 : ℝ≥0∞))⁻¹ • ∑ q ∈ t, (q.2 : ℝ≥0∞) • Measure.dirac (u q.1) with hG_def
  refine ⟨(fun μ : WassersteinSpace p X ↦ ((μ : ProbabilityMeasure X) : Measure X)) ⁻¹'
    Set.range G, (Set.countable_range G).preimage fun _ _ h ↦ toProbabilityMeasure_injective
      (ProbabilityMeasure.toMeasure_injective h), ?_⟩
  refine Metric.dense_iff.2 fun μ r hr ↦ ?_
  have hquarter : (0 : ℝ) < r / 4 := by linarith
  obtain ⟨S, m, hSu, hmpos, hle⟩ := exists_natWeights_wassersteinEDist_le hu Fact.out hp_top
    μ.hasFiniteMoment hquarter
  set ν₃ : Measure X := (∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ •
    ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x with hν₃_def
  have hprob₃ : IsProbabilityMeasure ν₃ := isProbabilityMeasure_natWeights hmpos
  obtain ⟨x₁, _⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hmpos
  have hmom₃ : HasFiniteMoment p ν₃ :=
    hasFiniteMoment_of_ae_mem_finset x₁ (mem_ae_iff.2 (natWeights_compl_eq_zero S m))
  -- the approximating law belongs to the countable family
  have hrange : ν₃ ∈ Set.range G := by
    obtain ⟨t, ht⟩ := exists_finset_prod_natWeights_eq m hSu
    exact ⟨t, ht⟩
  have hcoe : ((mk (⟨ν₃, hprob₃⟩ : ProbabilityMeasure X) hmom₃ : WassersteinSpace p X) :
      ProbabilityMeasure X) = ⟨ν₃, hprob₃⟩ := coe_mk _ _
  refine ⟨mk ⟨ν₃, hprob₃⟩ hmom₃, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm, dist_def, hcoe]
    refine lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (by positivity) hle) ?_
    linarith
  · rw [Set.mem_preimage, hcoe]
    exact hrange

/-- The separability of `P_p (X)` as an instance, reading the finiteness of the exponent off a
`Fact`, as the metric structure reads off `Fact (1 ≤ p)`. -/
instance instSeparableSpace [Fact (p ≠ ∞)] :
    TopologicalSpace.SeparableSpace (WassersteinSpace p X) :=
  separableSpace Fact.out

end Separable

end WassersteinSpace

namespace WassersteinComponent

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- For a finite exponent `1 ≤ p < ∞`, the finite-distance component of an anchor law of finite
`p`-moment is separable, being isometric to the separable space `P_p (X)`. -/
theorem separableSpace_of_hasFiniteMoment (hp : p ≠ ∞) (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    TopologicalSpace.SeparableSpace (WassersteinComponent p μ₀) :=
  have := WassersteinSpace.separableSpace (X := X) hp
  let e := WassersteinSpace.isometryEquivComponentOfFiniteMoment hμ₀
  e.surjective.denseRange.separableSpace e.continuous

end WassersteinComponent

end TauCeti
