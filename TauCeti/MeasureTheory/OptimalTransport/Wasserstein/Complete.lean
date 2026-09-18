/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Chain
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Completeness of the Wasserstein space

Over a complete separable pseudometric ground space carrying its Borel structure, and for a finite
exponent `1 ≤ p < ∞`, the `p`-Wasserstein distance is a complete pseudometric: on the finite-moment
laws `P_p (X)` of `TauCeti.WassersteinSpace` and, more generally, on every anchored
finite-distance component of `TauCeti.WassersteinComponent`.

The measure-level result `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_le_tsum` says that a
sequence of laws whose
consecutive Wasserstein distances are bounded by a summable sequence has a limit law, together
with the quantitative estimate that its distance to the `n`-th term is at most the `n`-th tail of
those bounds. It uses `TauCeti.Measure.chainMeasure` to realize consecutive couplings on one path
space; the exponent-independent part of that argument, extracting a measurable pathwise limit
coupled to every term, is `TauCeti.Measure.exists_measurable_isCoupling_map_chainMeasure`. The
criterion `TauCeti.WassersteinComponent.completeSpace_of_exists_tendsto_wassersteinEDist`
turns such a limit
theorem into completeness of every anchored component; finite-moment laws are then handled by their
isometric identification with a Dirac-anchored component. The finite-exponent hypothesis is
essential to the `L^p` limit estimate; the case `p = ∞` is treated in
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Complete`.

## Main statements

* `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_le_tsum` — a chain of laws with summable
  consecutive Wasserstein distances converges, with the tail bound on the distances to its limit;
* `TauCeti.WassersteinComponent.completeSpace_of_exists_tendsto_wassersteinEDist` — an
  anchored component is complete once geometrically controlled chains converge;
* `TauCeti.WassersteinComponent.completeSpace` and
  `TauCeti.WassersteinComponent.instCompleteSpace` — every anchored finite-distance component is
  complete;
* `TauCeti.WassersteinSpace.completeSpace` and `TauCeti.WassersteinSpace.instCompleteSpace` — the
  finite-moment Wasserstein space `P_p (X)` is complete.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  the Wasserstein space over a Polish space is proved to be Polish by this argument.
* F. Bolley, *Separability and completeness for the Wasserstein distance*, Séminaire de
  Probabilités XLI, Lecture Notes in Mathematics 1934, Springer 2008, pp. 371--377.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace TauCeti

universe u

variable {X : Type u} {p : ℝ≥0∞}

section Limit

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [StandardBorelSpace X]

/-- **A chain of laws with summable Wasserstein jumps converges.** If consecutive terms of a
sequence `μ` of probability measures have `p`-Wasserstein distance strictly below a summable
sequence `b`, then some probability measure `ν` satisfies
`W_p (μ n, ν) ≤ ∑' k, b (n + k)` for every `n`. -/
theorem exists_isProbabilityMeasure_wassersteinEDist_le_tsum (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)] {b : ℕ → ℝ≥0∞}
    (hb : ∑' n, b n ≠ ∞) (hμ : ∀ n, wassersteinEDist p (μ n) (μ (n + 1)) < b n) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∀ n, wassersteinEDist p (μ n) ν ≤ ∑' k, b (n + k) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  have : Nonempty X := Measure.nonempty_of_neZero (μ 0)
  -- the near-optimal couplings of consecutive laws, and their countable gluing
  choose π hπ hπb using fun n ↦ wassersteinEDist_lt_iff.1 (hμ n)
  have : ∀ n, IsProbabilityMeasure (π n) := fun n ↦ (hπ n).isProbabilityMeasure
  set P : Measure (ℕ → X) := TauCeti.Measure.chainMeasure (X := fun _ ↦ X) π
  have hev : ∀ n, Measurable fun x : ℕ → X ↦ x n := fun n ↦ measurable_pi_apply n
  have hadj : ∀ n, P.map (fun x ↦ (x n, x (n + 1))) = π n :=
    TauCeti.Measure.map_adjacent_chainMeasure_of_isCoupling hπ
  -- the jumps of the coordinate process have the prescribed `L^p` sizes
  have hjump : ∀ n, eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) p P < b n := fun n ↦ by
    have : eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) p P
        = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (π n) := by
      rw [← hadj n, eLpNorm_map_measure hd.aestronglyMeasurable
        ((hev n).prodMk (hev (n + 1))).aemeasurable]
      rfl
    rw [this]
    exact hπb n
  have hjumpmeas : ∀ n, Measurable fun x : ℕ → X ↦ edist (x n) (x (n + 1)) :=
    fun n ↦ hd.comp ((hev n).prodMk (hev (n + 1)))
  -- almost every path is Cauchy, since its jumps are summable in `L¹`
  have hint : ∀ n, ∫⁻ x, edist (x n) (x (n + 1)) ∂P ≤ b n := fun n ↦ by
    calc ∫⁻ x, edist (x n) (x (n + 1)) ∂P
        = eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) 1 P := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          simp
      _ ≤ eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) p P :=
          eLpNorm_le_eLpNorm_of_exponent_le hp (hjumpmeas n).aestronglyMeasurable
      _ ≤ b n := (hjump n).le
  have hcauchy : ∀ᵐ x ∂P, CauchySeq fun n ↦ x n := by
    have hlt : ∫⁻ x, ∑' n, edist (x n) (x (n + 1)) ∂P ≠ ∞ := by
      rw [lintegral_tsum fun n ↦ (hjumpmeas n).aemeasurable]
      exact ne_top_of_le_ne_top hb (ENNReal.tsum_le_tsum hint)
    filter_upwards [ae_lt_top (Measurable.tsum hjumpmeas) hlt] with x hx
    exact cauchySeq_of_edist_le_of_tsum_ne_top _ (fun _ ↦ le_rfl) hx.ne
  -- hence almost every path converges, to a measurable limit `Z` coupled to every `μ n`
  obtain ⟨Z, hZ, hZtendsto, hcoupling⟩ :=
    TauCeti.Measure.exists_measurable_isCoupling_map_chainMeasure hπ hcauchy
  refine ⟨P.map Z, (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance,
    fun n ↦ ?_⟩
  -- the displacement to the limit is the limit of the displacements along the chain
  have hstep : ∀ N, eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + N))) p P
      ≤ ∑ k ∈ Finset.range N, b (n + k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        calc eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + (N + 1)))) p P
            ≤ eLpNorm (fun x : ℕ → X ↦
                edist (x n) (x (n + N)) + edist (x (n + N)) (x (n + N + 1))) p P :=
              eLpNorm_mono_enorm fun x ↦ by
                simpa [← Nat.add_assoc] using edist_triangle (x n) (x (n + N)) (x (n + N + 1))
          _ ≤ eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + N))) p P
                + eLpNorm (fun x : ℕ → X ↦ edist (x (n + N)) (x (n + N + 1))) p P :=
              eLpNorm_add_le (hd.comp ((hev n).prodMk (hev (n + N)))).aestronglyMeasurable
                (hjumpmeas (n + N)).aestronglyMeasurable hp
          _ ≤ (∑ k ∈ Finset.range N, b (n + k)) + b (n + N) := by
              gcongr
              exact (hjump (n + N)).le
          _ = ∑ k ∈ Finset.range (N + 1), b (n + k) := (Finset.sum_range_succ _ _).symm
  calc wassersteinEDist p (μ n) (P.map Z)
      ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (P.map fun x ↦ (x n, Z x)) :=
        wassersteinEDist_le (hcoupling n) p
    _ = eLpNorm (fun x : ℕ → X ↦ edist (x n) (Z x)) p P := by
        rw [eLpNorm_map_measure hd.aestronglyMeasurable ((hev n).prodMk hZ).aemeasurable]
        rfl
    _ ≤ ∑' k, b (n + k) := by
        refine eLpNorm_le_of_ae_tendsto_ennreal hp0 hp'
          (fun N ↦ (hd.comp ((hev n).prodMk (hev (n + N)))).aemeasurable) ?_
          fun N ↦ (hstep N).trans (ENNReal.sum_le_tsum _)
        filter_upwards [hZtendsto] with x hx
        exact tendsto_const_nhds.edist
          (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))

end Limit

section Controlled

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [StandardBorelSpace X]

variable [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- **Completeness from geometrically controlled chains.** An anchored Wasserstein component is
complete as soon as every chain of probability laws whose consecutive distances are strictly
below `2⁻¹ ^ n` converges in Wasserstein distance to some probability law. The finite- and
infinite-exponent completeness theorems both apply this criterion. -/
theorem WassersteinComponent.completeSpace_of_exists_tendsto_wassersteinEDist
    (H : ∀ (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)],
      (∀ n, wassersteinEDist p (μ n) (μ (n + 1)) < 2⁻¹ ^ n) →
        ∃ ν : Measure X, IsProbabilityMeasure ν ∧
          Tendsto (fun n ↦ wassersteinEDist p (μ n) ν) atTop (𝓝 0)) :
    CompleteSpace (WassersteinComponent p μ₀) := by
  refine EMetric.complete_of_convergent_controlled_sequences (fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ ENNReal.pow_pos (by simp) n) fun u hu ↦ ?_
  have hjump : ∀ n, wassersteinEDist p ((u n : ProbabilityMeasure X) : Measure X)
      ((u (n + 1) : ProbabilityMeasure X) : Measure X) < 2⁻¹ ^ n := fun n ↦ by
    have := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rwa [edist_def] at this
  obtain ⟨ν, hν, hνlim⟩ := H _ hjump
  obtain ⟨n, hn⟩ := (hνlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hanchor : wassersteinEDist p (μ₀ : Measure X) ν ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨WassersteinComponent.wassersteinEDist_anchor_ne_top (u n),
        ne_top_of_lt (hn.trans ENNReal.one_lt_top)⟩)
      (wassersteinEDist_triangle measurable_edist Fact.out _ _ _)
  have hcoe : ((WassersteinComponent.mk (⟨ν, hν⟩ : ProbabilityMeasure X) hanchor :
      WassersteinComponent p μ₀) : ProbabilityMeasure X) = ⟨ν, hν⟩ :=
    WassersteinComponent.coe_mk _ _
  refine ⟨WassersteinComponent.mk ⟨ν, hν⟩ hanchor, tendsto_iff_edist_tendsto_0.2 ?_⟩
  simp_rw [WassersteinComponent.edist_def, hcoe]
  exact hνlim

end Controlled

section Complete

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [StandardBorelSpace X]

variable [Fact (1 ≤ p)]

namespace WassersteinComponent

variable {μ₀ : ProbabilityMeasure X}

/-- Every anchored finite-distance Wasserstein component over a Polish ground space is complete
for a finite exponent `1 ≤ p < ∞`. -/
theorem completeSpace (hp' : p ≠ ∞) : CompleteSpace (WassersteinComponent p μ₀) :=
  completeSpace_of_exists_tendsto_wassersteinEDist fun _ _ hμ ↦ by
    have hb : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ∞ := by
      simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    obtain ⟨ν, hν, hle⟩ := exists_isProbabilityMeasure_wassersteinEDist_le_tsum Fact.out hp' hb hμ
    refine ⟨ν, hν, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ zero_le) hle⟩
    simpa only [add_comm] using ENNReal.tendsto_sum_nat_add _ hb

/-- Every anchored finite-distance Wasserstein component over a Polish ground space is complete,
read off the exponent facts. -/
instance instCompleteSpace [Fact (p ≠ ∞)] : CompleteSpace (WassersteinComponent p μ₀) :=
  completeSpace Fact.out

end WassersteinComponent

namespace WassersteinSpace

/-- The finite-moment Wasserstein space over a Polish ground space is complete for a finite
exponent `1 ≤ p < ∞`. -/
theorem completeSpace (hp' : p ≠ ∞) : CompleteSpace (WassersteinSpace p X) := by
  rcases isEmpty_or_nonempty (WassersteinSpace p X) with h | h
  · infer_instance
  · obtain ⟨μ⟩ := h
    obtain ⟨x₀⟩ : Nonempty X :=
      Measure.nonempty_of_neZero ((μ : ProbabilityMeasure X) : Measure X)
    let _ : CompleteSpace (WassersteinComponent p (diracProba x₀)) :=
      WassersteinComponent.completeSpace hp'
    exact (isometryEquivComponent x₀).completeSpace

/-- The finite-moment Wasserstein space over a Polish ground space is complete, read off the
exponent facts. -/
instance instCompleteSpace [Fact (p ≠ ∞)] : CompleteSpace (WassersteinSpace p X) :=
  completeSpace Fact.out

end WassersteinSpace

end Complete

end TauCeti
