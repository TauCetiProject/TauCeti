/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.AscoliCounterexample
public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.Measure.Tight.ContinuousMap

/-!
# Tightness of laws of curves from a bound on the expected action

Let `P` be a law on the space `C([a, b], X)` of continuous curves in a pseudometric space,
concentrated on curves absolutely continuous on `[a, b]`, and let `A_p(γ)` be the `p`-action of a
curve. The Hölder estimate `d(γ s, γ t) ^ p ≤ |t - s| ^ (p - 1) A_p(γ)` and Markov's inequality
bound the probability that a curve oscillates by at least `η` over two times closer than `δ`:

`P {γ | ∃ s t, |s - t| < δ ∧ η ≤ d(γ s, γ t)} ≤ δ ^ (p - 1) * (∫ A_p dP) / η ^ p`.

For `1 < p` the right-hand side tends to `0` with `δ`. A set of such laws with uniformly bounded
expected `p`-action therefore satisfies the uniform modulus of continuity in probability of the
tightness criterion `TauCeti.isTightMeasureSet_of_map_eval_of_continuity_modulus`, and is tight as
soon as its time marginals are tight on a dense set of times. This is how tightness of laws on
path space is obtained in the proof of the superposition principle for absolutely continuous curves
of probability measures, where the expected action is controlled by the metric speed of the curve
of laws.

For `p = 1` the estimate gives no modulus. For every `p`, a bound on the action controls only the
oscillation of the curves, not where they are. On a carrier that is not proper, laws with expected
`p`-action at most `1` for every `p ≥ 0`, all concentrated on absolutely continuous curves starting
at the same point, need not be tight
(`TauCeti.exists_not_isTightMeasureSet_lintegral_curveAction_le`): take the Dirac masses at the
curves `t ↦ t • eₙ` of `ℓ²`. The tightness of the time marginals is a separate hypothesis.

## Main results

* `TauCeti.measure_continuity_modulus_le_lintegral_curveAction`: the Hölder–Markov estimate, for
  `1 ≤ p`.
* `TauCeti.exists_measure_continuity_modulus_le_of_lintegral_curveAction_le`: for `1 < p`, a
  uniform bound on the expected `p`-action gives a uniform modulus of continuity in probability.
* `TauCeti.isTightMeasureSet_of_map_eval_of_lintegral_curveAction_le`: tight time marginals on a
  dense set of times and a uniform bound on the expected `p`-action, `1 < p`, give tightness.
* `TauCeti.exists_not_isTightMeasureSet_lintegral_curveAction_le`: the bound on the expected action
  and a common starting point do not give tightness.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 8.2.1.
* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120, Section 3.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {a b p : ℝ}

/-- **Hölder–Markov estimate.** Let `P` be a measure on `C([a, b], X)` concentrated on curves
absolutely continuous on `[a, b]`, and `1 ≤ p`. For `η > 0` and every `δ`, the curves with two
times closer than `δ` at which their values are at least `η` apart have `P`-measure at most
`δ ^ (p - 1) * (∫ A_p dP) / η ^ p`, where `A_p` is the `p`-action over `[a, b]`. -/
theorem measure_continuity_modulus_le_lintegral_curveAction (hab : a ≤ b)
    {P : Measure C(Icc a b, X)} (hp : 1 ≤ p)
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂P, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    {η : ℝ} (hη : 0 < η) (δ : ℝ) :
    P {γ : C(Icc a b, X) | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} ≤
      ENNReal.ofReal δ ^ (p - 1) *
        (∫⁻ γ : C(Icc a b, X), curveAction p (IccExtend hab γ) a b ∂P) / ENNReal.ofReal η ^ p := by
  set A : C(Icc a b, X) → ℝ≥0∞ := fun γ ↦ curveAction p (IccExtend hab γ) a b
  have hηp : ENNReal.ofReal η ^ p ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hη)
    ENNReal.ofReal_ne_top).ne'
  have hηp' : ENNReal.ofReal η ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  -- An absolutely continuous curve oscillating by `η` over a window of length `< δ` has a large
  -- action, by the Hölder estimate on that window.
  have hbad : ∀ᵐ γ ∂P, γ ∈ {γ : C(Icc a b, X) | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} →
      γ ∈ {γ | ENNReal.ofReal η ^ p ≤ ENNReal.ofReal δ ^ (p - 1) * A γ} := by
    filter_upwards [hAC] with γ hγ ⟨s, t, hst, hη⟩
    have hs : (s : ℝ) ∈ uIcc a b := Icc_subset_uIcc s.2
    have ht : (t : ℝ) ∈ uIcc a b := Icc_subset_uIcc t.2
    have hHölder := hγ.edist_rpow_le_mul_curveAction hp hs ht
    rw [IccExtend_val, IccExtend_val] at hHölder
    calc ENNReal.ofReal η ^ p ≤ edist (γ s) (γ t) ^ p := by
          rw [edist_dist]
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hη) (by linarith)
      _ ≤ edist (s : ℝ) t ^ (p - 1) * curveAction p (IccExtend hab γ) s t := hHölder
      _ ≤ ENNReal.ofReal δ ^ (p - 1) * A γ := by
          gcongr
          · rw [edist_dist, ← Subtype.dist_eq]
            exact ENNReal.ofReal_le_ofReal hst.le
          · exact curveAction_mono _ _
              (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hs ht))
  -- Markov's inequality for the measurable action.
  have hA : Measurable A := measurable_curveAction_IccExtend hab p a b
  refine (measure_mono_ae hbad).trans ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl hηp) (Or.inl hηp'), mul_comm,
    ← lintegral_const_mul _ hA]
  exact mul_meas_ge_le_lintegral₀ (hA.const_mul _).aemeasurable _

/-- **A bound on the expected action gives a modulus of continuity in probability.** Let `S` be a
set of measures on `C([a, b], X)`, each concentrated on curves absolutely continuous on `[a, b]`,
whose expected `p`-actions are bounded by a common `C < ∞`, with `1 < p`. Then for all
`η, ε > 0` there is `δ > 0` such that, for every `P ∈ S`, the curves with two times closer than
`δ` at which their values are at least `η` apart have `P`-measure at most `ε`. -/
theorem exists_measure_continuity_modulus_le_of_lintegral_curveAction_le (hab : a ≤ b)
    {S : Set (Measure C(Icc a b, X))} (hp : 1 < p)
    (hAC : ∀ P ∈ S, ∀ᵐ γ : C(Icc a b, X) ∂P,
      AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hS : ∀ P ∈ S, ∫⁻ γ : C(Icc a b, X), curveAction p (IccExtend hab γ) a b ∂P ≤ C) :
    ∀ η > 0, ∀ ε > 0, ∃ δ > 0, ∀ P ∈ S,
      P {γ : C(Icc a b, X) | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} ≤ ε := by
  intro η hη ε hε
  have hηp : ENNReal.ofReal η ^ p ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hη)
    ENNReal.ofReal_ne_top).ne'
  -- The bound `δ ^ (p - 1) * C / η ^ p` of the Hölder–Markov estimate tends to `0` with `δ`.
  have hlim : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ ^ (p - 1) * C / ENNReal.ofReal η ^ p)
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ ^ (p - 1)) (𝓝[>] 0) (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := p - 1)).comp
        ENNReal.continuous_ofReal).tendsto 0
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (sub_pos.2 hp)] using
        this.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.div_const (ENNReal.Tendsto.mul_const h (Or.inr hC)) (Or.inr hηp)
  obtain ⟨δ, hδε, hδ⟩ := ((hlim.eventually (ge_mem_nhds hε)).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ, fun P hP ↦ ?_⟩
  refine (measure_continuity_modulus_le_lintegral_curveAction hab hp.le (hAC P hP) hη δ).trans
    (le_trans ?_ hδε)
  gcongr
  exact hS P hP

/-- **Tightness of laws of curves from a bound on the expected action.** Let `X` be a complete
metric space, `D ⊆ [a, b]` dense and `1 < p`. A set `S` of measures on `C([a, b], X)`, each
concentrated on curves absolutely continuous on `[a, b]`, is tight if its time marginals at the
times of `D` are tight and its expected `p`-actions are bounded by a common `C < ∞`. -/
theorem isTightMeasureSet_of_map_eval_of_lintegral_curveAction_le [CompleteSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (hab : a ≤ b) {S : Set (Measure C(Icc a b, X))}
    {D : Set (Icc a b)} (hD : Dense D)
    (h_eval : ∀ t ∈ D,
      IsTightMeasureSet ((fun P : Measure C(Icc a b, X) ↦ P.map fun γ ↦ γ t) '' S))
    (hp : 1 < p)
    (hAC : ∀ P ∈ S, ∀ᵐ γ : C(Icc a b, X) ∂P,
      AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hS : ∀ P ∈ S, ∫⁻ γ : C(Icc a b, X), curveAction p (IccExtend hab γ) a b ∂P ≤ C) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_map_eval_of_continuity_modulus hD h_eval
    (exists_measure_continuity_modulus_le_of_lintegral_curveAction_le hab hp hAC hC hS)

/-- **A bound on the expected action does not give tightness.** There is a set of probability
measures on the path space `C([0, 1], ℓ²)` that is not tight, although each of its members is
concentrated on curves absolutely continuous on `[0, 1]` and starting at `0`, so that its law at
time `0` is the Dirac mass at `0`, and has expected `p`-action at most `1` for every `p ≥ 0`. It
consists of the Dirac masses at the `1`-Lipschitz curves `t ↦ t • eₙ`. So the tightness of the
time marginals cannot be dropped from
`TauCeti.isTightMeasureSet_of_map_eval_of_lintegral_curveAction_le`. -/
theorem exists_not_isTightMeasureSet_lintegral_curveAction_le :
    ∃ S : Set (Measure C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2)),
      (∀ P ∈ S, IsProbabilityMeasure P) ∧
      (∀ P ∈ S, ∀ᵐ γ : C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2) ∂P,
        AbsolutelyContinuousOnInterval (IccExtend zero_le_one γ) 0 1 ∧
          γ ⟨0, left_mem_Icc.mpr zero_le_one⟩ = 0) ∧
      (∀ P ∈ S, ∀ p : ℝ, 0 ≤ p →
        ∫⁻ γ : C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2),
          curveAction p (IccExtend zero_le_one γ) 0 1 ∂P ≤ 1) ∧
      ¬ IsTightMeasureSet S := by
  obtain ⟨γ, hLip, h0, hγ⟩ := exists_lipschitzWith_one_not_isCompact_closure_range
  -- The extensions of the curves by constants are still `1`-Lipschitz.
  have hLip' (n : ℕ) : LipschitzWith 1 (IccExtend zero_le_one (γ n)) := by
    have hext : IccExtend zero_le_one (γ n) = γ n ∘ projIcc 0 1 zero_le_one :=
      funext fun _ ↦ IccExtend_apply _ _ _
    simpa [hext] using (hLip n).comp (LipschitzWith.projIcc zero_le_one)
  refine ⟨range fun n ↦ Measure.dirac (γ n), ?_, ?_, ?_, fun hS ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩
    infer_instance
  · rintro _ ⟨n, rfl⟩
    rw [ae_dirac_eq]
    exact eventually_pure.2
      ⟨(hLip' n).lipschitzOnWith.absolutelyContinuousOnInterval, h0 n⟩
  · rintro _ ⟨n, rfl⟩ p hp
    rw [lintegral_dirac' _ (measurable_curveAction_IccExtend zero_le_one p 0 1)]
    simpa [edist_dist] using (hLip' n).curveAction_le hp 0 1
  -- A compact set carrying mass at least `1 / 2` of every Dirac mass contains every curve.
  obtain ⟨K, hK, hKS⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hS (1 / 2)
    (by norm_num)
  have hmem : ∀ n, γ n ∈ K := fun n ↦ by
    by_contra hn
    have := hKS _ ⟨n, rfl⟩
    rw [Measure.dirac_apply_of_mem (mem_compl hn)] at this
    norm_num at this
  exact hγ (hK.closure_of_subset (range_subset_iff.2 hmem))

end TauCeti
