/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.Measure.Tight.ContinuousMap
import TauCeti.Analysis.Normed.Lp.AscoliCounterexample

/-!
# Tightness of laws of curves with bounded expected action

Let `1 < p`. By the Hölder estimate
`d(γ s, γ t) ^ p ≤ |t - s| ^ (p - 1) * A_p(γ)`
(`AbsolutelyContinuousOnInterval.edist_rpow_le_mul_curveAction`), the paths in `C([a, b], X)` that
are absolutely continuous with `p`-action `A_p(γ) ≤ M < ∞` are uniformly equicontinuous, with the
common modulus `δ ↦ δ ^ (1 - 1 / p) * M ^ (1 / p)`.

Consider a set `S` of measures on the path space whose members are concentrated on absolutely
continuous paths. If the expected actions are uniformly bounded, `∫ A_p dP ≤ C < ∞` for `P ∈ S`,
then Markov's inequality `P {A_p ≥ M} ≤ C / M` makes the action uniformly small in probability, and
the equicontinuity above turns this into the uniform modulus of continuity in probability of the
tightness criterion `TauCeti.isTightMeasureSet_of_map_eval_of_continuity_modulus`. If moreover the
time marginals of `S` at a dense set of times are tight and the pseudometric space `X` is
complete, then `S` is tight.
This is the compactness step for laws of random curves of finite action, for instance in the
superposition principle for absolutely continuous curves of probability measures.

The action bound supplies only the modulus of continuity. It does not control where the curves
are, so on a carrier that is not proper the tightness of the time marginals remains a separate
hypothesis: the Dirac masses at the curves `γₙ(t) = t • eₙ` in `ℓ²` have `p`-action at most `1` for
every `p ≥ 0`, yet they do not form a tight set
(`TauCeti.exists_lintegral_curveAction_le_one_not_isTightMeasureSet`). Both restrictions on the
curves are needed for the modulus: for `p = 1` the action bounds only the length, which allows
arbitrarily steep curves, and without absolute continuity the action does not bound the
displacement at all, since a continuous curve can have metric derivative zero almost everywhere
and still move, like the Cantor function.

## Main results

* `TauCeti.measure_continuity_modulus_le_lintegral_curveAction`: the explicit Hölder–Markov
  bound on oscillation probabilities, valid already for `1 ≤ p`.

* `TauCeti.uniformEquicontinuous_of_absolutelyContinuousOnInterval_of_curveAction_le`: absolutely
  continuous paths of `p`-action at most `M < ∞` are uniformly equicontinuous, for `1 < p`.
* `TauCeti.exists_continuity_modulus_le_of_absolutelyContinuousOnInterval_of_curveAction`: if the
  paths are almost surely absolutely continuous and the action is uniformly small in probability,
  the laws satisfy a uniform modulus of continuity in probability.
* `exists_continuity_modulus_le_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le`:
  the same under a uniform bound on the expected action.
* `isTightMeasureSet_of_map_eval_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le`:
  tight time marginals, almost surely absolutely continuous paths and a uniformly bounded expected
  action give tightness.
* `TauCeti.exists_lintegral_curveAction_le_one_not_isTightMeasureSet`: the bound on the expected
  action alone does not give tightness.

## References

* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley 1999, Theorem 7.3.
-/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Interval

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
  rw [← lintegral_const_mul _ hA]
  exact meas_ge_le_lintegral_div (hA.const_mul _).aemeasurable hηp hηp'

/-- **Paths of bounded action are uniformly equicontinuous.** For `1 < p` and `M < ∞`, the paths
`γ ∈ C([a, b], X)` that are absolutely continuous with `p`-action at most `M` form a uniformly
equicontinuous family: by the Hölder estimate, `d(γ s, γ t) ^ p ≤ |t - s| ^ (p - 1) * M`. -/
theorem uniformEquicontinuous_of_absolutelyContinuousOnInterval_of_curveAction_le (hab : a ≤ b)
    (hp : 1 < p) {M : ℝ≥0∞} (hM : M ≠ ∞) :
    UniformEquicontinuous fun γ : {γ : C(Icc a b, X) //
        AbsolutelyContinuousOnInterval (IccExtend hab γ) a b ∧
          curveAction p (IccExtend hab γ) a b ≤ M} ↦ ⇑(γ : C(Icc a b, X)) := by
  rw [Metric.uniformEquicontinuous_iff]
  intro η hη
  -- The Hölder bound `r ^ (p - 1) * M` on `d(γ s, γ t) ^ p` tends to `0` with the time step `r`.
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r ^ (p - 1) * M) (𝓝 0) (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := p - 1)).comp
      ENNReal.continuous_ofReal).tendsto 0
    simp only [Function.comp_apply, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (sub_pos.2 hp)] at h
    simpa using ENNReal.Tendsto.mul_const h (Or.inr hM)
  obtain ⟨δ, hδ, hδη⟩ := Metric.eventually_nhds_iff.mp (hlim.eventually (gt_mem_nhds
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hη) ENNReal.ofReal_ne_top)))
  refine ⟨δ, hδ, fun s t hst ⟨γ, hγ, hA⟩ ↦ ?_⟩
  have hs : (s : ℝ) ∈ uIcc a b := by simp [uIcc_of_le hab]
  have ht : (t : ℝ) ∈ uIcc a b := by simp [uIcc_of_le hab]
  have hsub : Ι (s : ℝ) t ⊆ Ι a b := uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hs ht)
  have hlt : edist (γ s) (γ t) ^ p < ENNReal.ofReal η ^ p := by
    calc edist (γ s) (γ t) ^ p
        ≤ edist (s : ℝ) t ^ (p - 1) * curveAction p (IccExtend hab γ) s t := by
          simpa only [IccExtend_val] using hγ.edist_rpow_le_mul_curveAction hp.le hs ht
      _ ≤ ENNReal.ofReal (dist s t) ^ (p - 1) * M := by
          rw [edist_dist]
          exact mul_le_mul_right ((curveAction_mono p _ hsub).trans hA) _
      _ < ENNReal.ofReal η ^ p := hδη (by simpa [abs_of_nonneg dist_nonneg] using hst)
  rw [ENNReal.rpow_lt_rpow_iff (by linarith), edist_dist,
    ENNReal.ofReal_lt_ofReal_iff hη] at hlt
  exact hlt

/-- **An action small in probability gives a modulus of continuity in probability.** Let `1 < p`
and let `S` be a set of measures on `C([a, b], X)`, each concentrated on absolutely continuous
paths, whose `p`-action is uniformly small in probability: for every `ε > 0` there is `M < ∞`
with `P {γ | M ≤ A_p(γ)} ≤ ε` for all `P ∈ S`. Then for all `η, ε > 0` there is `δ > 0` such that,
for every `P ∈ S`, the paths with two times closer than `δ` at which their values are at least
`η` apart have `P`-measure at most `ε`. -/
theorem exists_continuity_modulus_le_of_absolutelyContinuousOnInterval_of_curveAction
    (hab : a ≤ b) (hp : 1 < p) {S : Set (Measure C(Icc a b, X))}
    (hAC : ∀ P ∈ S, ∀ᵐ γ : C(Icc a b, X) ∂P, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hA : ∀ ε > 0, ∃ M ≠ ∞, ∀ P ∈ S,
      P {γ : C(Icc a b, X) | M ≤ curveAction p (IccExtend hab γ) a b} ≤ ε) :
    ∀ η > 0, ∀ ε > 0, ∃ δ > 0, ∀ P ∈ S,
      P {γ : C(Icc a b, X) | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} ≤ ε := by
  intro η hη ε hε
  obtain ⟨M, hM, hMS⟩ := hA ε hε
  obtain ⟨δ, hδ, hδη⟩ := Metric.uniformEquicontinuous_iff.mp
    (uniformEquicontinuous_of_absolutelyContinuousOnInterval_of_curveAction_le (X := X) hab hp hM)
      η hη
  refine ⟨δ, hδ, fun P hP ↦ ?_⟩
  -- An oscillating path is either not absolutely continuous or has action at least `M`.
  calc P {γ : C(Icc a b, X) | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)}
      ≤ P ({γ | ¬AbsolutelyContinuousOnInterval (IccExtend hab γ) a b} ∪
          {γ | M ≤ curveAction p (IccExtend hab γ) a b}) := by
        refine measure_mono fun γ ⟨s, t, hst, hle⟩ ↦ ?_
        by_contra h
        simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_le] at h
        exact (hδη s t hst ⟨γ, h.1, h.2.le⟩).not_ge hle
    _ ≤ 0 + ε := (measure_union_le _ _).trans (add_le_add (ae_iff.mp (hAC P hP)).le (hMS P hP))
    _ = ε := zero_add ε

/-- **A bounded expected action gives a modulus of continuity in probability.** Let `1 < p` and
let `S` be a set of measures on `C([a, b], X)`, each concentrated on absolutely continuous paths,
with uniformly bounded expected `p`-action `∫ A_p dP ≤ C < ∞`. Then for all `η, ε > 0` there is
`δ > 0` such that, for every `P ∈ S`, paths with two times closer than `δ` at which their values
are at least `η` apart have `P`-measure at most `ε`. -/
theorem exists_continuity_modulus_le_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le
    (hab : a ≤ b) (hp : 1 < p) {S : Set (Measure C(Icc a b, X))} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hAC : ∀ P ∈ S, ∀ᵐ γ : C(Icc a b, X) ∂P, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hA : ∀ P ∈ S, ∫⁻ γ : C(Icc a b, X), curveAction p (IccExtend hab γ) a b ∂P ≤ C) :
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
  exact hA P hP

/-- **Tightness of laws of curves with bounded expected action.** Let `X` be a complete pseudometric
space, `1 < p`, and `D ⊆ [a, b]` dense. A set `S` of measures on `C([a, b], X)` is tight if the time
marginals at the times of `D` are tight and its members are concentrated on absolutely continuous
paths with uniformly bounded expected `p`-action `∫ A_p dP ≤ C < ∞`. -/
theorem isTightMeasureSet_of_map_eval_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] (hab : a ≤ b) (hp : 1 < p)
    {S : Set (Measure C(Icc a b, X))} {D : Set (Icc a b)} (hD : Dense D)
    (h_eval : ∀ t ∈ D,
      IsTightMeasureSet ((fun P : Measure C(Icc a b, X) ↦ P.map fun γ ↦ γ t) '' S))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hAC : ∀ P ∈ S, ∀ᵐ γ : C(Icc a b, X) ∂P, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hA : ∀ P ∈ S, ∫⁻ γ : C(Icc a b, X), curveAction p (IccExtend hab γ) a b ∂P ≤ C) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_map_eval_of_continuity_modulus hD h_eval
    (exists_continuity_modulus_le_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le
      hab hp hC hAC hA)

/-- **A bounded expected action does not give tightness.** The Dirac masses at the curves
`γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors `eₙ` of `ℓ²` are concentrated on
absolutely continuous paths starting at zero, of `p`-action at most `1` for every `p ≥ 0`, but they
do not form a tight set of measures on `C([0, 1], ℓ²)`. The hypothesis on the time marginals of
`isTightMeasureSet_of_map_eval_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le`
therefore cannot be dropped. -/
theorem exists_lintegral_curveAction_le_one_not_isTightMeasureSet :
    ∃ γ : ℕ → C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2),
      (∀ n, AbsolutelyContinuousOnInterval (IccExtend zero_le_one (γ n)) 0 1) ∧
      (∀ n, γ n ⟨0, left_mem_Icc.mpr zero_le_one⟩ = 0) ∧
      (∀ n p, 0 ≤ p →
        ∫⁻ c, curveAction p (IccExtend zero_le_one c) 0 1 ∂Measure.dirac (γ n) ≤ 1) ∧
      ¬IsTightMeasureSet (range fun n ↦ Measure.dirac (γ n)) := by
  obtain ⟨γ, hlip, h0, hγ⟩ := exists_lipschitzWith_one_not_isCompact_closure_range
  have hlip' (n : ℕ) : LipschitzWith 1 (IccExtend zero_le_one (γ n)) := by
    simpa [IccExtend] using (hlip n).comp (LipschitzWith.projIcc zero_le_one)
  refine ⟨γ, fun n ↦ (hlip' n).lipschitzOnWith.absolutelyContinuousOnInterval,
    h0, fun n p hp ↦ ?_, fun hS ↦ ?_⟩
  · rw [lintegral_dirac' _ (measurable_curveAction_IccExtend zero_le_one p 0 1)]
    simpa using (hlip' n).curveAction_le hp 0 1
  -- A tight set of Dirac masses has its atoms in one compact set.
  obtain ⟨K, hK, hKS⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hS (1 / 2) (by norm_num)
  refine hγ (hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed))
  rintro _ ⟨n, rfl⟩
  by_contra h
  have h' := hKS _ ⟨n, rfl⟩
  rw [Measure.dirac_apply_of_mem h] at h'
  norm_num at h'

end TauCeti
