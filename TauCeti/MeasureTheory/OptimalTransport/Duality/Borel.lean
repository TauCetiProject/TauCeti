/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous

import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.MeasureTheory.Constructions.Polish.Capacitability
import TauCeti.MeasureTheory.Function.Lp.ConvexHull
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# Strong Kantorovich duality for bounded Borel costs

This file proves strong Kantorovich duality on Polish spaces for bounded Borel measurable costs
`c : X × Y → ℝ≥0∞` (`c ≤ B` for a finite constant `B : ℝ≥0`), with the dual supremum taken over
either bounded Borel measurable potential pairs or integrable potential pairs. This supplies the
bounded-cost core behind relaxed Borel Kantorovich duality in
`TauCeti.MeasureTheory.OptimalTransport.Duality.Relaxed`.

Continuous potentials do not suffice even for `{0, 1}`-valued Borel costs: on `[0, 1]` with
Lebesgue measure, the indicator of `([0, 1] \ ℚ) × [0, 1]` has transport cost `1`, whereas density
of `ℚ` forces every continuous dual-feasible pair to satisfy `φ x + ψ y ≤ 0` everywhere.

## Proof outline

Subtracting a bounded Borel cost `c ≤ B` from `B` flips primal minimization and dual maximization
into primal maximization `sup_π ∫⁻ f dπ` and `[0, B]`-valued Borel upper-envelope minimization
`inf_{u + v ≥ f} (∫⁻ u dμ + ∫⁻ v dν)` for `f = B - c`.

1. **Agreement and downward continuity on upper-semicontinuous functions.** For upper-semicontinuous
   `g ≤ B`, `B - g` is lower semicontinuous, so Polish lower-semicontinuous duality equates the two
   functionals, while tightness of couplings (`TauCeti.transportCost_iSup_eq_iSup`) gives downward
   continuity along decreasing upper-semicontinuous sequences.
2. **Upward continuity via `L²` tail convex combinations.** Along any increasing sequence of
   `[0, B]`-valued functions, almost-minimizing envelopes form bounded sequences in `L²(μ)` and
   `L²(ν)`. Passing to jointly almost everywhere convergent finite tail convex combinations
   (`TauCeti.exists_tendsto_sum_smul_toLp_and_ae_prod_of_isBounded_range`) and taking pointwise
   `limsup` preserves measurability, `[0, B]` bounds, marginal integrals, and the upper-envelope
   inequality in the limit.
3. **Choquet capacitability on finite-level subgraphs.** Lifting a `[0, 1]`-valued Borel integrand
   `f` to its `N`-level subgraph in `(X × Y) × Fin N` turns the upper-envelope functional into a
   Choquet capacity (`TauCeti.IsChoquetCapacity`). Inner compact approximation of analytic sets
   (`TauCeti.IsChoquetCapacity.analyticSet_eq_biSup_isCompact`) reduces Borel `f` to compact sets,
   whose slice counts are upper semicontinuous.

## Main statements

* `TauCeti.isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le` and
  `TauCeti.transportCost_eq_sSup_ofReal_kantorovichDualValue_bounded_measurable_of_le` — **strong
  Kantorovich duality for bounded Borel costs** over bounded Borel measurable potentials;
* `TauCeti.isLUB_ofReal_kantorovichDualValue_integrable_of_measurable_of_le` and
  `TauCeti.transportCost_eq_sSup_ofReal_kantorovichDualValue_integrable_of_measurable_of_le` —
  **strong Kantorovich duality for bounded Borel costs** over integrable potentials.

## References

* M. Beiglböck, C. Léonard and W. Schachermayer, *A general duality theorem for the
  Monge--Kantorovich transport problem*, Studia Math. 209 (2012), 151--167, Proposition 2.1.
* H. G. Kellerer, *Duality theorems for marginal problems*, Z. Wahrsch. Verw. Gebiete 67 (1984),
  399--432.
* G. Choquet, *Theory of capacities*, Ann. Inst. Fourier 5 (1954), 131--295.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace TauCeti

/-! ### Bounded primal maximization and Borel upper-envelope scaffolding -/

section UpperEnvelope

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

/-- Maximum coupling integral `sup_π ∫⁻ f dπ` of a nonnegative integrand, used internally to flip
bounded Borel minimization into a Choquet-capacitable maximization problem. -/
private def primalMaxValue (μ : Measure X) (ν : Measure Y) (f : X × Y → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), ∫⁻ z, f z ∂π

/-- Infimum of `∫⁻ u dμ + ∫⁻ v dν` over `[0, B]`-valued measurable upper-envelope pairs
`u x + v y ≥ f (x, y)`. -/
private def dualUpperValue (B : ℝ≥0) (μ : Measure X) (ν : Measure Y)
    (f : X × Y → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (u : X → ℝ≥0∞) (_ : Measurable u) (_ : ∀ x, u x ≤ B)
    (v : Y → ℝ≥0∞) (_ : Measurable v) (_ : ∀ y, v y ≤ B)
    (_ : ∀ x y, f (x, y) ≤ u x + v y), ((∫⁻ x, u x ∂μ) + ∫⁻ y, v y ∂ν)

private lemma primalMaxValue_mono {f g : X × Y → ℝ≥0∞} (hfg : f ≤ g) :
    primalMaxValue μ ν f ≤ primalMaxValue μ ν g :=
  iSup₂_mono fun _ _ ↦ lintegral_mono hfg

private lemma mul_primalMaxValue_le {c : ℝ≥0∞} {f g : X × Y → ℝ≥0∞} (hf : Measurable f)
    (hfg : ∀ z, c * f z ≤ g z) :
    c * primalMaxValue μ ν f ≤ primalMaxValue μ ν g := by
  rw [primalMaxValue, ENNReal.mul_iSup]
  refine iSup_le fun π ↦ ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun hπ ↦ ((lintegral_const_mul c hf).symm.le.trans (lintegral_mono hfg)).trans
    (le_iSup₂_of_le π hπ le_rfl)

private lemma dualUpperValue_le {B : ℝ≥0} {f : X × Y → ℝ≥0∞} {u : X → ℝ≥0∞} {v : Y → ℝ≥0∞}
    (hu : Measurable u) (huB : ∀ x, u x ≤ B) (hv : Measurable v) (hvB : ∀ y, v y ≤ B)
    (huv : ∀ x y, f (x, y) ≤ u x + v y) :
    dualUpperValue B μ ν f ≤ (∫⁻ x, u x ∂μ) + ∫⁻ y, v y ∂ν :=
  iInf₂_le_of_le u hu <| iInf_le_of_le huB <|
    iInf₂_le_of_le v hv <| iInf₂_le hvB huv

private lemma dualUpperValue_mono {B : ℝ≥0} {f g : X × Y → ℝ≥0∞} (hfg : f ≤ g) :
    dualUpperValue B μ ν f ≤ dualUpperValue B μ ν g :=
  iInf₂_mono fun _ _ ↦ iInf_mono fun _ ↦ iInf₂_mono fun _ _ ↦ iInf_mono fun _ ↦
    iInf_mono' fun h ↦ ⟨fun x y ↦ (hfg (x, y)).trans (h x y), le_rfl⟩

private lemma dualUpperValue_le_mul_univ {B : ℝ≥0} {f : X × Y → ℝ≥0∞} (hf : ∀ z, f z ≤ B) :
    dualUpperValue B μ ν f ≤ (B : ℝ≥0∞) * μ univ := by
  have hle := dualUpperValue_le (μ := μ) (ν := ν) (u := fun _ ↦ (B : ℝ≥0∞)) (v := fun _ ↦ 0)
    measurable_const (fun _ ↦ le_rfl) measurable_const (fun _ ↦ zero_le)
    (fun x y ↦ by simpa using hf (x, y))
  simpa using hle

private lemma primalMaxValue_le_dualUpperValue {B : ℝ≥0} (f : X × Y → ℝ≥0∞) :
    primalMaxValue μ ν f ≤ dualUpperValue B μ ν f := by
  refine iSup₂_le fun π hπ ↦ le_iInf₂ fun u hu ↦ le_iInf fun _ ↦
    le_iInf₂ fun v hv ↦ le_iInf fun _ ↦ le_iInf fun huv ↦ ?_
  calc
    ∫⁻ z, f z ∂π ≤ ∫⁻ z, (u z.1 + v z.2) ∂π := lintegral_mono fun z ↦ huv z.1 z.2
    _ = (∫⁻ z, u z.1 ∂π) + ∫⁻ z, v z.2 ∂π :=
      lintegral_add_left (hu.comp measurable_fst) _
    _ = (∫⁻ x, u x ∂μ) + ∫⁻ y, v y ∂ν := by
      rw [hπ.lintegral_comp_fst hu.aemeasurable, hπ.lintegral_comp_snd hv.aemeasurable]

private lemma le_mul_dualUpperValue_add {B : ℝ≥0} {f : X × Y → ℝ≥0∞}
    {a c d : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (h : ∀ (u : X → ℝ≥0∞), Measurable u → (∀ x, u x ≤ B) → ∀ (v : Y → ℝ≥0∞), Measurable v →
      (∀ y, v y ≤ B) → (∀ x y, f (x, y) ≤ u x + v y) →
      a ≤ c * ((∫⁻ x, u x ∂μ) + ∫⁻ y, v y ∂ν) + d) :
    a ≤ c * dualUpperValue B μ ν f + d := by
  rw [dualUpperValue]
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hctop, ENNReal.iInf_add]
  exact le_iInf₂ fun u hu ↦ le_iInf fun huB ↦ le_iInf₂ fun v hv ↦ le_iInf₂ (h u hu huB v hv)

private lemma primalMaxValue_eq_sub_transportCost [IsProbabilityMeasure μ]
    {B : ℝ≥0} {f : X × Y → ℝ≥0∞} (hf_meas : Measurable f)
    (hf_le : ∀ z, f z ≤ B) :
    primalMaxValue μ ν f = (B : ℝ≥0∞) - transportCost (fun z ↦ (B : ℝ≥0∞) - f z) μ ν := by
  have hπ_eq {π : Measure (X × Y)} (hπ : IsCoupling π μ ν) :
      ∫⁻ z, f z ∂π = (B : ℝ≥0∞) - ∫⁻ z, ((B : ℝ≥0∞) - f z) ∂π := by
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    have hsum : (∫⁻ z, f z ∂π) + ∫⁻ z, ((B : ℝ≥0∞) - f z) ∂π = B := by
      rw [← lintegral_add_left hf_meas]
      have hcongr : (fun z ↦ f z + ((B : ℝ≥0∞) - f z)) = fun _ ↦ (B : ℝ≥0∞) :=
        funext fun z ↦ add_tsub_cancel_of_le (hf_le z)
      simp [hcongr]
    exact ENNReal.eq_sub_of_add_eq' ENNReal.coe_ne_top hsum
  rw [transportCost_def, ENNReal.sub_iInf]
  refine iSup_congr fun π ↦ ?_
  by_cases hπ : IsCoupling π μ ν
  · simp [hπ, hπ_eq hπ]
  · simp [hπ]

/-! ### Upward continuity of the upper-envelope functional via `L²` tail convex hulls -/

/-- Given measurable upper-envelope sequences bounded above by `B` that converge `μ`- and `ν`-almost
everywhere with marginal integral sums at most `M`, taking pointwise `limsup` produces a measurable
`[0, B]`-valued upper envelope for `⨆ n, fs n` and bounds `dualUpperValue` by `M`. -/
private lemma dualUpperValue_iSup_le_of_tendsto_ae [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : ℝ≥0} {fs : ℕ → X × Y → ℝ≥0∞} (hmono : Monotone fs)
    {u' : ℕ → X → ℝ} {v' : ℕ → Y → ℝ}
    (hu'_meas : ∀ n, Measurable (u' n)) (hu'_le : ∀ n x, u' n x ≤ B)
    (hv'_meas : ∀ n, Measurable (v' n)) (hv'_le : ∀ n y, v' n y ≤ B)
    (huv' : ∀ n x y, fs n (x, y) ≤ ENNReal.ofReal (u' n x) + ENNReal.ofReal (v' n y))
    {M : ℝ≥0∞}
    (hM' : ∀ n, (∫⁻ x, ENNReal.ofReal (u' n x) ∂μ) + ∫⁻ y, ENNReal.ofReal (v' n y) ∂ν ≤ M)
    (hae₁ : ∀ᵐ x ∂μ, ∃ l, Tendsto (fun n ↦ u' n x) atTop (𝓝 l))
    (hae₂ : ∀ᵐ y ∂ν, ∃ l, Tendsto (fun n ↦ v' n y) atTop (𝓝 l)) :
    dualUpperValue B μ ν (fun z ↦ ⨆ n, fs n z) ≤ M := by
  let U_lim : X → ℝ≥0∞ := fun x ↦ limsup (fun n ↦ ENNReal.ofReal (u' n x)) atTop
  let V_lim : Y → ℝ≥0∞ := fun y ↦ limsup (fun n ↦ ENNReal.ofReal (v' n y)) atTop
  have hU_lim_le (x : X) : U_lim x ≤ B :=
    limsup_le_of_le ⟨0, fun _ _ ↦ zero_le⟩ <| .of_forall fun n ↦ by
      simpa using ENNReal.ofReal_le_ofReal (hu'_le n x)
  have hV_lim_le (y : Y) : V_lim y ≤ B :=
    limsup_le_of_le ⟨0, fun _ _ ↦ zero_le⟩ <| .of_forall fun n ↦ by
      simpa using ENNReal.ofReal_le_ofReal (hv'_le n y)
  have hUV_lim (x : X) (y : Y) : (⨆ m, fs m (x, y)) ≤ U_lim x + V_lim y := by
    refine iSup_le fun m ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_pos.2 hε).ne').ne'
    have hu_ev := eventually_lt_of_limsup_lt (f := atTop)
      (ENNReal.lt_add_right (ne_top_of_le_ne_top ENNReal.coe_ne_top (hU_lim_le x)) hε2)
      ⟨⊤, .of_forall fun _ ↦ le_top⟩
    have hv_ev := eventually_lt_of_limsup_lt (f := atTop)
      (ENNReal.lt_add_right (ne_top_of_le_ne_top ENNReal.coe_ne_top (hV_lim_le y)) hε2)
      ⟨⊤, .of_forall fun _ ↦ le_top⟩
    obtain ⟨n, hmn, hun, hvn⟩ := ((eventually_ge_atTop m).and (hu_ev.and hv_ev)).exists
    calc
      fs m (x, y) ≤ ENNReal.ofReal (u' n x) + ENNReal.ofReal (v' n y) :=
        (hmono hmn (x, y)).trans (huv' n x y)
      _ ≤ (U_lim x + ε / 2) + (V_lim y + ε / 2) := add_le_add hun.le hvn.le
      _ = (U_lim x + V_lim y) + ε := by rw [add_add_add_comm, ENNReal.add_halves]
  have hint_u : Tendsto (fun n ↦ ∫⁻ x, ENNReal.ofReal (u' n x) ∂μ) atTop (𝓝 (∫⁻ x, U_lim x ∂μ)) :=
    tendsto_lintegral_filter_limsup_of_dominated_convergence (fun _ ↦ (B : ℝ≥0∞))
      (.of_forall fun n ↦ (hu'_meas n).ennreal_ofReal.aemeasurable)
      (.of_forall fun n ↦ .of_forall fun x ↦ by simpa using ENNReal.ofReal_le_ofReal (hu'_le n x))
      (by simp [ENNReal.mul_ne_top, measure_ne_top])
      (hae₁.mono fun _ ⟨_, hx⟩ ↦ ⟨_, ENNReal.tendsto_ofReal hx⟩)
  have hint_v : Tendsto (fun n ↦ ∫⁻ y, ENNReal.ofReal (v' n y) ∂ν) atTop (𝓝 (∫⁻ y, V_lim y ∂ν)) :=
    tendsto_lintegral_filter_limsup_of_dominated_convergence (fun _ ↦ (B : ℝ≥0∞))
      (.of_forall fun n ↦ (hv'_meas n).ennreal_ofReal.aemeasurable)
      (.of_forall fun n ↦ .of_forall fun y ↦ by simpa using ENNReal.ofReal_le_ofReal (hv'_le n y))
      (by simp [ENNReal.mul_ne_top, measure_ne_top])
      (hae₂.mono fun _ ⟨_, hy⟩ ↦ ⟨_, ENNReal.tendsto_ofReal hy⟩)
  exact (dualUpperValue_le (Measurable.limsup fun n ↦ (hu'_meas n).ennreal_ofReal) hU_lim_le
    (Measurable.limsup fun n ↦ (hv'_meas n).ennreal_ofReal) hV_lim_le hUV_lim).trans <|
    le_of_tendsto (hint_u.add hint_v) (.of_forall hM')

/-- Along an increasing sequence of functions dominated by `[0, B]`-valued measurable upper-envelope
pairs with marginal integral sum at most `M`, passing to jointly almost everywhere convergent `L²`
tail convex combinations bounds `dualUpperValue` of the supremum by `M`. -/
private lemma dualUpperValue_iSup_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : ℝ≥0} {fs : ℕ → X × Y → ℝ≥0∞} (hmono : Monotone fs)
    {U : ℕ → X → ℝ≥0∞} {V : ℕ → Y → ℝ≥0∞}
    (hU_meas : ∀ n, Measurable (U n)) (hU_le : ∀ n x, U n x ≤ B)
    (hV_meas : ∀ n, Measurable (V n)) (hV_le : ∀ n y, V n y ≤ B)
    (hUV : ∀ n x y, fs n (x, y) ≤ U n x + V n y)
    {M : ℝ≥0∞} (hM : ∀ n, (∫⁻ x, U n x ∂μ) + ∫⁻ y, V n y ∂ν ≤ M) :
    dualUpperValue B μ ν (fun z ↦ ⨆ n, fs n z) ≤ M := by
  let u : ℕ → X → ℝ := fun n x ↦ (U n x).toReal
  let v : ℕ → Y → ℝ := fun n y ↦ (V n y).toReal
  have hu_bdd (n : ℕ) : ∀ᵐ x ∂μ, ‖u n x‖ ≤ B := .of_forall fun x ↦ by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_coe_of_le_coe (hU_le n x)
  have hv_bdd (n : ℕ) : ∀ᵐ y ∂ν, ‖v n y‖ ≤ B := .of_forall fun y ↦ by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_coe_of_le_coe (hV_le n y)
  have hu_lp (n : ℕ) : MemLp (u n) 2 μ :=
    MemLp.of_bound (hU_meas n).ennreal_toReal.aestronglyMeasurable B (hu_bdd n)
  have hv_lp (n : ℕ) : MemLp (v n) 2 ν :=
    MemLp.of_bound (hV_meas n).ennreal_toReal.aestronglyMeasurable B (hv_bdd n)
  obtain ⟨_, _, s, w, hw0, hw1, -, -, hae₁, hae₂⟩ :=
    exists_tendsto_sum_smul_toLp_and_ae_prod_of_isBounded_range hu_lp hv_lp
      (isBounded_range_toLp_of_ae_bound hu_lp hu_bdd)
      (isBounded_range_toLp_of_ae_bound hv_lp hv_bdd)
  let u' : ℕ → X → ℝ := fun n x ↦ ∑ i ∈ s n, w n i * u (n + i) x
  let v' : ℕ → Y → ℝ := fun n y ↦ ∑ i ∈ s n, w n i * v (n + i) y
  have hsum_w (n : ℕ) : ∑ i ∈ s n, ENNReal.ofReal (w n i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (hw0 n), hw1 n, ENNReal.ofReal_one]
  refine dualUpperValue_iSup_le_of_tendsto_ae (u' := u') (v' := v') hmono
    (fun n ↦ Finset.measurable_sum _ fun i _ ↦
      measurable_const.mul (hU_meas (n + i)).ennreal_toReal)
    (fun n x ↦ ((convex_Icc (0 : ℝ) B).sum_mem (hw0 n) (hw1 n) fun i _ ↦
      ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_coe_of_le_coe (hU_le (n + i) x)⟩).2)
    (fun n ↦ Finset.measurable_sum _ fun i _ ↦
      measurable_const.mul (hV_meas (n + i)).ennreal_toReal)
    (fun n y ↦ ((convex_Icc (0 : ℝ) B).sum_mem (hw0 n) (hw1 n) fun i _ ↦
      ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_coe_of_le_coe (hV_le (n + i) y)⟩).2)
    (fun n x y ↦ ?_) (fun n ↦ ?_)
    (hae₁.mono fun _ hx ↦ ⟨_, by simpa only [u', smul_eq_mul] using hx⟩)
    (hae₂.mono fun _ hy ↦ ⟨_, by simpa only [v', smul_eq_mul] using hy⟩)
  · have hu_eq : ENNReal.ofReal (u' n x) = ∑ i ∈ s n, ENNReal.ofReal (w n i) * U (n + i) x := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i hi ↦ mul_nonneg (hw0 n i hi) ENNReal.toReal_nonneg]
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [ENNReal.ofReal_mul (hw0 n i hi),
          ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hU_le (n + i) x))]
    have hv_eq : ENNReal.ofReal (v' n y) = ∑ i ∈ s n, ENNReal.ofReal (w n i) * V (n + i) y := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i hi ↦ mul_nonneg (hw0 n i hi) ENNReal.toReal_nonneg]
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [ENNReal.ofReal_mul (hw0 n i hi),
          ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hV_le (n + i) y))]
    rw [hu_eq, hv_eq, ← Finset.sum_add_distrib]
    refine (Finset.sum_le_sum fun i _ ↦ (mul_le_mul_of_nonneg_left
      ((hmono (Nat.le_add_right n i) (x, y)).trans (hUV (n + i) x y)) zero_le).trans_eq
      (mul_add _ _ _)).trans_eq' ?_
    rw [← Finset.sum_mul, hsum_w n, one_mul]
  · rw [lintegral_ofReal_finsetSum_mul_toReal (hw0 n)
        (fun i _ ↦ (hU_meas (n + i)).aemeasurable)
        (fun i _ ↦ .of_forall fun x ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hU_le (n + i) x)),
      lintegral_ofReal_finsetSum_mul_toReal (hw0 n)
        (fun i _ ↦ (hV_meas (n + i)).aemeasurable)
        (fun i _ ↦ .of_forall fun y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hV_le (n + i) y)),
      ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum fun i _ ↦ (mul_add _ _ _).symm.le.trans
      (mul_le_mul_of_nonneg_left (hM (n + i)) zero_le)).trans_eq
      (by rw [← Finset.sum_mul, hsum_w n, one_mul])

/-- **Upward continuity of the bounded Borel upper-envelope functional.** Along any increasing
sequence of `[0, B]`-valued functions (with no measurability or topology required), `dualUpperValue`
commutes with the pointwise supremum. -/
private lemma dualUpperValue_iSup_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B : ℝ≥0}
    {fs : ℕ → X × Y → ℝ≥0∞} (hmono : Monotone fs) (hfs_le : ∀ n z, fs n z ≤ B) :
    dualUpperValue B μ ν (fun z ↦ ⨆ n, fs n z) = ⨆ n, dualUpperValue B μ ν (fs n) := by
  refine le_antisymm ?_ (iSup_le fun n ↦ dualUpperValue_mono fun z ↦ le_iSup (fun m ↦ fs m z) n)
  let α : ℝ≥0∞ := ⨆ n, dualUpperValue B μ ν (fs n)
  have hα_fin : α ≠ ∞ :=
    ne_top_of_le_ne_top (b := (B : ℝ≥0∞) * μ univ)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top μ univ))
      (iSup_le fun n ↦ dualUpperValue_le_mul_univ (hfs_le n))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hlt (n : ℕ) : dualUpperValue B μ ν (fs n) < α + ε :=
    (le_iSup (fun m ↦ dualUpperValue B μ ν (fs m)) n).trans_lt
      (ENNReal.lt_add_right hα_fin (ENNReal.coe_pos.2 hε).ne')
  have hex (n : ℕ) :
      ∃ (U : X → ℝ≥0∞) (V : Y → ℝ≥0∞),
        Measurable U ∧ (∀ x, U x ≤ B) ∧ Measurable V ∧ (∀ y, V y ≤ B) ∧
        (∀ x y, fs n (x, y) ≤ U x + V y) ∧
        (∫⁻ x, U x ∂μ) + ∫⁻ y, V y ∂ν ≤ α + ε := by
    simp only [dualUpperValue, iInf_lt_iff] at hlt
    obtain ⟨U, hUm, hUB, V, hVm, hVB, hUV, hint⟩ := hlt n
    exact ⟨U, V, hUm, hUB, hVm, hVB, hUV, hint.le⟩
  choose U V hU_meas hU_le hV_meas hV_le hUV hM using hex
  exact dualUpperValue_iSup_le hmono hU_meas hU_le hV_meas hV_le hUV hM

end UpperEnvelope

/-! ### Finite-level slice counting and upper semicontinuity on closed sets -/

section SliceCount

/-- Slice-counting integrand `z ↦ ∑ k : Fin N, S.indicator 1 (z, k)` associated with a subset
`S ⊆ Z × Fin N`. -/
private def sliceCount {Z : Type*} (N : ℕ) (S : Set (Z × Fin N)) (z : Z) : ℝ≥0∞ :=
  ∑ k : Fin N, S.indicator 1 (z, k)

private lemma sliceCount_le {Z : Type*} (N : ℕ) (S : Set (Z × Fin N)) (z : Z) :
    sliceCount N S z ≤ (N : ℝ≥0) :=
  (Finset.sum_le_sum fun k _ ↦ indicator_le_self S 1 (z, k)).trans_eq (by simp)

private lemma upperSemicontinuous_sliceCount_of_isClosed {Z : Type*} [TopologicalSpace Z] {N : ℕ}
    {S : Set (Z × Fin N)} (hS : IsClosed S) :
    UpperSemicontinuous (sliceCount N S) := by
  refine upperSemicontinuous_sum fun k _ ↦ ?_
  have hk_closed : IsClosed {z : Z | (z, k) ∈ S} :=
    hS.preimage (continuous_id.prodMk continuous_const)
  have heq : (fun z : Z ↦ S.indicator (1 : Z × Fin N → ℝ≥0∞) (z, k)) =
      {z : Z | (z, k) ∈ S}.indicator fun _ ↦ (1 : ℝ≥0∞) := by
    ext z; by_cases hz : (z, k) ∈ S <;> simp [hz]
  rw [heq]
  exact hk_closed.upperSemicontinuous_indicator zero_le_one

/-- Pointwise quantization sandwich `sliceCount N E z ≤ N * f z ≤ sliceCount N E z + 1` for the
`N`-level subgraph `E = {(z, k) | (k + 1) / N ≤ f z}` of a `[0, 1]`-valued function `f`. -/
private lemma sliceCount_subgraph_bounds {Z : Type*} {N : ℕ} (hN_pos : 0 < N)
    {f : Z → ℝ≥0∞} (hf_le : ∀ z, f z ≤ 1) (z : Z) :
    let E : Set (Z × Fin N) := {p | ((p.2.1 + 1 : ℕ) : ℝ≥0∞) / N ≤ f p.1}
    sliceCount N E z ≤ (N : ℝ≥0∞) * f z ∧ (N : ℝ≥0∞) * f z ≤ sliceCount N E z + 1 := by
  intro E
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN_pos.ne'
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hNf_le : (N : ℝ≥0∞) * f z ≤ N := by
    simpa using mul_le_mul_of_nonneg_left (hf_le z) zero_le
  let r : ℝ≥0 := ((N : ℝ≥0∞) * f z).toNNReal
  have hr_coe : (r : ℝ≥0∞) = (N : ℝ≥0∞) * f z :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top hNtop hNf_le)
  let m : ℕ := ⌊r⌋₊
  have hm_le_r : (m : ℝ≥0) ≤ r := Nat.floor_le zero_le
  have hr_lt_succ : r < (m : ℝ≥0) + 1 := Nat.lt_floor_add_one r
  have hm_le_N : m ≤ N := by
    have : (m : ℝ≥0∞) ≤ N := (ENNReal.coe_le_coe.2 hm_le_r).trans (hr_coe.trans_le hNf_le)
    exact_mod_cast this
  have hmem_iff (k : Fin N) : (z, k) ∈ E ↔ k.1 < m := by
    simp only [E, mem_ofPred_eq]
    rw [ENNReal.div_le_iff_le_mul (Or.inl hN0) (Or.inl hNtop), mul_comm _ (N : ℝ≥0∞), ← hr_coe]
    refine ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
    · have hk' : ((k.1 + 1 : ℕ) : ℝ≥0) ≤ r := by exact_mod_cast hk
      exact Nat.lt_of_succ_le (Nat.le_floor hk')
    · have hk' : ((k.1 + 1 : ℕ) : ℝ≥0) ≤ (m : ℝ≥0) := by exact_mod_cast hk
      exact ENNReal.coe_le_coe.2 (hk'.trans hm_le_r)
  have hcount : sliceCount N E z = m := by
    simp only [sliceCount, indicator_apply, Pi.one_apply, hmem_iff, Finset.sum_boole,
      Fin.card_filter_val_lt, min_eq_right hm_le_N]
  rw [hcount, ← hr_coe]
  exact ⟨ENNReal.coe_le_coe.2 hm_le_r, by exact_mod_cast hr_lt_succ.le⟩

end SliceCount

/-! ### Agreement on upper-semicontinuous functions and Choquet capacitability on Polish spaces -/

section PolishAux

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Every bounded-continuous pair `(φ, ψ)` feasible for `B - g` with positive dual value shifts and
truncates to a `[0, B]`-valued measurable upper-envelope pair `(U, V)` for `g` whose marginal
integral sum is at most `B - kantorovichDualValue μ ν φ ψ`. -/
private lemma dualUpperValue_le_sub_ofReal_kantorovichDualValue {B : ℝ≥0}
    {g : X × Y → ℝ≥0∞} (hg_le : ∀ z, g z ≤ B) {φ : X →ᵇ ℝ} {ψ : Y →ᵇ ℝ}
    (hfeas : DualFeasible (fun z ↦ (((B : ℝ≥0∞) - g z : ℝ≥0∞) : EReal)) φ ψ)
    (hd0 : 0 < kantorovichDualValue μ ν φ ψ) :
    dualUpperValue B μ ν g ≤ (B : ℝ≥0∞) - ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let u₀ : X → ℝ := fun x ↦ (B : ℝ) - φ x
  let v₀ : Y → ℝ := fun y ↦ -ψ y
  have hpoint (x : X) (y : Y) : (g (x, y)).toReal ≤ u₀ x + v₀ y := by
    have hxy := hfeas.ofReal_add_le x y
    have hgle : (g (x, y)).toReal ≤ B := ENNReal.toReal_le_coe_of_le_coe (hg_le (x, y))
    have hc_eq : (B : ℝ≥0∞) - g (x, y) = ENNReal.ofReal ((B : ℝ) - (g (x, y)).toReal) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hg_le (x, y)))]
    rw [hc_eq] at hxy
    linarith [(ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 hgle)).1 hxy]
  have hu₀_bdd : BddBelow (range u₀) := ⟨(B : ℝ) - ‖φ‖, forall_mem_range.2 fun x ↦
    sub_le_sub_left ((le_abs_self _).trans (φ.norm_coe_le_norm x)) _⟩
  let α₀ : ℝ := ⨅ x : X, u₀ x
  let u₁ : X → ℝ := fun x ↦ u₀ x - α₀
  let v₁ : Y → ℝ := fun y ↦ v₀ y + α₀
  have hu₁_nn (x : X) : 0 ≤ u₁ x := sub_nonneg.2 (ciInf_le hu₀_bdd x)
  have hv₁_nn (y : Y) : 0 ≤ v₁ y := by
    have : -v₀ y ≤ α₀ := le_ciInf fun x ↦ by
      linarith [hpoint x y, @ENNReal.toReal_nonneg (g (x, y))]
    linarith
  let U : X → ℝ≥0∞ := fun x ↦ min (ENNReal.ofReal (u₁ x)) B
  let V : Y → ℝ≥0∞ := fun y ↦ min (ENNReal.ofReal (v₁ y)) B
  have hUV_ge (x : X) (y : Y) : g (x, y) ≤ U x + V y := by
    have hg_sum : g (x, y) ≤ ENNReal.ofReal (u₁ x) + ENNReal.ofReal (v₁ y) := by
      have heq : u₁ x + v₁ y = u₀ x + v₀ y := by ring
      rw [← ENNReal.ofReal_add (hu₁_nn x) (hv₁_nn y), heq,
        ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hg_le (x, y)))]
      exact ENNReal.ofReal_le_ofReal (hpoint x y)
    rcases le_total (ENNReal.ofReal (u₁ x)) B with huB | hBu
    · rcases le_total (ENNReal.ofReal (v₁ y)) B with hvB | hBv
      · simpa [U, V, min_eq_left huB, min_eq_left hvB] using hg_sum
      · exact (hg_le (x, y)).trans ((le_add_self : (B : ℝ≥0∞) ≤ U x + B).trans_eq
          (by simp [V, min_eq_right hBv]))
    · exact (hg_le (x, y)).trans ((le_self_add : (B : ℝ≥0∞) ≤ B + V y).trans_eq
        (by simp [U, min_eq_right hBu]))
  refine (dualUpperValue_le
    (((continuous_const.sub φ.continuous).sub continuous_const).measurable.ennreal_ofReal.min
      measurable_const) (fun _ ↦ min_le_right _ _)
    ((ψ.continuous.neg.add continuous_const).measurable.ennreal_ofReal.min measurable_const)
    (fun _ ↦ min_le_right _ _) hUV_ge).trans ?_
  have hu₀_int : Integrable u₀ μ := (integrable_const (B : ℝ)).sub (φ.integrable μ)
  have hu₁_int : Integrable u₁ μ := hu₀_int.sub (integrable_const α₀)
  have hv₀_int : Integrable v₀ ν := (ψ.integrable ν).neg
  have hv₁_int : Integrable v₁ ν := hv₀_int.add (integrable_const α₀)
  have hlu : ∫⁻ x, U x ∂μ ≤ ENNReal.ofReal (∫ x, u₁ x ∂μ) :=
    (lintegral_mono fun _ ↦ min_le_left _ _).trans_eq
      (ofReal_integral_eq_lintegral_ofReal hu₁_int (.of_forall hu₁_nn)).symm
  have hlv : ∫⁻ y, V y ∂ν ≤ ENNReal.ofReal (∫ y, v₁ y ∂ν) :=
    (lintegral_mono fun _ ↦ min_le_left _ _).trans_eq
      (ofReal_integral_eq_lintegral_ofReal hv₁_int (.of_forall hv₁_nn)).symm
  have hsum_int : (∫ x, u₁ x ∂μ) + ∫ y, v₁ y ∂ν = (B : ℝ) - kantorovichDualValue μ ν φ ψ := by
    rw [integral_sub hu₀_int (integrable_const α₀),
      integral_sub (integrable_const (B : ℝ)) (φ.integrable μ),
      integral_add hv₀_int (integrable_const α₀), integral_neg, kantorovichDualValue_def]
    simp; ring
  exact (add_le_add hlu hlv).trans_eq <| (ENNReal.ofReal_add (integral_nonneg hu₁_nn)
    (integral_nonneg hv₁_nn)).symm.trans <| by
      rw [hsum_int, ENNReal.ofReal_sub _ hd0.le, ENNReal.ofReal_coe_nnreal]

variable [PolishSpace X] [PolishSpace Y]

/-- On Polish spaces, the bounded Borel upper-envelope functional and primal maximization agree on
every `[0, B]`-valued upper-semicontinuous integrand. -/
private lemma dualUpperValue_eq_primalMaxValue_of_upperSemicontinuous {B : ℝ≥0}
    {g : X × Y → ℝ≥0∞} (hg_usc : UpperSemicontinuous g) (hg_le : ∀ z, g z ≤ B) :
    dualUpperValue B μ ν g = primalMaxValue μ ν g := by
  refine le_antisymm ?_ (primalMaxValue_le_dualUpperValue g)
  rw [primalMaxValue_eq_sub_transportCost hg_usc.measurable hg_le]
  let c : X × Y → ℝ≥0∞ := fun z ↦ (B : ℝ≥0∞) - g z
  have hc_lsc : LowerSemicontinuous c :=
    (ENNReal.continuous_sub_left ENNReal.coe_ne_top).comp_upperSemicontinuous_antitone hg_usc
      (fun _ _ h ↦ tsub_le_tsub_left h _)
  have hd_le_B : dualUpperValue B μ ν g ≤ B := by
    simpa using dualUpperValue_le_mul_univ (μ := μ) (ν := ν) hg_le
  have hd_fin : dualUpperValue B μ ν g ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hd_le_B
  have hcost_B : transportCost c μ ν ≤ B :=
    (transportCost_le_lintegral (isCoupling_prod μ ν) c).trans <|
      (lintegral_mono fun _ ↦ tsub_le_self).trans_eq (by simp)
  have hcost_le : transportCost c μ ν ≤ (B : ℝ≥0∞) - dualUpperValue B μ ν g := by
    refine (isLUB_ofReal_kantorovichDualValue_boundedContinuous_of_lowerSemicontinuous
      (μ := μ) (ν := ν) hc_lsc).2 ?_
    rintro _ ⟨φ, ψ, hfeas, rfl⟩
    rcases le_or_gt (kantorovichDualValue μ ν φ ψ) 0 with hd0 | hd0
    · simp [ENNReal.ofReal_eq_zero.2 hd0]
    have hd_upper := dualUpperValue_le_sub_ofReal_kantorovichDualValue hg_le hfeas hd0
    have hle_B : ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ B :=
      (hfeas.ofReal_kantorovichDualValue_le_transportCost
        (φ.integrable μ) (ψ.integrable ν)).trans hcost_B
    refine ENNReal.le_sub_of_add_le_right hd_fin ?_
    exact (add_le_add le_rfl hd_upper).trans_eq (add_tsub_cancel_of_le hle_B)
  refine ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.coe_ne_top hcost_B) ?_
  exact (add_le_add le_rfl hcost_le).trans_eq (add_tsub_cancel_of_le hd_le_B)

/-- Along a decreasing sequence of `[0, B]`-valued upper-semicontinuous functions on a product of
Polish spaces, `dualUpperValue` commutes with the pointwise infimum. -/
private lemma dualUpperValue_iInf_eq_of_upperSemicontinuous {B : ℝ≥0}
    {gs : ℕ → X × Y → ℝ≥0∞} (hanti : Antitone gs)
    (husc : ∀ n, UpperSemicontinuous (gs n)) (hle : ∀ n z, gs n z ≤ B) :
    dualUpperValue B μ ν (fun z ↦ ⨅ n, gs n z) = ⨅ n, dualUpperValue B μ ν (gs n) := by
  have husc_inf : UpperSemicontinuous fun z ↦ ⨅ n, gs n z := upperSemicontinuous_iInf husc
  have hle_inf (z : X × Y) : (⨅ n, gs n z) ≤ B := iInf_le_of_le 0 (hle 0 z)
  rw [dualUpperValue_eq_primalMaxValue_of_upperSemicontinuous husc_inf hle_inf,
    primalMaxValue_eq_sub_transportCost husc_inf.measurable hle_inf]
  let cs : ℕ → X × Y → ℝ≥0∞ := fun n z ↦ (B : ℝ≥0∞) - gs n z
  have hcs_lsc (n : ℕ) : LowerSemicontinuous (cs n) :=
    (ENNReal.continuous_sub_left ENNReal.coe_ne_top).comp_upperSemicontinuous_antitone (husc n)
      (fun _ _ h ↦ tsub_le_tsub_left h _)
  have hcs_mono : Monotone cs := fun _ _ hmn z ↦ tsub_le_tsub_left (hanti hmn z) _
  have hsub_inf : (fun z ↦ (B : ℝ≥0∞) - ⨅ n, gs n z) = fun z ↦ ⨆ n, cs n z :=
    funext fun _ ↦ ENNReal.sub_iInf
  rw [hsub_inf,
    transportCost_iSup_eq_iSup isTightMeasureSet_singleton isTightMeasureSet_singleton
      hcs_lsc hcs_mono,
    ENNReal.sub_iSup ENNReal.coe_ne_top]
  refine iInf_congr fun n ↦ ?_
  rw [← primalMaxValue_eq_sub_transportCost (husc n).measurable (hle n),
    dualUpperValue_eq_primalMaxValue_of_upperSemicontinuous (husc n) (hle n)]

/-- For every `N : ℕ`, `S ↦ dualUpperValue N μ ν (sliceCount N S)` is a Choquet capacity on
`(X × Y) × Fin N`. -/
private lemma isChoquetCapacity_dualUpperValue_sliceCount (N : ℕ) :
    IsChoquetCapacity (fun S : Set ((X × Y) × Fin N) ↦
      dualUpperValue (N : ℝ≥0) μ ν (sliceCount N S)) where
  mono _ _ hST := dualUpperValue_mono fun z ↦
    Finset.sum_le_sum fun k _ ↦
      Set.indicator_le_indicator_of_subset hST (fun _ ↦ zero_le) (z, k)
  iUnion_eq A hA := by
    have hfun : sliceCount N (⋃ n, A n) = fun z ↦ ⨆ n, sliceCount N (A n) z := by
      ext z
      simp only [sliceCount, Set.indicator_iUnion_apply (M := ℝ≥0∞) rfl]
      exact ENNReal.finsetSum_iSup_of_monotone fun k _ _ hmn ↦
        Set.indicator_le_indicator_of_subset (hA hmn) (fun _ ↦ zero_le) (z, k)
    rw [hfun]
    exact dualUpperValue_iSup_eq
      (fun _ _ hmn z ↦ Finset.sum_le_sum fun k _ ↦
        Set.indicator_le_indicator_of_subset (hA hmn) (fun _ ↦ zero_le) (z, k))
      (fun n ↦ sliceCount_le N (A n))
  iInter_isClosed_eq F hF hanti := by
    have hfun : sliceCount N (⋂ n, F n) = fun z ↦ ⨅ n, sliceCount N (F n) z := by
      ext z
      refine le_antisymm (le_iInf fun n ↦ Finset.sum_le_sum fun k _ ↦
        Set.indicator_le_indicator_of_subset (iInter_subset F n) (fun _ ↦ zero_le) (z, k)) ?_
      have hstab (k : Fin N) : ∃ n₀ : ℕ, (z, k) ∈ F n₀ → (z, k) ∈ ⋂ n, F n := by
        by_cases hk : (z, k) ∈ ⋂ n, F n
        · exact ⟨0, fun _ ↦ hk⟩
        · simp only [mem_iInter, not_forall] at hk
          obtain ⟨n₀, hn₀⟩ := hk; exact ⟨n₀, fun h ↦ (hn₀ h).elim⟩
      choose n₀ hn₀ using hstab
      refine iInf_le_of_le (Finset.univ.sup n₀) (Finset.sum_le_sum fun k _ ↦ ?_)
      by_cases hk : (z, k) ∈ F (Finset.univ.sup n₀)
      · simp [hk, hn₀ k (hanti (Finset.le_sup (Finset.mem_univ k)) hk)]
      · simp [hk]
    rw [hfun]
    exact dualUpperValue_iInf_eq_of_upperSemicontinuous
      (fun _ _ hmn z ↦ Finset.sum_le_sum fun k _ ↦
        Set.indicator_le_indicator_of_subset (hanti hmn) (fun _ ↦ zero_le) (z, k))
      (fun n ↦ upperSemicontinuous_sliceCount_of_isClosed (hF n))
      (fun n ↦ sliceCount_le N (F n))

/-- **Strong duality between `dualUpperValue` and `primalMaxValue` for `[0, 1]`-valued Borel
integrands** on Polish spaces, proved by Choquet capacitability on `(X × Y) × Fin N`. -/
private lemma dualUpperValue_one_eq_primalMaxValue_of_measurable
    {f : X × Y → ℝ≥0∞} (hf_meas : Measurable f) (hf_le : ∀ z, f z ≤ 1) :
    dualUpperValue 1 μ ν f = primalMaxValue μ ν f := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
    (primalMaxValue_le_dualUpperValue f)
  obtain ⟨N, hN_lt, hN_pos⟩ := ((ENNReal.tendsto_inv_nat_nhds_zero.eventually
    (gt_mem_nhds (ENNReal.coe_pos.2 hε))).and (eventually_gt_atTop 0)).exists
  let E : Set ((X × Y) × Fin N) := {p | ((p.2.1 + 1 : ℕ) : ℝ≥0∞) / N ≤ f p.1}
  have hE_meas : MeasurableSet E := measurableSet_le
    ((measurable_of_countable fun k : Fin N ↦ ((k.1 + 1 : ℕ) : ℝ≥0∞) / N).comp measurable_snd)
    (hf_meas.comp measurable_fst)
  have hE_le : dualUpperValue (N : ℝ≥0) μ ν (sliceCount N E) ≤
      primalMaxValue μ ν (sliceCount N E) := by
    rw [(isChoquetCapacity_dualUpperValue_sliceCount (μ := μ) (ν := ν) N)
      |>.analyticSet_eq_biSup_isCompact hE_meas.analyticSet]
    refine iSup₂_le fun K hKc ↦ iSup_le fun hKE ↦ ?_
    rw [dualUpperValue_eq_primalMaxValue_of_upperSemicontinuous
      (upperSemicontinuous_sliceCount_of_isClosed hKc.isClosed) (sliceCount_le N K)]
    exact primalMaxValue_mono fun z ↦ Finset.sum_le_sum fun k _ ↦
      Set.indicator_le_indicator_of_subset hKE (fun _ ↦ zero_le) (z, k)
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN_pos.ne'
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hslice_bounds := sliceCount_subgraph_bounds hN_pos hf_le
  have hd_scale : dualUpperValue 1 μ ν f ≤
      (N : ℝ≥0∞)⁻¹ * dualUpperValue (N : ℝ≥0) μ ν (sliceCount N E) + (N : ℝ≥0∞)⁻¹ :=
    le_mul_dualUpperValue_add (ENNReal.inv_ne_zero.2 hNtop)
      (ENNReal.inv_ne_top.2 hN0) fun U hUm _ V hVm hVN hUV ↦ by
      let u₁ : X → ℝ≥0∞ := fun x ↦ min ((N : ℝ≥0∞)⁻¹ * (U x + 1)) 1
      let v₁ : Y → ℝ≥0∞ := fun y ↦ (N : ℝ≥0∞)⁻¹ * V y
      have hv₁_le (y : Y) : v₁ y ≤ 1 :=
        (mul_le_mul_of_nonneg_left (hVN y) zero_le).trans_eq (ENNReal.inv_mul_cancel hN0 hNtop)
      have huv₁ (x : X) (y : Y) : f (x, y) ≤ u₁ x + v₁ y := by
        rcases le_total ((N : ℝ≥0∞)⁻¹ * (U x + 1)) 1 with hle1 | hge1
        · simp only [u₁, v₁, min_eq_left hle1]
          rw [← mul_add, add_right_comm]
          have hf_mul : f (x, y) = (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * f (x, y)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
          exact hf_mul.trans_le (mul_le_mul_of_nonneg_left
            ((hslice_bounds (x, y)).2.trans (add_le_add_left (hUV x y) 1)) zero_le)
        · exact (hf_le (x, y)).trans
            ((le_self_add : (1 : ℝ≥0∞) ≤ 1 + v₁ y).trans_eq (by simp [u₁, min_eq_right hge1]))
      refine (dualUpperValue_le
        (((hUm.add_const 1).const_mul _).min measurable_const)
        (fun _ ↦ min_le_right _ _) (hVm.const_mul _) hv₁_le huv₁).trans ?_
      have hlu : ∫⁻ x, u₁ x ∂μ ≤ (N : ℝ≥0∞)⁻¹ * (∫⁻ x, U x ∂μ) + (N : ℝ≥0∞)⁻¹ :=
        (lintegral_mono fun _ ↦ min_le_left _ _).trans_eq <| by
          rw [lintegral_const_mul _ (hUm.add_const 1), lintegral_add_left hUm,
            lintegral_const, measure_univ, mul_one, mul_add, mul_one]
      exact (add_le_add hlu (lintegral_const_mul _ hVm).le).trans_eq (by rw [mul_add]; ac_rfl)
  have hp_scale : (N : ℝ≥0∞)⁻¹ * primalMaxValue μ ν (sliceCount N E) ≤ primalMaxValue μ ν f :=
    mul_primalMaxValue_le
      (Finset.measurable_sum _ fun k _ ↦
        measurable_const.indicator (hE_meas.preimage (measurable_id.prodMk measurable_const)))
      fun z ↦ (mul_le_mul_of_nonneg_left (hslice_bounds z).1 zero_le).trans_eq <| by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
  exact hd_scale.trans ((add_le_add (by gcongr) le_rfl).trans (add_le_add hp_scale hN_lt.le))

/-- **Strong duality between `dualUpperValue` and `primalMaxValue` for `[0, B]`-valued Borel
integrands** on Polish spaces. -/
private lemma dualUpperValue_eq_primalMaxValue_of_measurable {B : ℝ≥0}
    {f : X × Y → ℝ≥0∞} (hf_meas : Measurable f) (hf_le : ∀ z, f z ≤ B) :
    dualUpperValue B μ ν f = primalMaxValue μ ν f := by
  rcases eq_or_ne B 0 with rfl | hB0
  · have hf0 : f = 0 := funext fun z ↦ le_antisymm (by simpa using hf_le z) zero_le
    subst hf0
    exact le_antisymm ((dualUpperValue_le_mul_univ fun _ ↦ le_rfl).trans (by simp))
      (primalMaxValue_le_dualUpperValue 0)
  have hB_coe0 : (B : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hB0
  let f₁ : X × Y → ℝ≥0∞ := fun z ↦ (B : ℝ≥0∞)⁻¹ * f z
  have hf₁_meas : Measurable f₁ := hf_meas.const_mul _
  have hf₁_le (z : X × Y) : f₁ z ≤ 1 :=
    (mul_le_mul_of_nonneg_left (hf_le z) zero_le).trans_eq
      (ENNReal.inv_mul_cancel hB_coe0 ENNReal.coe_ne_top)
  have h1 := dualUpperValue_one_eq_primalMaxValue_of_measurable (μ := μ) (ν := ν) hf₁_meas hf₁_le
  refine le_antisymm ?_ (primalMaxValue_le_dualUpperValue f)
  have hd_le : dualUpperValue B μ ν f ≤ (B : ℝ≥0∞) * dualUpperValue 1 μ ν f₁ := by
    have h0 := le_mul_dualUpperValue_add (f := f₁) (μ := μ) (ν := ν)
      (a := dualUpperValue B μ ν f) (c := (B : ℝ≥0∞)) (d := 0) hB_coe0 ENNReal.coe_ne_top
      fun u hum hu1 v hvm hv1 huv ↦ by
      rw [add_zero]
      refine (dualUpperValue_le (hum.const_mul _)
        (fun x ↦ (mul_le_mul_of_nonneg_left (hu1 x) zero_le).trans_eq (mul_one _))
        (hvm.const_mul _)
        (fun y ↦ (mul_le_mul_of_nonneg_left (hv1 y) zero_le).trans_eq (mul_one _))
        (fun x y ↦ ?_)).trans_eq ?_
      · calc
          f (x, y) = (B : ℝ≥0∞) * f₁ (x, y) := by
            simp [f₁, ← mul_assoc, ENNReal.mul_inv_cancel hB_coe0 ENNReal.coe_ne_top]
          _ ≤ (B : ℝ≥0∞) * (u x + v y) := mul_le_mul_of_nonneg_left (huv x y) zero_le
          _ = (B : ℝ≥0∞) * u x + (B : ℝ≥0∞) * v y := mul_add _ _ _
      · rw [lintegral_const_mul _ hum, lintegral_const_mul _ hvm, mul_add]
    simpa only [add_zero] using h0
  have hp_le : (B : ℝ≥0∞) * primalMaxValue μ ν f₁ ≤ primalMaxValue μ ν f :=
    mul_primalMaxValue_le hf₁_meas fun _ ↦ by
      simp [f₁, ← mul_assoc, ENNReal.mul_inv_cancel hB_coe0 ENNReal.coe_ne_top]
  exact hd_le.trans ((mul_le_mul_of_nonneg_left h1.le zero_le).trans hp_le)

end PolishAux

/-! ### Strong Kantorovich duality for bounded Borel costs -/

/-- Every `[0, B]`-valued measurable upper-envelope pair `(U, V)` for `B - c` converts into a
bounded Borel dual-feasible pair `(B - U, -V)` for `c`, bounding `(B : ℝ≥0∞) - b` by
`dualUpperValue B μ ν (B - c)` whenever `b` bounds all bounded Borel dual values. -/
private lemma sub_le_dualUpperValue_of_upperBounds {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : X × Y → ℝ≥0∞} {B : ℝ≥0} (hB : ∀ z, c z ≤ B) {b : ℝ≥0∞}
    (hb : b ∈ upperBounds {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r}) :
    (B : ℝ≥0∞) - b ≤ dualUpperValue B μ ν (fun z ↦ (B : ℝ≥0∞) - c z) := by
  refine le_iInf₂ fun U hUm ↦ le_iInf fun hUB ↦
    le_iInf₂ fun V hVm ↦ le_iInf fun hVB ↦ le_iInf fun hUV ↦ ?_
  let φ : X → ℝ := fun x ↦ (B : ℝ) - (U x).toReal
  let ψ : Y → ℝ := fun y ↦ -(V y).toReal
  have hU_toReal (x : X) : (U x).toReal ≤ B := ENNReal.toReal_le_coe_of_le_coe (hUB x)
  have hV_toReal (y : Y) : (V y).toReal ≤ B := ENNReal.toReal_le_coe_of_le_coe (hVB y)
  have hfeas : DualFeasible (fun z ↦ (c z : EReal)) φ ψ := by
    rw [dualFeasible_iff_ofReal_add_le]; intro x y
    rcases le_or_gt (φ x + ψ y) 0 with hneg | _
    · simp [ENNReal.ofReal_eq_zero.2 hneg]
    have hUV_xy := hUV x y; dsimp only at hUV_xy
    have hU_eq := ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hUB x))
    have hV_eq := ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hVB y))
    have hc_eq := ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hB (x, y)))
    have hf_eq : (B : ℝ≥0∞) - c (x, y) = ENNReal.ofReal ((B : ℝ) - (c (x, y)).toReal) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_coe_nnreal, hc_eq]
    rw [hf_eq, ← hU_eq, ← hV_eq,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at hUV_xy
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).1 hUV_xy
    exact hc_eq ▸ ENNReal.ofReal_le_ofReal (by linarith)
  have hb_le : ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ b :=
    hb ⟨φ, ψ, measurable_const.sub hUm.ennreal_toReal, hVm.ennreal_toReal.neg,
      ⟨B, fun x ↦ abs_le.2 ⟨by linarith [hU_toReal x, B.coe_nonneg],
        by linarith [@ENNReal.toReal_nonneg (U x)]⟩⟩,
      ⟨B, fun y ↦ abs_le.2 ⟨by linarith [hV_toReal y],
        by linarith [@ENNReal.toReal_nonneg (V y), B.coe_nonneg]⟩⟩, hfeas, rfl⟩
  have hU_int : Integrable (fun x ↦ (U x).toReal) μ :=
    .of_bound hUm.ennreal_toReal.aestronglyMeasurable B <| .of_forall fun x ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]; exact hU_toReal x
  have hlu : ∫⁻ x, U x ∂μ = ENNReal.ofReal (∫ x, (U x).toReal ∂μ) := by
    rw [integral_toReal hUm.aemeasurable (.of_forall fun x ↦ (hUB x).trans_lt ENNReal.coe_lt_top),
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top (b := B) ENNReal.coe_ne_top
        ((lintegral_mono hUB).trans_eq (by simp)))]
  have hlv : ∫⁻ y, V y ∂ν = ENNReal.ofReal (∫ y, (V y).toReal ∂ν) := by
    rw [integral_toReal hVm.aemeasurable (.of_forall fun y ↦ (hVB y).trans_lt ENNReal.coe_lt_top),
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top (b := B) ENNReal.coe_ne_top
        ((lintegral_mono hVB).trans_eq (by simp)))]
  have hd_val : kantorovichDualValue μ ν φ ψ =
      (B : ℝ) - ((∫ x, (U x).toReal ∂μ) + ∫ y, (V y).toReal ∂ν) := by
    rw [kantorovichDualValue_def, integral_sub (integrable_const _) hU_int, integral_neg]
    simp; ring
  have hsum_nn : 0 ≤ (∫ x, (U x).toReal ∂μ) + ∫ y, (V y).toReal ∂ν :=
    add_nonneg (integral_nonneg fun _ ↦ ENNReal.toReal_nonneg)
      (integral_nonneg fun _ ↦ ENNReal.toReal_nonneg)
  refine tsub_le_iff_left.2 ?_
  rw [hlu, hlv, ← ENNReal.ofReal_add (integral_nonneg fun _ ↦ ENNReal.toReal_nonneg)
    (integral_nonneg fun _ ↦ ENNReal.toReal_nonneg)]
  rcases le_or_gt (B : ℝ) ((∫ x, (U x).toReal ∂μ) + ∫ y, (V y).toReal ∂ν) with hle | hgt
  · exact (ENNReal.ofReal_coe_nnreal ▸ ENNReal.ofReal_le_ofReal hle).trans le_add_self
  · have hB_eq : (B : ℝ≥0∞) = ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) +
        ENNReal.ofReal ((∫ x, (U x).toReal ∂μ) + ∫ y, (V y).toReal ∂ν) := by
      rw [← ENNReal.ofReal_add (by linarith) hsum_nn, hd_val]; simp
    exact hB_eq.le.trans (add_le_add hb_le le_rfl)

section Polish

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {c : X × Y → ℝ≥0∞}

/-- **Strong Kantorovich duality for bounded Borel costs over bounded measurable potentials.**
For a Borel measurable cost `c ≤ B` on a product of Polish spaces and two probability measures,
`transportCost c μ ν` is the least upper bound of the positive parts of the dual values of
feasible bounded Borel potential pairs `(φ, ψ)`. -/
theorem isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le {B : ℝ≥0}
    (hc : Measurable c) (hB : ∀ z, c z ≤ B) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (transportCost c μ ν) := by
  constructor
  · rintro r ⟨φ, ψ, hφm, hψm, ⟨M₁, hM₁⟩, ⟨M₂, hM₂⟩, hfeas, rfl⟩
    exact hfeas.ofReal_kantorovichDualValue_le_transportCost
      (.of_bound hφm.aestronglyMeasurable M₁ (.of_forall hM₁))
      (.of_bound hψm.aestronglyMeasurable M₂ (.of_forall hM₂))
  · intro b hb
    let f : X × Y → ℝ≥0∞ := fun z ↦ (B : ℝ≥0∞) - c z
    have hf_meas : Measurable f := measurable_const.sub hc
    have hf_le (z : X × Y) : f z ≤ B := tsub_le_self
    have hc_recover : (fun z ↦ (B : ℝ≥0∞) - f z) = c :=
      funext fun z ↦ ENNReal.sub_sub_cancel ENNReal.coe_ne_top (hB z)
    have hcost_B : transportCost c μ ν ≤ B :=
      (transportCost_le_lintegral (isCoupling_prod μ ν) c).trans <|
        (lintegral_mono hB).trans_eq (by simp)
    have hdual_eq : dualUpperValue B μ ν f = (B : ℝ≥0∞) - transportCost c μ ν :=
      (dualUpperValue_eq_primalMaxValue_of_measurable hf_meas hf_le).trans <| by
        simpa only [hc_recover] using
          primalMaxValue_eq_sub_transportCost (μ := μ) (ν := ν) hf_meas hf_le
    have hsub_le : (B : ℝ≥0∞) - b ≤ (B : ℝ≥0∞) - transportCost c μ ν :=
      (sub_le_dualUpperValue_of_upperBounds hB hb).trans_eq hdual_eq
    rcases le_or_gt (B : ℝ≥0∞) b with hBb | hbB
    · exact hcost_B.trans hBb
    · have hcalc : transportCost c μ ν + ((B : ℝ≥0∞) - b) ≤ b + ((B : ℝ≥0∞) - b) :=
        calc
          transportCost c μ ν + ((B : ℝ≥0∞) - b)
              ≤ transportCost c μ ν + ((B : ℝ≥0∞) - transportCost c μ ν) :=
            add_le_add le_rfl hsub_le
          _ = B := add_tsub_cancel_of_le hcost_B
          _ = b + ((B : ℝ≥0∞) - b) := (add_tsub_cancel_of_le hbB.le).symm
      exact (ENNReal.add_le_add_iff_right
        (ne_top_of_le_ne_top ENNReal.coe_ne_top tsub_le_self)).1 hcalc

/-- Supremum formula for bounded Borel strong Kantorovich duality over bounded measurable
potentials. -/
theorem transportCost_eq_sSup_ofReal_kantorovichDualValue_bounded_measurable_of_le {B : ℝ≥0}
    (hc : Measurable c) (hB : ∀ z, c z ≤ B) :
    transportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le hc hB).sSup_eq.symm

/-- **Strong Kantorovich duality for bounded Borel costs over integrable potentials.** -/
theorem isLUB_ofReal_kantorovichDualValue_integrable_of_measurable_of_le {B : ℝ≥0}
    (hc : Measurable c) (hB : ∀ z, c z ≤ B) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (transportCost c μ ν) := by
  constructor
  · rintro r ⟨φ, ψ, hφ, hψ, hfeas, rfl⟩
    exact hfeas.ofReal_kantorovichDualValue_le_transportCost hφ hψ
  · intro b hb
    refine (isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le
      (μ := μ) (ν := ν) hc hB).2 ?_
    rintro r ⟨φ, ψ, hφm, hψm, ⟨M₁, hM₁⟩, ⟨M₂, hM₂⟩, hfeas, rfl⟩
    exact hb ⟨φ, ψ, .of_bound hφm.aestronglyMeasurable M₁ (.of_forall hM₁),
      .of_bound hψm.aestronglyMeasurable M₂ (.of_forall hM₂), hfeas, rfl⟩

/-- Supremum formula for bounded Borel strong Kantorovich duality over integrable potentials. -/
theorem transportCost_eq_sSup_ofReal_kantorovichDualValue_integrable_of_measurable_of_le
    {B : ℝ≥0} (hc : Measurable c) (hB : ∀ z, c z ≤ B) :
    transportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_integrable_of_measurable_of_le hc hB).sSup_eq.symm

end Polish

end TauCeti
