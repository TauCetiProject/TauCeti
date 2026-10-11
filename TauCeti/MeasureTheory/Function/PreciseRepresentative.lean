/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Convex.Integral
import TauCeti.Topology.MetricSpace.Holder

/-!
# The precise representative of a function

For a function `f` on a metric measure space, the *precise representative* is the limit of the
averages of `f` over the closed balls `closedBall x r` as `r → 0⁺`, taken at every point where
this limit exists (and a junk value elsewhere). It depends only on the almost-everywhere class of
`f`, and by the Lebesgue differentiation theorem it agrees almost everywhere with `f` when `f` is
locally integrable and the measure is doubling. It is therefore a canonical pointwise choice of
representative of an `L¹_loc` class, and the natural candidate for a continuous representative.

The second half of the file turns bounds on the essential oscillation of `f` on small balls into
continuity and Hölder estimates for the precise representative. If `f` takes values almost
everywhere on `ball x r` in a closed convex set `S`, then the averages over the closed balls
around `x` lie in `S` once their radius is below `r`, and so does their limit. This gives:

* if the essential oscillation of `f` on `ball x r` tends to `0` with `r`, the averages converge
  at `x`, and the precise representative is their limit there;
* if the essential oscillation of `f` on `ball x r` is at most `C r^α` for the points `x` of a set
  `s` and all radii `r ≤ ρ`, and `f` is essentially bounded near `s`, then the precise
  representative is Hölder continuous on `s` with exponent `α`.

The second statement is how an a-priori estimate on the decay of the oscillation, such as the one
for solutions of elliptic equations in De Giorgi's theorem, becomes Hölder continuity of a
representative.

## Main declarations

* `TauCeti.MeasureTheory.preciseRepresentative`: the limit of the averages over shrinking closed
  balls.
* `TauCeti.MeasureTheory.preciseRepresentative_congr_ae`: the precise representative depends only
  on the almost-everywhere class.
* `TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`: a function locally integrable on
  an open set agrees almost everywhere there with its precise representative.
* `TauCeti.MeasureTheory.preciseRepresentative_eq_of_continuousAt`: the precise representative at
  `x` of a function equal almost everywhere near `x` to a function `g` continuous at `x` is `g x`.
* `TauCeti.MeasureTheory.tendsto_setAverage_closedBall_preciseRepresentative`: the averages
  converge at points where the essential oscillation vanishes.
* `TauCeti.MeasureTheory.tendsto_setAverage_closedBall_preciseRepresentative_of_rpow`: the
  averages converge at points where the essential oscillation decays like a power of the radius.
* `TauCeti.MeasureTheory.dist_preciseRepresentative_le`: two points of a ball on which `f` takes
  values in a closed ball of radius `L` have precise representatives at distance at most `2 L`.
* `TauCeti.MeasureTheory.holderOnWith_preciseRepresentative`: oscillation decaying like `r^α`
  makes the precise representative Hölder continuous.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §1.7 and §4.8
  (Lebesgue points and the precise representative).
-/

public section

noncomputable section

open Filter Metric Set Topology MeasureTheory
open scoped NNReal

namespace TauCeti

namespace MeasureTheory

variable {X E : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : X → E} {x : X}

variable (μ f) in
/-- The precise representative of `f` with respect to `μ`: at each point `x`, the limit of the
averages of `f` over `closedBall x r` as `r → 0⁺`. Where this limit does not exist, the value is
the junk value of `limUnder`. -/
def preciseRepresentative (x : X) : E :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => ⨍ y in closedBall x r, f y ∂μ

/-- The precise representative is the limit of the averages over shrinking closed balls, whenever
this limit exists. -/
theorem preciseRepresentative_eq_of_tendsto {v : E}
    (h : Tendsto (fun r => ⨍ y in closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 v)) :
    preciseRepresentative μ f x = v :=
  h.limUnder_eq

/-- The precise representative at `x` only depends on the almost-everywhere class of `f` on a
neighbourhood of `x`. -/
theorem preciseRepresentative_congr_ae_nhds {V : Set X} (hV : V ∈ 𝓝 x)
    (h : f =ᵐ[μ.restrict V] g) : preciseRepresentative μ f x = preciseRepresentative μ g x := by
  obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hV
  have hev : (fun r => ⨍ y in closedBall x r, f y ∂μ) =ᶠ[𝓝[>] 0]
      fun r => ⨍ y in closedBall x r, g y ∂μ := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    exact average_congr (ae_restrict_of_ae_restrict_of_subset
      ((closedBall_subset_closedBall hr.2.le).trans hsub) h)
  simp only [preciseRepresentative, limUnder, map_congr hev]

/-- The precise representative only depends on the almost-everywhere class of `f`. -/
theorem preciseRepresentative_congr_ae (h : f =ᵐ[μ] g) :
    preciseRepresentative μ f = preciseRepresentative μ g :=
  funext fun _ => preciseRepresentative_congr_ae_nhds univ_mem (by rwa [Measure.restrict_univ])

/-- **Lebesgue differentiation for the precise representative.** For a uniformly locally doubling
measure, a function which is locally integrable on an open set `U` agrees almost everywhere on `U`
with its precise representative. -/
theorem ae_eq_restrict_preciseRepresentative [SecondCountableTopology X] [BorelSpace X]
    [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ] [CompleteSpace E] {U : Set X}
    (hU : IsOpen U) (hf : LocallyIntegrableOn f U μ) :
    f =ᵐ[μ.restrict U] preciseRepresentative μ f := by
  obtain ⟨u, hu, hUu, hint⟩ := hf.exists_nat_integrableOn
  -- On each piece `u n ∩ U`, apply the Lebesgue differentiation theorem to the integrable
  -- function `f` cut off outside the piece, which has the same precise representative there.
  have key : ∀ n, ∀ᵐ x ∂μ, x ∈ u n ∩ U → f x = preciseRepresentative μ f x := by
    intro n
    have hV : IsOpen (u n ∩ U) := (hu n).inter hU
    have hli : LocallyIntegrable ((u n ∩ U).indicator f) μ :=
      ((integrable_indicator_iff hV.measurableSet).2 (hint n)).locallyIntegrable
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hli 1] with x hx hxV
    have hlim := hx (fun _ => x) id tendsto_id
      (by filter_upwards [self_mem_nhdsWithin] with r hr using by simpa using (le_of_lt hr))
    rw [indicator_of_mem hxV] at hlim
    rw [preciseRepresentative_congr_ae_nhds (hV.mem_nhds hxV)
      (g := (u n ∩ U).indicator f) ?_, preciseRepresentative_eq_of_tendsto hlim]
    filter_upwards [self_mem_ae_restrict hV.measurableSet] with y hy
    rw [indicator_of_mem hy]
  rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [ae_all_iff.2 key] with x hx hxU
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hUu hxU)
  exact hx n ⟨hn, hxU⟩

/-- **Lebesgue differentiation for the precise representative.** For a uniformly locally doubling
measure, a locally integrable function agrees almost everywhere with its precise
representative. -/
theorem ae_eq_preciseRepresentative [SecondCountableTopology X] [BorelSpace X]
    [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ] [CompleteSpace E]
    (hf : LocallyIntegrable f μ) : f =ᵐ[μ] preciseRepresentative μ f := by
  simpa using ae_eq_restrict_preciseRepresentative isOpen_univ (hf.locallyIntegrableOn univ)

section Oscillation

variable [CompleteSpace E] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- If `f` takes values almost everywhere on `ball x r` in a closed convex set `S`, then so do its
averages over the closed balls around `x` of small radius. -/
theorem eventually_setAverage_closedBall_mem {S : Set E} (hSc : Convex ℝ S) (hS : IsClosed S)
    {r : ℝ} (hr : 0 < r) (hf : IntegrableAtFilter f (𝓝 x) μ)
    (hfS : ∀ᵐ y ∂μ.restrict (ball x r), f y ∈ S) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⨍ y in closedBall x ε, f y ∂μ ∈ S := by
  obtain ⟨t, ht, hint⟩ := hf
  obtain ⟨t', ht', hfin⟩ := μ.finiteAt_nhds x
  obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1
    (inter_mem (inter_mem ht ht') (ball_mem_nhds x hr))
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hε' : closedBall x ε ⊆ t ∩ t' ∩ ball x r :=
    (closedBall_subset_closedBall hε.2.le).trans hsub
  exact hSc.set_average_mem hS (measure_closedBall_pos μ x hε.1).ne'
    ((measure_mono fun _ hy => (hε' hy).1.2).trans_lt hfin).ne
    (ae_restrict_of_ae_restrict_of_subset (fun _ hy => (hε' hy).2) hfS)
    (hint.mono_set fun _ hy => (hε' hy).1.1)

/-- If `f` takes values almost everywhere on `ball x r` in a closed convex set `S`, and the
averages of `f` over the closed balls around `x` converge, then the precise representative of `f`
at `x` lies in `S`. -/
theorem preciseRepresentative_mem {S : Set E} (hSc : Convex ℝ S) (hS : IsClosed S) {r : ℝ}
    (hr : 0 < r) (hf : IntegrableAtFilter f (𝓝 x) μ)
    (hfS : ∀ᵐ y ∂μ.restrict (ball x r), f y ∈ S)
    (hlim : Tendsto (fun ε => ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x))) :
    preciseRepresentative μ f x ∈ S :=
  hS.mem_of_tendsto hlim (eventually_setAverage_closedBall_mem hSc hS hr hf hfS)

/-- **The precise representative reproduces continuous representatives.** If `f` agrees almost
everywhere near `x` with a function `g` which is continuous at `x`, then the precise
representative of `f` at `x` is `g x`. -/
theorem preciseRepresentative_eq_of_continuousAt [OpensMeasurableSpace X] {V : Set X}
    (hV : V ∈ 𝓝 x) (hf : IntegrableAtFilter f (𝓝 x) μ) (h : f =ᵐ[μ.restrict V] g)
    (hg : ContinuousAt g x) : preciseRepresentative μ f x = g x := by
  refine preciseRepresentative_eq_of_tendsto (Metric.tendsto_nhds.2 fun ε hε => ?_)
  obtain ⟨δ, hδ, hsub⟩ := nhds_basis_ball.mem_iff.1
    (inter_mem hV (hg.preimage_mem_nhds (closedBall_mem_nhds (g x) (half_pos hε))))
  have hfg : ∀ᵐ y ∂μ.restrict (ball x δ), f y ∈ closedBall (g x) (ε / 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (fun _ hy => (hsub hy).1) h,
      self_mem_ae_restrict measurableSet_ball] with y hy hyδ
    exact hy ▸ (hsub hyδ).2
  filter_upwards [eventually_setAverage_closedBall_mem (convex_closedBall _ _) isClosed_closedBall
    hδ hf hfg] with r hr
  exact (mem_closedBall.1 hr).trans_lt (half_lt_self hε)

/-- The precise representative of a function agrees on an open set `U` with any function `g`
continuous on `U` which equals it almost everywhere on `U`. -/
theorem eqOn_preciseRepresentative_of_continuousOn [OpensMeasurableSpace X] {U : Set X}
    (hU : IsOpen U) (hf : LocallyIntegrableOn f U μ) (h : f =ᵐ[μ.restrict U] g)
    (hg : ContinuousOn g U) :
    EqOn (preciseRepresentative μ f) g U := fun x hx =>
  preciseRepresentative_eq_of_continuousAt (hU.mem_nhds hx)
    (by simpa [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx)] using hf x hx) h (hg.continuousAt
      (hU.mem_nhds hx))

/-- The precise representative of a locally integrable continuous function is the function
itself. -/
theorem preciseRepresentative_eq_self_of_continuous [OpensMeasurableSpace X]
    (hf : LocallyIntegrable f μ) (hcont : Continuous f) : preciseRepresentative μ f = f :=
  funext fun x => preciseRepresentative_eq_of_continuousAt univ_mem (hf x)
    (ae_of_all _ fun _ => rfl) hcont.continuousAt

/-- **Vanishing oscillation gives convergence of the averages.** If the essential oscillation of
`f` on `ball x r` tends to `0` with `r`, in the sense that for every `ε > 0` the function takes
values almost everywhere on some ball around `x` in a closed ball of radius `ε`, then the averages
of `f` over the closed balls around `x` converge to the precise representative of `f` at `x`. -/
theorem tendsto_setAverage_closedBall_preciseRepresentative
    (hf : IntegrableAtFilter f (𝓝 x) μ)
    (hosc : ∀ ε > 0, ∃ r > 0, ∃ c : E, ∀ᵐ y ∂μ.restrict (ball x r), f y ∈ closedBall c ε) :
    Tendsto (fun ε => ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := by
  -- The averages form a Cauchy filter: eventually they all lie in a ball of radius `ε / 3`.
  have hcauchy : Cauchy (map (fun ε => ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] (0 : ℝ))) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨r, hr, c, hc⟩ := hosc (ε / 3) (by positivity)
    refine ⟨closedBall c (ε / 3),
      eventually_setAverage_closedBall_mem (convex_closedBall c _) isClosed_closedBall hr hf hc,
      fun a ha b hb => ?_⟩
    calc dist a b ≤ dist a c + dist b c := dist_triangle_right a b c
      _ ≤ ε / 3 + ε / 3 := add_le_add ha hb
      _ < ε := by linarith
  obtain ⟨v, hv⟩ := CompleteSpace.complete hcauchy
  exact tendsto_nhds_limUnder ⟨v, hv⟩

/-- If `f` takes values almost everywhere on `ball x r` in the closed ball `closedBall c L`, then
the precise representatives of `f` at `x` and at any `y ∈ ball x r` are at distance at most
`2 L`, provided the averages of `f` over the closed balls around `x` and around `y` converge. -/
theorem dist_preciseRepresentative_le {y : X} {c : E} {r L : ℝ} (hxy : dist x y < r)
    (hfx : IntegrableAtFilter f (𝓝 x) μ) (hfy : IntegrableAtFilter f (𝓝 y) μ)
    (hc : ∀ᵐ z ∂μ.restrict (ball x r), f z ∈ closedBall c L)
    (hlimx : Tendsto (fun ε => ⨍ z in closedBall x ε, f z ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)))
    (hlimy : Tendsto (fun ε => ⨍ z in closedBall y ε, f z ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f y))) :
    dist (preciseRepresentative μ f x) (preciseRepresentative μ f y) ≤ 2 * L := by
  have hxc := preciseRepresentative_mem (convex_closedBall c L) isClosed_closedBall
    (dist_nonneg.trans_lt hxy) hfx hc hlimx
  -- `ball y (r - dist x y) ⊆ ball x r`, so the hypothesis also holds on a ball around `y`.
  have hyc := preciseRepresentative_mem (convex_closedBall c L) isClosed_closedBall
    (sub_pos.2 hxy) hfy
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball' (by rw [dist_comm]; linarith)) hc)
    hlimy
  calc _ ≤ dist (preciseRepresentative μ f x) c + dist (preciseRepresentative μ f y) c :=
        dist_triangle_right _ _ _
    _ ≤ L + L := add_le_add hxc hyc
    _ = 2 * L := by ring

/-- If `f` is essentially bounded by `M` on `ball x r` and the averages of `f` over the closed balls
around `x` converge, then the precise representative of `f` at `x` has norm at most `M`. -/
theorem norm_preciseRepresentative_le {r M : ℝ} (hr : 0 < r) (hf : IntegrableAtFilter f (𝓝 x) μ)
    (hbdd : ∀ᵐ y ∂μ.restrict (ball x r), ‖f y‖ ≤ M)
    (hlim : Tendsto (fun ε => ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x))) :
    ‖preciseRepresentative μ f x‖ ≤ M := by
  simpa using preciseRepresentative_mem (convex_closedBall (0 : E) M) isClosed_closedBall hr hf
    (by simpa using hbdd) hlim

/-- **Power-law oscillation decay gives convergence of the averages.** Let `α > 0` and `ρ > 0`. If
for every `0 < r ≤ ρ` the function `f` takes values almost everywhere on `ball x r` in a closed
ball of radius `C r^α`, then the averages of `f` over the closed balls around `x` converge to the
precise representative of `f` at `x`. -/
theorem tendsto_setAverage_closedBall_preciseRepresentative_of_rpow {C α ρ : ℝ} (hα : 0 < α)
    (hρ : 0 < ρ) (hf : IntegrableAtFilter f (𝓝 x) μ)
    (hosc : ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∃ c : E, ∀ᵐ y ∂μ.restrict (ball x r), f y ∈ closedBall c (C * r ^ α)) :
    Tendsto (fun ε => ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := by
  refine tendsto_setAverage_closedBall_preciseRepresentative hf fun ε hε => ?_
  have hcont : Continuous fun r : ℝ => C * r ^ α :=
    continuous_const.mul (Real.continuous_rpow_const hα.le)
  have h0 : Tendsto (fun r : ℝ => C * r ^ α) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using hcont.continuousWithinAt.tendsto (x := 0) (s := Ioi 0)
  obtain ⟨r, hrε, hr⟩ := ((h0.eventually (gt_mem_nhds hε)).and (Ioc_mem_nhdsGT hρ)).exists
  obtain ⟨c, hc⟩ := hosc r hr.1 hr.2
  exact ⟨r, hr.1, c, by filter_upwards [hc] with y hy using closedBall_subset_closedBall hrε.le hy⟩

/-- **Hölder continuity from oscillation decay.** Let `s` be a set, `ρ > 0` and `α > 0`. Suppose
`f` is integrable near every point of `s`, essentially bounded by `M` on the balls `ball x ρ`,
`x ∈ s`, and that its essential oscillation decays like a power of the radius: for every `x ∈ s`
and `0 < r ≤ ρ`, almost everywhere on `ball x r` the function takes values in a closed ball of
radius `C r^α`. Then the precise representative of `f` is Hölder continuous on `s` with exponent
`α`, with a constant depending only on `C`, `M`, `ρ` and `α`. -/
theorem holderOnWith_preciseRepresentative {s : Set X} {C M α ρ : ℝ≥0}
    (hα : 0 < α) (hρ : 0 < ρ) (hf : ∀ x ∈ s, IntegrableAtFilter f (𝓝 x) μ)
    (hosc : ∀ x ∈ s, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∃ c : E, ∀ᵐ y ∂μ.restrict (ball x r), f y ∈ closedBall c (C * r ^ (α : ℝ)))
    (hbdd : ∀ x ∈ s, ∀ᵐ y ∂μ.restrict (ball x ρ), ‖f y‖ ≤ M) :
    HolderOnWith (max (2 * C) (2 * M / ρ ^ (α : ℝ))) α (preciseRepresentative μ f) s := by
  have hα' : (0 : ℝ) < α := NNReal.coe_pos.2 hα
  have hρ' : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ
  have hlim : ∀ x ∈ s, Tendsto (fun ε => ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := fun x hx =>
    tendsto_setAverage_closedBall_preciseRepresentative_of_rpow hα' hρ' (hf x hx) (hosc x hx)
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  push_cast
  rcases lt_or_ge (dist x y) ρ with hd | hd
  · -- Nearby points: both values lie in the closed ball of radius `C r^α` supplied by the
    -- oscillation bound on `ball x r`, for every `r ∈ (dist x y, ρ]`; let `r → dist x y`.
    have key : ∀ r, dist x y < r → r ≤ ρ →
        dist (preciseRepresentative μ f x) (preciseRepresentative μ f y) ≤
          2 * (C * r ^ (α : ℝ)) := fun r hdr hrρ => by
      obtain ⟨c, hc⟩ := hosc x hx r (dist_nonneg.trans_lt hdr) hrρ
      exact dist_preciseRepresentative_le hdr (hf x hx) (hf y hy) hc (hlim x hx) (hlim y hy)
    have hle : dist (preciseRepresentative μ f x) (preciseRepresentative μ f y) ≤
        2 * C * dist x y ^ (α : ℝ) := by
      have hcont : Continuous fun r : ℝ => (C : ℝ) * r ^ (α : ℝ) :=
        continuous_const.mul (Real.continuous_rpow_const hα'.le)
      have ht : Tendsto (fun r : ℝ => 2 * ((C : ℝ) * r ^ (α : ℝ))) (𝓝[>] (dist x y))
          (𝓝 (2 * (C * dist x y ^ (α : ℝ)))) :=
        (hcont.tendsto _).mono_left nhdsWithin_le_nhds |>.const_mul 2
      rw [mul_assoc]
      refine ge_of_tendsto ht ?_
      filter_upwards [Ioc_mem_nhdsGT hd] with r hr
      exact key r hr.1 hr.2
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · -- Distant points: both values have norm at most `M`, and `2M ≤ (2M / ρ^α) dist^α`.
    have hbound : ∀ z ∈ s, ‖preciseRepresentative μ f z‖ ≤ M := fun z hz =>
      norm_preciseRepresentative_le hρ' (hf z hz) (hbdd z hz) (hlim z hz)
    have _ : (0 : ℝ) < (ρ : ℝ) ^ (α : ℝ) := Real.rpow_pos_of_pos hρ' _
    calc dist (preciseRepresentative μ f x) (preciseRepresentative μ f y)
        ≤ ‖preciseRepresentative μ f x‖ + ‖preciseRepresentative μ f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hbound x hx, hbound y hy]
      _ = 2 * M / ρ ^ (α : ℝ) * ρ ^ (α : ℝ) := by field_simp
      _ ≤ 2 * M / ρ ^ (α : ℝ) * dist x y ^ (α : ℝ) := by gcongr
      _ ≤ max (2 * C) (2 * M / ρ ^ (α : ℝ)) * dist x y ^ (α : ℝ) := by
        gcongr
        exact le_max_right _ _

end Oscillation

end MeasureTheory

end TauCeti
