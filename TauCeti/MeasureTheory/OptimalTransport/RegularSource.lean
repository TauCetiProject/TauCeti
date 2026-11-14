/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CCHypersurface
public import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.MeasureTheory.Constructions.BorelSpace.Prod

/-!
# Regular sources for quadratic optimal transport

Brenier's theorem in `TauCeti/MeasureTheory/OptimalTransport/Brenier.lean` assumes that the source
law `μ` on a finite-dimensional real inner product space `E` is absolutely continuous with respect
to an additive Haar measure. That hypothesis is sufficient — Rademacher's theorem makes every convex
potential differentiable almost everywhere — but far from necessary: in `ℝ²`, the one-dimensional
Hausdorff measure along a strictly convex circle still admits a unique, map-induced optimal plan to
every target of finite second moment, whereas one-dimensional Hausdorff measure along a line segment
can split symmetrically to the two sides of the segment.

The sharp hypothesis on `μ`, isolated by Gangbo and McCann (1996) through Zajíček's covering theorem
for convex nondifferentiability sets (1979) and recorded as Definition 1.25 and Theorem 1.26 of
Ambrosio and Gigli (2013), is that `μ` vanishes on every `c - c` hypersurface (`IsCCHypersurface`):
we call such a measure **`c - c`-regular** (`TauCeti.IsCCRegular`, avoiding a collision with
Mathlib's topological `MeasureTheory.Measure.Regular`).

Four layers of results organize this module:

1. **Calculus and sufficient conditions for `IsCCRegular`:** closure under absolute continuity,
   domination, restriction, addition, and scalar multiplication; automatic regularity of every
   additive Haar measure (`TauCeti.isCCRegular_of_isAddHaarMeasure`), every measure absolutely
   continuous with respect to Haar measure (`TauCeti.isCCRegular_of_absolutelyContinuous`), and
   every measure vanishing on all Lipschitz hypersurfaces
   (`TauCeti.isCCRegular_of_forall_isLipschitzHypersurface`); equivalence with
   `NullSingletonClass` in dimension `1` (`TauCeti.isCCRegular_iff_nullSingletonClass`); and
   equivalence with `μ`-almost everywhere differentiability of every convex function `u : E → ℝ`
   (`TauCeti.isCCRegular_iff_forall_convexOn_ae_differentiableAt`).
2. **Almost everywhere differentiability on effective domains:** for any `u : E → EReal` with convex
   real epigraph and any `c - c`-regular Borel measure `μ`, at `μ`-almost every point where
   `u x ≠ ⊤`, `u` is finite on a neighborhood of `x` and `u.toReal` is differentiable at `x`
   (`TauCeti.IsCCRegular.ae_eventually_ne_top_and_differentiableAt_toReal`), because both the
   frontier of `{x | u x ≠ ⊤}` and the interior nondifferentiability locus are covered by countably
   many `c - c` hypersurfaces.
3. **Regular-source Brenier theory:** replacing `μ ≪ ρ` by `IsCCRegular μ` throughout Brenier's
   theorem yields determinism of plans on subdifferential graphs
   (`TauCeti.IsCCRegular.eq_graphPlan_gradient_of_ae_mem_subdifferential`), uniqueness of optimal
   quadratic plans (`TauCeti.IsOptimalCoupling.unique_of_isCCRegular`), uniqueness of the monotone
   rearrangement (`TauCeti.IsCCRegular.gradient_ae_eq_gradient_of_hasLaw`), existence and almost
   everywhere uniqueness of a convex-gradient optimal transport map
   (`TauCeti.IsCCRegular.exists_isKantorovichOptimalTransportMap_gradient`), and strict convexity of
   the quadratic transport cost in the target
   (`TauCeti.IsCCRegular.transportCost_smul_add_smul_lt`).
4. **Sharpness (Ambrosio–Gigli Theorem 1.26):** conversely, if a probability measure `μ` of finite
   second moment charges some `c - c` hypersurface `s`, then `μ` charges a bounded piece
   `s ∩ closedBall 0 N`; adding `‖x‖ ^ 2 / 2` to the Lipschitz convex splitting potential from
   `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_subgradients` produces two
   Borel measurable subgradient selections `S₁, S₂` of linear growth that disagree everywhere on
   `s ∩ closedBall 0 N`. The half-and-half mixture `π = 2⁻¹ • graphPlan S₁ μ + 2⁻¹ • graphPlan S₂ μ`
   is quadratic-optimal for its second marginal `ν` (which also has finite second moment) yet is not
   of the form `graphPlan T μ` for any map `T : E → E`
   (`TauCeti.exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular`). Thus
   `IsCCRegular μ` is necessary and sufficient for every `P₂(E)` target to have all its optimal
   plans (equivalently, a unique optimal plan) induced by a transport map. Note that uniqueness of
   optimal plans *alone*, without map-inducibility, does not force `IsCCRegular μ`: a Dirac mass
   `δ_x` has a unique coupling with every target, yet is not `c - c`-regular in positive dimension.

## Main definitions

* `TauCeti.IsCCRegular μ` — a measure `μ` on a real inner product space `E` assigns zero mass to
  every `c - c` hypersurface (`∀ ⦃s⦄, IsCCHypersurface s → μ s = 0`).

## Main statements

* `TauCeti.isCCRegular_of_forall_isLipschitzHypersurface`,
  `TauCeti.isCCRegular_of_isAddHaarMeasure`, and `TauCeti.isCCRegular_of_absolutelyContinuous` —
  measures null on Lipschitz hypersurfaces, additive Haar measures, and measures absolutely
  continuous with respect to Haar measure are `c - c`-regular;
* `TauCeti.isCCRegular_iff_nullSingletonClass` — on a one-dimensional inner product space,
  `IsCCRegular μ` is equivalent to `NullSingletonClass μ`;
* `TauCeti.isCCRegular_iff_forall_convexOn_ae_differentiableAt` — a measure on a finite-dimensional
  inner product space is `c - c`-regular if and only if every convex function `u : E → ℝ` is
  differentiable `μ`-almost everywhere;
* `TauCeti.IsCCRegular.exists_isKantorovichOptimalTransportMap_gradient` and
  `TauCeti.IsOptimalCoupling.unique_of_isCCRegular` — **Brenier's theorem for `c - c`-regular
  sources**;
* `TauCeti.exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular` — **converse
  splitting construction** when `¬ IsCCRegular μ`;
* `TauCeti.isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan`,
  `TauCeti.isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique`,
  `TauCeti.WassersteinSpace.isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan`, and
  `WassersteinSpace.isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique`
  — **Ambrosio–Gigli Theorem 1.26**: sharp characterization of `c - c`-regular sources in `P₂(E)`.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340--348.
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Mathematics
  2062, Springer, 2013, Definition 1.25 and Theorem 1.26.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, AMS, 2003,
  §2.1.3 and §2.4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace

namespace TauCeti

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ ν : Measure E}

/-- A measure `μ` on a real inner product space `E` is **`c - c`-regular** if it assigns measure
zero to every `c - c` hypersurface (`TauCeti.IsCCHypersurface`), i.e., every codimension-one graph
of a difference of two finite convex functions. In finite dimensions, this is the sharp condition
under which quadratic optimal transport out of `μ` is uniquely solved by convex gradients for all
targets of finite second moment (Ambrosio–Gigli, Definition 1.25 and Theorem 1.26). -/
def IsCCRegular (μ : Measure E) : Prop :=
  ∀ ⦃s : Set E⦄, IsCCHypersurface s → μ s = 0

/-- Unfolding lemma for `TauCeti.IsCCRegular`. -/
theorem isCCRegular_def (μ : Measure E) :
    IsCCRegular μ ↔ ∀ ⦃s : Set E⦄, IsCCHypersurface s → μ s = 0 :=
  Iff.rfl

/-- A `c - c`-regular measure vanishes on every `c - c` hypersurface. -/
theorem IsCCRegular.measure_eq_zero (hμ : IsCCRegular μ) {s : Set E} (hs : IsCCHypersurface s) :
    μ s = 0 :=
  hμ hs

/-- A `c - c`-regular measure vanishes on any countable union of `c - c` hypersurfaces. -/
theorem IsCCRegular.measure_sUnion_eq_zero (hμ : IsCCRegular μ) {C : Set (Set E)}
    (hC : C.Countable) (hs : ∀ s ∈ C, IsCCHypersurface s) : μ (⋃₀ C) = 0 :=
  (measure_sUnion_null_iff hC).2 fun s h => hμ (hs s h)

/-- A `c - c`-regular measure vanishes on any indexed countable union of `c - c` hypersurfaces. -/
theorem IsCCRegular.measure_iUnion_eq_zero {ι : Sort*} [Countable ι] (hμ : IsCCRegular μ)
    {s : ι → Set E} (hs : ∀ i, IsCCHypersurface (s i)) : μ (⋃ i, s i) = 0 :=
  measure_iUnion_null fun i => hμ (hs i)

/-- Any set covered by countably many `c - c` hypersurfaces is null for every `c - c`-regular
measure. -/
theorem IsCCRegular.measure_eq_zero_of_subset_sUnion (hμ : IsCCRegular μ) {A : Set E}
    {C : Set (Set E)} (hC : C.Countable) (hs : ∀ s ∈ C, IsCCHypersurface s) (hA : A ⊆ ⋃₀ C) :
    μ A = 0 :=
  measure_mono_null hA (hμ.measure_sUnion_eq_zero hC hs)

/-- The zero measure is `c - c`-regular. -/
@[simp]
theorem isCCRegular_zero : IsCCRegular (0 : Measure E) :=
  fun _ _ => rfl

/-- On a `0`-dimensional inner product space there are no `c - c` hypersurfaces, so every measure is
`c - c`-regular. -/
theorem isCCRegular_of_subsingleton [Subsingleton E] (μ : Measure E) : IsCCRegular μ :=
  fun s hs => (not_isCCHypersurface_of_subsingleton s hs).elim

/-- Absolute continuity transfers `c - c`-regularity downward. -/
theorem IsCCRegular.mono_ac (h : μ ≪ ν) (hν : IsCCRegular ν) : IsCCRegular μ :=
  fun _ hs => h (hν hs)

/-- Measure domination transfers `c - c`-regularity downward. -/
theorem IsCCRegular.mono (h : μ ≤ ν) (hν : IsCCRegular ν) : IsCCRegular μ :=
  hν.mono_ac (Measure.absolutelyContinuous_of_le h)

/-- Restricting a `c - c`-regular measure to any set preserves `c - c`-regularity. -/
theorem IsCCRegular.restrict (hμ : IsCCRegular μ) (t : Set E) : IsCCRegular (μ.restrict t) :=
  hμ.mono Measure.restrict_le_self

/-- The sum of two `c - c`-regular measures is `c - c`-regular. -/
theorem IsCCRegular.add (hμ : IsCCRegular μ) (hν : IsCCRegular ν) : IsCCRegular (μ + ν) :=
  fun s hs => by simp [hμ hs, hν hs]

/-- Scaling a `c - c`-regular measure by any factor in `ℝ≥0∞` preserves `c - c`-regularity. -/
theorem IsCCRegular.smul (hμ : IsCCRegular μ) (c : ℝ≥0∞) : IsCCRegular (c • μ) :=
  fun s hs => by simp [hμ hs]

/-- On a one-dimensional real inner product space, `c - c` hypersurfaces are singletons, so
`IsCCRegular μ` is equivalent to `NullSingletonClass μ`. -/
theorem isCCRegular_iff_nullSingletonClass (hd : Module.finrank ℝ E = 1) :
    IsCCRegular μ ↔ NullSingletonClass μ := by
  refine ⟨fun h => ⟨fun x => h ((isCCHypersurface_iff_exists_eq_singleton hd).2 ⟨x, rfl⟩)⟩,
    fun h s hs => ?_⟩
  have := h
  obtain ⟨x, rfl⟩ := (isCCHypersurface_iff_exists_eq_singleton hd).1 hs
  exact measure_singleton x

end Basic

private theorem convex_ne_top_of_convex_epigraph {E : Type*} [AddCommGroup E] [Module ℝ E]
    {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) :
    Convex ℝ {x : E | u x ≠ ⊤} := by
  intro x hx y hy a b ha hb hab
  have hle : ∀ z : E, u z ≠ ⊤ → u z ≤ ((u z).toReal : EReal) := fun z hz => by
    rcases eq_bot_or_bot_lt (u z) with hbot | hbot
    · simp [hbot]
    · exact (EReal.coe_toReal hz hbot.ne').symm.le
  have hmem := hconv (x := (x, (u x).toReal)) (hle x hx) (y := (y, (u y).toReal)) (hle y hy)
    ha hb hab
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hmem

section SufficientConditions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- **Measures null on Lipschitz hypersurfaces are `c - c`-regular.** Every `c - c` hypersurface in
a finite-dimensional inner product space is covered by countably many Lipschitz hypersurfaces
(`TauCeti.IsCCHypersurface.subset_iUnion_isLipschitzHypersurface`), so vanishing on all Lipschitz
hypersurfaces implies `IsCCRegular`. -/
theorem isCCRegular_of_forall_isLipschitzHypersurface {μ : Measure E}
    (h : ∀ ⦃s : Set E⦄, IsLipschitzHypersurface s → μ s = 0) : IsCCRegular μ := fun _ hs => by
  obtain ⟨t, ht, hsub⟩ := hs.subset_iUnion_isLipschitzHypersurface
  exact measure_mono_null hsub (measure_iUnion_null fun n => h (ht n))

/-- **Differentiability characterization of `c - c`-regularity.** By Zajíček's theorem
(`TauCeti.exists_convexOn_subset_not_differentiableAt_iff`), a measure `μ` on a finite-dimensional
real inner product space `E` is `c - c`-regular if and only if every globally convex function
`u : E → ℝ` is differentiable `μ`-almost everywhere. -/
theorem isCCRegular_iff_forall_convexOn_ae_differentiableAt {μ : Measure E} :
    IsCCRegular μ ↔ ∀ u : E → ℝ, ConvexOn ℝ univ u → ∀ᵐ x ∂μ, DifferentiableAt ℝ u x := by
  refine ⟨fun hμ u hu => ?_, fun h s hs => ?_⟩
  · obtain ⟨C, hC, hCs, hsub⟩ :=
      exists_convexOn_subset_not_differentiableAt_iff.1 ⟨u, hu, Subset.rfl⟩
    exact ae_iff.2 (hμ.measure_eq_zero_of_subset_sUnion hC hCs hsub)
  · obtain ⟨u, hu, hsub⟩ := (exists_convexOn_subset_not_differentiableAt_iff (A := s)).2
      ⟨{s}, countable_singleton s, by simpa, by simp⟩
    exact measure_mono_null hsub (ae_iff.1 (h u hu))

/-- **Rademacher's theorem for convex functions against a `c - c`-regular measure.** For any
extended-real function `u : E → EReal` with convex real epigraph and any `c - c`-regular measure
`μ`, at `μ`-almost every point `x` where `u x ≠ ⊤`, `u` is finite on a neighborhood of `x` and
`u.toReal` is differentiable at `x`. Unlike the Lebesgue version
`TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`, this needs no `u x ≠ ⊥` assumption. -/
theorem IsCCRegular.ae_eventually_ne_top_and_differentiableAt_toReal {μ : Measure E}
    (hμ : IsCCRegular μ) {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) :
    ∀ᵐ x ∂μ, u x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
  let D : Set E := {x | u x ≠ ⊤}
  have hD_conv : Convex ℝ D := convex_ne_top_of_convex_epigraph hconv
  obtain ⟨C₁, hC₁, hs₁, hfr⟩ := hD_conv.exists_countable_isCCHypersurface_cover_frontier
  obtain ⟨C₂, hC₂, hs₂, hnd⟩ :=
    exists_countable_isCCHypersurface_cover_not_differentiableAt_toReal hconv
  have hfr_sub : D \ interior D ⊆ frontier D := fun _ hx => ⟨subset_closure hx.1, hx.2⟩
  have hnull₁ : μ (D \ interior D) = 0 :=
    hμ.measure_eq_zero_of_subset_sUnion hC₁ hs₁ (hfr_sub.trans hfr)
  have hnull₂ : μ {x | x ∈ interior D ∧ ¬ DifferentiableAt ℝ (fun x' => (u x').toReal) x} = 0 :=
    hμ.measure_eq_zero_of_subset_sUnion hC₂ hs₂ hnd
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull₁,
    measure_eq_zero_iff_ae_notMem.1 hnull₂] with x hx₁ hx₂ hxD
  have hx_int : x ∈ interior D := by
    by_contra hni
    exact hx₁ ⟨hxD, hni⟩
  have hxdiff : DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
    by_contra hndiff
    exact hx₂ ⟨hx_int, hndiff⟩
  exact ⟨mem_interior_iff_mem_nhds.1 hx_int, hxdiff⟩

section Borel

variable [BorelSpace E]

/-- **Every additive Haar measure is `c - c`-regular.** -/
theorem isCCRegular_of_isAddHaarMeasure (μ : Measure E) [μ.IsAddHaarMeasure] : IsCCRegular μ :=
  fun _ hs => hs.addHaar_eq_zero μ

/-- **Every measure absolutely continuous with respect to an additive Haar measure is
`c - c`-regular.** -/
theorem isCCRegular_of_absolutelyContinuous {μ ρ : Measure E} [ρ.IsAddHaarMeasure] (h : μ ≪ ρ) :
    IsCCRegular μ :=
  (isCCRegular_of_isAddHaarMeasure ρ).mono_ac h

end Borel

end SufficientConditions

section RegularBrenier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E} {π : Measure (E × E)}

/-- **A plan on a subdifferential graph over a `c - c`-regular source is a gradient graph plan.**
Generalizes `TauCeti.eq_graphPlan_gradient_of_ae_mem_subdifferential` from absolutely continuous
sources to `c - c`-regular sources. -/
theorem IsCCRegular.eq_graphPlan_gradient_of_ae_mem_subdifferential (hπ : π.fst = μ)
    (hμ : IsCCRegular μ) {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous u)
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ := by
  have hdom : ∀ᵐ x ∂μ, u x ≠ ⊤ := by
    rw [← hπ]
    refine (ae_map_iff measurable_fst.aemeasurable
      (hlsc.measurable (measurableSet_singleton ⊤).compl)).2 ?_
    filter_upwards [hsub] with z hz using ne_top_of_mem_subdifferential (innerₗ E) hz
  have hdiff : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
    filter_upwards [hμ.ae_eventually_ne_top_and_differentiableAt_toReal hconv, hdom]
      with x hx hx' using hx hx'
  have hgraph : ∀ᵐ z ∂π, z.2 = ∇ (fun x => (u x).toReal) z.1 := by
    rw [← hπ] at hdiff
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdiff, hsub] with z ⟨hdom, hd⟩ hz
    exact (gradient_toReal_eq_of_mem_subdifferential hz hdom hd).symm
  refine ⟨hdiff, ?_⟩
  rw [eq_graphPlan_of_ae_snd_eq (measurable_gradient _).aemeasurable hgraph, hπ]

/-- **An optimal quadratic plan out of a `c - c`-regular source is the graph plan of a convex
gradient.** Generalizes `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_gradient`. -/
theorem IsOptimalCoupling.exists_eq_graphPlan_gradient_of_isCCRegular [IsFiniteMeasure μ]
    (hμ : IsCCRegular μ)
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ := by
  obtain ⟨u, hconv, hlsc, hbot, -, hsub⟩ := h.exists_support_subset_subdifferential hfin
  have hsub' : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
    filter_upwards [π.support_mem_ae] with z hz using hsub hz
  obtain ⟨hdiff, hgraph⟩ :=
    hμ.eq_graphPlan_gradient_of_ae_mem_subdifferential h.fst_eq hconv hlsc hsub'
  exact ⟨u, hconv, hlsc, hbot, hdiff, hgraph⟩

/-- **Regular-source Brenier theorem for the cost `edist ^ 2`.** Generalizes
`TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_absolutelyContinuous`. -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_isCCRegular [IsFiniteMeasure μ]
    (hμ : IsCCRegular μ)
    (h : IsOptimalCoupling (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) π μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ T : E → E, Measurable T ∧ π = graphPlan T μ := by
  have hfin' : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
    have h2 := wassersteinEDist_rpow_eq_transportCost measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top μ ν
    rw [ENNReal.toReal_ofNat, funext edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two,
      transportCost_const_mul two_ne_zero ENNReal.ofNat_ne_top] at h2
    refine fun htop => ENNReal.rpow_ne_top_of_nonneg zero_le_two hfin ?_
    rw [h2, htop, ENNReal.mul_top two_ne_zero]
  have hopt := isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two h
  obtain ⟨u, -, -, -, -, hgraph⟩ := hopt.exists_eq_graphPlan_gradient_of_isCCRegular hμ hfin'
  exact ⟨_, measurable_gradient _, hgraph⟩

/-- **Uniqueness of the optimal quadratic plan out of a `c - c`-regular source.** Generalizes
`TauCeti.IsOptimalCoupling.unique`. -/
theorem IsOptimalCoupling.unique_of_isCCRegular [IsFiniteMeasure μ] (hμ : IsCCRegular μ)
    {π' : Measure (E × E)}
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (h' : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π' μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    π = π' := by
  have hsum := h.add h'
  have hfin' : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (μ + μ) (ν + ν) ≠ ∞ := by
    rw [← hsum.lintegral_eq, lintegral_add_measure, h.lintegral_eq, h'.lintegral_eq]
    exact ENNReal.add_ne_top.2 ⟨hfin, hfin⟩
  obtain ⟨u, -, -, -, -, hgraph⟩ :=
    hsum.exists_eq_graphPlan_gradient_of_isCCRegular (hμ.add hμ) hfin'
  have hT := measurable_gradient fun x => (u x).toReal
  have hae : ∀ᵐ z ∂(π + π'), z.2 = ∇ (fun x => (u x).toReal) z.1 :=
    hgraph ▸ ae_snd_eq_graphPlan hT.aemeasurable
  rw [eq_graphPlan_of_ae_snd_eq hT.aemeasurable (ae_mono (Measure.le_add_right le_rfl) hae),
    eq_graphPlan_of_ae_snd_eq hT.aemeasurable (ae_mono (Measure.le_add_left le_rfl) hae),
    h.fst_eq, h'.fst_eq]

/-- **Uniqueness of the monotone rearrangement out of a `c - c`-regular source.** Generalizes
`TauCeti.gradient_ae_eq_gradient_of_hasLaw`. -/
theorem IsCCRegular.gradient_ae_eq_gradient_of_hasLaw [IsFiniteMeasure μ] (hμ : IsCCRegular μ)
    (hμ2 : MemLp id 2 μ) (hν2 : MemLp id 2 ν) {u v : E → EReal}
    (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hubot : ∀ x, u x ≠ ⊥)
    (hudiff : ∀ᵐ x ∂μ, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (huν : HasLaw (∇ fun x => (u x).toReal) ν μ)
    (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hvbot : ∀ x, v x ≠ ⊥)
    (hvdiff : ∀ᵐ x ∂μ, v x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (v x').toReal) x)
    (hvν : HasLaw (∇ fun x => (v x).toReal) ν μ) :
    (∇ fun x => (u x).toReal) =ᵐ[μ] ∇ fun x => (v x).toReal := by
  have hc := continuous_ofReal_norm_sub_sq_div_two (F := E)
  have hu' := (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan huν
    hc.measurable.aemeasurable).1 (isKantorovichOptimalTransportMap_gradient hμ2 hν2 hu hubot
      hudiff huν)
  have hv' := (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hvν
    hc.measurable.aemeasurable).1 (isKantorovichOptimalTransportMap_gradient hμ2 hν2 hv hvbot
      hvdiff hvν)
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
    rw [← hu'.lintegral_eq, hu'.toIsCoupling.lintegral_norm_sub_sq_div_two hμ2 hν2]
    exact ENNReal.ofReal_ne_top
  exact (graphPlan_eq_graphPlan_iff huν.aemeasurable hvν.aemeasurable).1
    (hu'.unique_of_isCCRegular hμ hv' hfin)

/-- **Brenier's theorem for `c - c`-regular sources.** Let `μ` be a `c - c`-regular probability
measure on a finite-dimensional real inner product space `E`, and suppose `ν` has finite quadratic
transport cost from `μ`. Then there exists a proper lower semicontinuous convex potential
`u : E → EReal`, finite near `μ`-almost every point with differentiable real representative there,
whose gradient `T = ∇ (fun x => (u x).toReal)` is the `μ`-a.e. unique optimal transport map from
`μ` to `ν` and induces the unique optimal coupling `graphPlan T μ`. -/
theorem IsCCRegular.exists_isKantorovichOptimalTransportMap_gradient [IsProbabilityMeasure μ]
    (hμ : IsCCRegular μ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      (∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ↔
        π = graphPlan (∇ fun x => (u x).toReal) μ) ∧
      ∀ S : E → E,
        IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
          μ ν S → S =ᵐ[μ] ∇ fun x => (u x).toReal := by
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin
  have hc : Continuous fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    continuous_ofReal_norm_sub_sq_div_two
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ ν hc.lowerSemicontinuous
  obtain ⟨u, hconv, hlsc, hbot, hdiff, hgraph⟩ :=
    hπ.exists_eq_graphPlan_gradient_of_isCCRegular hμ hfin
  have hT := measurable_gradient fun x => (u x).toReal
  have hlaw : HasLaw (∇ fun x => (u x).toReal) ν μ :=
    (isCoupling_graphPlan_iff hT.aemeasurable).1 (hgraph ▸ hπ.toIsCoupling)
  have hiff : ∀ S : E → E, HasLaw S ν μ →
      (IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν S ↔ IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
          (graphPlan S μ) μ ν) := fun S hS =>
    isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hS
      hc.measurable.aemeasurable
  refine ⟨u, hconv, hlsc, hbot, hdiff, (hiff _ hlaw).2 (hgraph ▸ hπ),
    fun σ => ⟨fun hσ => (hσ.unique_of_isCCRegular hμ hπ hfin).trans hgraph,
      fun hσ => hσ ▸ hgraph ▸ hπ⟩,
    fun S hS => ?_⟩
  exact (graphPlan_eq_graphPlan_iff hS.toHasLaw.aemeasurable hT.aemeasurable).1
    ((((hiff S hS.toHasLaw).1 hS).unique_of_isCCRegular hμ hπ hfin).trans hgraph)

/-- **Strict convexity of the quadratic transport cost in the target for `c - c`-regular sources.**
Whenever `μ` is a `c - c`-regular probability measure and `ν₀ ≠ ν₁` have finite quadratic transport
cost from `μ`, any nontrivial convex combination `a • ν₀ + b • ν₁` (`a, b ≠ 0`, `a + b = 1`) has
strictly smaller transport cost than the convex combination of the two costs. -/
theorem IsCCRegular.transportCost_smul_add_smul_lt [IsProbabilityMeasure μ] (hμ : IsCCRegular μ)
    {ν₀ ν₁ : Measure E} {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfin₀ : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₀ ≠ ∞)
    (hfin₁ : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₁ ≠ ∞)
    (hne : ν₀ ≠ ν₁) :
    transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ (a • ν₀ + b • ν₁) <
      a * transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₀ +
        b * transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₁ := by
  let c : E × E → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)
  have hc : LowerSemicontinuous c := continuous_ofReal_norm_sub_sq_div_two.lowerSemicontinuous
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin₀
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin₁
  obtain ⟨π₀, hπ₀⟩ := exists_isOptimalCoupling μ ν₀ hc
  obtain ⟨π₁, hπ₁⟩ := exists_isOptimalCoupling μ ν₁ hc
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
  have hbtop : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have hfin_mix : transportCost c μ (a • ν₀ + b • ν₁) ≠ ∞ := by
    have hle : transportCost c (a • μ + b • μ) (a • ν₀ + b • ν₁) ≤
        a * transportCost c μ ν₀ + b * transportCost c μ ν₁ := by
      simpa only [transportCost_smul hatop, transportCost_smul hbtop] using
        transportCost_add_le c (a • μ) (b • μ) (a • ν₀) (b • ν₁)
    rw [← add_smul, hab, one_smul] at hle
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hatop hfin₀, ENNReal.mul_ne_top hbtop hfin₁⟩) hle
  refine TauCeti.transportCost_smul_add_smul_lt hab ha hb hπ₀ hπ₁ (fun π hπ => ?_) hne
  obtain ⟨u, -, -, -, -, hgraph⟩ := hπ.exists_eq_graphPlan_gradient_of_isCCRegular hμ hfin_mix
  exact ⟨_, (measurable_gradient _).aemeasurable, hgraph⟩

end RegularBrenier

private theorem mem_subdifferential_norm_sq_div_two_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ψ : E → ℝ} {T : E → E}
    (hT : ∀ x z, ψ x + inner ℝ (z - x) (T x) ≤ ψ z) (x : E) :
    x + T x ∈ subdifferential (innerₗ E) (fun z => ((‖z‖ ^ 2 / 2 + ψ z : ℝ) : EReal)) x := by
  refine (mem_subdifferential_iff (innerₗ E)).2
    ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, fun z => ?_⟩
  rw [innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hsq : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at hsq
  have hin : inner ℝ (z - x) (x + T x) = inner ℝ z x - ‖x‖ ^ 2 + inner ℝ (z - x) (T x) := by
    rw [inner_add_right, inner_sub_left, real_inner_self_eq_norm_sq]
  linarith [hT x z]

private theorem exists_closedBall_inter_measure_ne_zero {E : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace E] {μ : Measure E} {s : Set E} (hμs : μ s ≠ 0) :
    ∃ N : ℕ, μ (s ∩ closedBall 0 N) ≠ 0 := by
  by_contra! hall
  apply hμs
  have hcover : s = ⋃ N : ℕ, (s ∩ closedBall 0 N) := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_closedBall_zero_iff]
    exact ⟨fun hx => let ⟨N, hN⟩ := exists_nat_ge ‖x‖; ⟨N, hx, hN⟩, fun ⟨_, hx, _⟩ => hx⟩
  rw [hcover, measure_iUnion_null hall]

private theorem smul_graphPlan_add_apply_eq_lt_one {E : Type*} [MeasurableSpace E]
    [MeasurableEq E] {μ : Measure E} [IsProbabilityMeasure μ] {B : Set E} (hBm : MeasurableSet B)
    (hμB : μ B ≠ 0) {S₁ S₂ T' : E → E} (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (hBne : ∀ x ∈ B, S₁ x ≠ S₂ x) (hT' : Measurable T') :
    ((2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ)
      {z : E × E | z.2 = T' z.1} < 1 := by
  let G : Set (E × E) := {z | z.2 = T' z.1}
  have hGm : MeasurableSet G := measurableSet_eq_fun measurable_snd (hT'.comp measurable_fst)
  let E₁ : Set E := {x | S₁ x = T' x}
  let E₂ : Set E := {x | S₂ x = T' x}
  have hE₂ : MeasurableSet E₂ := measurableSet_eq_fun hS₂ hT'
  have hinter : E₁ ∩ E₂ ⊆ Bᶜ := fun x ⟨h₁, h₂⟩ hxB => hBne x hxB (h₁.trans h₂.symm)
  have hBc_lt : μ Bᶜ < 1 := by
    have hsum : μ B + μ Bᶜ = 1 := by rw [measure_add_measure_compl hBm, measure_univ]
    refine lt_of_le_of_ne (hsum ▸ le_add_self) fun h1 => hμB ?_
    exact (ENNReal.add_left_inj ENNReal.one_ne_top).1 (by simpa [h1] using hsum)
  have hsum_lt : μ E₁ + μ E₂ < 2 := by
    calc μ E₁ + μ E₂ = μ (E₁ ∪ E₂) + μ (E₁ ∩ E₂) := (measure_union_add_inter E₁ hE₂).symm
      _ ≤ μ univ + μ Bᶜ := add_le_add (measure_mono (subset_univ _)) (measure_mono hinter)
      _ = 1 + μ Bᶜ := by rw [measure_univ]
      _ < 1 + 1 := ENNReal.add_lt_add_left ENNReal.one_ne_top hBc_lt
      _ = 2 := one_add_one_eq_two
  have hval : ((2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ) G =
      (μ E₁ + μ E₂) * 2⁻¹ := by
    rw [FunLike.coe_add, Pi.add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_add, mul_comm, graphPlan_apply hS₁.aemeasurable hGm,
      graphPlan_apply hS₂.aemeasurable hGm]
    rfl
  rw [hval, ← ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
    (ENNReal.inv_ne_top.2 two_ne_zero) hsum_lt

private theorem ne_graphPlan_of_smul_graphPlan_add {E : Type*} [Nonempty E] [MeasurableSpace E]
    [MeasurableEq E] {μ : Measure E} [IsProbabilityMeasure μ] {B : Set E} (hBm : MeasurableSet B)
    (hμB : μ B ≠ 0) {S₁ S₂ : E → E} (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (hBne : ∀ x ∈ B, S₁ x ≠ S₂ x) (T : E → E) :
    (2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ ≠ graphPlan T μ := by
  intro hEq
  by_cases hT : AEMeasurable T μ
  · let T' : E → E := hT.mk T
    have hT' : Measurable T' := hT.measurable_mk
    have hlt := smul_graphPlan_add_apply_eq_lt_one hBm hμB hS₁ hS₂ hBne hT'
    have hGm : MeasurableSet {z : E × E | z.2 = T' z.1} :=
      measurableSet_eq_fun measurable_snd (hT'.comp measurable_fst)
    rw [hEq, graphPlan_congr hT.ae_eq_mk, graphPlan_apply hT'.aemeasurable hGm] at hlt
    exact hlt.ne (by simp)
  · have hg : ¬ AEMeasurable (fun x => (x, T x)) μ :=
      fun h => hT (measurable_snd.comp_aemeasurable h)
    have hdir : graphPlan T μ = Measure.dirac Classical.ofNonempty := by
      rw [graphPlan_def,
        Measure.map_of_not_aemeasurable_of_ne_zero hg (IsProbabilityMeasure.ne_zero μ)]
    let z₀ : E × E := Classical.ofNonempty
    let T' : E → E := fun _ => z₀.2
    have hlt := smul_graphPlan_add_apply_eq_lt_one hBm hμB hS₁ hS₂ hBne (T' := T') measurable_const
    have hGm : MeasurableSet {z : E × E | z.2 = T' z.1} :=
      measurableSet_eq_fun measurable_snd (measurable_const.comp measurable_fst)
    rw [hEq, hdir, Measure.dirac_apply' z₀ hGm] at hlt
    exact hlt.ne (by simp [T', z₀])

section SharpCharacterization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Converse splitting construction for non-regular sources (Ambrosio–Gigli Theorem 1.26,
necessity).** If a probability measure `μ` of finite second moment on a finite-dimensional real
inner product space `E` is *not* `c - c`-regular, then there exist a probability measure `ν` on `E`
with `MemLp id 2 ν` and a quadratic optimal coupling `π` between `μ` and `ν` that is not of the form
`graphPlan T μ` for any map `T : E → E`. -/
theorem exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular {μ : Measure E}
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hnot : ¬ IsCCRegular μ) :
    ∃ (ν : Measure E) (_ : IsProbabilityMeasure ν) (_ : MemLp id 2 ν) (π : Measure (E × E)),
      IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ∧
        ∀ T : E → E, π ≠ graphPlan T μ := by
  have : MeasurableEq E := ⟨isClosed_diagonal.measurableSet⟩
  simp only [IsCCRegular, not_forall] at hnot
  obtain ⟨s, hs, hμs⟩ := hnot
  obtain ⟨N, hμB⟩ := exists_closedBall_inter_measure_ne_zero hμs
  obtain ⟨K, ψ, T₁, T₂, -, -, hT₁m, hT₂m, hT₁s, hT₂s, hT₁n, hT₂n, hTne⟩ :=
    hs.exists_convexOn_lipschitzWith_measurable_subgradients (N : ℝ)
  let S₁ : E → E := fun x => x + T₁ x
  let S₂ : E → E := fun x => x + T₂ x
  have hS₁m : Measurable S₁ := measurable_id.add hT₁m
  have hS₂m : Measurable S₂ := measurable_id.add hT₂m
  have hS₁_lp : MemLp id 2 (μ.map S₁) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hS₁m.aemeasurable).2
      (hμ2.add (MemLp.of_bound hT₁m.aestronglyMeasurable K (.of_forall hT₁n)))
  have hS₂_lp : MemLp id 2 (μ.map S₂) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hS₂m.aemeasurable).2
      (hμ2.add (MemLp.of_bound hT₂m.aestronglyMeasurable K (.of_forall hT₂n)))
  have hhalf_ne_top : (2⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.2 two_ne_zero
  have hhalf_add : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  let ν : Measure E := (2⁻¹ : ℝ≥0∞) • μ.map S₁ + (2⁻¹ : ℝ≥0∞) • μ.map S₂
  have hν_prob : IsProbabilityMeasure ν := ⟨by
    simp only [ν, FunLike.coe_add, Pi.add_apply, smul_apply, smul_eq_mul, measure_univ, mul_one,
      hhalf_add]⟩
  have hν2 : MemLp id 2 ν :=
    (hS₁_lp.smul_measure hhalf_ne_top).add_measure (hS₂_lp.smul_measure hhalf_ne_top)
  let π : Measure (E × E) := (2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ
  have hπ_coup : IsCoupling π μ ν := by
    have h := ((isCoupling_graphPlan_map (μ := μ) hS₁m.aemeasurable).smul (2⁻¹ : ℝ≥0∞)).add
      ((isCoupling_graphPlan_map (μ := μ) hS₂m.aemeasurable).smul (2⁻¹ : ℝ≥0∞))
    rwa [← add_smul, hhalf_add, one_smul] at h
  let u : E → EReal := fun z => ((‖z‖ ^ 2 / 2 + ψ z : ℝ) : EReal)
  have hπ_sub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
    have h₁ : ∀ᵐ z ∂graphPlan S₁ μ, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
      filter_upwards [ae_snd_eq_graphPlan hS₁m.aemeasurable] with z hz
      exact hz ▸ mem_subdifferential_norm_sq_div_two_add hT₁s z.1
    have h₂ : ∀ᵐ z ∂graphPlan S₂ μ, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
      filter_upwards [ae_snd_eq_graphPlan hS₂m.aemeasurable] with z hz
      exact hz ▸ mem_subdifferential_norm_sq_div_two_add hT₂s z.1
    exact ae_add_measure_iff.2 ⟨Measure.ae_smul_measure h₁ _, Measure.ae_smul_measure h₂ _⟩
  exact ⟨ν, hν_prob, hν2, π, hπ_coup.isOptimalCoupling_of_ae_mem_subdifferential hμ2 hν2 hπ_sub,
    ne_graphPlan_of_smul_graphPlan_add (hs.measurableSet.inter measurableSet_closedBall) hμB
      hS₁m hS₂m (fun x hx hEq => hTne x hx (add_left_cancel hEq))⟩

/-- **Ambrosio–Gigli Theorem 1.26 (determinism of all optimal plans).** Let `μ` be a probability
measure with `MemLp id 2 μ` on a finite-dimensional real inner product space `E`. Then `μ` is
`c - c`-regular if and only if for every probability measure `ν` on `E` with `MemLp id 2 ν`, every
optimal quadratic coupling between `μ` and `ν` is induced by a transport map. -/
theorem isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan {μ : Measure E}
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) :
    IsCCRegular μ ↔
      ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν →
        ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν →
          ∃ T : E → E, π = graphPlan T μ := by
  refine ⟨fun hμ ν _ hν2 π hπ => ?_, fun hall => ?_⟩
  · have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
      rw [← hπ.lintegral_eq, hπ.toIsCoupling.lintegral_norm_sub_sq_div_two hμ2 hν2]
      exact ENNReal.ofReal_ne_top
    obtain ⟨u, -, -, -, -, hgraph⟩ := hπ.exists_eq_graphPlan_gradient_of_isCCRegular hμ hfin
    exact ⟨_, hgraph⟩
  · by_contra hnot
    obtain ⟨ν, hνp, hν2, π, hπ, hne⟩ :=
      exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular hμ2 hnot
    obtain ⟨T, hT⟩ := @hall ν hνp hν2 π hπ
    exact hne T hT

/-- **Ambrosio–Gigli Theorem 1.26 (existence of a unique, map-induced optimal plan).** Let `μ` be a
probability measure with `MemLp id 2 μ` on a finite-dimensional real inner product space `E`. Then
`μ` is `c - c`-regular if and only if for every probability measure `ν` on `E` with `MemLp id 2 ν`,
there exists an optimal transport map `T : E → E` from `μ` to `ν` whose graph plan `graphPlan T μ`
is the unique optimal quadratic coupling between `μ` and `ν`. -/
theorem isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique
    {μ : Measure E} [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) :
    IsCCRegular μ ↔
      ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν →
        ∃ T : E → E,
          IsKantorovichOptimalTransportMap
            (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν T ∧
          ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ↔
            π = graphPlan T μ := by
  refine ⟨fun hμ ν _ hν2 => ?_, fun hall =>
    (isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan hμ2).2
      fun ν _ hν2 π hπ => let ⟨T, _, hiff⟩ := hall ν hν2; ⟨T, (hiff π).1 hπ⟩⟩
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (transportCost_le_lintegral (isCoupling_prod μ ν) _)
    rw [(isCoupling_prod μ ν).lintegral_norm_sub_sq_div_two hμ2 hν2]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, -, -, -, -, hT, hiff, -⟩ := hμ.exists_isKantorovichOptimalTransportMap_gradient hfin
  exact ⟨_, hT, hiff⟩

/-- **Ambrosio–Gigli Theorem 1.26 on `WassersteinSpace 2 E` (determinism form).** A quadratic
Wasserstein law `μ : WassersteinSpace 2 E` has `c - c`-regular underlying measure if and only if for
every target `ν : WassersteinSpace 2 E`, every optimal quadratic coupling between `μ` and `ν` is
induced by a transport map. -/
theorem WassersteinSpace.isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan
    (μ : WassersteinSpace 2 E) :
    IsCCRegular ((μ : ProbabilityMeasure E) : Measure E) ↔
      ∀ (ν : WassersteinSpace 2 E) (π : Measure (E × E)),
        IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
          ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
        ∃ T : E → E, π = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan μ.hasFiniteMoment.memLp_id]
  refine ⟨fun h ν π hπ => h ((ν : ProbabilityMeasure E) : Measure E)
    ν.hasFiniteMoment.memLp_id π hπ, fun h ν _ hν2 π hπ => ?_⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hν_mom : HasFiniteMoment 2 (νP : Measure E) := hasFiniteMoment_def.2
    ⟨0, (memLp_congr_eNorm aestronglyMeasurable_id measurable_edist_right.aestronglyMeasurable
      (.of_forall fun x => by simp [eDist_eq_eNorm_sub])).1 hν2⟩
  have hmk := h (WassersteinSpace.mk νP hν_mom) π
  simp only [WassersteinSpace.coe_mk] at hmk
  exact hmk hπ

/-- **Ambrosio–Gigli Theorem 1.26 on `WassersteinSpace 2 E` (existence and uniqueness form).** A
quadratic Wasserstein law `μ : WassersteinSpace 2 E` has `c - c`-regular underlying measure if and
only if for every target `ν : WassersteinSpace 2 E`, there exists an optimal transport map `T` whose
graph plan is the unique optimal quadratic coupling between `μ` and `ν`. -/
theorem WassersteinSpace.isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique
    (μ : WassersteinSpace 2 E) :
    IsCCRegular ((μ : ProbabilityMeasure E) : Measure E) ↔
      ∀ ν : WassersteinSpace 2 E,
        ∃ T : E → E,
          IsKantorovichOptimalTransportMap
            (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
            ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) T ∧
          ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
            ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) ↔
            π = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique
    μ.hasFiniteMoment.memLp_id]
  refine ⟨fun h ν => h ((ν : ProbabilityMeasure E) : Measure E) ν.hasFiniteMoment.memLp_id,
    fun h ν _ hν2 => ?_⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hν_mom : HasFiniteMoment 2 (νP : Measure E) := hasFiniteMoment_def.2
    ⟨0, (memLp_congr_eNorm aestronglyMeasurable_id measurable_edist_right.aestronglyMeasurable
      (.of_forall fun x => by simp [eDist_eq_eNorm_sub])).1 hν2⟩
  have hmk := h (WassersteinSpace.mk νP hν_mom)
  simp only [WassersteinSpace.coe_mk] at hmk
  exact hmk

end SharpCharacterization

end TauCeti
