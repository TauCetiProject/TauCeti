/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Stability
import TauCeti.MeasureTheory.MeasurableSpace.Analytic
import TauCeti.MeasureTheory.OptimalTransport.Duality.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Duality.SchachermayerTeichmann

/-!
# Restriction and reparameterization of generalized geodesics

Let `γ` be a three-plan on `E × E × E`, the joint law of a triple `(x, y₀, y₁)`, and let
`ν_t` be its generalized geodesic, the law of `(1 - t) • y₀ + t • y₁`. For times `a` and `b`, the
piece of `ν_t` between `a` and `b`, run over `[0, 1]`, is again the generalized geodesic of a
three-plan: the law `TauCeti.lineMapPlan γ a b` of `(x, y_a, y_b)`, where
`y_s = (1 - s) • y₀ + s • y₁` (`TauCeti.generalizedGeodesic_lineMapPlan`). Its endpoint coupling
has quadratic cost `(b - a) ^ 2` times that of `γ`. For `a = 1` and `b = 0` this runs the
generalized geodesic backwards.

The substance is that restriction preserves the defining optimality. In a separable Hilbert
space, if `γ` is a quadratic generalized-geodesic plan from `ν₀` to `ν₁` based at `μ`, at finite
`W₂` distances, then for every `s ∈ [0, 1]` the coupling `(x, y_s)` of `μ` and `ν_s` carried by
`γ` is optimal (`TauCeti.IsGeneralizedGeodesicPlan.isOptimalCoupling_map`). Optimality of
`(x, y₀)` and `(x, y₁)` concentrates them on cyclically monotone sets, by the
Schachermayer–Teichmann theorem. For the quadratic cost, cyclical monotonicity is linear in
the target, so the coupling `(x, y_s)` is concentrated on the cyclically monotone set of
interpolated pairs, hence optimal. That set is a continuous image of a Borel set, so only
analytic; Lusin's theorem makes it measurable for the completed law. Consequently
`TauCeti.lineMapPlan γ a b` is a generalized-geodesic plan from `ν_a` to `ν_b` based at `μ` for
all `a, b ∈ [0, 1]` (`TauCeti.IsGeneralizedGeodesicPlan.lineMapPlan`).

For energies, this gives the restriction lemma for convexity along every generalized geodesic:
an energy that is `m`-convex along every quadratic generalized-geodesic plan based at `μ` is
`m`-convex along each piece of such a plan, reparametrised over `[0, 1]`, with the quadratic
cost of the piece in the remainder
(`TauCeti.ConvexAlongGeneralizedGeodesics.convexAlongGeneralizedGeodesicPlan_lineMapPlan`).
Convexity along a single fixed plan is preserved by reversal
(`TauCeti.ConvexAlongGeneralizedGeodesicPlan.lineMapPlan_one_zero`). It is not inherited by
restrictions in general, since its inequality only compares with the two endpoints; this is why
the restriction lemma is stated for convexity along every plan.

## Main definitions

* `TauCeti.lineMapPlan γ a b`: the law under `γ` of `(x, y_a, y_b)`.

## Main statements

* `TauCeti.lineMapPlan_lineMapPlan`: a piece of a piece of a generalized geodesic is a piece.
* `TauCeti.generalizedGeodesic_lineMapPlan`: the generalized geodesic of `lineMapPlan γ a b` is
  that of `γ` reparametrised by `t ↦ (1 - t) a + t b`.
* `TauCeti.integral_norm_sub_sq_snd_lineMapPlan`: the endpoint coupling of `lineMapPlan γ a b`
  has quadratic cost `(b - a) ^ 2` times that of `γ`.
* `TauCeti.IsGeneralizedGeodesicPlan.lineMapPlan_one_zero`: reversing a generalized-geodesic plan
  for any exponent.
* `TauCeti.IsGeneralizedGeodesicPlan.isOptimalCoupling_map`: in a separable Hilbert space, the
  base point is optimally coupled with every point of a quadratic generalized geodesic.
* `TauCeti.IsGeneralizedGeodesicPlan.lineMapPlan`: the restriction of a quadratic
  generalized-geodesic plan is a generalized-geodesic plan.
* `TauCeti.ConvexAlongGeneralizedGeodesicPlan.lineMapPlan_one_zero` and
  `TauCeti.ConvexAlongGeneralizedGeodesics.convexAlongGeneralizedGeodesicPlan_lineMapPlan`:
  reversal and restriction of convexity along generalized geodesics.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.2, Definition 9.2.2.
* W. Schachermayer and J. Teichmann, *Characterization of optimal transport plans for the
  Monge--Kantorovich problem*, Proc. Amer. Math. Soc. 137 (2009), 519--529.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section Interpolation

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] {γ : Measure (E × E × E)}

/-- The three-plan of the piece of a generalized geodesic between the times `a` and `b`: the law
under `γ` of `(x, (1 - a) • y₀ + a • y₁, (1 - b) • y₀ + b • y₁)`. Its generalized geodesic is the
generalized geodesic of `γ` reparametrised by `t ↦ (1 - t) a + t b`. -/
def lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) : Measure (E × E × E) :=
  γ.map fun w ↦ (w.1, (1 - a) • w.2.1 + a • w.2.2, (1 - b) • w.2.1 + b • w.2.2)

/-- `lineMapPlan γ a b` is the pushforward of `γ` along
`(x, y₀, y₁) ↦ (x, (1 - a) • y₀ + a • y₁, (1 - b) • y₀ + b • y₁)`. -/
theorem lineMapPlan_def (γ : Measure (E × E × E)) (a b : ℝ) :
    lineMapPlan γ a b =
      γ.map fun w ↦ (w.1, (1 - a) • w.2.1 + a • w.2.2, (1 - b) • w.2.1 + b • w.2.2) := by
  rw [lineMapPlan]

/-- The piece of a generalized geodesic between the times `0` and `1` is the whole of it. -/
@[simp]
theorem lineMapPlan_zero_one (γ : Measure (E × E × E)) : lineMapPlan γ 0 1 = γ := by
  simp [lineMapPlan_def]

/-- The pieces of a probability three-plan are probability three-plans. -/
instance isProbabilityMeasure_lineMapPlan (γ : Measure (E × E × E)) [IsProbabilityMeasure γ]
    (a b : ℝ) : IsProbabilityMeasure (lineMapPlan γ a b) := by
  rw [lineMapPlan_def]
  infer_instance

variable [MeasurableAdd₂ E] [MeasurableSMul ℝ E]

/-- **A piece of a piece is a piece.** The piece between the times `c` and `d` of the piece of `γ`
between `a` and `b` is the piece of `γ` between `AffineMap.lineMap a b c` and
`AffineMap.lineMap a b d`. -/
theorem lineMapPlan_lineMapPlan (γ : Measure (E × E × E)) (a b c d : ℝ) :
    lineMapPlan (lineMapPlan γ a b) c d =
      lineMapPlan γ (AffineMap.lineMap a b c) (AffineMap.lineMap a b d) := by
  rw [lineMapPlan_def, lineMapPlan_def, lineMapPlan_def,
    Measure.map_map (by fun_prop) (by fun_prop), AffineMap.lineMap_apply_ring,
    AffineMap.lineMap_apply_ring]
  congr 1
  funext w
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  constructor <;> module

/-- The projection of `lineMapPlan γ a b` to its first two coordinates is the law of
`(x, (1 - a) • y₀ + a • y₁)`. -/
theorem map_prodMap_fst_lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) :
    (lineMapPlan γ a b).map (Prod.map id Prod.fst) =
      γ.map fun w ↦ (w.1, (1 - a) • w.2.1 + a • w.2.2) := by
  rw [lineMapPlan_def, Measure.map_map (measurable_id.prodMap measurable_fst) (by fun_prop)]
  rfl

/-- The projection of `lineMapPlan γ a b` to its first and last coordinates is the law of
`(x, (1 - b) • y₀ + b • y₁)`. -/
theorem map_prodMap_snd_lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) :
    (lineMapPlan γ a b).map (Prod.map id Prod.snd) =
      γ.map fun w ↦ (w.1, (1 - b) • w.2.1 + b • w.2.2) := by
  rw [lineMapPlan_def, Measure.map_map (measurable_id.prodMap measurable_snd) (by fun_prop)]
  rfl

/-- The base marginal of `lineMapPlan γ a b` is that of `γ`. -/
@[simp]
theorem fst_lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) : (lineMapPlan γ a b).fst = γ.fst := by
  rw [lineMapPlan_def, Measure.fst, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
  rfl

/-- **Reparameterization of a generalized geodesic.** The generalized geodesic of
`lineMapPlan γ a b` at time `t` is that of `γ` at time `AffineMap.lineMap a b t`,
that is `(1 - t) a + t b`. -/
@[simp]
theorem generalizedGeodesic_lineMapPlan (γ : Measure (E × E × E)) (a b t : ℝ) :
    generalizedGeodesic (lineMapPlan γ a b) t =
      generalizedGeodesic γ (AffineMap.lineMap a b t) := by
  rw [generalizedGeodesic_def, generalizedGeodesic_def, lineMapPlan_def,
    Measure.map_map (by fun_prop) (by fun_prop), AffineMap.lineMap_apply_ring]
  congr 1
  funext w
  simp only [Function.comp_apply]
  module

/-- The middle marginal of `lineMapPlan γ a b` is the generalized geodesic of `γ` at time `a`. -/
@[simp]
theorem snd_fst_lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) :
    (lineMapPlan γ a b).snd.fst = generalizedGeodesic γ a := by
  rw [← generalizedGeodesic_zero, generalizedGeodesic_lineMapPlan, AffineMap.lineMap_apply_zero]

/-- The last marginal of `lineMapPlan γ a b` is the generalized geodesic of `γ` at time `b`. -/
@[simp]
theorem snd_snd_lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) :
    (lineMapPlan γ a b).snd.snd = generalizedGeodesic γ b := by
  rw [← generalizedGeodesic_one, generalizedGeodesic_lineMapPlan, AffineMap.lineMap_apply_one]

variable [EDist E] {p : ℝ≥0∞} {μ ν₀ ν₁ : Measure E}

/-- **Reversal of a generalized-geodesic plan.** Exchanging the two endpoints of a
generalized-geodesic plan from `ν₀` to `ν₁` based at `μ` gives one from `ν₁` to `ν₀`, for every
exponent. -/
theorem IsGeneralizedGeodesicPlan.lineMapPlan_one_zero
    (hγ : IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁) :
    IsGeneralizedGeodesicPlan p (lineMapPlan γ 1 0) μ ν₁ ν₀ := by
  have h₀ : (lineMapPlan γ 1 0).map (Prod.map id Prod.fst) = γ.map (Prod.map id Prod.snd) := by
    rw [map_prodMap_fst_lineMapPlan]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    rfl
  have h₁ : (lineMapPlan γ 1 0).map (Prod.map id Prod.snd) = γ.map (Prod.map id Prod.fst) := by
    rw [map_prodMap_snd_lineMapPlan]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    rfl
  exact ⟨h₀ ▸ hγ.isCoupling_right, h₀ ▸ hγ.eLpNorm_right, h₁ ▸ hγ.isCoupling_left,
    h₁ ▸ hγ.eLpNorm_left⟩

end Interpolation

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The endpoint coupling of `lineMapPlan γ a b` has quadratic cost `(b - a) ^ 2` times the
quadratic cost of the endpoint coupling of `γ`, since `y_a - y_b = (b - a) • (y₀ - y₁)`. -/
theorem integral_norm_sub_sq_snd_lineMapPlan (γ : Measure (E × E × E)) (a b : ℝ) :
    ∫ z, ‖z.1 - z.2‖ ^ 2 ∂(lineMapPlan γ a b).snd =
      (b - a) ^ 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd := by
  have hc : Continuous fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 := by fun_prop
  rw [lineMapPlan_def, Measure.snd, Measure.snd, Measure.map_map measurable_snd (by fun_prop),
    integral_map (by fun_prop) hc.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hc.aestronglyMeasurable, ← integral_const_mul]
  congr 1
  funext w
  have : (1 - a) • w.2.1 + a • w.2.2 - ((1 - b) • w.2.1 + b • w.2.2) =
      (b - a) • (w.2.1 - w.2.2) := by
    module
  simp only [Function.comp_apply, this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

variable {m : ℝ} {φ : WassersteinSpace 2 E → EReal} {ν₀ ν₁ : WassersteinSpace 2 E}
  {γ : Measure (E × E × E)}

/-- **Reversal of convexity along a three-plan.** If `φ` is `m`-convex along the three-plan `γ`
from `ν₀` to `ν₁`, then it is `m`-convex along the reversed plan `lineMapPlan γ 1 0` from `ν₁` to
`ν₀`. -/
theorem ConvexAlongGeneralizedGeodesicPlan.lineMapPlan_one_zero
    (h : ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ) :
    ConvexAlongGeneralizedGeodesicPlan m φ ν₁ ν₀ (lineMapPlan γ 1 0) := by
  rw [convexAlongGeneralizedGeodesicPlan_def] at h ⊢
  intro t ht ν hν
  rw [generalizedGeodesic_lineMapPlan, AffineMap.lineMap_apply_ring, mul_one, mul_zero,
    add_zero] at hν
  have h' := h (1 - t) ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩ ν hν
  rw [sub_sub_cancel] at h'
  rw [integral_norm_sub_sq_snd_lineMapPlan, zero_sub, neg_one_sq, one_mul,
    add_comm (((1 - t : ℝ) : EReal) * φ ν₁)]
  convert h' using 4
  ring

end NormedSpace

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] in
/-- A coupling realizing `W₂ (μ, ν) < ∞` is concentrated on a measurable set that is cyclically
monotone for the quadratic cost. -/
private theorem exists_isCyclicallyMonotone_of_eLpNorm_eq {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {π : Measure (E × E)}
    (hπ : IsCoupling π μ ν)
    (hopt : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 π = wassersteinEDist 2 μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ S : Set (E × E), MeasurableSet S ∧
      IsCyclicallyMonotone (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 / 2) S ∧ π Sᶜ = 0 := by
  have h2 := (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top).2 ⟨hπ, hopt⟩
  rw [ENNReal.toReal_ofNat] at h2
  have hq := isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two h2
  -- The half-squared cost is dominated by the squared distance, whose integral is `W₂ ^ 2`.
  have hcost : transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
    rw [← hq.lintegral_eq]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun z ↦
      (le_mul_of_one_le_left zero_le one_le_two).trans_eq
        (edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two z).symm)
    have h2' := h2.lintegral_edist_rpow_eq measurable_edist two_ne_zero ENNReal.ofNat_ne_top
    rw [ENNReal.toReal_ofNat] at h2'
    rw [h2']
    exact ENNReal.rpow_ne_top_of_nonneg zero_le_two hfin
  obtain ⟨S, hS, hcm, hπS⟩ :=
    hq.exists_isCyclicallyMonotone_of_lowerSemicontinuous
      continuous_ofReal_norm_sub_sq_div_two.lowerSemicontinuous hcost
  exact ⟨S, hS, (isCyclicallyMonotone_ofReal_iff fun _ ↦ by positivity).1 hcm, hπS⟩

variable {γ : Measure (E × E × E)} {μ ν₀ ν₁ : Measure E} {s a b : ℝ}

/-- **The base point is optimally coupled with every point of a generalized geodesic.** In a
separable Hilbert space, let `γ` be a quadratic generalized-geodesic plan from `ν₀` to `ν₁` based
at a probability measure `μ`, with `W₂ (μ, ν₀)` and `W₂ (μ, ν₁)` finite. For `s ∈ [0, 1]`, the law
of `(x, (1 - s) • y₀ + s • y₁)` under `γ` is an optimal coupling of `μ` and the generalized
geodesic at time `s` for the squared distance. -/
theorem IsGeneralizedGeodesicPlan.isOptimalCoupling_map [IsProbabilityMeasure μ]
    (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁) (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞)
    (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hs : s ∈ Icc (0 : ℝ) 1) :
    IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ))
      (γ.map fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2)) μ (generalizedGeodesic γ s) := by
  have : IsProbabilityMeasure γ := ⟨by rw [← Measure.fst_univ, hγ.fst_eq, measure_univ]⟩
  have : IsProbabilityMeasure ν₀ := hγ.isCoupling_snd.fst_eq ▸ inferInstance
  have : IsProbabilityMeasure ν₁ := hγ.isCoupling_snd.snd_eq ▸ inferInstance
  obtain ⟨S₀, hS₀, hcm₀, hπ₀⟩ :=
    exists_isCyclicallyMonotone_of_eLpNorm_eq hγ.isCoupling_left hγ.eLpNorm_left h₀
  obtain ⟨S₁, hS₁, hcm₁, hπ₁⟩ :=
    exists_isCyclicallyMonotone_of_eLpNorm_eq hγ.isCoupling_right hγ.eLpNorm_right h₁
  set F : E × E × E → E × E := fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2) with hF
  have hFc : Continuous F := by fun_prop
  -- The plan `γ` is concentrated on the triples whose two projections lie in `S₀` and `S₁`.
  set T : Set (E × E × E) := {w | (w.1, w.2.1) ∈ S₀ ∧ (w.1, w.2.2) ∈ S₁}
  have hT : MeasurableSet T :=
    (measurable_id.prodMap measurable_fst hS₀).inter (measurable_id.prodMap measurable_snd hS₁)
  have hγT : ∀ᵐ w ∂γ, w ∈ T :=
    ((ae_map_iff (by fun_prop) hS₀).1 (ae_iff.2 hπ₀)).and
      ((ae_map_iff (by fun_prop) hS₁).1 (ae_iff.2 hπ₁))
  -- Its image under `F` is cyclically monotone and analytic, hence null-measurable, and it
  -- carries the coupling `F₊ γ`.
  have hcm := isCyclicallyMonotone_norm_sub_sq_div_two_image_smul_add_smul hcm₀ hcm₁ hs
  have hnull : NullMeasurableSet (F '' T)ᶜ (γ.map F) :=
    (MeasureTheory.AnalyticSet.nullMeasurableSet
      (hT.analyticSet.image_of_continuous hFc) _).compl
  have hae : ∀ᵐ z ∂γ.map F, z ∈ F '' T := by
    rw [ae_iff, ← compl_def, Measure.map_apply₀ hFc.aemeasurable hnull]
    refine measure_mono_null ?_ (ae_iff.1 hγT)
    intro w hw hwT
    exact hw ⟨w, hwT, rfl⟩
  have hπ : IsCoupling (γ.map F) μ (generalizedGeodesic γ s) := by
    constructor
    · rw [← hγ.fst_eq, Measure.fst, Measure.fst, Measure.map_map measurable_fst hFc.measurable]
      rfl
    · rw [Measure.snd, Measure.map_map measurable_snd hFc.measurable, generalizedGeodesic_def]
      rfl
  exact isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two <|
    hπ.isOptimalCoupling_of_isCyclicallyMonotone
      continuous_ofReal_norm_sub_sq_div_two.measurable (fun _ ↦ ENNReal.ofReal_ne_top)
      ((isCyclicallyMonotone_ofReal_iff fun _ ↦ by positivity).2 hcm) hae

/-- **Restriction of a generalized-geodesic plan.** In a separable Hilbert space, let `γ` be a
quadratic generalized-geodesic plan from `ν₀` to `ν₁` based at a probability measure `μ`, with
`W₂ (μ, ν₀)` and `W₂ (μ, ν₁)` finite. For `a, b ∈ [0, 1]`, `lineMapPlan γ a b` is a quadratic
generalized-geodesic plan from the generalized geodesic at time `a` to the one at time `b`, based
at `μ`. -/
theorem IsGeneralizedGeodesicPlan.lineMapPlan [IsProbabilityMeasure μ]
    (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁) (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞)
    (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IsGeneralizedGeodesicPlan 2 (TauCeti.lineMapPlan γ a b) μ (generalizedGeodesic γ a)
      (generalizedGeodesic γ b) := by
  have hopt (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := by
    have h := hγ.isOptimalCoupling_map h₀ h₁ hs
    rw [← ENNReal.toReal_ofNat 2] at h
    exact (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top).1 h
  obtain ⟨ha₁, ha₂⟩ := hopt a ha
  obtain ⟨hb₁, hb₂⟩ := hopt b hb
  rw [← map_prodMap_fst_lineMapPlan γ a b] at ha₁ ha₂
  rw [← map_prodMap_snd_lineMapPlan γ a b] at hb₁ hb₂
  exact ⟨ha₁, ha₂, hb₁, hb₂⟩

variable {m : ℝ} {φ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E}
  {ν₀ ν₁ νa νb : WassersteinSpace 2 E}

/-- **Restriction of convexity along generalized geodesics.** In a separable Hilbert space, let
`φ` be `m`-convex along every quadratic generalized-geodesic plan based at `μ`, and let `γ` be such
a plan from `ν₀` to `ν₁`, both of energy `≠ ⊤`. For `a, b ∈ [0, 1]`, `φ` is `m`-convex along
`lineMapPlan γ a b`, the piece of `γ` between the times `a` and `b` reparametrised over `[0, 1]`:
along it the remainder is `(m / 2) t (1 - t) (b - a) ^ 2 ∫ ‖y₀ - y₁‖² dγ`
(`TauCeti.integral_norm_sub_sq_snd_lineMapPlan`). -/
theorem ConvexAlongGeneralizedGeodesics.convexAlongGeneralizedGeodesicPlan_lineMapPlan
    (h : ConvexAlongGeneralizedGeodesics m φ μ) (h₀ : φ ν₀ ≠ ⊤) (h₁ : φ ν₁ ≠ ⊤)
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E))
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hνa : ((νa : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ a)
    (hνb : ((νb : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ b) :
    ConvexAlongGeneralizedGeodesicPlan m φ νa νb (lineMapPlan γ a b) := by
  have hfin (ν : WassersteinSpace 2 E) :
      wassersteinEDist 2 ((μ : ProbabilityMeasure E) : Measure E)
        ((ν : ProbabilityMeasure E) : Measure E) ≠ ∞ := by
    rw [← WassersteinSpace.edist_def]
    exact edist_ne_top μ ν
  refine convexAlongGeneralizedGeodesics_def.1 h (h.apply_ne_top h₀ h₁ hγ ha hνa)
    (h.apply_ne_top h₀ h₁ hγ hb hνb) ?_
  rw [hνa, hνb]
  exact hγ.lineMapPlan (hfin ν₀) (hfin ν₁) ha hb

end Hilbert

end TauCeti
