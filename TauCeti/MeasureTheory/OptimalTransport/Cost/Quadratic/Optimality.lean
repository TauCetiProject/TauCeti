/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Quadratic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Duality.Basic

/-!
# Quadratic optimality criteria for cyclically monotone plans

Between finite measures on a real inner product space, every optimal quadratic plan of finite cost
for `‖x - y‖ ^ 2 / 2` has support — and on separable spaces almost every pair — contained in the
subdifferential graph of a proper lower semicontinuous convex function `u : E → EReal`
(`TauCeti.IsOptimalCoupling.exists_support_subset_subdifferential`,
`TauCeti.IsOptimalCoupling.exists_ae_mem_subdifferential`).

Conversely, between finite measures with finite second moments on a real inner product space, every
coupling concentrated on a `c`-cyclically monotone set for the quadratic cost `‖x - y‖ ^ 2 / 2` —
and in particular every coupling concentrated on the subdifferential graph of any function
`u : E → EReal` — is an optimal quadratic transport plan.

Expanding the square writes the quadratic cost of a coupling as a fixed second-moment term minus its
correlation `∫ ⟪x, y⟫`. By Rockafellar's theorem, a cyclically monotone set lies in the
subdifferential graph of a Legendre–Fenchel conjugate `u`, where the Fenchel–Young inequality
`⟪x, y⟫ ≤ u x + u⋆ y` is an equality. The real representatives of `u` and `u⋆` are integrable,
being squeezed between affine functions and the correlation, so integrating Fenchel–Young against
any other coupling bounds its correlation by that of the given plan.

## Main statements

* `TauCeti.IsOptimalCoupling.exists_support_subset_subdifferential` — on any real inner product
  space, for a finite source `μ`, the support of an optimal quadratic plan of finite cost lies in
  the subdifferential graph of a proper lower semicontinuous convex function;
* `TauCeti.IsOptimalCoupling.exists_ae_mem_subdifferential` — on a separable real inner product
  space, an optimal quadratic plan of finite cost concentrates almost everywhere on the
  subdifferential graph of a proper lower semicontinuous convex function;
* `TauCeti.IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two` — a coupling
  of finite measures with finite second moments concentrated on a `c`-cyclically monotone set for
  `‖x - y‖ ^ 2 / 2` is optimal;
* `TauCeti.IsCoupling.isOptimalCoupling_of_ae_mem_subdifferential` — a coupling of finite measures
  with finite second moments concentrated on the subdifferential graph of any function is optimal.

## References

* M. Knott and C. S. Smith, *On the optimal mapping of distributions*, J. Optim. Theory Appl. 43
  (1984), 39–49.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ ν : Measure E} {π σ : Measure (E × E)}

/-- **The support of an optimal quadratic plan lies in a subdifferential graph.** On a real inner
product space, if `π` is an optimal plan of finite cost for `‖x - y‖ ^ 2 / 2` between finite
measures, there is a proper (never `⊥`, and finite somewhere) convex, lower semicontinuous
`u : E → EReal` such that every `(x, y)` in the support of `π` has `y ∈ ∂u(x)`. -/
theorem IsOptimalCoupling.exists_support_subset_subdifferential
    [OpensMeasurableSpace (E × E)] [IsFiniteMeasure μ]
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧ (∃ x, u x ≠ ⊤) ∧
        π.support ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1} := by
  -- The function is a Legendre–Fenchel conjugate `g⋆`; it is proper because some point of the
  -- support carries a subgradient, or, for an empty support, because `g = 0` is finite and has
  -- `g⋆ 0 = 0`.
  obtain ⟨g, hsub, hbot, htop⟩ : ∃ g : E → EReal,
      π.support ⊆ {p | p.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) g) p.1} ∧
        (∀ x, fenchelConjugate (innerₗ E) g x ≠ ⊥) ∧ ∃ x, fenchelConjugate (innerₗ E) g x ≠ ⊤ := by
    rcases π.support.eq_empty_or_nonempty with hπ | ⟨z, hz⟩
    · refine ⟨fun _ => 0, by simp [hπ],
        fenchelConjugate_ne_bot (innerₗ E) (x := 0) EReal.zero_ne_top, 0, ?_⟩
      exact ((fenchelConjugate_le (innerₗ E) fun x => by simp).trans_lt EReal.zero_lt_top).ne
    · have hcm : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) π.support :=
        (isCyclicallyMonotone_ofReal_iff fun _ => by positivity).1
          (h.isCyclicallyMonotone_support continuous_ofReal_norm_sub_sq_div_two hfin)
      obtain ⟨g, hg⟩ := hcm.exists_fenchelConjugate_innerₗ_subset_subdifferential
      exact ⟨g, hg, apply_ne_bot_of_mem_subdifferential (innerₗ E) (hg hz), z.1,
        ne_top_of_mem_subdifferential (innerₗ E) (hg hz)⟩
  exact ⟨_, convex_epigraph_fenchelConjugate (innerₗ E) g,
    lowerSemicontinuous_fenchelConjugate_innerₗ g, hbot, htop, hsub⟩

/-- **An optimal quadratic plan concentrates on a subdifferential graph.** On a separable real
inner product space, if `π` is an optimal plan of finite cost for `‖x - y‖ ^ 2 / 2` between finite
measures, there is a proper convex, lower semicontinuous `u : E → EReal` such that `y ∈ ∂u(x)`
for `π`-almost every `(x, y)`. -/
theorem IsOptimalCoupling.exists_ae_mem_subdifferential
    [OpensMeasurableSpace (E × E)] [SecondCountableTopology E] [IsFiniteMeasure μ]
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧ (∃ x, u x ≠ ⊤) ∧ ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
  obtain ⟨u, hconv, hlsc, hbot, htop, hsub⟩ := h.exists_support_subset_subdifferential hfin
  refine ⟨u, hconv, hlsc, hbot, htop, ?_⟩
  filter_upwards [π.support_mem_ae] with z hz using hsub hz

/-- For a coupling `π` of finite measures with finite second moments concentrated on the
subdifferential graph of `u`, the real representatives of `u` and of its conjugate `v` are
integrable for the marginals: on the support of `π` each is squeezed between an affine function and
the correlation minus an affine function. -/
private theorem IsCoupling.integrable_toReal_of_ae_mem_subdifferential [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν)
    {u : E → EReal} (hu : Measurable u) (hv : Measurable (fenchelConjugate (innerₗ E) u))
    (hgraph : ∀ᵐ z ∂π, u z.1 ≠ ⊤ ∧ fenchelConjugate (innerₗ E) u z.2 ≠ ⊤ ∧
      (u z.1).toReal + (fenchelConjugate (innerₗ E) u z.2).toReal = ⟪z.1, z.2⟫)
    {x₀ y₀ : E} (h₀ : y₀ ∈ subdifferential (innerₗ E) u x₀) :
    Integrable (fun x => (u x).toReal) μ ∧
      Integrable (fun y => (fenchelConjugate (innerₗ E) u y).toReal) ν := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  have hx₀ := ne_top_of_mem_subdifferential (innerₗ E) h₀
  have hy₀ := fenchelConjugate_ne_top_of_mem_subdifferential (innerₗ E) h₀
  have hμ1 : Integrable (fun z : E × E => z.1) π :=
    hπ.integrable_comp_fst (hμ.integrable one_le_two)
  have hν1 : Integrable (fun z : E × E => z.2) π :=
    hπ.integrable_comp_snd (hν.integrable one_le_two)
  refine ⟨?_, ?_⟩
  · refine (hπ.measurePreserving_fst.integrable_comp hu.ereal_toReal.aestronglyMeasurable).1 <|
      integrable_of_le_of_le (f := fun z => (u z.1).toReal)
        (hu.ereal_toReal.comp measurable_fst).aestronglyMeasurable
        (g₁ := fun z : E × E => ⟪z.1, y₀⟫ - (fenchelConjugate (innerₗ E) u y₀).toReal)
        (g₂ := fun z : E × E => ⟪z.1, z.2⟫ - (⟪x₀, z.2⟫ - (u x₀).toReal)) ?_ ?_
        ((hμ1.inner_const y₀).sub (integrable_const _))
        ((hπ.integrable_inner hμ hν).sub ((hν1.const_inner x₀).sub (integrable_const _)))
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate (innerₗ E) hz.1 hy₀,
        innerₗ_apply_apply z.1 y₀]
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate (innerₗ E) hx₀ hz.2.1,
        innerₗ_apply_apply x₀ z.2, hz.2.2]
  · refine (hπ.measurePreserving_snd.integrable_comp hv.ereal_toReal.aestronglyMeasurable).1 <|
      integrable_of_le_of_le (f := fun z => (fenchelConjugate (innerₗ E) u z.2).toReal)
        (hv.ereal_toReal.comp measurable_snd).aestronglyMeasurable
        (g₁ := fun z : E × E => ⟪x₀, z.2⟫ - (u x₀).toReal)
        (g₂ := fun z : E × E =>
          ⟪z.1, z.2⟫ - (⟪z.1, y₀⟫ - (fenchelConjugate (innerₗ E) u y₀).toReal)) ?_ ?_
        ((hν1.const_inner x₀).sub (integrable_const _))
        ((hπ.integrable_inner hμ hν).sub ((hμ1.inner_const y₀).sub (integrable_const _)))
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate (innerₗ E) hx₀ hz.2.1,
        innerₗ_apply_apply x₀ z.2]
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate (innerₗ E) hz.1 hy₀,
        innerₗ_apply_apply z.1 y₀, hz.2.2]

/-- A plan concentrated on the subdifferential graph of a function `u`, such that `u` and its
Legendre–Fenchel conjugate are measurable, has the largest correlation among the couplings of its
marginals, provided these have finite second moments. -/
private theorem IsCoupling.integral_inner_le_of_ae_mem_subdifferential [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hσ : IsCoupling σ μ ν) (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν)
    {u : E → EReal} (hu : Measurable u) (hv : Measurable (fenchelConjugate (innerₗ E) u))
    (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    ∫ z, ⟪z.1, z.2⟫ ∂σ ≤ ∫ z, ⟪z.1, z.2⟫ ∂π := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  rcases eq_or_ne π 0 with rfl | hπ0
  · have hσ0 : σ = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← hσ.measure_univ_left, hπ.measure_univ_left,
        FunLike.coe_zero, Pi.zero_apply]
    simp [hσ0]
  have := ae_neBot.2 hπ0
  obtain ⟨⟨x₀, y₀⟩, h₀⟩ := h.exists
  have hgraph : ∀ᵐ z ∂π, u z.1 ≠ ⊤ ∧ fenchelConjugate (innerₗ E) u z.2 ≠ ⊤ ∧
      (u z.1).toReal + (fenchelConjugate (innerₗ E) u z.2).toReal = ⟪z.1, z.2⟫ :=
    h.mono fun z hz =>
    ⟨ne_top_of_mem_subdifferential (innerₗ E) hz,
      fenchelConjugate_ne_top_of_mem_subdifferential (innerₗ E) hz,
      by simpa only [innerₗ_apply_apply] using
        toReal_add_toReal_fenchelConjugate_eq_of_mem_subdifferential (innerₗ E) hz⟩
  obtain ⟨hφ, hψ⟩ := hπ.integrable_toReal_of_ae_mem_subdifferential hμ hν hu hv hgraph h₀
  -- Both potentials are finite almost everywhere for the marginals, hence along `σ`.
  have hμfin : ∀ᵐ x ∂μ, u x ≠ ⊤ := by
    rw [← hπ.measurePreserving_fst.map_eq, ae_map_iff (p := fun x => u x ≠ ⊤)
      measurable_fst.aemeasurable (hu (measurableSet_singleton ⊤).compl)]
    exact hgraph.mono fun z hz => hz.1
  have hνfin : ∀ᵐ y ∂ν, fenchelConjugate (innerₗ E) u y ≠ ⊤ := by
    rw [← hπ.measurePreserving_snd.map_eq,
      ae_map_iff (p := fun y => fenchelConjugate (innerₗ E) u y ≠ ⊤)
      measurable_snd.aemeasurable (hv (measurableSet_singleton ⊤).compl)]
    exact hgraph.mono fun z hz => hz.2.1
  have hσfin : ∀ᵐ z ∂σ,
      ⟪z.1, z.2⟫ ≤ (u z.1).toReal + (fenchelConjugate (innerₗ E) u z.2).toReal := by
    filter_upwards [hσ.measurePreserving_fst.quasiMeasurePreserving.ae hμfin,
      hσ.measurePreserving_snd.quasiMeasurePreserving.ae hνfin] with z hx hy
    simpa only [innerₗ_apply_apply] using
      le_toReal_add_toReal_fenchelConjugate (innerₗ E) hx hy
  calc ∫ z, ⟪z.1, z.2⟫ ∂σ
      ≤ ∫ z, ((u z.1).toReal + (fenchelConjugate (innerₗ E) u z.2).toReal) ∂σ :=
        integral_mono_ae (hσ.integrable_inner hμ hν)
          ((hσ.integrable_comp_fst hφ).add (hσ.integrable_comp_snd hψ)) hσfin
    _ = ∫ z, ((u z.1).toReal + (fenchelConjugate (innerₗ E) u z.2).toReal) ∂π := by
        rw [← kantorovichDualValue_eq_integral hσ hφ hψ, kantorovichDualValue_eq_integral hπ hφ hψ]
    _ = ∫ z, ⟪z.1, z.2⟫ ∂π := integral_congr_ae (hgraph.mono fun z hz => hz.2.2)

/-- **Plans on cyclically monotone sets are optimal for the quadratic cost.** Let `μ` and `ν`
be finite measures with finite second moments on a real inner product space. A coupling `π` of
`μ` and `ν` concentrated on a `c`-cyclically monotone set for the cost `‖x - y‖ ^ 2 / 2` is an
optimal plan for that cost. -/
theorem IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two
    [OpensMeasurableSpace E] [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν)
    {S : Set (E × E)} (hS : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S)
    (h : ∀ᵐ z ∂π, z ∈ S) :
    IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν := by
  -- By Rockafellar's theorem `S` lies in the subdifferential graph of a conjugate `u = g⋆`; both
  -- `u` and `u⋆` are lower semicontinuous, hence measurable.
  obtain ⟨g, hg⟩ := hS.exists_fenchelConjugate_innerₗ_subset_subdifferential
  have hu := (lowerSemicontinuous_fenchelConjugate_innerₗ g).measurable
  have hv :=
    (lowerSemicontinuous_fenchelConjugate_innerₗ (fenchelConjugate (innerₗ E) g)).measurable
  refine isOptimalCoupling_iff.2 ⟨hπ, fun σ hσ => ?_⟩
  rw [hπ.lintegral_norm_sub_sq_div_two hμ hν, hσ.lintegral_norm_sub_sq_div_two hμ hν]
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left
    (hπ.integral_inner_le_of_ae_mem_subdifferential hσ hμ hν hu hv (h.mono fun _ hz => hg hz)) _)

/-- **Plans on subdifferential graphs are optimal for the quadratic cost.** Let `μ` and `ν` be
finite measures with finite second moments on a real inner product space, and `u : E → EReal`
any function. A coupling `π` of `μ` and `ν` such that `y ∈ ∂u(x)` for `π`-almost every
`(x, y)` is an optimal plan for the cost `‖x - y‖ ^ 2 / 2`. -/
theorem IsCoupling.isOptimalCoupling_of_ae_mem_subdifferential
    [OpensMeasurableSpace E] [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν)
    {u : E → EReal} (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν :=
  hπ.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two hμ hν
    (isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential u) h

end InnerProduct

end TauCeti
