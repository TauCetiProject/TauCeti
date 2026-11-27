/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Quadratic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Duality.FenchelYoung

/-!
# Quadratic optimality criteria for cyclically monotone plans

Between finite measures on a real inner product space `E` whose product `E × E` has measurable
open sets (`[OpensMeasurableSpace (E × E)]`), every optimal quadratic plan of finite cost for
`‖x - y‖ ^ 2 / 2` has support — and on separable spaces almost every pair — contained in the
subdifferential graph of a proper lower semicontinuous convex function `u : E → EReal`
(`TauCeti.IsOptimalCoupling.exists_support_subset_subdifferential`,
`TauCeti.IsOptimalCoupling.exists_ae_mem_subdifferential`).

Conversely, between finite measures with finite second moments on a real inner product space with
measurable open sets (`[OpensMeasurableSpace E]`), every coupling concentrated on a
`c`-cyclically monotone set for the quadratic cost `‖x - y‖ ^ 2 / 2` — and in particular every
coupling concentrated on the subdifferential graph of any function `u : E → EReal` — is an optimal
quadratic transport plan.

Expanding the square writes the quadratic cost of a coupling as a fixed second-moment term minus its
correlation `∫ ⟪x, y⟫`. By Rockafellar's theorem, a cyclically monotone set lies in the
subdifferential graph of a Legendre–Fenchel conjugate `u`, where the Fenchel–Young inequality
`⟪x, y⟫ ≤ u x + u⋆ y` is an equality. Using
`TauCeti.IsCoupling.integral_apply_le_of_ae_mem_subdifferential`, integrating Fenchel–Young against
any other coupling bounds its correlation by that of the given plan.

## Main statements

* `TauCeti.IsOptimalCoupling.exists_support_subset_subdifferential` — on any real inner product
  space with measurable open sets in `E × E`, for a finite source `μ`, the support of an optimal
  quadratic plan of finite cost lies in the subdifferential graph of a proper lower
  semicontinuous convex function;
* `TauCeti.IsOptimalCoupling.exists_ae_mem_subdifferential` — on a separable real inner product
  space with measurable open sets in `E × E`, an optimal quadratic plan of finite cost concentrates
  almost everywhere on the subdifferential graph of a proper lower semicontinuous convex function;
* `TauCeti.IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two` — on a real
  inner product space with measurable open sets, a coupling of finite measures with finite second
  moments concentrated on a `c`-cyclically monotone set for `‖x - y‖ ^ 2 / 2` is optimal;
* `TauCeti.IsCoupling.isOptimalCoupling_of_ae_mem_subdifferential` — on a real inner product
  space with measurable open sets, a coupling of finite measures with finite second moments
  concentrated on the subdifferential graph of any function is optimal.

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
product space with measurable open sets in `E × E`, if `π` is an optimal plan of finite cost for
`‖x - y‖ ^ 2 / 2` between finite measures, there is a proper (never `⊥`, and finite somewhere)
convex, lower semicontinuous `u : E → EReal` such that every `(x, y)` in the support of `π` has
`y ∈ ∂u(x)`. -/
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
inner product space with measurable open sets in `E × E`, if `π` is an optimal plan of finite cost
for `‖x - y‖ ^ 2 / 2` between finite measures, there is a proper convex, lower semicontinuous
`u : E → EReal` such that `y ∈ ∂u(x)` for `π`-almost every `(x, y)`. -/
theorem IsOptimalCoupling.exists_ae_mem_subdifferential
    [OpensMeasurableSpace (E × E)] [SecondCountableTopology E] [IsFiniteMeasure μ]
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧ (∃ x, u x ≠ ⊤) ∧ ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
  obtain ⟨u, hconv, hlsc, hbot, htop, hsub⟩ := h.exists_support_subset_subdifferential hfin
  refine ⟨u, hconv, hlsc, hbot, htop, ?_⟩
  filter_upwards [π.support_mem_ae] with z hz using hsub hz

/-- **Plans on cyclically monotone sets are optimal for the quadratic cost.** Let `μ` and `ν`
be finite measures with finite second moments on a real inner product space with measurable open
sets. A coupling `π` of `μ` and `ν` concentrated on a `c`-cyclically monotone set for the cost
`‖x - y‖ ^ 2 / 2` is an optimal plan for that cost. -/
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
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ Set.univ⟩
  refine isOptimalCoupling_iff.2 ⟨hπ, fun σ hσ => ?_⟩
  rw [hπ.lintegral_norm_sub_sq_div_two hμ hν, hσ.lintegral_norm_sub_sq_div_two hμ hν]
  refine ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ _)
  simpa only [innerₗ_apply_apply] using hπ.integral_apply_le_of_ae_mem_subdifferential hσ hu hv
    (by simpa only [innerₗ_apply_apply] using hπ.integrable_inner hμ hν)
    (by simpa only [innerₗ_apply_apply] using hσ.integrable_inner hμ hν)
    (fun y => by simpa only [innerₗ_apply_apply, id_eq] using
      (hμ.integrable one_le_two).inner_const y)
    (fun x => by simpa only [innerₗ_apply_apply, id_eq] using
      (hν.integrable one_le_two).const_inner x)
    (h.mono fun _ hz => hg hz)

/-- **Plans on subdifferential graphs are optimal for the quadratic cost.** Let `μ` and `ν` be
finite measures with finite second moments on a real inner product space with measurable open sets,
and `u : E → EReal` any function. A coupling `π` of `μ` and `ν` such that `y ∈ ∂u(x)` for
`π`-almost every `(x, y)` is an optimal plan for the cost `‖x - y‖ ^ 2 / 2`. -/
theorem IsCoupling.isOptimalCoupling_of_ae_mem_subdifferential
    [OpensMeasurableSpace E] [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν)
    {u : E → EReal} (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν :=
  hπ.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two hμ hν
    (isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential u) h

end InnerProduct

end TauCeti
