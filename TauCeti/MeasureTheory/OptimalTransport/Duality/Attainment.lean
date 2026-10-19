/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Polish
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Certificate
import TauCeti.MeasureTheory.OptimalTransport.CTransform.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# Dual attainment for bounded continuous costs

For a bounded continuous nonnegative cost `c` on a product of two Polish spaces, the Kantorovich
dual problem is *attained*: there is an integrable pair of potentials `φ`, `ψ` with
`φ x + ψ y ≤ c (x, y)` whose value `∫ φ dμ + ∫ ψ dν` equals the optimal transport cost. No
compactness is assumed, so this is strong duality with dual attainment in the Polish regime.

The results are phrased through optimality certificates (`TauCeti.IsDualCertificate`): a
coupling `π` together with integrable dual feasible potentials `φ`, `ψ` such that `π` is
concentrated on the contact set `{(x, y) | φ x + ψ y = c (x, y)}`. Such a certificate proves at
once that `π` is an optimal plan, that `(φ, ψ)` is an optimal dual pair, and that there is no
duality gap. Here every optimal plan admits a certificate, so the dual optimizer may be chosen
to certify any given optimal plan, not only one produced by an existence theorem.

The potentials obtained are *`c`-conjugate*: each is the real infimal transform of the other,
`φ x = ⨅ y, (c (x, y) - ψ y)` and `ψ y = ⨅ x, (c (x, y) - φ x)`. In particular they are bounded,
and they inherit any uniform modulus of continuity that the sections of the cost share, through
`TauCeti.uniformContinuous_iInf_sub`.

## Main statements

* `TauCeti.IsOptimalCoupling.exists_isDualCertificate_of_continuous` — every optimal plan of a
  bounded continuous nonnegative cost between probability measures on spaces whose product is
  hereditarily Lindelöf (for instance second countable) is certified by a pair of `c`-conjugate
  integrable potentials;
* `TauCeti.exists_isDualCertificate_of_continuous` — on Polish spaces, an optimal plan together
  with such a certificate exists;
* `TauCeti.isGreatest_kantorovichDualValue_integrable` — **strong duality with dual attainment**
  on Polish spaces: the primal value is the maximum of the values of the integrable dual feasible
  pairs.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 5,
  Theorem 5.10, whose proof builds the dual optimizer from the cyclically monotone support of an
  optimal plan.
* L. Rüschendorf, *On c-optimal random variables*, Statist. Probab. Lett. 27 (1996), 267--270,
  for the `c`-concave potential of a cyclically monotone set.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} {c : X × Y → ℝ}

/-- **Optimal plans of bounded continuous costs are certified.** Let `c` be a bounded continuous
nonnegative cost and `π` an optimal coupling of two probability measures, on spaces whose product
is hereditarily Lindelöf with measurable open sets (for instance, two second-countable Borel
spaces). Then there are integrable potentials `φ`, `ψ` forming an optimality certificate with
`π`: they are dual feasible and `π` is concentrated on their contact set. The potentials are
`c`-conjugate, each being the real infimal transform of the other. -/
theorem IsOptimalCoupling.exists_isDualCertificate_of_continuous [OpensMeasurableSpace X]
    [OpensMeasurableSpace Y] [OpensMeasurableSpace (X × Y)] [HereditarilyLindelofSpace (X × Y)]
    [IsProbabilityMeasure μ] {π : Measure (X × Y)}
    (hπ : IsOptimalCoupling (fun z ↦ ENNReal.ofReal (c z)) π μ ν) (hc : Continuous c)
    (hc0 : ∀ z, 0 ≤ c z) (hcb : BddAbove (range c)) :
    ∃ φ ψ, IsDualCertificate (fun z ↦ ENNReal.ofReal (c z)) π μ ν φ ψ ∧
      (∀ x, φ x = ⨅ y, (c (x, y) - ψ y)) ∧ ∀ y, ψ y = ⨅ x, (c (x, y) - φ x) := by
  obtain ⟨M, hM⟩ := hcb
  have : IsProbabilityMeasure π := hπ.toIsCoupling.isProbabilityMeasure
  have : IsProbabilityMeasure ν := hπ.toIsCoupling.isProbabilityMeasure_right
  -- A bounded cost has finite optimal value, so the support of `π` is cyclically monotone.
  have hfin : transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν ≠ ∞ := by
    rw [← hπ.lintegral_eq]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal M ∂π) (by simp) ?_
    exact lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal (hM (mem_range_self z))
  have hcm : IsCyclicallyMonotone c π.support :=
    (isCyclicallyMonotone_ofReal_iff hc0).1
      (hπ.isCyclicallyMonotone_support (ENNReal.continuous_ofReal.comp hc) hfin)
  -- Rockafellar–Rüschendorf gives a `c`-concave potential, which is bounded and real.
  obtain ⟨φ, hφ, hsub⟩ := hcm.exists_isCConcave_subset_cSuperdifferential
  obtain ⟨⟨x₀, y₀⟩, hz₀⟩ := (π.nonempty_support (IsProbabilityMeasure.ne_zero π)).mono hsub
  obtain ⟨a, -, ha, -, -⟩ := exists_coe_of_mem_contactSet (cSuperdifferential_def c φ ▸ hz₀)
  obtain ⟨f, g, hf, hg, hfb, hgb, hfg, hgf⟩ := hφ.exists_real_conjugate
    ⟨0, forall_mem_range.2 hc0⟩ ⟨M, hM⟩ ⟨x₀, a, ha⟩
  -- Both potentials are upper semicontinuous transforms, hence Borel; being bounded, they are
  -- integrable.
  have hfm : Measurable f := by
    have h := measurable_cTransformSymm_of_upperSemicontinuous
      (fun y ↦ (hc.comp (by fun_prop : Continuous fun x : X ↦ (x, y))).upperSemicontinuous)
      (cTransform c φ)
    rw [hφ.cTransformSymm_cTransform, funext hf] at h
    simpa using h.ereal_toReal
  have hgm : Measurable g := by
    have h := measurable_cTransform_of_upperSemicontinuous
      (fun x ↦ (hc.comp (by fun_prop : Continuous fun y : Y ↦ (x, y))).upperSemicontinuous) φ
    rw [funext hg] at h
    simpa using h.ereal_toReal
  obtain ⟨Cf, hCf⟩ := isBounded_iff_forall_norm_le.1 hfb
  obtain ⟨Cg, hCg⟩ := isBounded_iff_forall_norm_le.1 hgb
  refine ⟨f, g, ⟨hπ.toIsCoupling, (dualFeasible_ofReal_iff hc0 f g).2 fun x y ↦ ?_,
    .of_bound hfm.aestronglyMeasurable Cf (ae_of_all _ fun x ↦ hCf _ (mem_range_self x)),
    .of_bound hgm.aestronglyMeasurable Cg (ae_of_all _ fun y ↦ hCg _ (mem_range_self y)), ?_⟩,
    hfg, hgf⟩
  · -- Feasibility is the defining inequality of the transform.
    have h := add_cTransform_le c φ x y
    rw [hf, hg, ← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.1 h
  · -- `π` is concentrated on its support, which lies in the contact set.
    filter_upwards [π.support_mem_ae] with z hz
    have hz' := hsub hz
    rwa [cSuperdifferential_def, funext hg, funext hf, ← dualContactSet_ofReal hc0] at hz'

section Polish

variable [PolishSpace X] [BorelSpace X] [PolishSpace Y] [BorelSpace Y]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Existence of a certified optimal plan on Polish spaces.** For a bounded continuous
nonnegative cost and two probability measures on Polish spaces, there are an optimal coupling and
a pair of `c`-conjugate integrable potentials certifying it. -/
theorem exists_isDualCertificate_of_continuous (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z)
    (hcb : BddAbove (range c)) :
    ∃ π φ ψ, IsDualCertificate (fun z ↦ ENNReal.ofReal (c z)) π μ ν φ ψ ∧
      (∀ x, φ x = ⨅ y, (c (x, y) - ψ y)) ∧ ∀ y, ψ y = ⨅ x, (c (x, y) - φ x) := by
  obtain ⟨π, hπ⟩ :=
    exists_isOptimalCoupling μ ν (ENNReal.continuous_ofReal.comp hc).lowerSemicontinuous
  obtain ⟨φ, ψ, h⟩ := hπ.exists_isDualCertificate_of_continuous hc hc0 hcb
  exact ⟨π, φ, ψ, h⟩

/-- **Strong Kantorovich duality with dual attainment on Polish spaces.** For a bounded continuous
nonnegative cost and two probability measures on Polish spaces, the optimal transport cost is the
*greatest* value of an integrable dual feasible pair: the dual supremum is attained. -/
theorem isGreatest_kantorovichDualValue_integrable (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z)
    (hcb : BddAbove (range c)) :
    IsGreatest {r : ℝ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧ (∀ x y, φ x + ψ y ≤ c (x, y)) ∧
        kantorovichDualValue μ ν φ ψ = r}
      (transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν).toReal := by
  obtain ⟨π, φ, ψ, h, -⟩ := exists_isDualCertificate_of_continuous (μ := μ) (ν := ν) hc hc0 hcb
  refine ⟨⟨φ, ψ, h.integrable_left, h.integrable_right,
    (dualFeasible_ofReal_iff hc0 φ ψ).1 h.dualFeasible, h.toReal_transportCost_eq.symm⟩, ?_⟩
  rintro r ⟨φ', ψ', hφ', hψ', hfeas, rfl⟩
  exact ((dualFeasible_ofReal_iff hc0 φ' ψ').2 hfeas).kantorovichDualValue_le_toReal_transportCost
    h.transportCost_ne_top hφ' hψ'

end Polish

end TauCeti
