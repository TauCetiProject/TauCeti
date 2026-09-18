/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Separable
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.LowerSemicontinuous

/-!
# The Wasserstein spaces are Borel spaces

The finite-moment space `TauCeti.WassersteinSpace p X` and the anchored components
`TauCeti.WassersteinComponent p μ₀` carry two structures of different origin: the measurable
structure inherited from the Giry σ-algebra on `ProbabilityMeasure X`, and the topology of the
Wasserstein metric. This file proves that, over a Polish ground space and for a finite exponent
`1 ≤ p < ∞`, the first is the Borel σ-algebra of the second. Consequently the open sets of the
Wasserstein topology are measurable, and measures on the Wasserstein space — random laws, such as
the population laws on `P_p (P_p (X))` of Wasserstein barycentre problems — may be manipulated with
the topological and metric tools of a Borel space.

The comparison goes through the weak topology, which is coarser than the Wasserstein topology.

* Every Giry-measurable set is Wasserstein-Borel: the inclusion into `ProbabilityMeasure X` is
  continuous for the Wasserstein topology
  (`TauCeti.WassersteinSpace.continuous_toProbabilityMeasure`), and weakly continuous maps are
  Giry measurable (`Continuous.measurable_probabilityMeasure`).
* Every Wasserstein-open set is Giry measurable: the space is separable
  (`TauCeti.WassersteinSpace.separableSpace`), so every open set is a countable union of balls; a
  ball is a strict sublevel set of `μ ↦ W_p (μ, ν)`, which is lower semicontinuous for the weak
  topology (`TauCeti.lowerSemicontinuous_wassersteinEDist_of_ne_top`). Hence the ball is Borel for
  the weak topology on the set of laws in question, and that set, being separable and
  pseudometrizable, carries the Giry σ-algebra as its weak Borel σ-algebra
  (`TauCeti.MeasureTheory.ProbabilityMeasure.borelSpace_subtype`).

Separability is the only property of the carrier that the argument uses. It holds for `P_p (X)`,
hence for every component anchored at a law of finite `p`-moment, which is isometric to it. The
exponent `p = ∞` is excluded: `P_∞ (X)` need not be separable.

## Main statements

* `TauCeti.WassersteinSpace.borelSpace` — `P_p (X)` is a Borel space for `1 ≤ p < ∞`, with
  `TauCeti.WassersteinSpace.instBorelSpace` its instance form;
* `TauCeti.WassersteinComponent.borelSpace` — a separable anchored component is a Borel space, with
  `TauCeti.WassersteinComponent.instBorelSpace` its instance form.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti

universe u

variable {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
  {p : ℝ≥0∞}

/-- A separable pseudometric space `Y` of laws on a Polish space whose distance is the
`p`-Wasserstein distance, for a finite exponent, whose inclusion into `ProbabilityMeasure X` is
weakly continuous, and whose measurable structure is pulled back from the Giry σ-algebra, is a Borel
space. This is the common argument behind `TauCeti.WassersteinSpace.borelSpace` and
`TauCeti.WassersteinComponent.borelSpace`. -/
private theorem borelSpace_of_edist_eq {Y : Type*} [PseudoMetricSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] (hp : p ≠ ∞) (toPM : Y → ProbabilityMeasure X) (hcont : Continuous toPM)
    (hm : ‹MeasurableSpace Y› = .comap toPM inferInstance)
    (hedist : ∀ μ ν, edist μ ν = wassersteinEDist p (toPM μ : Measure X) (toPM ν : Measure X)) :
    BorelSpace Y := by
  -- The range of `toPM`, with the weak topology, is a second countable space of laws, so its Giry
  -- σ-algebra is its Borel σ-algebra.
  let S := range toPM
  have : SecondCountableTopology S := (isSeparable_range hcont).secondCountableTopology
  let e : Y → S := rangeFactorization toPM
  have he : Continuous e := hcont.subtype_mk _
  have hm' : ‹MeasurableSpace Y› = .comap e (borel S) := by
    rw [hm, ← BorelSpace.measurable_eq (α := S)]
    exact (MeasurableSpace.comap_comp (f := Subtype.val) (g := e)).symm
  have hem : Measurable e := by
    rw [hm', ← BorelSpace.measurable_eq (α := S)]
    exact comap_measurable e
  refine ⟨le_antisymm ?_ ?_⟩
  · -- Giry-measurable sets are Borel, because `e` is continuous.
    rw [hm']
    exact he.borel_measurable.comap_le
  · -- Every open set is a countable union of balls, and each ball is the preimage under `e` of a
    -- strict sublevel set of a weakly lower semicontinuous function.
    refine MeasurableSpace.generateFrom_le fun U hU ↦ ?_
    have hball : ∀ ν : Y, ∀ r, MeasurableSet (Metric.eball ν r) := fun ν r ↦ by
      have hlsc : LowerSemicontinuous fun s : S ↦
          wassersteinEDist p ((s : ProbabilityMeasure X) : Measure X) (toPM ν : Measure X) :=
        (lowerSemicontinuous_wassersteinEDist_of_ne_top hp).comp
          (continuous_subtype_val.prodMk continuous_const)
      have : Metric.eball ν r = e ⁻¹' {s | wassersteinEDist p
          ((s : ProbabilityMeasure X) : Measure X) (toPM ν : Measure X) < r} := by
        ext μ
        simp [Metric.mem_eball, hedist, e]
      rw [this]
      exact hem (measurableSet_lt hlsc.measurable measurable_const)
    choose ε hε hsub using fun a : U ↦ EMetric.isOpen_iff.1 hU a a.2
    have hunion : ⋃ a : U, Metric.eball (a : Y) (ε a) = U :=
      Subset.antisymm (iUnion_subset hsub) fun a ha ↦
        mem_iUnion.2 ⟨⟨a, ha⟩, Metric.mem_eball_self (hε _)⟩
    obtain ⟨t, htc, ht⟩ := eq_open_union_countable (fun a : U ↦ Metric.eball (a : Y) (ε a))
      fun _ ↦ Metric.isOpen_eball
    rw [← hunion, ← ht]
    exact MeasurableSet.biUnion htc fun a _ ↦ hball _ _

namespace WassersteinSpace

variable [Fact (1 ≤ p)]

/-- **`P_p (X)` is a Borel space.** For a finite exponent `1 ≤ p < ∞` and a Polish ground space,
the measurable structure of the finite-moment Wasserstein space, inherited from the Giry σ-algebra
on `ProbabilityMeasure X`, is the Borel σ-algebra of the Wasserstein metric. -/
theorem borelSpace (hp : p ≠ ∞) : BorelSpace (WassersteinSpace p X) := by
  have := separableSpace (X := X) hp
  refine borelSpace_of_edist_eq hp toProbabilityMeasure continuous_toProbabilityMeasure
    (le_antisymm (fun s hs ↦ ?_) measurable_toProbabilityMeasure.comap_le) edist_def
  -- The inherited structure is the pullback: `mk` is measurable out of the pulled-back structure.
  have h := @measurable_mk X p _ _ _ (.comap toProbabilityMeasure inferInstance) _
    (comap_measurable _) hasFiniteMoment
  simpa using h hs

/-- `P_p (X)` as a Borel space, reading the finiteness of the exponent off a `Fact`, as its
separability does. -/
instance instBorelSpace [Fact (p ≠ ∞)] : BorelSpace (WassersteinSpace p X) :=
  borelSpace Fact.out

end WassersteinSpace

namespace WassersteinComponent

variable [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- **A separable Wasserstein component is a Borel space.** For a finite exponent `1 ≤ p < ∞` and a
Polish ground space, if the finite-distance component anchored at `μ₀` is separable, then its
measurable structure, inherited from the Giry σ-algebra on `ProbabilityMeasure X`, is the Borel
σ-algebra of the Wasserstein metric. Separability holds for every anchor of finite `p`-moment,
by `TauCeti.WassersteinComponent.separableSpace_of_hasFiniteMoment`. -/
theorem borelSpace (hp : p ≠ ∞) [SeparableSpace (WassersteinComponent p μ₀)] :
    BorelSpace (WassersteinComponent p μ₀) := by
  refine borelSpace_of_edist_eq hp toProbabilityMeasure continuous_toProbabilityMeasure
    (le_antisymm (fun s hs ↦ ?_) measurable_toProbabilityMeasure.comap_le) edist_def
  -- The inherited structure is the pullback: `mk` is measurable out of the pulled-back structure.
  have h := @measurable_mk X p _ _ μ₀ _ (.comap toProbabilityMeasure inferInstance) _
    (comap_measurable _) wassersteinEDist_anchor_ne_top
  simpa using h hs

/-- A separable anchored component as a Borel space, reading the finiteness of the exponent off a
`Fact`. -/
instance instBorelSpace [Fact (p ≠ ∞)] [SeparableSpace (WassersteinComponent p μ₀)] :
    BorelSpace (WassersteinComponent p μ₀) :=
  borelSpace Fact.out

end WassersteinComponent

end TauCeti
