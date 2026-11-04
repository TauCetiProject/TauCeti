/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FoelnerFilter
public import TauCeti.MeasureTheory.Measure.AddContent

/-!
# The density-limit content of a Følner family

Let a group `G` act on a measure space `X` in which every subset is measurable, and let
`F : ι → Set X` be a Følner family along an ultrafilter `u`. Mathlib's `IsFoelner.mean μ u F s`
is the limit along `u` of the densities `μ (s ∩ F i) / μ (F i)`. It is the finitely additive
probability behind `IsFoelner.amenable`, which only records its properties in an existential
statement. This file bundles it as a content on all subsets of `X`
(`IsFoelner.addContent`), so that it can be compared with other finitely additive probabilities,
such as the content of a mean on a discrete group. The content has total mass one and is
invariant under `G` when `μ` is.

## Main definitions

* `IsFoelner.addContent`: the density-limit content `s ↦ lim_u μ (s ∩ F i) / μ (F i)` of a Følner
  family along an ultrafilter.

## Main results

* `IsFoelner.tendsto_addContent`: the densities of `s` tend to the content of `s` along `u`.
* `IsFoelner.addContent_univ`: the content has total mass one.
* `IsFoelner.addContent_smul`: the content is invariant under the action of `G`.

## References

* A. Garrido, *An introduction to amenable groups*, Definition 3.1 and Theorem 3.6.
-/

public section

noncomputable section

open Filter Set Topology

open scoped ENNReal Pointwise

namespace IsFoelner

variable {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] {μ : MeasureTheory.Measure X} {u : Ultrafilter ι} {F : ι → Set X}

/-- The density-limit content of a Følner family `F` along an ultrafilter `u`: the content of `s`
is the limit along `u` of the densities `μ (s ∩ F i) / μ (F i)`. Every subset of `X` is measurable,
so this is a finitely additive set function on all subsets. -/
def addContent (hF : IsFoelner G μ u F) :
    MeasureTheory.AddContent ℝ≥0∞ (univ : Set (Set X)) :=
  MeasureTheory.isSetRing_univ.addContent_of_union (mean μ u F)
    (tendsto_nhds_unique (hF.tendsto_nhds_mean ∅) (by simp))
    fun _ _ hst ↦ hF.mean_union_eq_add_of_disjoint _ _ .of_discrete hst

theorem addContent_apply (hF : IsFoelner G μ u F) (s : Set X) :
    hF.addContent s = mean μ u F s :=
  (rfl)

/-- The densities `μ (s ∩ F i) / μ (F i)` tend to the content of `s` along the ultrafilter. -/
theorem tendsto_addContent (hF : IsFoelner G μ u F) (s : Set X) :
    Tendsto (fun i ↦ μ (s ∩ F i) / μ (F i)) u (𝓝 (hF.addContent s)) :=
  hF.tendsto_nhds_mean s

/-- The density-limit content has total mass one. -/
@[simp]
theorem addContent_univ (hF : IsFoelner G μ u F) : hF.addContent univ = 1 :=
  hF.mean_univ_eq_one

/-- The density-limit content of a Følner family for a `G`-invariant measure is `G`-invariant. -/
theorem addContent_smul [MeasureTheory.SMulInvariantMeasure G X μ] (hF : IsFoelner G μ u F)
    (g : G) (s : Set X) : hF.addContent (g • s) = hF.addContent s :=
  hF.mean_smul_eq_mean g s

end IsFoelner
