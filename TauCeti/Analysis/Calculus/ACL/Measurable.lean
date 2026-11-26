/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import TauCeti.Topology.UrysohnsLemma

/-!
# Measurability of the formal derivative on an open set

Let `Ω ⊆ ℝⁿ` be open and `F` a real Banach space. If `u : ℝⁿ → F` is continuous on `Ω`, its formal
derivative `u'` (`TauCeti.formalDeriv`) is almost everywhere strongly measurable on `Ω` for every
measure on `ℝⁿ` (`ContinuousOn.aestronglyMeasurable_formalDeriv`); in particular this holds for
every map `ACL` on `Ω` (`TauCeti.IsACLOn.aestronglyMeasurable_formalDeriv`). This generalises
`Continuous.stronglyMeasurable_formalDeriv` from maps continuous on all of `ℝⁿ` to maps
continuous on an open set.

The proof writes `Ω` as the union of countably many open sets `Vₖ` whose closures lie in `Ω`
(`Disjoint.hasSeparatingCover_closed_gdelta_right`, as `Ωᶜ` is closed and hence Gδ). On the
closure of `Vₖ`, `u` agrees with a map continuous on all of `ℝⁿ`, its product with a Urysohn cutoff
(`ContinuousOn.exists_continuous_eqOn_of_isClosed`, which holds in any normal space). The formal
derivatives of the two maps agree on `Vₖ` because the formal derivative depends only on germs
(`Filter.EventuallyEq.formalDeriv_eq`).
-/

public section

open MeasureTheory Set Filter

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {μ : Measure (EuclideanSpace ℝ (Fin n))}

/-- **Measurability of the formal derivative.** If `u` is continuous on an open set `Ω`, the formal
derivative of `u` is almost everywhere strongly measurable on `Ω` with respect to any measure. -/
theorem _root_.ContinuousOn.aestronglyMeasurable_formalDeriv [CompleteSpace F]
    (hu : ContinuousOn u Ω) (hΩ : IsOpen Ω) :
    AEStronglyMeasurable (formalDeriv u) (μ.restrict Ω) := by
  -- Open sets `V k` covering `Ω`, each with closure inside `Ω`: as `Ωᶜ` is closed, hence Gδ,
  -- `Ω` has a countable open cover separated from `Ωᶜ`.
  obtain ⟨V, hΩV, hV⟩ := disjoint_compl_right.hasSeparatingCover_closed_gdelta_right
    hΩ.isClosed_compl hΩ.isClosed_compl.isGδ
  have hVΩ (k : ℕ) : closure (V k) ⊆ Ω := disjoint_compl_right_iff_subset.1 (hV k).2
  rw [← (iUnion_subset fun k ↦ subset_closure.trans (hVΩ k)).antisymm hΩV,
    aestronglyMeasurable_iUnion_iff]
  intro k
  -- A continuous map `g` on `ℝⁿ` agreeing with `u` on `closure (V k)`.
  obtain ⟨g, hg, hgu⟩ := hu.exists_continuous_eqOn_of_isClosed hΩ isClosed_closure (hVΩ k)
  -- On the open set `V k`, the formal derivatives of `u` and `g` agree.
  have heq : EqOn (formalDeriv g) (formalDeriv u) (V k) := fun x hx ↦
    Filter.EventuallyEq.formalDeriv_eq <|
      Filter.mem_of_superset ((hV k).1.mem_nhds hx) fun y hy ↦ hgu (subset_closure hy)
  exact (hg.stronglyMeasurable_formalDeriv.aestronglyMeasurable).congr
    ((ae_restrict_mem (hV k).1.measurableSet).mono heq)

/-- The formal derivative of a map `ACL` on an open set `Ω` is almost everywhere strongly
measurable on `Ω` with respect to any measure. -/
theorem IsACLOn.aestronglyMeasurable_formalDeriv [CompleteSpace F] (hu : IsACLOn u Ω)
    (hΩ : IsOpen Ω) : AEStronglyMeasurable (formalDeriv u) (μ.restrict Ω) :=
  hu.continuousOn.aestronglyMeasurable_formalDeriv hΩ

end TauCeti
