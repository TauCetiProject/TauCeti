/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UrysohnsLemma

/-!
# Measurability of the formal derivative on an open set

Let `Ω ⊆ ℝⁿ` be open and `F` a real Banach space. If `u : ℝⁿ → F` is continuous on `Ω`, its formal
derivative `u'` (`TauCeti.formalDeriv`) is almost everywhere strongly measurable on `Ω` for every
measure on `ℝⁿ` (`ContinuousOn.aestronglyMeasurable_formalDeriv`); in particular this holds for
every map `ACL` on `Ω` (`TauCeti.IsACLOn.aestronglyMeasurable_formalDeriv`). This generalises
`Continuous.stronglyMeasurable_formalDeriv` from maps continuous on all of `ℝⁿ` to maps
continuous on an open set.

The proof writes `Ω` as the union of the open sets `Vₖ = {x | 1/(k+1) < d(x, Ωᶜ)}`, each
contained in the closed set `Kₖ = {x | 1/(k+1) ≤ d(x, Ωᶜ)} ⊆ Ω`. On `Kₖ`, `u` agrees with a map
continuous on all of `ℝⁿ`, its product with a Urysohn cutoff
(`ContinuousOn.exists_continuous_eqOn_of_isClosed`, which holds in any normal space). The formal
derivatives of the two maps agree on `Vₖ` because the formal derivative depends only on germs
(`Filter.EventuallyEq.formalDeriv_eq`).
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {μ : Measure (EuclideanSpace ℝ (Fin n))}

/-- A map continuous on an open set `Ω` of a normal space agrees on each closed subset `K ⊆ Ω` with
a map continuous everywhere, namely its product with a Urysohn cutoff equal to `1` on `K` and to `0`
near `Ωᶜ`. -/
theorem _root_.ContinuousOn.exists_continuous_eqOn_of_isClosed {X E : Type*} [TopologicalSpace X]
    [NormalSpace X] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [ContinuousSMul ℝ E]
    {u : X → E} {Ω K : Set X} (hu : ContinuousOn u Ω) (hΩ : IsOpen Ω) (hK : IsClosed K)
    (hKΩ : K ⊆ Ω) : ∃ g : X → E, Continuous g ∧ EqOn g u K := by
  -- The cutoff `χ` is `1` on `K` and `0` off an open `W ⊇ K` with `closure W ⊆ Ω`.
  obtain ⟨W, hW, hKW, hWΩ⟩ := normal_exists_closure_subset hK hΩ hKΩ
  obtain ⟨χ, hχW, hχK, -⟩ := exists_continuous_zero_one_of_isClosed hW.isClosed_compl hK
    (disjoint_compl_left_iff_subset.2 hKW)
  refine ⟨fun x ↦ χ x • u x, continuous_iff_continuousAt.2 fun x ↦ ?_,
    fun x hx ↦ by simp [hχK hx]⟩
  by_cases hx : x ∈ Ω
  · exact χ.continuous.continuousAt.smul (hu.continuousAt (hΩ.mem_nhds hx))
  -- Near `x ∉ Ω`, that is off `closure W`, the cutoff and hence the product vanish.
  refine continuousAt_const.congr (f := fun _ ↦ (0 : E)) ?_
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (mem_compl fun h ↦ hx (hWΩ h))]
    with y hy
  simp [hχW (mem_compl fun h ↦ notMem_of_mem_compl hy (subset_closure h))]

/-- **Measurability of the formal derivative.** If `u` is continuous on an open set `Ω`, the formal
derivative of `u` is almost everywhere strongly measurable on `Ω` with respect to any measure. -/
theorem _root_.ContinuousOn.aestronglyMeasurable_formalDeriv [CompleteSpace F]
    (hu : ContinuousOn u Ω) (hΩ : IsOpen Ω) :
    AEStronglyMeasurable (formalDeriv u) (μ.restrict Ω) := by
  -- The open sets `V k` and the closed sets `K k`, with `V k ⊆ K k ⊆ Ω` and `⋃ k, V k = Ω`.
  set V : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k ↦ {x | ((k : ℝ≥0∞) + 1)⁻¹ < infEDist x Ωᶜ}
  set K : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k ↦ {x | ((k : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Ωᶜ}
  have hVK (k : ℕ) : V k ⊆ K k := fun x hx ↦ by
    simp only [V, K, mem_ofPred_eq] at hx ⊢
    exact hx.le
  have hV (k : ℕ) : IsOpen (V k) := isOpen_lt continuous_const continuous_infEDist
  have hK (k : ℕ) : IsClosed (K k) := isClosed_le continuous_const continuous_infEDist
  have hKΩ (k : ℕ) : K k ⊆ Ω := fun x hx ↦ by
    by_contra hxΩ
    have h0 : infEDist x Ωᶜ = 0 := infEDist_zero_of_mem hxΩ
    simp only [K, mem_ofPred_eq, h0, nonpos_iff_eq_zero, ENNReal.inv_eq_zero] at hx
    exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩ hx
  have hUnion : ⋃ k, V k = Ω := by
    refine Subset.antisymm (iUnion_subset fun k ↦ (hVK k).trans (hKΩ k)) fun x hx ↦ ?_
    have hpos : 0 < infEDist x Ωᶜ := by
      rw [pos_iff_ne_zero, ne_eq, ← mem_closure_iff_infEDist_zero, hΩ.isClosed_compl.closure_eq]
      exact fun h ↦ h hx
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    exact mem_iUnion.2 ⟨k, (ENNReal.inv_le_inv.2 (le_self_add)).trans_lt hk⟩
  rw [← hUnion, aestronglyMeasurable_iUnion_iff]
  intro k
  -- A continuous map `g` on `ℝⁿ` agreeing with `u` on `K k`.
  obtain ⟨g, hg, hgu⟩ := hu.exists_continuous_eqOn_of_isClosed hΩ (hK k) (hKΩ k)
  -- On the open set `V k`, the formal derivatives of `u` and `g` agree.
  have heq : EqOn (formalDeriv g) (formalDeriv u) (V k) := fun x hx ↦
    Filter.EventuallyEq.formalDeriv_eq <|
      Filter.mem_of_superset ((hV k).mem_nhds hx) fun y hy ↦ hgu (hVK k hy)
  exact (hg.stronglyMeasurable_formalDeriv.aestronglyMeasurable).congr
    ((ae_restrict_mem (hV k).measurableSet).mono heq)

/-- The formal derivative of a map `ACL` on an open set `Ω` is almost everywhere strongly
measurable on `Ω` with respect to any measure. -/
theorem IsACLOn.aestronglyMeasurable_formalDeriv [CompleteSpace F] (hu : IsACLOn u Ω)
    (hΩ : IsOpen Ω) : AEStronglyMeasurable (formalDeriv u) (μ.restrict Ω) :=
  hu.continuousOn.aestronglyMeasurable_formalDeriv hΩ

end TauCeti
