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
derivative `u'` (`TauCeti.formalDeriv`) is almost everywhere strongly measurable on `Ω`
(`ContinuousOn.aestronglyMeasurable_formalDeriv`); in particular this holds for every map `ACL` on
`Ω` (`TauCeti.IsACLOn.aestronglyMeasurable_formalDeriv`). This generalises
`Continuous.stronglyMeasurable_formalDeriv` from maps continuous on all of `ℝⁿ` to maps
continuous on an open set.

The proof writes `Ω` as the union of the open sets `Vₖ = {x | 1/(k+1) < d(x, Ωᶜ)}`, each
contained in the closed set `Kₖ = {x | 1/(k+1) ≤ d(x, Ωᶜ)} ⊆ Ω`. Multiplying `u` by a Urysohn
cutoff equal to `1` on `Kₖ` and to `0` near `Ωᶜ` gives a continuous map on `ℝⁿ` that agrees with
`u` on `Kₖ`, and the formal derivatives of the two maps agree on `Vₖ` because the formal derivative
depends only on germs (`Filter.EventuallyEq.formalDeriv_eq`).
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- **Measurability of the formal derivative.** If `u` is continuous on an open set `Ω`, the formal
derivative of `u` is almost everywhere strongly measurable on `Ω`. -/
theorem _root_.ContinuousOn.aestronglyMeasurable_formalDeriv [CompleteSpace F]
    (hu : ContinuousOn u Ω) (hΩ : IsOpen Ω) :
    AEStronglyMeasurable (formalDeriv u) (volume.restrict Ω) := by
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
  -- A continuous map `g` on `ℝⁿ` agreeing with `u` on `K k`: the product of `u` with a Urysohn
  -- cutoff `χ` equal to `1` on `K k` and to `0` on the closed neighbourhood `L` of `Ωᶜ`.
  set L : Set (EuclideanSpace ℝ (Fin n)) := {x | infEDist x Ωᶜ ≤ ((k : ℝ≥0∞) + 2)⁻¹}
  have hlt : ((k : ℝ≥0∞) + 2)⁻¹ < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_lt_inv.2 <|
    (ENNReal.add_lt_add_iff_left (ENNReal.natCast_ne_top k)).2 ENNReal.one_lt_two
  have hKL : Disjoint (K k) L := disjoint_left.2 fun x hxK hxL ↦ (hxL.trans_lt hlt).not_ge hxK
  obtain ⟨χ, hχL, hχK, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_le continuous_infEDist continuous_const) (hK k) hKL.symm
  set g : EuclideanSpace ℝ (Fin n) → F := fun x ↦ χ x • u x
  have hg : Continuous g := continuous_iff_continuousAt.2 fun x ↦ by
    by_cases hx : x ∈ Ω
    · exact χ.continuous.continuousAt.smul (hu.continuousAt (hΩ.mem_nhds hx))
    -- Near a point of `Ωᶜ`, the cutoff and hence `g` vanish.
    have hW : {y | infEDist y Ωᶜ < ((k : ℝ≥0∞) + 2)⁻¹} ∈ 𝓝 x :=
      (isOpen_lt continuous_infEDist continuous_const).mem_nhds <| by
        simp [infEDist_zero_of_mem (show x ∈ Ωᶜ from hx)]
    exact continuousAt_const.congr (mem_of_superset hW fun y hy ↦
      by simp [g, hχL (le_of_lt (show infEDist y Ωᶜ < _ from hy))] : (fun _ ↦ (0 : F)) =ᶠ[𝓝 x] g)
  have hgu : EqOn g u (K k) := fun x hx ↦ by simp [g, hχK hx]
  -- On the open set `V k`, the formal derivatives of `u` and `g` agree.
  have heq : EqOn (formalDeriv g) (formalDeriv u) (V k) := fun x hx ↦
    Filter.EventuallyEq.formalDeriv_eq <|
      Filter.mem_of_superset ((hV k).mem_nhds hx) fun y hy ↦ hgu (hVK k hy)
  exact (hg.stronglyMeasurable_formalDeriv.aestronglyMeasurable).congr
    ((ae_restrict_mem (hV k).measurableSet).mono heq)

/-- The formal derivative of a map `ACL` on an open set `Ω` is almost everywhere strongly
measurable on `Ω`. -/
theorem IsACLOn.aestronglyMeasurable_formalDeriv [CompleteSpace F] (hu : IsACLOn u Ω)
    (hΩ : IsOpen Ω) : AEStronglyMeasurable (formalDeriv u) (volume.restrict Ω) :=
  hu.continuousOn.aestronglyMeasurable_formalDeriv hΩ

end TauCeti
