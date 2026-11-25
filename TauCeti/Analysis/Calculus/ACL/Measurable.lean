/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Measurability of the formal derivative on an open set

Let `Ω ⊆ ℝⁿ` be open and `F` a finite-dimensional real normed space. If `u : ℝⁿ → F` is continuous
on `Ω`, its formal derivative `u'` (`TauCeti.formalDeriv`) is almost everywhere strongly
measurable on `Ω` (`ContinuousOn.aestronglyMeasurable_formalDeriv`); in particular this holds for
every map `ACL` on `Ω` (`TauCeti.IsACLOn.aestronglyMeasurable_formalDeriv`). This is the
measurability clause of QuasiregularMaps §5.1, which main has for maps continuous on all of `ℝⁿ`
(`Continuous.stronglyMeasurable_formalDeriv`).

The formal derivative at `x` depends only on `u` near `x`
(`Filter.EventuallyEq.formalDeriv_eq`). The proof writes `Ω` as the union of the open sets
`Vₖ = {x | 1/(k+1) < d(x, Ωᶜ)}`, each contained in the closed set
`Kₖ = {x | 1/(k+1) ≤ d(x, Ωᶜ)} ⊆ Ω`, extends `u|Kₖ` to a continuous map on `ℝⁿ` by the Tietze
extension theorem (here finite dimensionality of `F` is used), and compares formal derivatives
on `Vₖ`.
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u v : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- The formal derivative at `x` depends only on the germ of the map at `x`. -/
theorem _root_.Filter.EventuallyEq.formalDeriv_eq {x : EuclideanSpace ℝ (Fin n)}
    (h : u =ᶠ[𝓝 x] v) : formalDeriv u x = formalDeriv v x := by
  ext w
  rw [formalDeriv_apply, formalDeriv_apply]
  simp_rw [h.lineDeriv_eq]

/-- **Measurability of the formal derivative.** If `u` is continuous on an open set `Ω` and `F`
is finite-dimensional, the formal derivative of `u` is almost everywhere strongly measurable on
`Ω`. -/
theorem _root_.ContinuousOn.aestronglyMeasurable_formalDeriv [FiniteDimensional ℝ F]
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
  -- Extend `u` from `K k` to a continuous map on `ℝⁿ`.
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (hK k)
    ⟨(K k).domRestrict u, (hu.mono (hKΩ k)).domRestrict⟩
  have hgu : EqOn g u (K k) := fun x hx ↦ congrArg (fun φ : C(K k, F) ↦ φ ⟨x, hx⟩) hg
  -- On the open set `V k`, the formal derivatives of `u` and `g` agree.
  have heq : EqOn (formalDeriv g) (formalDeriv u) (V k) := fun x hx ↦
    Filter.EventuallyEq.formalDeriv_eq <|
      Filter.mem_of_superset ((hV k).mem_nhds hx) fun y hy ↦ hgu (hVK k hy)
  exact (g.continuous.stronglyMeasurable_formalDeriv.aestronglyMeasurable).congr
    ((ae_restrict_mem (hV k).measurableSet).mono heq)

/-- The formal derivative of a map `ACL` on an open set `Ω`, with values in a finite-dimensional
space, is almost everywhere strongly measurable on `Ω`. -/
theorem IsACLOn.aestronglyMeasurable_formalDeriv [FiniteDimensional ℝ F] (hu : IsACLOn u Ω)
    (hΩ : IsOpen Ω) : AEStronglyMeasurable (formalDeriv u) (volume.restrict Ω) :=
  hu.continuousOn.aestronglyMeasurable_formalDeriv hΩ

end TauCeti
