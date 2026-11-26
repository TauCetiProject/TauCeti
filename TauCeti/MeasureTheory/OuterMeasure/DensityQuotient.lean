/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Vanishing density quotients for outer measures

Comparison lemmas for vanishing quotients `μ (S r) / d r → 0` along a filter `l`
(`TauCeti.tendsto_measure_div_of_subset`, `TauCeti.tendsto_measure_div_of_subset_union`,
`TauCeti.tendsto_measure_sep_inter_div_of_sdiff`,
`TauCeti.tendsto_measure_symmDiff_inter_div_iff`,
`TauCeti.tendsto_measure_inter_div_of_measure_eq_zero`,
`TauCeti.tendsto_measure_inter_div_of_eventually_notMem`, and
`TauCeti.tendsto_measure_symmDiff_inter_div_of_eventuallyEq`), stated for `OuterMeasureClass`.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal symmDiff Topology

namespace TauCeti

variable {α X F : Type*} [FunLike F (Set X) ℝ≥0∞] [OuterMeasureClass F X] {μ : F}

/-- Monotonicity of vanishing density quotients: if `S r ⊆ T r` for all `r` and `μ (T r) / d r → 0`,
then `μ (S r) / d r → 0`. -/
theorem tendsto_measure_div_of_subset {S T : α → Set X} {d : α → ℝ≥0∞} {l : Filter α}
    (h : Tendsto (fun r => μ (T r) / d r) l (𝓝 0)) (hsub : ∀ r, S r ⊆ T r) :
    Tendsto (fun r => μ (S r) / d r) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun r => ENNReal.div_le_div_right (measure_mono (hsub r)) _)

/-- Subadditivity of vanishing density quotients: if `S r ⊆ T₁ r ∪ T₂ r` for all `r` and both
`μ (T₁ r) / d r → 0` and `μ (T₂ r) / d r → 0`, then `μ (S r) / d r → 0`. -/
theorem tendsto_measure_div_of_subset_union {S T₁ T₂ : α → Set X} {d : α → ℝ≥0∞} {l : Filter α}
    (h₁ : Tendsto (fun r => μ (T₁ r) / d r) l (𝓝 0))
    (h₂ : Tendsto (fun r => μ (T₂ r) / d r) l (𝓝 0)) (hsub : ∀ r, S r ⊆ T₁ r ∪ T₂ r) :
    Tendsto (fun r => μ (S r) / d r) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using h₁.add h₂)
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
  rw [← ENNReal.add_div]
  exact ENNReal.div_le_div_right ((measure_mono (hsub r)).trans (measure_union_le _ _)) _

/-- Replacing `E₁` by `E₂` in `{z ∈ E₁ ∩ t r | p z}` preserves vanishing density quotients when
`E₂ \ E₁` has vanishing density quotients against `t`. -/
theorem tendsto_measure_sep_inter_div_of_sdiff {E₁ E₂ : Set X} {t : α → Set X} {p : X → Prop}
    {d : α → ℝ≥0∞} {l : Filter α}
    (h₁ : Tendsto (fun r => μ {z ∈ E₁ ∩ t r | p z} / d r) l (𝓝 0))
    (hdiff : Tendsto (fun r => μ ((E₂ \ E₁) ∩ t r) / d r) l (𝓝 0)) :
    Tendsto (fun r => μ {z ∈ E₂ ∩ t r | p z} / d r) l (𝓝 0) := by
  classical
  exact tendsto_measure_div_of_subset_union h₁ hdiff fun _ z ⟨⟨hzE₂, hzt⟩, hzp⟩ =>
    if hzE₁ : z ∈ E₁ then Or.inl ⟨⟨hzE₁, hzt⟩, hzp⟩ else Or.inr ⟨⟨hzE₂, hzE₁⟩, hzt⟩

/-- Symmetric-difference density quotients vanish if and only if both one-sided set-difference
density quotients vanish. -/
theorem tendsto_measure_symmDiff_inter_div_iff {E₁ E₂ : Set X} {t : α → Set X}
    {d : α → ℝ≥0∞} {l : Filter α} :
    Tendsto (fun r => μ ((E₁ ∆ E₂) ∩ t r) / d r) l (𝓝 0) ↔
      Tendsto (fun r => μ ((E₁ \ E₂) ∩ t r) / d r) l (𝓝 0) ∧
        Tendsto (fun r => μ ((E₂ \ E₁) ∩ t r) / d r) l (𝓝 0) :=
  ⟨fun hsym =>
    ⟨tendsto_measure_div_of_subset hsym fun _ => inter_subset_inter_left _ subset_union_left,
      tendsto_measure_div_of_subset hsym fun _ => inter_subset_inter_left _ subset_union_right⟩,
    fun ⟨h12, h21⟩ =>
      tendsto_measure_div_of_subset_union h12 h21 fun _ _ ⟨hzsym, hzt⟩ =>
        hzsym.elim (fun h1 => Or.inl ⟨h1, hzt⟩) (fun h2 => Or.inr ⟨h2, hzt⟩)⟩

/-- Any subset `T` of a `μ`-null set `S` has vanishing density quotients against arbitrary test
sets. -/
theorem tendsto_measure_inter_div_of_measure_eq_zero {S T : Set X} (hTS : T ⊆ S) (hS : μ S = 0)
    (t : α → Set X) (d : α → ℝ≥0∞) (l : Filter α) :
    Tendsto (fun r => μ (T ∩ t r) / d r) l (𝓝 0) := by
  refine tendsto_const_nhds.congr fun r => ?_
  rw [measure_mono_null (inter_subset_left.trans hTS) hS, ENNReal.zero_div]

/-- A set `S` that is eventually avoided along a filter `f` (`∀ᶠ z in f, z ∉ S`) has vanishing
density quotients against any family `t` shrinking into `f` (`Tendsto t l f.smallSets`). -/
theorem tendsto_measure_inter_div_of_eventually_notMem {S : Set X} {f : Filter X}
    (hS : ∀ᶠ z in f, z ∉ S) {t : α → Set X} {l : Filter α} (ht : Tendsto t l f.smallSets)
    (d : α → ℝ≥0∞) :
    Tendsto (fun r => μ (S ∩ t r) / d r) l (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_smallSets_iff.1 ht _ hS] with r hr
  rw [(disjoint_left.2 fun _ hz hzt => hr hzt hz).inter_eq, measure_empty, ENNReal.zero_div]

/-- If two sets agree eventually along a filter `f` (`E₁ =ᶠ[f] E₂`), then their symmetric
difference `E₁ ∆ E₂` has vanishing density quotients against any family `t` shrinking into `f`
(`Tendsto t l f.smallSets`). -/
theorem tendsto_measure_symmDiff_inter_div_of_eventuallyEq {E₁ E₂ : Set X} {f : Filter X}
    (h : E₁ =ᶠ[f] E₂) {t : α → Set X} {l : Filter α} (ht : Tendsto t l f.smallSets)
    (d : α → ℝ≥0∞) :
    Tendsto (fun r => μ ((E₁ ∆ E₂) ∩ t r) / d r) l (𝓝 0) :=
  tendsto_measure_inter_div_of_eventually_notMem (S := E₁ ∆ E₂)
    (h.mono fun _ hz hmem => hmem.elim (fun ⟨h1, h2⟩ => h2 (hz.mp h1))
      (fun ⟨h1, h2⟩ => h2 (hz.mpr h1))) ht d

end TauCeti
