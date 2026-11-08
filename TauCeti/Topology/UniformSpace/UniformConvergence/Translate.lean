/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Locally uniform limits of translates along a strip

Let `u` be continuous on a set `F ⊆ ℝ × β`, and translate it along the first coordinate by
parameters `s_i`. If the translated windows `[a + s_i, b + s_i] × T` eventually lie in `F`, the
translates `z ↦ u (z + (s_i, 0))` are eventually continuous on `[a, b] × T`. When they converge
locally uniformly on the strip `ℝ × T` and `T` is compact, the convergence is uniform on each
window and the limit is continuous there
(`TauCeti.tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn`). A relation
`u (r + s_i, t₀) = u (r + s_i, t₁)` holding eventually passes to the limit
(`TauCeti.apply_eq_apply_of_tendstoLocallyUniformlyOn_comp_add`), as for boundary conditions
along the end.

This is the setting of translates of a map along a cylindrical end, as for Floer cylinders.
-/

public section

open Filter Set

namespace TauCeti

variable {ι β γ : Type*} [TopologicalSpace β] [AddZeroClass β]
  [UniformSpace γ] {l : Filter ι} {s : ι → ℝ} {T : Set β} {F : Set (ℝ × β)} {u v : ℝ × β → γ}

/-- Let `u` be continuous on `F`, and let the translated window `[a + s_i, b + s_i] × T`
eventually lie in `F`. If the translates `z ↦ u (z + (s_i, 0))` converge locally uniformly on the
strip `ℝ × T` to `v`, and `T` is compact, then on the window `[a, b] × T` the translates converge
uniformly to `v`, they are eventually continuous, and `v` is continuous. -/
theorem tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn [l.NeBot] {a b : ℝ}
    (hT : IsCompact T) (hu : ContinuousOn u F)
    (hW : ∀ᶠ i in l, Icc (a + s i) (b + s i) ×ˢ T ⊆ F)
    (hv : TendstoLocallyUniformlyOn (fun i z ↦ u (z + (s i, 0))) v l ((univ : Set ℝ) ×ˢ T)) :
    TendstoUniformlyOn (fun i z ↦ u (z + (s i, 0))) v l (Icc a b ×ˢ T) ∧
      (∀ᶠ i in l, ContinuousOn (fun z ↦ u (z + (s i, 0))) (Icc a b ×ˢ T)) ∧
      ContinuousOn v (Icc a b ×ˢ T) := by
  have hUC : TendstoUniformlyOn (fun i z ↦ u (z + (s i, 0))) v l (Icc a b ×ˢ T) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_Icc.prod hT)).1
      (hv.mono (prod_mono (subset_univ _) le_rfl))
  have hcont : ∀ᶠ i in l, ContinuousOn (fun z ↦ u (z + (s i, 0))) (Icc a b ×ˢ T) := by
    filter_upwards [hW] with i hi
    have hadd : Continuous fun z : ℝ × β ↦ z + (s i, 0) :=
      ((continuous_fst.add (continuous_const (y := s i))).prodMk continuous_snd).congr fun z ↦ by
        ext <;> simp
    refine hu.comp hadd.continuousOn fun z hz ↦ hi ?_
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hz
    exact ⟨⟨by simp [h₁], by simp [h₂]⟩, by simpa using h₃⟩
  exact ⟨hUC, hcont, hUC.continuousOn hcont.frequently⟩

/-- If the translates `z ↦ u (z + (s_i, 0))` converge locally uniformly on the strip `ℝ × T` to
`v`, and the values `u (r + s_i, t₀)` and `u (r + s_i, t₁)` at two points `t₀, t₁ ∈ T` eventually
agree, then `v (r, t₀) = v (r, t₁)`. For instance, a boundary condition `u (s, 0) = u (s, 1)`
along a cylindrical end passes to the limit of the translates. -/
theorem apply_eq_apply_of_tendstoLocallyUniformlyOn_comp_add [l.NeBot] [T2Space γ] {t₀ t₁ : β}
    (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) (r : ℝ)
    (hper : ∀ᶠ i in l, u (r + s i, t₀) = u (r + s i, t₁))
    (hv : TendstoLocallyUniformlyOn (fun i z ↦ u (z + (s i, 0))) v l ((univ : Set ℝ) ×ˢ T)) :
    v (r, t₀) = v (r, t₁) := by
  refine tendsto_nhds_unique ((hv.tendsto_at ⟨mem_univ r, ht₀⟩).congr' ?_)
    (hv.tendsto_at ⟨mem_univ r, ht₁⟩)
  filter_upwards [hper] with i hi
  simpa using hi

end TauCeti
