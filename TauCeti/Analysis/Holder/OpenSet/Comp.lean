/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic
import TauCeti.Analysis.Holder.FaaDiBruno
import TauCeti.Analysis.Holder.IsBigO
import TauCeti.Analysis.Holder.Leibniz

/-!
# Local Hölder bounds after a change of variables and a field of linear maps

An element `f` of `C^{k,α}(Ω, F)` on an open set `Ω`, composed with a `C^{k+1}` map `τ` into `Ω`
and multiplied by a `C^{k+1}` field `Φ` of linear maps, has locally `α`-Hölder `k`-th derivative
(`TauCeti.CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_clm_apply_comp`). This is the local
estimate behind the change of chart and frame of a section of a vector bundle.

The `k`-th derivative of `f ∘ τ` is Hölder near each point by the Hölder chain rule
`TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp`, that of `Φ` is `C¹` hence Hölder, and the
Leibniz rule `ContinuousLinearMap.exists_holderOnWith_iteratedFDeriv_comp₂` multiplies the two.
-/

public section

open Set TopologicalSpace
open scoped NNReal ContDiff

namespace TauCeti

namespace CkHolderSpaceOn

variable {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {k : ℕ} {α : ℝ≥0}

/-- **Local Hölder bound after a change of variables and a field of linear maps.** Let
`f ∈ C^{k,α}(Ω, F)` for an open set `Ω`, let `τ` be a `C^{k+1}` map from an open set `N` into `Ω`,
and let `Φ` be a `C^{k+1}` field of linear maps from `F` to `G` on `N`. For `α ≤ 1`, the `k`-th
derivative of `z ↦ Φ z (f (τ z))` is `α`-Hölder on a ball inside `N` around every point of `N`. -/
theorem exists_holderOnWith_iteratedFDeriv_clm_apply_comp {Ω : Opens E}
    (f : CkHolderSpaceOn k α Ω F) {N : Set E'} (hN : IsOpen N) {τ : E' → E}
    {Φ : E' → F →L[ℝ] G} (hτ : ContDiffOn ℝ (k + 1) τ N) (hΦ : ContDiffOn ℝ (k + 1) Φ N)
    (hτN : MapsTo τ N Ω) (hα : α ≤ 1) {y : E'} (hy : y ∈ N) :
    ∃ r > 0, Metric.ball y r ⊆ N ∧ ∃ L : ℝ≥0,
      HolderOnWith L α (_root_.iteratedFDeriv ℝ k fun z ↦ Φ z (f.extend (τ z)))
        (Metric.ball y r) := by
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ k + 1 := by exact_mod_cast le_self_add
  -- The `k`-th derivative of `f ∘ τ` is Hölder on a ball, by the Hölder chain rule.
  have hH : HolderOnWith _ α (iteratedFDerivWithin ℝ k f.extend Ω) Ω := fun a ha b hb ↦ by
    rw [iteratedFDerivWithin_of_isOpen k Ω.isOpen ha, iteratedFDerivWithin_of_isOpen k Ω.isOpen hb]
    exact f.holderOnWith_iteratedFDeriv_extend a ha b hb
  obtain ⟨r₁, hr₁, L₁, hL₁⟩ := exists_holderOnWith_iteratedFDerivWithin_comp hα
    (hN.mem_nhds hy) Ω.isOpen.uniqueDiffOn hτ f.contDiffOn_extend hτN self_mem_nhdsWithin hH
  -- The `k`-th derivative of `Φ` is `C¹`, hence Hölder on a ball.
  obtain ⟨r₂, hr₂, L₂, hL₂⟩ := (((hΦ.contDiffAt (hN.mem_nhds hy)).iteratedFDeriv_right
    (m := 1) (i := k) (by rw [add_comm])).isBigO_sub_dist_rpow one_ne_zero
      hα).exists_holderOnWith_ball
  obtain ⟨r₃, hr₃, hr₃N⟩ := Metric.isOpen_iff.1 hN _ hy
  set ρ := min r₁ (min r₂ r₃)
  have hρ₁ : Metric.ball y ρ ⊆ Metric.ball y r₁ := Metric.ball_subset_ball (min_le_left _ _)
  have hρ₂ : Metric.ball y ρ ⊆ Metric.ball y r₂ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hρN : Metric.ball y ρ ⊆ N :=
    (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hr₃N
  have hGH : HolderOnWith L₁ α (_root_.iteratedFDeriv ℝ k (f.extend ∘ τ)) (Metric.ball y ρ) :=
    fun a ha b hb ↦ by
      rw [← iteratedFDerivWithin_of_isOpen k hN (hρN ha),
        ← iteratedFDerivWithin_of_isOpen k hN (hρN hb)]
      exact hL₁ a (hρ₁ ha) b (hρ₁ hb)
  -- The Leibniz rule multiplies the two.
  obtain ⟨r, hr, hrρ, -, K, hK⟩ := ContinuousLinearMap.exists_holderOnWith_iteratedFDeriv_comp₂
    (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) (Metric.ball_mem_nhds _ (lt_min hr₁ (lt_min hr₂ hr₃)))
    hα ((hΦ.of_le hk).mono hρN) ((f.contDiffOn_extend.comp (hτ.of_le hk) hτN).mono hρN)
    (hL₂.mono hρ₂) hGH
  exact ⟨r, hr, hrρ.trans hρN, K, hK⟩

end CkHolderSpaceOn

end TauCeti
