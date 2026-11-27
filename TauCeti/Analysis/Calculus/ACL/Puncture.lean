/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Maps that are `C¹` off the origin are `ACL`

In dimension `n ≥ 2`, a map `u : ℝⁿ → F` continuous on an open set `Ω` and `C¹` on `Ω ∖ {0}` is
`ACL` on `Ω` (`TauCeti.isACLOn_of_contDiffOn_diff_singleton`). The coordinate lines in the `i`-th
direction through the origin form the axis `ℝ eᵢ`, a null set since `n ≥ 2`; every other coordinate
segment of a closed box in `Ω` is a compact subset of `Ω ∖ {0}`, on which `u` is Lipschitz, so its
line function is absolutely continuous. This covers radial maps such as `x ↦ |x|^a`, `a > 0`,
which are not locally Lipschitz at the origin for `a < 1`.

## Main results

* `TauCeti.isACLOn_of_contDiffOn_diff_singleton`: continuity on `Ω` and `C¹` regularity on
  `Ω ∖ {0}` give `ACL` on `Ω`, for `n ≥ 2`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- In dimension at least `2`, the points `x` whose coordinate line in the `i`-th direction passes
through the origin, those with `x j = 0` for every `j ≠ i`, form a null set. -/
theorem volume_setOf_forall_ne_eq_zero (hn : 2 ≤ n) (i : Fin n) :
    volume {x : EuclideanSpace ℝ (Fin n) | ∀ j, j ≠ i → x j = 0} = 0 := by
  obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i := by
    by_contra! h
    have : Fintype.card (Fin n) ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ (h a).trans (h b).symm
    simp only [Fintype.card_fin] at this
    omega
  let s : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := ℝ ∙ EuclideanSpace.single i 1
  have hsub : {x : EuclideanSpace ℝ (Fin n) | ∀ j, j ≠ i → x j = 0} ⊆ s := by
    intro x hx
    refine Submodule.mem_span_singleton.2 ⟨x i, ?_⟩
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, hx k hk]
  have hs : s ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℝ) ∈ s := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) hc
    simp [hji] at this
  exact measure_mono_null hsub (Measure.addHaar_submodule volume s hs)

/-- **Maps that are `C¹` off the origin are `ACL`.** In dimension at least `2`, a map continuous
on an open set `Ω` and `C¹` on `Ω ∖ {0}` is `ACL` on `Ω`. -/
theorem isACLOn_of_contDiffOn_diff_singleton (hn : 2 ≤ n) (hΩ : IsOpen Ω)
    (hc : ContinuousOn u Ω) (hd : ContDiffOn ℝ 1 u (Ω \ {0})) : IsACLOn u Ω where
  continuousOn := hc
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    have hL : LocallyLipschitzOn (Ω \ {0}) u :=
      hd.locallyLipschitzOn_of_isOpen (hΩ.sdiff isClosed_singleton)
    have hnull : ∀ᵐ x ∂volume.restrict (coordinateBox a b),
        x ∉ {x : EuclideanSpace ℝ (Fin n) | ∀ j, j ≠ i → x j = 0} :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (volume_setOf_forall_ne_eq_zero hn i))
    filter_upwards [ae_restrict_mem (measurableSet_coordinateBox a b), hnull] with x hx hxA
    simp only [not_forall] at hxA
    obtain ⟨j, hji, hxj⟩ := hxA
    let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t ↦ x + (t - x i) • EuclideanSpace.single i 1
    have hγ : LipschitzWith 1 γ := EuclideanSpace.lipschitzWith_add_sub_smul_single x i
    have hS : γ '' Icc (a i) (b i) ⊆ Ω \ {0} := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨hQ (add_sub_smul_single_mem_coordinateBox hx ht), fun h0 ↦ hxj ?_⟩
      have := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) h0
      simpa [γ, hji] using this
    obtain ⟨C, hC⟩ := (hL.mono hS).exists_lipschitzOnWith_of_compact
      (isCompact_Icc.image hγ.continuous)
    have h := hC.comp hγ.lipschitzOnWith (mapsTo_image γ (Icc (a i) (b i)))
    rw [mul_one] at h
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := C) ?_
    rw [uIcc_of_le (hab i).le]
    exact (show u ∘ γ = lineFunction u x i from
      funext fun t ↦ (lineFunction_apply u x i t).symm) ▸ h

end TauCeti
