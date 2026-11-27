/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.MeasureTheory.Constructions.EuclideanSpace

/-!
# Maps that are locally Lipschitz off a point are `ACL`

In dimension `n ≥ 2`, a map `u : ℝⁿ → F` continuous on `Ω` and locally Lipschitz on `Ω ∖ {c}` is
`ACL` on `Ω` (`LocallyLipschitzOn.isACLOn_of_diff_singleton`). The coordinate lines in the `i`-th
direction through `c` form the line `c + ℝ eᵢ`, a null set since `n ≥ 2`
(`EuclideanSpace.volume_setOf_forall_ne_eq_zero`); every other coordinate segment of a closed box
in `Ω` is a compact subset of `Ω ∖ {c}`, on which `u` is Lipschitz, so its line function is
absolutely continuous. In particular a map continuous on an open set `Ω` and `C¹` on `Ω ∖ {c}` is
`ACL` on `Ω`. This covers radial maps such as `x ↦ |x|^a`, `a > 0`, which are not locally
Lipschitz at the origin for `a < 1`.

## Main results

* `LocallyLipschitzOn.isACLOn_of_diff_singleton`: continuity on `Ω` and local Lipschitzness on
  `Ω ∖ {c}` give `ACL` on `Ω`, for `n ≥ 2`.
* `TauCeti.isACLOn_of_contDiffOn_diff_singleton`: continuity on an open `Ω` and `C¹` regularity on
  `Ω ∖ {c}` give `ACL` on `Ω`, for `n ≥ 2`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {c : EuclideanSpace ℝ (Fin n)}

omit [NormedSpace ℝ F] in
/-- **Maps that are locally Lipschitz off a point are `ACL`.** In dimension at least `2`, a map
continuous on `Ω` and locally Lipschitz on `Ω ∖ {c}` is `ACL` on `Ω`. -/
theorem _root_.LocallyLipschitzOn.isACLOn_of_diff_singleton (hn : 2 ≤ n)
    (hcont : ContinuousOn u Ω) (hu : LocallyLipschitzOn (Ω \ {c}) u) : IsACLOn u Ω where
  continuousOn := hcont
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    have := Fin.nontrivial_iff_two_le.2 hn
    have hnull : ∀ᵐ x ∂volume.restrict (coordinateBox a b),
        x ∉ {x : EuclideanSpace ℝ (Fin n) | ∀ j, j ≠ i → x j = c j} :=
      ae_restrict_of_ae
        (measure_eq_zero_iff_ae_notMem.1 (EuclideanSpace.volume_setOf_forall_ne_eq_zero c i))
    filter_upwards [ae_restrict_mem (measurableSet_coordinateBox a b), hnull] with x hx hxA
    simp only [not_forall] at hxA
    obtain ⟨j, hji, hxj⟩ := hxA
    let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t ↦ x + (t - x i) • EuclideanSpace.single i 1
    have hS : γ '' Icc (a i) (b i) ⊆ Ω \ {c} := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨hQ (add_sub_smul_single_mem_coordinateBox hx ht), fun hc ↦ hxj ?_⟩
      have := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) hc
      simpa [γ, hji] using this
    obtain ⟨C, hC⟩ := (hu.mono hS).exists_lipschitzOnWith_of_compact
      (isCompact_Icc.image (EuclideanSpace.lipschitzWith_add_sub_smul_single x i).continuous)
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := C) ?_
    simpa [uIcc_of_le (hab i).le] using hC.lineFunction fun t ht ↦ mem_image_of_mem γ ht

/-- **Maps that are `C¹` off a point are `ACL`.** In dimension at least `2`, a map continuous on an
open set `Ω` and `C¹` on `Ω ∖ {c}` is `ACL` on `Ω`. -/
theorem isACLOn_of_contDiffOn_diff_singleton (hn : 2 ≤ n) (hΩ : IsOpen Ω)
    (hcont : ContinuousOn u Ω) (hd : ContDiffOn ℝ 1 u (Ω \ {c})) : IsACLOn u Ω :=
  (hd.locallyLipschitzOn_of_isOpen (hΩ.sdiff isClosed_singleton)).isACLOn_of_diff_singleton hn hcont

end TauCeti
