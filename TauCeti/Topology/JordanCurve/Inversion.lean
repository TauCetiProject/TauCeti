/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import TauCeti.Topology.JordanCurve.OnePoint
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Inverting a closed line into a Jordan curve

The inversion `z ↦ (z - p)⁻¹` about a point `p` of a division ring is a bijection (it sends `p`
to `0` because `0⁻¹ = 0`), inverted by `w ↦ w⁻¹ + p`.  It is not continuous at `p`, but it is
continuous on any set omitting `p`.

In `ℂ`, a closed subset `C` homeomorphic to the real line has both ends at infinity, so inverting
it about a point off `C` and adjoining `0`, the image of the point at infinity, gives a Jordan
curve.

## Main results

* `TauCeti.injective_inv_sub`, `TauCeti.bijOn_inv_add_image_inv_sub`: the inversion about `p` is
  injective, inverted on its image by `w ↦ w⁻¹ + p`.
* `TauCeti.continuousOn_inv_sub`: the inversion about `p` is continuous on any set omitting `p`.
* `TauCeti.isJordanCurve_insert_zero_image_inv_sub`: a closed copy of the real line in `ℂ`,
  inverted about a point off it and completed by `0`, is a Jordan curve.
-/

public section

open Bornology Filter Function Set Topology

namespace TauCeti

section DivisionRing

variable {K : Type*} [DivisionRing K] {p : K}

/-- The inversion about `p` is injective. -/
theorem injective_inv_sub : Injective fun z : K => (z - p)⁻¹ :=
  fun _ _ h => sub_left_injective (inv_injective h)

/-- The inversion about `p` is inverted by `w ↦ w⁻¹ + p`, so it maps any set `S` bijectively onto
its image with that inverse. -/
theorem bijOn_inv_add_image_inv_sub (S : Set K) :
    BijOn (fun w : K => w⁻¹ + p) ((fun z : K => (z - p)⁻¹) '' S) S :=
  injective_inv_sub.injOn.bijOn_image.symm ⟨fun _ _ => by simp, fun _ _ => by simp⟩

/-- The inversion about `p` vanishes only at `p`. -/
theorem zero_notMem_image_inv_sub {S : Set K} (hp : p ∉ S) :
    (0 : K) ∉ (fun z : K => (z - p)⁻¹) '' S := by
  rintro ⟨z, hz, hz0⟩
  rw [inv_eq_zero, sub_eq_zero] at hz0
  exact hp (hz0 ▸ hz)

/-- The inversion about `p` is continuous on any set omitting `p`. -/
theorem continuousOn_inv_sub [TopologicalSpace K] [IsTopologicalDivisionRing K] {S : Set K}
    (hp : p ∉ S) : ContinuousOn (fun z : K => (z - p)⁻¹) S := fun _ hz =>
  ((continuous_sub_right p).continuousAt.inv₀
    (sub_ne_zero.2 fun h => hp (h ▸ hz))).continuousWithinAt

end DivisionRing

/-- **A line through infinity, inverted, is a Jordan curve.**  If `C` is a closed subset of `ℂ`
homeomorphic to the real line and `p ∉ C`, then the image of `C` under the inversion about `p`,
completed by `0`, is a Jordan curve: the homeomorphism is proper, so both ends of the line tend to
infinity, and inverting sends them both to `0`. -/
theorem isJordanCurve_insert_zero_image_inv_sub {p : ℂ} {C : Set ℂ} (hC : IsClosed C)
    (e : C ≃ₜ ℝ) (hp : p ∉ C) : IsJordanCurve (insert 0 ((fun z : ℂ => (z - p)⁻¹) '' C)) := by
  let Φ : OnePoint ℝ → ℂ := fun x => x.elim 0 fun t => ((e.symm t : ℂ) - p)⁻¹
  have hemb : IsClosedEmbedding fun t => (e.symm t : ℂ) :=
    hC.isClosedEmbedding_subtypeVal.comp e.symm.isClosedEmbedding
  have hΦ : Continuous Φ := by
    refine (OnePoint.continuous_iff Φ).2 ⟨?_, ?_⟩
    · rw [coclosedCompact_eq_cocompact]
      exact tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded p).comp
        (Metric.cobounded_eq_cocompact (α := ℂ) ▸ hemb.tendsto_cocompact))
    · exact (continuousOn_inv_sub hp).comp_continuous hemb.continuous fun t => (e.symm t).2
  have hΦi : Injective Φ := by
    have hne (t : ℝ) : ((e.symm t : ℂ) - p)⁻¹ ≠ 0 :=
      inv_ne_zero (sub_ne_zero.2 fun h => hp (h ▸ (e.symm t).2))
    rintro (_ | s) (_ | t) h
    · rfl
    · exact absurd h.symm (hne t)
    · exact absurd h (hne s)
    · exact congrArg _ (e.symm.injective (Subtype.ext (injective_inv_sub h)))
  convert isJordanCurve_univ_onePoint_real.image hΦ.continuousOn hΦi.injOn using 1
  ext w
  simp only [mem_insert_iff, mem_image, mem_univ, true_and, OnePoint.exists]
  refine or_congr (eq_comm.trans (by rfl)) ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e ⟨z, hz⟩, by simp [Φ]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, (e.symm t).2, rfl⟩

end TauCeti
