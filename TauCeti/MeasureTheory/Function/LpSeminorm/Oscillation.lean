/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# `Lᵖ` oscillation on a preconnected space from local oscillation

Let `μ` be a finite measure on a preconnected space `X` that charges every nonempty open set, and
let `V i`, `i ∈ t`, be finitely many open sets covering `X`. Suppose a function `f` deviates little
from some constant on each `V i`: `‖f - a i‖_{Lᵖ(V i)} ≤ C i * G`. Then `f` deviates little from a
single constant on all of `X`: `‖f - c‖_{Lᵖ(X)} ≤ K * G`, where the constant `K` depends only on
the cover, the measure, `p` and the local constants `C i`, and not on `f`, the local constants
`a i` or the bound `G` (`TauCeti.exists_eLpNorm_sub_const_le_of_isOpen_cover`).

This is the chaining step that turns a local Poincaré inequality into a global one on a connected
domain or a closed connected manifold. On the overlap of two pieces both local constants
approximate `f`, so they differ by at most a fixed multiple of `G`, because the overlap is a
nonempty open set and so has positive measure. Connectedness joins every piece to a fixed one by
a chain of overlapping pieces, and there are finitely many pieces.

Connectedness cannot be dropped: on a disjoint union of two open sets the function equal to `0`
on one and `1` on the other is constant on each piece but not close to any single constant.

## Main results

* `TauCeti.enorm_sub_le_div_of_eLpNorm_restrict_sub_le`: two constants approximating `f` in `Lᵖ`
  on overlapping sets are close.
* `TauCeti.exists_eLpNorm_sub_const_le_of_isOpen_cover`: local `Lᵖ` closeness to constants on a
  finite open cover of a preconnected space gives global closeness to one constant.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), §7.8.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X F : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F] {p : ℝ≥0∞}

omit [TopologicalSpace X] in
/-- **Constants approximating `f` on overlapping sets are close.** If `‖f - a‖_{Lᵖ(U)} ≤ A` and
`‖f - b‖_{Lᵖ(W)} ≤ B`, and the overlap `U ∩ W` has positive finite measure, then
`‖b - a‖ ≤ (A + B) / μ (U ∩ W) ^ (1 / p)`. -/
theorem enorm_sub_le_div_of_eLpNorm_restrict_sub_le (hp : 1 ≤ p) {U W : Set X}
    (h0 : μ (U ∩ W) ≠ 0) (htop : μ (U ∩ W) ≠ ∞) {f : X → F} {a b : F} {A B : ℝ≥0∞}
    (ha : eLpNorm (fun x ↦ f x - a) p (μ.restrict U) ≤ A)
    (hb : eLpNorm (fun x ↦ f x - b) p (μ.restrict W) ≤ B) :
    ‖b - a‖ₑ ≤ (A + B) / μ (U ∩ W) ^ (1 / p.toReal) := by
  have hm0 : μ (U ∩ W) ^ (1 / p.toReal) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) htop).ne'
  have hmtop : μ (U ∩ W) ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) htop
  rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)]
  have hconst : eLpNorm (fun _ ↦ b - a) p (μ.restrict (U ∩ W)) =
      ‖b - a‖ₑ * μ (U ∩ W) ^ (1 / p.toReal) := by
    rw [eLpNorm_const _ (zero_lt_one.trans_le hp).ne' (by simpa using h0),
      Measure.restrict_apply_univ]
  rw [← hconst]
  calc eLpNorm (fun _ ↦ b - a) p (μ.restrict (U ∩ W))
      = eLpNorm ((fun x ↦ f x - a) - fun x ↦ f x - b) p (μ.restrict (U ∩ W)) := by
        congr 1
        ext x
        simp
    _ ≤ eLpNorm (fun x ↦ f x - a) p (μ.restrict (U ∩ W)) +
          eLpNorm (fun x ↦ f x - b) p (μ.restrict (U ∩ W)) := eLpNorm_sub_le hp
    _ ≤ A + B := by
        gcongr
        · exact (eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_left le_rfl)).trans ha
        · exact (eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_right le_rfl)).trans hb

/-- **Local `Lᵖ` closeness to constants on a connected cover gives global closeness.** Let `μ` be
a finite measure on a preconnected space, positive on nonempty open sets, and let `V i`, `i ∈ t`,
be finitely many open sets covering the space. For constants `C i` there is a constant `K` such
that whenever `‖f - a i‖_{Lᵖ(V i)} ≤ C i * G` for every `i ∈ t`, some constant `c` satisfies
`‖f - c‖_{Lᵖ} ≤ K * G`. The constant `K` does not depend on `f`, `a` or `G`. -/
theorem exists_eLpNorm_sub_const_le_of_isOpen_cover [PreconnectedSpace X] [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hp : 1 ≤ p) {ι : Type*} (t : Finset ι) {V : ι → Set X}
    (hV : ∀ i ∈ t, IsOpen (V i)) (hcover : ∀ x, ∃ i ∈ t, x ∈ V i) (C : ι → ℝ≥0) :
    ∃ K : ℝ≥0, ∀ (f : X → F) (a : ι → F) (G : ℝ≥0∞),
      (∀ i ∈ t, eLpNorm (fun x ↦ f x - a i) p (μ.restrict (V i)) ≤ C i * G) →
      ∃ c : F, eLpNorm (fun x ↦ f x - c) p μ ≤ K * G := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, fun _ _ _ _ ↦ ⟨0, by simp [Measure.eq_zero_of_isEmpty μ]⟩⟩
  obtain ⟨i₀, hi₀, hx₀⟩ := hcover x₀
  -- The hypothesis on `(f, a, G)`, and the overlap relation between the pieces of the cover.
  let P : (X → F) → (ι → F) → ℝ≥0∞ → Prop := fun f a G ↦
    ∀ i ∈ t, eLpNorm (fun x ↦ f x - a i) p (μ.restrict (V i)) ≤ C i * G
  let R : ι → ι → Prop := fun i j ↦ i ∈ t ∧ j ∈ t ∧ (V i ∩ V j).Nonempty
  -- Constants on overlapping pieces are uniformly close.
  have hadj : ∀ i j, R i j → ∃ D : ℝ≥0, ∀ f a G, P f a G → ‖a j - a i‖ₑ ≤ D * G := by
    rintro i j ⟨hi, hj, hij⟩
    have h0 : μ (V i ∩ V j) ≠ 0 := ((hV i hi).inter (hV j hj)).measure_ne_zero μ hij
    refine ⟨((C i + C j : ℝ≥0∞) / μ (V i ∩ V j) ^ (1 / p.toReal)).toNNReal,
      fun f a G hP ↦ ?_⟩
    have hm0 : μ (V i ∩ V j) ^ (1 / p.toReal) ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) (measure_ne_top _ _)).ne'
    rw [ENNReal.coe_toNNReal (ENNReal.div_ne_top (by simp) hm0)]
    refine (enorm_sub_le_div_of_eLpNorm_restrict_sub_le hp h0 (measure_ne_top _ _) (hP i hi)
      (hP j hj)).trans_eq ?_
    rw [← add_mul, ENNReal.mul_div_right_comm]
  -- Constants on pieces joined by a chain of overlaps are uniformly close.
  have hchain : ∀ j, Relation.ReflTransGen R i₀ j →
      ∃ D : ℝ≥0, ∀ f a G, P f a G → ‖a j - a i₀‖ₑ ≤ D * G := by
    intro j hj
    induction hj with
    | refl => exact ⟨0, fun _ _ _ _ ↦ by simp⟩
    | @tail j k _ hjk ih =>
      obtain ⟨D₁, hD₁⟩ := ih
      obtain ⟨D₂, hD₂⟩ := hadj j k hjk
      refine ⟨D₂ + D₁, fun f a G hP ↦ ?_⟩
      calc ‖a k - a i₀‖ₑ = ‖(a k - a j) + (a j - a i₀)‖ₑ := by rw [sub_add_sub_cancel]
        _ ≤ ‖a k - a j‖ₑ + ‖a j - a i₀‖ₑ := enorm_add_le _ _
        _ ≤ D₂ * G + D₁ * G := add_le_add (hD₂ f a G hP) (hD₁ f a G hP)
        _ = ↑(D₂ + D₁) * G := by push_cast; ring
  -- Since the space is preconnected, every nonempty piece is joined to `V i₀` by such a chain.
  have hconn : ∀ j ∈ t, (V j).Nonempty → Relation.ReflTransGen R i₀ j := by
    intro j hj hVj
    have hU : IsPreconnected (⋃ k : t, V k) := by
      rw [eq_univ_of_forall fun x ↦ mem_iUnion.2 <| (hcover x).elim fun k hk ↦ ⟨⟨k, hk.1⟩, hk.2⟩]
      exact isPreconnected_univ
    exact (hU.transGen_of_iUnion (fun k ↦ hV k k.2) ⟨i₀, hi₀⟩ ⟨j, hj⟩
      ⟨x₀, hx₀⟩ hVj).to_reflTransGen.lift Subtype.val (fun k l hkl ↦ ⟨k.2, l.2, hkl⟩)
  -- On each piece, `f` is uniformly close to the constant of `V i₀`.
  have hpiece : ∀ j ∈ t, ∃ D : ℝ≥0, ∀ f a G, P f a G →
      eLpNorm (fun x ↦ f x - a i₀) p (μ.restrict (V j)) ≤ D * G := by
    intro j hj
    rcases (V j).eq_empty_or_nonempty with hVj | hVj
    · exact ⟨0, fun _ _ _ _ ↦ by simp [hVj]⟩
    obtain ⟨D, hD⟩ := hchain j (hconn j hj hVj)
    have h0 : μ (V j) ≠ 0 := (hV j hj).measure_ne_zero μ hVj
    refine ⟨C j + D * (μ (V j) ^ (1 / p.toReal)).toNNReal, fun f a G hP ↦ ?_⟩
    have hconst : eLpNorm (fun _ ↦ a j - a i₀) p (μ.restrict (V j)) =
        ‖a j - a i₀‖ₑ * μ (V j) ^ (1 / p.toReal) := by
      rw [eLpNorm_const _ (zero_lt_one.trans_le hp).ne' (by simpa using h0),
        Measure.restrict_apply_univ]
    calc eLpNorm (fun x ↦ f x - a i₀) p (μ.restrict (V j))
        = eLpNorm ((fun x ↦ f x - a j) + fun _ ↦ a j - a i₀) p (μ.restrict (V j)) := by
          congr 1
          ext x
          simp
      _ ≤ eLpNorm (fun x ↦ f x - a j) p (μ.restrict (V j)) +
            eLpNorm (fun _ ↦ a j - a i₀) p (μ.restrict (V j)) := eLpNorm_add_le hp
      _ ≤ C j * G + D * G * μ (V j) ^ (1 / p.toReal) := by
          rw [hconst]
          gcongr
          · exact hP j hj
          · exact hD f a G hP
      _ = ↑(C j + D * (μ (V j) ^ (1 / p.toReal)).toNNReal) * G := by
          rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_toNNReal
            (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _))]
          ring
  choose! D hD using hpiece
  refine ⟨∑ j ∈ t, D j, fun f a G hP ↦ ⟨a i₀, ?_⟩⟩
  have hU : (⋃ j ∈ t, V j) = univ :=
    eq_univ_of_forall fun x ↦ by simpa only [mem_iUnion₂, exists_prop] using hcover x
  calc eLpNorm (fun x ↦ f x - a i₀) p μ
      = eLpNorm (fun x ↦ f x - a i₀) p (μ.restrict (⋃ j ∈ t, V j)) := by
        rw [hU, Measure.restrict_univ]
    _ ≤ ∑ j ∈ t, eLpNorm (fun x ↦ f x - a i₀) p (μ.restrict (V j)) :=
        eLpNorm_restrict_biUnion_finset_le _ hp t V
    _ ≤ ∑ j ∈ t, D j * G := Finset.sum_le_sum fun j hj ↦ hD j hj f a G hP
    _ = ↑(∑ j ∈ t, D j) * G := by push_cast; rw [Finset.sum_mul]

end TauCeti
