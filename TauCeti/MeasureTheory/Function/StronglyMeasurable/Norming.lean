/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Measurable norming vectors for operator-valued functions

Over a densely normed field, every bounded linear map `T : E →L[𝕜] F` and every `c < 1` admit a
vector `x` of norm at most one with `c ‖T‖ ≤ ‖T x‖`. This file chooses such vectors measurably
along a strongly measurable operator field `G : S → E →L[𝕜] F`: there is a strongly measurable,
countably valued `x : S → E` with `‖x s‖ ≤ 1` and `c ‖G s‖ ≤ ‖G s (x s)‖` for every `s`.

Consequently the `Lʳ` norm of an almost everywhere strongly measurable operator field is the
supremum of the `Lʳ` norms of `s ↦ G s (x s)` over strongly measurable fields `x` of vectors of
norm at most one (`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_eLpNorm_apply_le`).

Taking `F` to be the scalar field, this chooses almost norming vectors for a strongly measurable
family of functionals. Through the isometric embedding of a normed space into its bidual, it also
chooses almost norming functionals for a strongly measurable vector-valued function. These are the
pointwise test functions used to compute the norm of the integral pairing between Bochner spaces
`Lᵖ(μ; X)` and `L^q(μ; X⋆)`.

The construction follows the separable-range argument for strongly measurable functions: fix a
countable dense subset `{yₙ}` of the range of `G` together with `0`, a norming vector `vₙ` for each
`yₙ`, and set `x s = v_{n(s)}` for the least `n(s)` such that `yₙ` is relatively close to `G s`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Proposition 1.3.1.
-/

public section

open Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A vector `v` of norm at most one on which `T` has ratio `c ∈ [0, 1]` is almost norming for
every `G` relatively close to `T`: if `‖G - T‖ ≤ δ ‖G‖`, then `(c - 2 δ) ‖G‖ ≤ ‖G v‖`. -/
private theorem mul_norm_le_norm_apply_of_norm_sub_le {G T : E →L[𝕜] F} {v : E} {c δ : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hδ : 0 ≤ δ) (hv1 : ‖v‖ ≤ 1) (hTv : c * ‖T‖ ≤ ‖T v‖)
    (hGT : ‖G - T‖ ≤ δ * ‖G‖) :
    (c - 2 * δ) * ‖G‖ ≤ ‖G v‖ := by
  have hT : ‖G‖ - ‖G - T‖ ≤ ‖T‖ := by simpa using norm_sub_norm_le G (G - T)
  have hdiff : ‖(G - T) v‖ ≤ ‖G - T‖ :=
    ((G - T).le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv1)
  have happly : ‖T v‖ ≤ ‖G v‖ + ‖(G - T) v‖ :=
    calc ‖T v‖ = ‖G v - (G - T) v‖ := by simp
      _ ≤ ‖G v‖ + ‖(G - T) v‖ := norm_sub_le _ _
  have hG := norm_nonneg G
  calc (c - 2 * δ) * ‖G‖ ≤ c * ‖G‖ - (c + 1) * (δ * ‖G‖) := by
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hc1) hδ) hG]
    _ ≤ c * ‖G‖ - (c + 1) * ‖G - T‖ := by gcongr
    _ ≤ c * ‖T‖ - ‖G - T‖ := by nlinarith [mul_le_mul_of_nonneg_left hT hc0]
    _ ≤ ‖G v‖ := by linarith

/-- **Measurable norming vectors.** For a strongly measurable operator field
`G : S → E →L[𝕜] F` and `c < 1`, there is a strongly measurable `x : S → E` with `‖x s‖ ≤ 1` and
`c ‖G s‖ ≤ ‖G s (x s)‖` for every `s`. -/
theorem StronglyMeasurable.exists_stronglyMeasurable_norming {G : S → E →L[𝕜] F}
    (hG : StronglyMeasurable G) {c : ℝ} (hc : c < 1) :
    ∃ x : S → E, StronglyMeasurable x ∧ (∀ s, ‖x s‖ ≤ 1) ∧ ∀ s, c * ‖G s‖ ≤ ‖G s (x s)‖ := by
  classical
  -- Work with `m = max c 0 ∈ [0, 1)`, a norming ratio `c' = (1 + m) / 2` for each `yₙ` and a
  -- relative approximation error `δ = (1 - m) / 4`, so that `c' - 2 δ = m`.
  set m := max c 0
  have hm1 : m < 1 := max_lt hc one_pos
  have hm0 : 0 ≤ m := le_max_right c 0
  set c' := (1 + m) / 2
  set δ := (1 - m) / 4
  have hδ : 0 < δ := by simp only [δ]; linarith
  -- A norming vector of ratio `c'` for every single operator.
  have hnorming : ∀ T : E →L[𝕜] F, ∃ v : E, ‖v‖ ≤ 1 ∧ c' * ‖T‖ ≤ ‖T v‖ := by
    intro T
    rcases (norm_nonneg T).eq_or_lt with h0 | hpos
    · exact ⟨0, by simp, by simp [← h0]⟩
    · obtain ⟨v, hv1, hv⟩ := T.exists_lt_apply_of_lt_opNorm (r := c' * ‖T‖)
        (by simp only [c']; nlinarith)
      exact ⟨v, hv1.le, hv.le⟩
  choose v hv1 hv using hnorming
  -- A countable dense subset `range y` of `range G ∪ {0}`.
  obtain ⟨t, -, htc, hdense⟩ := hG.isSeparable_range.exists_countable_dense_subset
  obtain ⟨y, hy⟩ := (htc.insert 0).exists_eq_range (insert_nonempty 0 t)
  have hex : ∀ s, ∃ n, ‖G s - y n‖ ≤ δ * ‖G s‖ := by
    intro s
    rcases (norm_nonneg (G s)).eq_or_lt with h0 | hGs
    · obtain ⟨n, hn⟩ : (0 : E →L[𝕜] F) ∈ range y := hy ▸ mem_insert 0 t
      exact ⟨n, by simp [← h0, hn]⟩
    · obtain ⟨z, hz, hzs⟩ := Metric.mem_closure_iff.1 (hdense (mem_range_self s)) _
        (mul_pos hδ hGs)
      obtain ⟨n, rfl⟩ : z ∈ range y := hy ▸ mem_insert_of_mem 0 hz
      exact ⟨n, by rw [← dist_eq_norm]; exact hzs.le⟩
  have hN : Measurable fun s ↦ Nat.find (hex s) :=
    measurable_find hex fun n ↦ _root_.measurableSet_le
      (hG.sub stronglyMeasurable_const).norm.measurable (measurable_const.mul hG.norm.measurable)
  -- Choose `x s = v (y n)` for the least `n` with `y n` relatively close to `G s`.
  refine ⟨fun s ↦ v (y (Nat.find (hex s))),
    (StronglyMeasurable.of_discrete (f := fun n : ℕ ↦ v (y n))).comp_measurable hN,
    fun s ↦ hv1 _, fun s ↦ ?_⟩
  calc c * ‖G s‖ ≤ (c' - 2 * δ) * ‖G s‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simp only [c', δ, m]
        linarith [le_max_left c 0]
    _ ≤ _ := mul_norm_le_norm_apply_of_norm_sub_le (by simp only [c']; linarith)
        (by simp only [c']; linarith) hδ.le (hv1 _) (hv _) (Nat.find_spec (hex s))

/-- **Measurable norming vectors, almost everywhere version.** For an almost everywhere strongly
measurable operator field `G : S → E →L[𝕜] F` and `c < 1`, there is a strongly measurable
`x : S → E` with `‖x s‖ ≤ 1` for every `s` and `c ‖G s‖ ≤ ‖G s (x s)‖` for almost every `s`. -/
theorem AEStronglyMeasurable.exists_stronglyMeasurable_norming {G : S → E →L[𝕜] F}
    (hG : AEStronglyMeasurable G μ) {c : ℝ} (hc : c < 1) :
    ∃ x : S → E, StronglyMeasurable x ∧ (∀ s, ‖x s‖ ≤ 1) ∧
      ∀ᵐ s ∂μ, c * ‖G s‖ ≤ ‖G s (x s)‖ := by
  obtain ⟨x, hx, hx1, hxG⟩ := hG.stronglyMeasurable_mk.exists_stronglyMeasurable_norming hc
  exact ⟨x, hx, hx1, hG.ae_eq_mk.mono fun s hs ↦ by rw [hs]; exact hxG s⟩

/-- **Norming an operator field by measurable unit vector fields.** If the `Lʳ` norm of
`s ↦ G s (x s)` is at most `C` for every strongly measurable `x : S → E` with `‖x s‖ ≤ 1`, then
the `Lʳ` norm of the almost everywhere strongly measurable operator field `G` is at most `C`. -/
theorem AEStronglyMeasurable.eLpNorm_le_of_forall_eLpNorm_apply_le {G : S → E →L[𝕜] F}
    (hG : AEStronglyMeasurable G μ) {r C : ℝ≥0∞}
    (hC : ∀ x : S → E, StronglyMeasurable x → (∀ s, ‖x s‖ ≤ 1) →
      eLpNorm (fun s ↦ G s (x s)) r μ ≤ C) :
    eLpNorm G r μ ≤ C := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  have ha_top : a ≠ ∞ := ha.ne_top
  obtain ⟨x, hx, hx1, hGx⟩ := hG.exists_stronglyMeasurable_norming
    (ENNReal.toReal_lt_of_lt_ofReal (by simpa using ha))
  calc a * eLpNorm G r μ = eLpNorm (fun s ↦ a * ‖G s‖ₑ) r μ := by
        rw [eLpNorm_const_mul_ennreal hG.eNorm.aestronglyMeasurable, eLpNorm_eNorm G hG]
    _ ≤ eLpNorm (fun s ↦ G s (x s)) r μ := eLpNorm_mono_eNorm_ae
        (hG.eNorm.const_mul a).aestronglyMeasurable <| hGx.mono fun s hs ↦ by
        rw [eNorm_eq_self, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_toReal ha_top,
          ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        exact ENNReal.ofReal_le_ofReal hs
    _ ≤ C := hC x hx hx1

end MeasureTheory
