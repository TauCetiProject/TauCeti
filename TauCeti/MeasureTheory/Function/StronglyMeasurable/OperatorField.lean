/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Orbitwise measurability of operator fields

An operator field whose fixed-vector orbits are strongly measurable sends strongly measurable
vectors to strongly measurable vectors. The same holds almost everywhere, allowing a separate
exceptional set for each fixed vector. Finite strong measurability of the vector gives finite
strong measurability of its image for arbitrary measures: linear operators preserve zero.

Over a densely normed field, a strongly measurable operator field `G : S → E →L[𝕜] F` admits
measurable almost norming vectors: for every `c < 1` there is a strongly measurable, countably
valued `x : S → E` with `‖x s‖ ≤ 1` and `c ‖G s‖ ≤ ‖G s (x s)‖` for every `s`
(`MeasureTheory.StronglyMeasurable.exists_stronglyMeasurable_norming`). The open sets
`{T | c ‖T‖ < ‖T v‖}`, for `‖v‖ ≤ 1`, cover the nonzero operators in the separable range of `G`,
so countably many vectors `vₙ` suffice (`TopologicalSpace.isOpen_iUnion_countable`), and
`x s = v_{n(s)}` for the least `n(s)` with `c ‖G s‖ ≤ ‖G s v_{n(s)}‖`.

For composition of operator fields, apply the evaluation lemma as
`(hB x).clm_apply_of_forall hA` for each fixed vector `x`.
For finite-support conclusions it suffices that the right field has finitely strongly
measurable orbits. Neither completeness nor operator-norm measurability is needed. Addition
and scalar multiplication of orbits use the native strong-measurability arithmetic lemmas.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, Proposition 1.1.28, and §1.3, Proposition 1.3.1.
-/

public section

open MeasureTheory Set TopologicalSpace

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [NormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace MeasureTheory

/-- An orbitwise strongly measurable operator field applied to a strongly measurable vector
is strongly measurable. -/
theorem StronglyMeasurable.clm_apply_of_forall {u : S → E} (hu : StronglyMeasurable u)
    {A : S → E →L[𝕜] F} (hA : ∀ x, StronglyMeasurable (fun s ↦ A s x)) :
    StronglyMeasurable (fun s ↦ A s (u s)) :=
  hu.apply_of_forall_of_continuousAt hA (fun s ↦ (A s).continuous.continuousAt)

/-- Orbitwise a.e. strong measurability suffices for evaluating an operator field at an a.e.
strongly measurable vector; exceptional sets for the orbits may depend on the vector. -/
theorem AEStronglyMeasurable.clm_apply_of_forall {u : S → E} (hu : AEStronglyMeasurable u μ)
    {A : S → E →L[𝕜] F} (hA : ∀ x, AEStronglyMeasurable (fun s ↦ A s x) μ) :
    AEStronglyMeasurable (fun s ↦ A s (u s)) μ :=
  hu.apply_of_forall_of_continuousAt hA (.of_forall fun s ↦ (A s).continuous.continuousAt)

/-- An orbitwise strongly measurable field preserves finite strong measurability of vectors
for arbitrary measures. -/
theorem FinStronglyMeasurable.clm_apply_of_forall {u : S → E}
    (hu : FinStronglyMeasurable u μ)
    {A : S → E →L[𝕜] F} (hA : ∀ x, StronglyMeasurable (fun s ↦ A s x)) :
    FinStronglyMeasurable (fun s ↦ A s (u s)) μ :=
  hu.apply_of_forall_of_continuousAt hA (fun s ↦ (A s).continuous.continuousAt)
    (fun s ↦ (A s).map_zero)

/-- An orbitwise a.e. strongly measurable field preserves a.e. finite strong measurability
of vectors, without sigma-finiteness of the ambient measure. -/
theorem AEFinStronglyMeasurable.clm_apply_of_forall {u : S → E}
    (hu : AEFinStronglyMeasurable u μ)
    {A : S → E →L[𝕜] F} (hA : ∀ x, AEStronglyMeasurable (fun s ↦ A s x) μ) :
    AEFinStronglyMeasurable (fun s ↦ A s (u s)) μ :=
  hu.apply_of_forall_of_continuousAt hA (.of_forall fun s ↦ (A s).continuous.continuousAt)
    (.of_forall fun s ↦ (A s).map_zero)

section Norming

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Measurable norming vectors.** For a strongly measurable operator field
`G : S → E →L[𝕜] F` and `c < 1`, there is a strongly measurable, countably valued `x : S → E`
with `‖x s‖ ≤ 1` and `c ‖G s‖ ≤ ‖G s (x s)‖` for every `s`. -/
theorem StronglyMeasurable.exists_stronglyMeasurable_norming {G : S → E →L[𝕜] F}
    (hG : StronglyMeasurable G) {c : ℝ} (hc : c < 1) :
    ∃ x : S → E, StronglyMeasurable x ∧ (range x).Countable ∧ (∀ s, ‖x s‖ ≤ 1) ∧
      ∀ s, c * ‖G s‖ ≤ ‖G s (x s)‖ := by
  classical
  -- On the second-countable range of `G`, countably many unit-ball vectors `v` suffice to cover
  -- the open sets `{T | c ‖T‖ < ‖T v‖}`.
  have := hG.isSeparable_range.secondCountableTopology
  obtain ⟨V, hVc, hV⟩ := isOpen_iUnion_countable
    (fun v : Metric.closedBall (0 : E) 1 ↦ {T : range G | c * ‖(T : E →L[𝕜] F)‖ < ‖T.val v‖})
    fun v ↦ isOpen_lt (by fun_prop)
      (((continuous_eval_const (v : E)).comp continuous_subtypeVal).norm)
  obtain ⟨w, hw⟩ := (hVc.insert ⟨0, by simp⟩).exists_eq_range (insert_nonempty _ _)
  have hw1 : ∀ n, ‖(w n : E)‖ ≤ 1 := fun n ↦ mem_closedBall_zero_iff.1 (w n).property
  have hex : ∀ s, ∃ n, c * ‖G s‖ ≤ ‖G s (w n)‖ := by
    intro s
    rcases (norm_nonneg (G s)).eq_or_lt with h0 | hGs
    · exact ⟨0, by simp [← h0]⟩
    -- A nonzero `G s` is almost normed by some unit-ball vector, hence by one of the `w n`.
    obtain ⟨v, hv1, hv⟩ := (G s).exists_lt_apply_of_lt_opNorm (r := c * ‖G s‖) (by nlinarith)
    have hmem : (⟨G s, mem_range_self s⟩ : range G) ∈ ⋃ v : Metric.closedBall (0 : E) 1,
        {T : range G | c * ‖(T : E →L[𝕜] F)‖ < ‖T.val v‖} :=
      mem_iUnion.2 ⟨⟨v, by simpa using hv1.le⟩, hv⟩
    rw [← hV] at hmem
    obtain ⟨u, hu, hTu⟩ := mem_iUnion₂.1 hmem
    obtain ⟨n, hn⟩ : u ∈ range w := hw ▸ mem_insert_of_mem _ hu
    exact ⟨n, by rw [hn]; exact hTu.le⟩
  have hN : Measurable fun s ↦ Nat.find (hex s) :=
    measurable_find hex fun n ↦ _root_.measurableSet_le (measurable_const.mul hG.norm.measurable)
      ((continuous_eval_const (w n : E)).comp_stronglyMeasurable hG).norm.measurable
  -- Choose `x s = w n` for the least `n` with `c ‖G s‖ ≤ ‖G s (w n)‖`.
  exact ⟨fun s ↦ w (Nat.find (hex s)),
    (StronglyMeasurable.of_discrete (f := fun n : ℕ ↦ (w n : E))).comp_measurable hN,
    (countable_range fun n ↦ (w n : E)).mono (by rintro _ ⟨s, rfl⟩; exact mem_range_self _),
    fun s ↦ hw1 _, fun s ↦ Nat.find_spec (hex s)⟩

/-- **Measurable norming vectors, almost everywhere version.** For an almost everywhere strongly
measurable operator field `G : S → E →L[𝕜] F` and `c < 1`, there is a strongly measurable,
countably valued `x : S → E` with `‖x s‖ ≤ 1` for every `s` and `c ‖G s‖ ≤ ‖G s (x s)‖` for almost
every `s`. -/
theorem AEStronglyMeasurable.exists_stronglyMeasurable_norming {G : S → E →L[𝕜] F}
    (hG : AEStronglyMeasurable G μ) {c : ℝ} (hc : c < 1) :
    ∃ x : S → E, StronglyMeasurable x ∧ (range x).Countable ∧ (∀ s, ‖x s‖ ≤ 1) ∧
      ∀ᵐ s ∂μ, c * ‖G s‖ ≤ ‖G s (x s)‖ := by
  obtain ⟨x, hx, hxc, hx1, hxG⟩ := hG.stronglyMeasurable_mk.exists_stronglyMeasurable_norming hc
  exact ⟨x, hx, hxc, hx1, hG.ae_eq_mk.mono fun s hs ↦ by rw [hs]; exact hxG s⟩

end Norming

end MeasureTheory
