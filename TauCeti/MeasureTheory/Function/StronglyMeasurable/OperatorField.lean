/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Orbitwise measurability of operator fields

An operator field whose fixed-vector orbits are strongly measurable sends strongly measurable
vectors to strongly measurable vectors. The same holds almost everywhere, allowing a separate
exceptional set for each fixed vector. Finite strong measurability of the vector gives finite
strong measurability of its image for arbitrary measures: linear operators preserve zero.

Over a densely normed field, a strongly measurable operator field `G : S → E →L[𝕜] F` admits
measurable almost norming vectors: for every `c < 1` there is a strongly measurable, countably
valued `x : S → E` with `‖x s‖ ≤ 1` and `c ‖G s‖ ≤ ‖G s (x s)‖` for every `s`
(`MeasureTheory.StronglyMeasurable.exists_stronglyMeasurable_norming`). The construction fixes a
countable dense subset `{yₙ}` of the range of `G` together with `0`, a norming vector `vₙ` for
each `yₙ`, and sets `x s = v_{n(s)}` for the least `n(s)` such that `yₙ` is relatively close to
`G s`.

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
    (countable_range fun n ↦ v (y n)).mono (by rintro _ ⟨s, rfl⟩; exact mem_range_self _),
    fun s ↦ hv1 _, fun s ↦ ?_⟩
  calc c * ‖G s‖ ≤ (c' - 2 * δ) * ‖G s‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simp only [c', δ, m]
        linarith [le_max_left c 0]
    _ ≤ _ := ContinuousLinearMap.mul_norm_le_norm_apply_of_norm_sub_le (by simp only [c']; linarith)
        (by simp only [c']; linarith) hδ.le (hv1 _) (hv _) (Nat.find_spec (hex s))

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
