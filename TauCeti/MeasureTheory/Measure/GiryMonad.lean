/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Order and finite-additivity properties of the Giry monad

This file adds monotonicity, binary and finite-sum additivity in the mixing measure, and a
singleton lower bound for `MeasureTheory.Measure.join` and `MeasureTheory.Measure.bind`. Since
composition `κ ∘ₘ μ` of a kernel with a measure is `μ.bind κ`, these lemmas apply directly to
kernel pushforwards of measures as well.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `Measure.join` is monotone in the measure on measures. -/
@[gcongr]
theorem join_mono {m₁ m₂ : Measure (Measure α)} (h : m₁ ≤ m₂) : m₁.join ≤ m₂.join :=
  le_iff.2 fun _ hs => by
    rw [join_apply hs, join_apply hs]
    exact lintegral_mono' h le_rfl

/-- `Measure.join` distributes over binary addition of measures. -/
@[simp]
theorem join_add (m₁ m₂ : Measure (Measure α)) : (m₁ + m₂).join = m₁.join + m₂.join := by
  ext s hs
  simp [hs]

/-- `Measure.bind` is monotone in both the mixing measure and the kernel family. -/
theorem bind_mono {μ ν : Measure α} {f g : α → Measure β} (hμν : μ ≤ ν)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    μ.bind f ≤ ν.bind g :=
  le_iff.2 fun s hs => by
    rw [bind_apply hs hf, bind_apply hs hg]
    exact (lintegral_mono_ae (hfg.mono fun _ hx => hx s)).trans (lintegral_mono' hμν le_rfl)

/-- `Measure.bind` is monotone in the mixing measure. -/
theorem bind_mono_left {μ ν : Measure α} {f : α → Measure β} (hf : AEMeasurable f ν) (h : μ ≤ ν) :
    μ.bind f ≤ ν.bind f :=
  bind_mono h (Filter.Eventually.of_forall fun _ => le_rfl) (hf.mono_measure h) hf

/-- `Measure.bind` distributes over binary addition in the mixing measure. -/
theorem bind_add {μ ν : Measure α} {f : α → Measure β} (hf : AEMeasurable f (μ + ν)) :
    (μ + ν).bind f = μ.bind f + ν.bind f := by
  ext s hs
  rw [bind_apply hs hf, add_apply,
    bind_apply hs (hf.mono_measure (Measure.le_add_right le_rfl)),
    bind_apply hs (hf.mono_measure (Measure.le_add_left le_rfl)), lintegral_add_measure]

/-- `Measure.bind` distributes over `Finset` sums in the mixing measure. -/
theorem bind_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure α) {f : α → Measure β}
    (hf : AEMeasurable f (∑ i ∈ s, μ i)) :
    (∑ i ∈ s, μ i).bind f = ∑ i ∈ s, (μ i).bind f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hf ⊢
    rw [bind_add hf, ih (hf.mono_measure (Measure.le_add_left le_rfl)), Finset.sum_insert ha]

/-- **Singleton lower bound for `Measure.bind`.** Restricting the mixture integral to a single
input point `x` bounds `(μ.bind f) s` below by `μ {x} * f x s`. -/
theorem singleton_mul_apply_le_bind_apply (μ : Measure α) {f : α → Measure β} (hf : Measurable f)
    (x : α) {s : Set β} (hs : MeasurableSet s) :
    μ {x} * f x s ≤ (μ.bind f) s := by
  have hfs : Measurable fun a => f a s := (measurable_coe hs).comp hf
  rw [bind_apply hs hf.aemeasurable, mul_comm, ← lintegral_singleton' hfs]
  exact setLIntegral_le_lintegral _ _

end MeasureTheory.Measure
