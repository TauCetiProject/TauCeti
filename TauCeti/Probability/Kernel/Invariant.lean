/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Invariance of conditional laws

If a measure-preserving map fixes every event of a conditioning σ-algebra up to null sets, then
almost every conditional law is invariant under that map. This is the invariance step in
decomposing a probability law into invariant components. The conditioning σ-algebra need not be
countably generated, nor contained in the ambient σ-algebra; standard Borelness is required only of
the space carrying the conditional laws.

## Implementation notes

The proof uses Mathlib's kernel uniqueness (`Kernel.ae_eq_of_compProd_eq`): pushing forward
the second coordinate of the conditional joint law leaves its values on rectangles unchanged.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The case of `map_condExpKernel_ae_eq_of_invariant` where `m` is a sub-σ-algebra. -/
private theorem map_condExpKernel_ae_eq_of_invariant_of_le
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hinv : ∀ s, MeasurableSet[m] s → T ⁻¹' s =ᵐ[μ] s) :
    ∀ᵐ x ∂μ, (condExpKernel μ m x).map T = condExpKernel μ m x := by
  have hid : @Measurable Ω Ω mΩ m id := measurable_id'' hm
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    hid.prodMk measurable_id
  have hpair : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) (fun x => (x, T x)) :=
    hid.prodMk hT.measurable
  have hjoint :
      @Measure.map (Ω × Ω) (Ω × Ω) (m.prod mΩ) (m.prod mΩ) (Prod.map id T)
        (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) =
        @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ := by
    rw [Measure.map_map (measurable_id.prodMap hT.measurable) hdiag]
    simp only [Function.comp_def, Function.diag_apply, Prod.map_apply, id_eq]
    refine Measure.ext_prod fun {s t} hs ht ↦ ?_
    rw [Measure.map_apply hpair (hs.prod ht), Measure.map_apply hdiag (hs.prod ht),
      Set.mk_preimage_prod, Set.preimage_id', Set.diag_preimage_prod,
      measure_congr ((hinv s hs).symm.inter .rfl),
      ← Set.preimage_inter, hT.measure_preimage ((hm s hs).inter ht).nullMeasurableSet]
  have hcomp : (μ.trim hm) ⊗ₘ (condExpKernel μ m).map T =
      (μ.trim hm) ⊗ₘ condExpKernel μ m := by
    rw [Measure.compProd_map hT.measurable, compProd_trim_condExpKernel hm, hjoint]
  simpa only [Kernel.map_apply _ hT.measurable] using
    ae_of_ae_trim hm (Kernel.ae_eq_of_compProd_eq hcomp)

/-- Conditioning on events fixed almost surely by a measure-preserving transformation gives
conditional laws that are almost surely invariant under that transformation. -/
theorem map_condExpKernel_ae_eq_of_invariant
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hinv : ∀ s, MeasurableSet[m] s → T ⁻¹' s =ᵐ[μ] s) :
    ∀ᵐ x ∂μ, (condExpKernel μ m x).map T = condExpKernel μ m x := by
  rcases isEmpty_or_nonempty Ω with h | _
  · simp [Measure.eq_zero_of_isEmpty μ]
  -- `condExpKernel μ m` only depends on the sub-σ-algebra `m ⊓ mΩ`.
  have h := map_condExpKernel_ae_eq_of_invariant_of_le (m := m ⊓ mΩ) inf_le_right hT
    fun s hs ↦ hinv s (MeasurableSpace.measurableSet_inf.1 hs).1
  simp only [condExpKernel_apply_eq_condDistrib] at h ⊢
  rwa [inf_right_idem] at h

end TauCeti.Probability
