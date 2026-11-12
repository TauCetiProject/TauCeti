/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# Ergodic actions along equivariant maps

Let a group act on two measurable spaces `α` and `β`, and let `f : α → β` be equivariant. Then
ergodicity passes to factors: if the action on `(α, μ)` is ergodic, so is the action on
`(β, μ.map f)` (`ErgodicSMul.map`). When `f` is a measurable embedding the converse holds as
well: the pushforward is invariant, respectively ergodic, exactly when `μ` is
(`MeasurableEmbedding.smulInvariantMeasure_map_iff`, `MeasurableEmbedding.ergodicSMul_map_iff`).
This lets ergodicity of a law be checked on whichever of two equivariantly embedded carriers is
more convenient, for instance a structure and its coordinate array.

## Main results

* `ErgodicSMul.map` — the pushforward of an ergodic measure along a measurable equivariant map is
  ergodic;
* `MeasurableEmbedding.smulInvariantMeasure_map_iff` — along an equivariant measurable embedding,
  the pushforward is invariant exactly when the measure is;
* `MeasurableEmbedding.ergodicSMul_map_iff` — along an equivariant measurable embedding, the
  pushforward is ergodic exactly when the measure is.
-/

public section

open Filter MeasureTheory Set

variable {G α β : Type*} [SMul G α] [SMul G β] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {f : α → β}

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- Along an equivariant map, taking the preimage under `f` commutes with taking the preimage
under the action. -/
private theorem preimage_smul_preimage (hfg : ∀ (g : G) x, f (g • x) = g • f x) (g : G)
    (s : Set β) : (g • ·) ⁻¹' (f ⁻¹' s) = f ⁻¹' ((g • ·) ⁻¹' s) := by
  ext x
  simp [hfg]

/-- The defining zero-one property of ergodicity passes to the pushforward along a measurable
equivariant map: an almost invariant measurable set downstairs pulls back to one upstairs. -/
private theorem eventuallyEmptyOrUniv_map_of_ergodicSMul [ErgodicSMul G α μ] (hf : Measurable f)
    (hfg : ∀ (g : G) x, f (g • x) = g • f x) {s : Set β} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (g • ·) ⁻¹' s =ᵐ[μ.map f] s) : EventuallyEmptyOrUniv s (ae (μ.map f)) := by
  have hmp := hf.measurePreserving μ
  rw [← hmp.aeconst_preimage hs.nullMeasurableSet]
  refine aeconst_of_forall_preimage_smul_ae_eq G (hs.preimage hf).nullMeasurableSet fun g => ?_
  rw [preimage_smul_preimage hfg]
  exact hmp.quasiMeasurePreserving.preimage_ae_eq (hinv g)

/-- **Ergodicity passes to factors**: the pushforward of an ergodic measure along a measurable
equivariant map is ergodic. -/
theorem ErgodicSMul.map [MeasurableConstSMul G β] [ErgodicSMul G α μ] (hf : Measurable f)
    (hfg : ∀ (g : G) x, f (g • x) = g • f x) : ErgodicSMul G β (μ.map f) where
  toSMulInvariantMeasure := smulInvariantMeasure_map μ f hfg hf
  aeconst_of_forall_preimage_smul_ae_eq hs hinv :=
    eventuallyEmptyOrUniv_map_of_ergodicSMul hf hfg hs hinv

namespace MeasurableEmbedding

/-- **Invariance along an equivariant embedding**: the pushforward of a measure along an
equivariant measurable embedding is invariant exactly when the measure is. -/
theorem smulInvariantMeasure_map_iff (hf : MeasurableEmbedding f)
    (hfg : ∀ (g : G) x, f (g • x) = g • f x) :
    SMulInvariantMeasure G β (μ.map f) ↔ SMulInvariantMeasure G α μ := by
  refine ⟨fun h => ⟨fun g s hs => ?_⟩, fun h => ⟨fun g s hs => ?_⟩⟩
  · -- Write `s` as the preimage of its image, which is measurable.
    rw [← hf.injective.preimage_image s, preimage_smul_preimage hfg, ← hf.map_apply,
      ← hf.map_apply, h.measure_preimage_smul g (hf.measurableSet_image' hs)]
  · rw [hf.map_apply, hf.map_apply, ← preimage_smul_preimage hfg,
      h.measure_preimage_smul g (hf.measurable hs)]

/-- **Ergodicity along an equivariant embedding**: the pushforward of a measure along an
equivariant measurable embedding is ergodic exactly when the measure is. -/
theorem ergodicSMul_map_iff (hf : MeasurableEmbedding f)
    (hfg : ∀ (g : G) x, f (g • x) = g • f x) :
    ErgodicSMul G β (μ.map f) ↔ ErgodicSMul G α μ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine { toSMulInvariantMeasure := (hf.smulInvariantMeasure_map_iff hfg).1 inferInstance
             aeconst_of_forall_preimage_smul_ae_eq := fun {s} hs hinv => ?_ }
    -- An almost invariant set upstairs is the preimage of its image, which is almost invariant
    -- downstairs.
    have himage : ∀ g : G, (g • ·) ⁻¹' (f '' s) =ᵐ[μ.map f] f '' s := fun g => by
      have hg := hinv g
      rw [← hf.injective.preimage_image s, preimage_smul_preimage hfg] at hg
      exact hf.ae_map_iff.2 hg
    have := aeconst_of_forall_preimage_smul_ae_eq G (hf.measurableSet_image' hs).nullMeasurableSet
      himage
    rwa [← (hf.measurable.measurePreserving μ).aeconst_preimage
      (hf.measurableSet_image' hs).nullMeasurableSet, hf.injective.preimage_image] at this
  · exact { toSMulInvariantMeasure := (hf.smulInvariantMeasure_map_iff hfg).2 inferInstance
            aeconst_of_forall_preimage_smul_ae_eq := fun hs hinv =>
              eventuallyEmptyOrUniv_map_of_ergodicSMul hf.measurable hfg hs hinv }

end MeasurableEmbedding
