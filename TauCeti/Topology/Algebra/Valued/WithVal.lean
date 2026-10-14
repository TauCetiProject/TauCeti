/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Valuation-preserving isomorphisms are uniformly continuous

Let `σ : K ≃+* K'` be an isomorphism of fields carrying a valuation `v` on `K` to a valuation `w`
on `K'`, in the sense that `w (σ x) = v x`. Then `σ` is uniformly continuous for the uniform
structures that `v` and `w` define, so it extends to an isomorphism of the completions
`v.Completion ≃+* w.Completion` (`UniformSpace.Completion.mapRingEquiv`). This is how an
automorphism of a field fixing a place acts on the completion at that place.

## Main results

* `WithVal.uniformContinuous_congr`: if every value of `v` is attained, the map
  `WithVal.congr v w σ : WithVal v ≃+* WithVal w` is uniformly continuous.
-/

public section

open Filter WithZeroTopology

namespace WithVal

variable {K K' : Type*} [Field K] [Field K'] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {w : Valuation K' Γ₀}

/-- **A valuation-preserving isomorphism is uniformly continuous.** If `σ : K ≃+* K'` carries the
valuation `v` to `w`, and every value of `v` is attained, then `σ` is uniformly continuous as a
map `WithVal v → WithVal w`. -/
theorem uniformContinuous_congr (hv : Function.Surjective v) (σ : K ≃+* K')
    (hσ : ∀ x, w (σ x) = v x) : UniformContinuous (WithVal.congr v w σ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  -- the preimage of a valuation ball is the valuation ball of the same radius
  have hcont : Continuous (Valued.v : Valuation (WithVal v) Γ₀) :=
    Valued.continuous_valuation_of_surjective fun δ ↦
      let ⟨a, ha⟩ := hv δ
      ⟨toVal v a, ha⟩
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_injective).mpr γ.ne_zero
  filter_upwards [hcont.continuousAt.preimage_mem_nhds <| by
    simpa using Iio_mem_nhds_zero hγ] with x hx
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa [hσ, WithVal.apply_ofVal] using hx

end WithVal
