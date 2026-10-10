/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Basic

/-!
# Bounded operators commuting with a one-parameter unitary group

A bounded operator that commutes with every `U t` preserves the generator's
domain and commutes with the generator.

`Basic.lean` proves this for the group's *own* elements
(`generator_domain_invariant`).  The statement here is the same fact for an
arbitrary element of the group's commutant, and it is what a block-diagonal
argument needs: spectral projections of `A` commute with the unitary group of
`A`, so cutting a vector into spectral blocks commutes with the flow, and
therefore with the generator.

The proof is the obvious one and does not use unitarity at all — only that `T`
is continuous and linear.  The difference quotient commutes with `T` term by
term, and a continuous map carries the limit to the limit.

## Sources

That a bounded operator commutes with a one-parameter unitary group exactly when it
commutes with its generator is standard in the Stone's-theorem literature
(Reed--Simon, *Methods of Modern Mathematical Physics I*).  The form here is the one
the spectral-projection argument consumes.

## Provenance

*New.*
-/

public section

noncomputable section

open InnerProductSpace Complex Filter Topology

namespace TauCeti
namespace OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A commuting bounded operator passes through the difference quotient. -/
theorem genDiffQuot_commute (U : OneParameterUnitaryGroup (H := H)) (T : H →L[ℂ] H)
    (hT : ∀ t : ℝ, ∀ y : H, T (U.U t y) = U.U t (T y)) (ψ : H) (t : ℝ) :
    genDiffQuot U (T ψ) t = T (genDiffQuot U ψ t) := by
  simp only [genDiffQuot_apply, map_smul, map_sub]
  rw [hT t ψ]

/-- **The commutant preserves the generator.**  A bounded operator commuting
with every `U t` maps the generator domain into itself and commutes with the
generator there. -/
theorem generator_commute (U : OneParameterUnitaryGroup (H := H)) (T : H →L[ℂ] H)
    (hT : ∀ t : ℝ, ∀ y : H, T (U.U t y) = U.U t (T y))
    (x : (generator U).domain) :
    ∃ hmem : T (x : H) ∈ (generator U).domain,
      generator U ⟨T (x : H), hmem⟩ = T (generator U x) := by
  have hlim : Tendsto (genDiffQuot U (T (x : H))) (𝓝[≠] (0 : ℝ))
      (𝓝 (T (generator U x))) := by
    have h := (T.continuous.tendsto (generator U x)).comp (generator_tendsto U x)
    refine h.congr fun t => ?_
    rw [Function.comp_apply, ← genDiffQuot_commute U T hT (x : H) t]
  exact ⟨mem_generatorDomain.mpr ⟨T (generator U x), hlim⟩, tendsto_nhds_unique
    (generator_tendsto U ⟨T (x : H), mem_generatorDomain.mpr ⟨T (generator U x), hlim⟩⟩) hlim⟩

end OneParameterUnitaryGroup
end TauCeti

end
