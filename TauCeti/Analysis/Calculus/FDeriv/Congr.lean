/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Congruence of Fréchet derivatives across equal codomain topologies and module structures

`HasFDerivAtFilter` and its specializations (`HasStrictFDerivAt`, `HasFDerivAt`,
`HasFDerivWithinAt`) take only `[AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]` on the
codomain. When a type carries two syntactically distinct `TopologicalSpace` or `Module 𝕜` instances
that are provably equal (for example, a matrix space equipped either with its entrywise product
topology or with a norm-induced topology), rewriting the instance directly inside
`HasStrictFDerivAt` is blocked by the dependent type `E →L[𝕜] F` of the candidate derivative. The
lemmas in this file transport Fréchet derivative predicates across `t₁ = t₂` and `m₁ = m₂` whenever
the two candidate continuous linear maps agree pointwise.

## Main results

* `TauCeti.hasFDerivAtFilter_congr_codomain`: transport `HasFDerivAtFilter` across equal codomain
  `TopologicalSpace` and `Module 𝕜` instances.
* `TauCeti.hasStrictFDerivAt_congr_codomain`, `TauCeti.hasFDerivAt_congr_codomain`, and
  `TauCeti.hasFDerivWithinAt_congr_codomain`: specializations to strict, pointwise, and within-set
  Fréchet derivatives.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F]

/-- Transport `HasFDerivAtFilter` across equal `TopologicalSpace` and `Module 𝕜` instances on the
codomain when the candidate continuous linear maps agree pointwise. -/
theorem hasFDerivAtFilter_congr_codomain {t₁ t₂ : TopologicalSpace F} (ht : t₁ = t₂)
    {m₁ m₂ : Module 𝕜 F} (hm : m₁ = m₂) {f : E → F}
    {f'₁ : letI := t₁; letI := m₁; E →L[𝕜] F}
    {f'₂ : letI := t₂; letI := m₂; E →L[𝕜] F}
    (hf' : ∀ x, (letI := t₁; letI := m₁; (f'₁ : E → F) x) =
                (letI := t₂; letI := m₂; (f'₂ : E → F) x))
    {L : Filter (E × E)} :
    (letI := t₁; letI := m₁; HasFDerivAtFilter f f'₁ L) ↔
      (letI := t₂; letI := m₂; HasFDerivAtFilter f f'₂ L) := by
  subst ht; subst hm; rw [ContinuousLinearMap.ext hf']

/-- Transport `HasStrictFDerivAt` across equal `TopologicalSpace` and `Module 𝕜` instances on the
codomain when the candidate continuous linear maps agree pointwise. -/
theorem hasStrictFDerivAt_congr_codomain {t₁ t₂ : TopologicalSpace F} (ht : t₁ = t₂)
    {m₁ m₂ : Module 𝕜 F} (hm : m₁ = m₂) {f : E → F}
    {f'₁ : letI := t₁; letI := m₁; E →L[𝕜] F}
    {f'₂ : letI := t₂; letI := m₂; E →L[𝕜] F}
    (hf' : ∀ x, (letI := t₁; letI := m₁; (f'₁ : E → F) x) =
                (letI := t₂; letI := m₂; (f'₂ : E → F) x))
    {a : E} :
    (letI := t₁; letI := m₁; HasStrictFDerivAt f f'₁ a) ↔
      (letI := t₂; letI := m₂; HasStrictFDerivAt f f'₂ a) :=
  hasFDerivAtFilter_congr_codomain ht hm hf'

/-- Transport `HasFDerivAt` across equal `TopologicalSpace` and `Module 𝕜` instances on the codomain
when the candidate continuous linear maps agree pointwise. -/
theorem hasFDerivAt_congr_codomain {t₁ t₂ : TopologicalSpace F} (ht : t₁ = t₂)
    {m₁ m₂ : Module 𝕜 F} (hm : m₁ = m₂) {f : E → F}
    {f'₁ : letI := t₁; letI := m₁; E →L[𝕜] F}
    {f'₂ : letI := t₂; letI := m₂; E →L[𝕜] F}
    (hf' : ∀ x, (letI := t₁; letI := m₁; (f'₁ : E → F) x) =
                (letI := t₂; letI := m₂; (f'₂ : E → F) x))
    {a : E} :
    (letI := t₁; letI := m₁; HasFDerivAt f f'₁ a) ↔
      (letI := t₂; letI := m₂; HasFDerivAt f f'₂ a) :=
  hasFDerivAtFilter_congr_codomain ht hm hf'

/-- Transport `HasFDerivWithinAt` across equal `TopologicalSpace` and `Module 𝕜` instances on the
codomain when the candidate continuous linear maps agree pointwise. -/
theorem hasFDerivWithinAt_congr_codomain {t₁ t₂ : TopologicalSpace F} (ht : t₁ = t₂)
    {m₁ m₂ : Module 𝕜 F} (hm : m₁ = m₂) {f : E → F}
    {f'₁ : letI := t₁; letI := m₁; E →L[𝕜] F}
    {f'₂ : letI := t₂; letI := m₂; E →L[𝕜] F}
    (hf' : ∀ x, (letI := t₁; letI := m₁; (f'₁ : E → F) x) =
                (letI := t₂; letI := m₂; (f'₂ : E → F) x))
    {s : Set E} {a : E} :
    (letI := t₁; letI := m₁; HasFDerivWithinAt f f'₁ s a) ↔
      (letI := t₂; letI := m₂; HasFDerivWithinAt f f'₂ s a) :=
  hasFDerivAtFilter_congr_codomain ht hm hf'

end TauCeti
