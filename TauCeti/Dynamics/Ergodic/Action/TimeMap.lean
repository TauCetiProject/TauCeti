/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Ergodicity of an action from one ergodic element

For an action of `M` on a measure space `(X, μ)` preserving `μ`, a set invariant up to null sets
under every `(m • ·)` is in particular invariant under a single `(m₀ • ·)`. So if one map
`(m₀ • ·)` is ergodic, the whole action is ergodic (`ErgodicSMul.of_ergodic_smul`). For a
measurable flow, an `AddAction ℝ X`, this says that ergodicity of one time-`t` map `(t +ᵥ ·)`
implies `ErgodicVAdd ℝ X μ` (`ErgodicVAdd.of_ergodic_vadd`). Each time-`t` map of a measurable
flow is an invertible system: Mathlib's `MeasurableEquiv.vadd t` has inverse
`MeasurableEquiv.vadd (-t)` (`MeasurableEquiv.symm_vadd`) and preserves every invariant measure
(`MeasureTheory.measurePreserving_vadd`).

Conversely, an action in which every element acts as the identity is not ergodic as soon as some
null-measurable set and its complement both have positive measure
(`not_ergodicSMul_of_forall_smul_eq`), while an invariant point mass is always ergodic
(`TauCeti.ergodicSMul_dirac`).

## Main results

* `ErgodicSMul.of_ergodic_smul`, `ErgodicVAdd.of_ergodic_vadd`: an invariant measure for which one
  element of the acting monoid acts ergodically is ergodic for the action.
* `not_ergodicSMul_of_forall_smul_eq`, `not_ergodicVAdd_of_forall_vadd_eq`: the trivial action on a
  space that is not almost a point is not ergodic.
* `TauCeti.ergodicSMul_dirac`, `TauCeti.ergodicVAdd_dirac`: an invariant point mass is ergodic.
-/

public section

open MeasureTheory Filter Set

variable {M X : Type*} [SMul M X] {_ : MeasurableSpace X} {μ : Measure X}

/-- **One ergodic element makes the action ergodic.** If `μ` is invariant under the action of `M`
and the map `(m • ·)` is ergodic for one `m : M`, then the action of `M` is ergodic. -/
@[to_additive /-- **One ergodic element makes the action ergodic.** If `μ` is invariant under the
action of `M` and the map `(m +ᵥ ·)` is ergodic for one `m : M`, then the action of `M` is
ergodic. For a measurable flow, ergodicity of one time-`t` map implies ergodicity of the flow. -/]
theorem ErgodicSMul.of_ergodic_smul [SMulInvariantMeasure M X μ] (m : M)
    (h : Ergodic (m • ·) μ) : ErgodicSMul M X μ where
  aeconst_of_forall_preimage_smul_ae_eq hs hinv :=
    h.quasiErgodic.aeconst_set hs.nullMeasurableSet (hinv m)

/-- **The trivial action is not ergodic.** If every element of `M` acts as the identity, and some
null-measurable set `s` and its complement both have positive measure, then the action is not
ergodic. -/
@[to_additive /-- **The trivial action is not ergodic.** If every element of `M` acts as the
identity, and some null-measurable set `s` and its complement both have positive measure, then
the action is not ergodic. -/]
theorem not_ergodicSMul_of_forall_smul_eq (h : ∀ (m : M) (x : X), m • x = x) {s : Set X}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) (hsc : μ sᶜ ≠ 0) : ¬ErgodicSMul M X μ := by
  intro hμ
  have hinv (m : M) : (m • ·) ⁻¹' s =ᵐ[μ] s := by
    rw [show (m • ·) ⁻¹' s = s by ext x; simp [h]]
  have hconst := aeconst_of_forall_preimage_smul_ae_eq M hs hinv
  rcases eventuallyEmptyOrUniv_iff'.mp hconst with h₀ | h₁
  · exact hs₀ (ae_eq_empty.mp h₀)
  · exact hsc (ae_eq_univ.mp h₁)

namespace TauCeti

/-- **Invariant point masses are ergodic.** Under the point mass `δ_x`, every measurable set has
measure `0` or `1`, so it is almost empty or almost everything. -/
@[to_additive /-- **Invariant point masses are ergodic.** Under the point mass `δ_x`, every
measurable set has measure `0` or `1`, so it is almost empty or almost everything. -/]
theorem ergodicSMul_dirac (x : X) [SMulInvariantMeasure M X (Measure.dirac x)] :
    ErgodicSMul M X (Measure.dirac x) where
  aeconst_of_forall_preimage_smul_ae_eq hs _ :=
    eventuallyEmptyOrUniv_ae_dirac hs.nullMeasurableSet

end TauCeti
