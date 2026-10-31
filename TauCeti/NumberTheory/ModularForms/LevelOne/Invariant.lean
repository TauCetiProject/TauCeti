/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# Holomorphic `SL₂(ℤ)`-invariant functions with a limit at `i∞`

A holomorphic function `F` on the upper half-plane with `F (γ τ) = F τ` for every `γ ∈ SL₂(ℤ)`
that converges to `c` at `i∞` is the constant `c`: it is a level-one modular form of weight zero,
and these are constant (Mathlib's `ModularFormClass.levelOne_weight_zero_const`). This is how
identities between modular functions are proved from their behaviour at the cusp: a combination
of modular functions whose poles at `i∞` cancel is determined by its constant term there.

## Main results

* `TauCeti.ModularForm.levelOne_eq_of_tendsto_atImInfty`: a holomorphic `SL₂(ℤ)`-invariant
  function on the upper half-plane with limit `c` at `i∞` is the constant `c`.
-/

public section

open Filter Topology UpperHalfPlane
open scoped MatrixGroups Manifold ModularForm

namespace TauCeti.ModularForm

/-- A holomorphic function on the upper half-plane that is invariant under `SL₂(ℤ)` and tends to
`c` at `i∞` is the constant function `c`. -/
theorem levelOne_eq_of_tendsto_atImInfty {F : ℍ → ℂ} (hF : MDiff F)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) {c : ℂ}
    (hc : Tendsto F atImInfty (𝓝 c)) (τ : ℍ) : F τ = c := by
  have hslash (γ : SL(2, ℤ)) : F ∣[(0 : ℤ)] γ = F := by
    ext τ
    rw [_root_.ModularForm.SL_slash_apply, hinv, zpow_neg, zpow_zero, inv_one, mul_one]
  let f : _root_.ModularForm 𝒮ℒ 0 :=
    { toFun := F
      slash_action_eq' γ hγ := by
        obtain ⟨γ, rfl⟩ := hγ
        exact hslash γ
      holo' := hF
      bdd_at_cusps' hc' := by
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
        intro γ _
        rw [hslash]
        exact hc.isBigO_one ℝ }
  obtain ⟨d, hd⟩ := ModularFormClass.levelOne_weight_zero_const f
  -- The coercion of `f` is `F` by construction.
  have hFd : F = Function.const ℍ d := hd
  rw [hFd] at hc ⊢
  exact tendsto_nhds_unique tendsto_const_nhds hc

end TauCeti.ModularForm
