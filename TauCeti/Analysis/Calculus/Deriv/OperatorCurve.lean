/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Infinitesimal symmetries of a curve of operators through the identity

Let `D : 𝕜 → E →L[𝕜] E` be a curve of operators with `D t₀ = 1` and derivative `L` at `t₀`. Every
symmetry shared by the operators `D t` near `t₀` passes to an infinitesimal symmetry of `L`:

* if every `D t` with `t` near `t₀` preserves a continuous bilinear map `B`, then `L` is skew for
  `B`, `B (L u) w = -B u (L w)` (`HasDerivAt.apply_left_eq_neg_of_eventually_apply_apply_eq`): this
  is the derivative of the pairings `t ↦ B (D t u) (D t w)`, which are constant near `t₀`;
* if every `D t` with `t` near `t₀` commutes with an operator `J`, then so does `L`
  (`HasDerivAt.apply_apply_eq_of_eventually_apply_apply_eq`).

For instance, the differentials at a fixed point of a one-parameter group of symplectomorphisms
which preserve an almost complex structure form such a curve, and these are the statements that its
generator lies in the symplectic Lie algebra and is complex linear.
-/

public section

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {D : 𝕜 → E →L[𝕜] E} {L : E →L[𝕜] E} {t₀ : 𝕜}

/-- **Generators of curves preserving a bilinear map are skew.** Let `D` be a curve of operators
with `D t₀ = 1` and derivative `L` at `t₀`. If every `D t` with `t` near `t₀` preserves a continuous
bilinear map `B`, then `B (L u) w = -B u (L w)`. -/
theorem HasDerivAt.apply_left_eq_neg_of_eventually_apply_apply_eq {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (hD : HasDerivAt D L t₀) (hD₀ : D t₀ = 1)
    (B : E →L[𝕜] E →L[𝕜] G) (hB : ∀ᶠ t in 𝓝 t₀, ∀ u w, B (D t u) (D t w) = B u w) (u w : E) :
    B (L u) w = -B u (L w) := by
  have hDv (v : E) : HasDerivAt (fun t ↦ D t v) (L v) t₀ := by
    simpa using hD.clm_apply (hasDerivAt_const t₀ v)
  -- The pairing `t ↦ B (D t u) (D t w)` is constant near `t₀`, so its derivative vanishes.
  have hzero := (B.hasDerivAt_of_bilinear (fun _ ↦ hDv u) (fun _ ↦ hDv w)).unique
    ((hasDerivAt_const t₀ (B u w)).congr_of_eventuallyEq (hB.mono fun t ht ↦ ht u w))
  rw [hD₀, one_apply_eq_self, one_apply_eq_self] at hzero
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hzero)

/-- **Generators of curves commuting with an operator commute with it.** Let `D` be a curve of
operators with derivative `L` at `t₀`. If every `D t` with `t` near `t₀` commutes with an operator
`J`, then so does `L`: `L (J v) = J (L v)`. -/
theorem HasDerivAt.apply_apply_eq_of_eventually_apply_apply_eq (hD : HasDerivAt D L t₀)
    (J : E →L[𝕜] E) (hJ : ∀ᶠ t in 𝓝 t₀, ∀ v, D t (J v) = J (D t v)) (v : E) :
    L (J v) = J (L v) := by
  have h₁ : HasDerivAt (fun t ↦ D t (J v)) (L (J v)) t₀ := by
    simpa using hD.clm_apply (hasDerivAt_const t₀ (J v))
  have h₂ : HasDerivAt (fun t ↦ J (D t v)) (J (L v)) t₀ := by
    simpa using (hasDerivAt_const t₀ J).clm_apply (hD.clm_apply (hasDerivAt_const t₀ v))
  exact h₁.unique (h₂.congr_of_eventuallyEq (hJ.mono fun t ht ↦ ht v))
