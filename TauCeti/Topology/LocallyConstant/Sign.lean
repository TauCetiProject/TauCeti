/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Basic.Sign.Basic

/-!
# The sign of a nowhere-vanishing continuous function

A continuous function `g` that vanishes nowhere, with values in a linear order carrying the order
topology such as `ℝ`, has a locally constant sign (`Continuous.isLocallyConstant_sign`): it keeps
one sign on each connected component. For a real function on a compact space, `|g|` is moreover
bounded below by a positive constant, so multiplying `g` by a suitable nonzero constant on each of
the sets where its sign is constant makes it exceed any given bound
(`Continuous.exists_isLocallyConstant_lt_mul`).

This is the rescaling by which a form `β` with the kernel of a nowhere-vanishing form `α` on a
compact manifold, multiplied by a locally constant factor, becomes `f α` with `f` above any given
bound.
-/

public section

namespace Continuous

variable {X : Type*} [TopologicalSpace X]

/-- The sign of a continuous function that vanishes nowhere, with values in a linear order with the
order topology, is locally constant. -/
theorem isLocallyConstant_sign {α : Type*} [Zero α] [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] {g : X → α} (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    IsLocallyConstant fun x ↦ SignType.sign (g x) :=
  (IsLocallyConstant.iff_continuous _).2 <| continuous_iff_continuousAt.2 fun x ↦
    (continuousAt_sign_of_ne_zero (h₀ x)).comp hg.continuousAt

/-- **Making a nowhere-vanishing function large by a locally constant factor.** On a compact
space, a continuous real function `g` that vanishes nowhere becomes larger than any given bound `a`
after multiplication by a suitable locally constant function `c` that vanishes nowhere. -/
theorem exists_isLocallyConstant_lt_mul [CompactSpace X] {g : X → ℝ} (hg : Continuous g)
    (h₀ : ∀ x, g x ≠ 0) (a : ℝ) :
    ∃ c : X → ℝ, IsLocallyConstant c ∧ (∀ x, c x ≠ 0) ∧ ∀ x, a < c x * g x := by
  -- `|g|` is bounded below by a positive constant `m` on the compact space.
  obtain ⟨m, hm, hmg⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ |g x| := by
    rcases isEmpty_or_nonempty X with hX | hX
    · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
    · obtain ⟨x₀, -, hx₀⟩ :=
        isCompact_univ.exists_isMinOn Set.univ_nonempty hg.abs.continuousOn
      exact ⟨|g x₀|, abs_pos.2 (h₀ x₀), fun x ↦ isMinOn_iff.1 hx₀ x trivial⟩
  -- Multiply the sign of `g` by a constant `k > 0` with `k m > a`.
  set k := (|a| + 1) / m with hk
  have hk₀ : 0 < k := by positivity
  refine ⟨fun x ↦ k * SignType.sign (g x),
    (hg.isLocallyConstant_sign h₀).comp fun s : SignType ↦ k * s, fun x ↦ ?_, fun x ↦ ?_⟩
  · refine mul_ne_zero hk₀.ne' (left_ne_zero_of_mul (b := g x) ?_)
    rw [sign_mul_self]
    exact abs_ne_zero.2 (h₀ x)
  · calc a < |a| + 1 := by linarith [le_abs_self a]
      _ = k * m := by rw [hk, div_mul_cancel₀ _ hm.ne']
      _ ≤ k * |g x| := by gcongr; exact hmg x
      _ = k * SignType.sign (g x) * g x := by rw [mul_assoc, sign_mul_self]

end Continuous
