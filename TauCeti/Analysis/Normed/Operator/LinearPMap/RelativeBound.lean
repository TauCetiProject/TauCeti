/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Relatively bounded partial linear maps

A partial linear map `V` is *relatively bounded* with respect to a partial linear map `A`, with
constants `a` and `b`, when the domain of `A` lies in the domain of `V` and

`‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` for every `x` in the domain of `A`.

This is the size condition of perturbation theory for unbounded operators: the perturbation is
controlled by the graph of `A` rather than by `‖x‖` alone, and the Kato–Rellich theorem asks for
`b < 1`. The infimum of the admissible `b` is Kato's *`A`-bound* of `V`.

This file sets up the predicate and its elementary calculus: the zero map is relatively bounded
with constants `0, 0`; the constants may be increased; relative bounds add under sums and
differences, scale under scalar multiplication and are unchanged by negation; and a bounded
operator on the whole space is relatively bounded with constants `‖T‖, 0`. Sums and differences
use Mathlib's addition of partial linear maps, whose domain is the intersection of the two domains.

## Main declarations

* `LinearPMap.IsRelativelyBounded V A a b`: `V` is `A`-bounded with constants `a, b`.
* `LinearPMap.IsRelativelyBounded.mono`: increasing the constants.
* `LinearPMap.IsRelativelyBounded.domain_add`: the domain of `A + V` is the domain of `A`.
* `LinearPMap.IsRelativelyBounded.add`, `.sub`, `.neg`, `.smul`: the linear calculus.
* `LinearPMap.isRelativelyBounded_zero`, `ContinuousLinearMap.isRelativelyBounded_toPMap`: the
  zero map and bounded operators.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), §IV.1.1.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975), §X.2.
-/

public section

namespace LinearPMap

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A partial linear map `V` is *relatively bounded* with respect to `A`, with constants `a` and
`b`, when `A.domain ≤ V.domain` and `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` for every `x` in the domain of
`A`. -/
structure IsRelativelyBounded (V : E →ₗ.[𝕜] G) (A : E →ₗ.[𝕜] F) (a b : ℝ) : Prop where
  /-- The domain of `A` lies in the domain of `V`. -/
  domain_le : A.domain ≤ V.domain
  /-- The relative bound `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` on the domain of `A`. -/
  norm_apply_le : ∀ x : A.domain, ‖V ⟨x, domain_le x.2⟩‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖

namespace IsRelativelyBounded

variable {V W : E →ₗ.[𝕜] G} {A : E →ₗ.[𝕜] F} {a b a' b' : ℝ}

/-- A relative bound holds at any larger pair of constants. -/
theorem mono (h : V.IsRelativelyBounded A a b) (ha : a ≤ a') (hb : b ≤ b') :
    V.IsRelativelyBounded A a' b' where
  domain_le := h.domain_le
  norm_apply_le x := (h.norm_apply_le x).trans <| add_le_add
    (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- If `V` is relatively bounded with respect to `A`, then `A + V` has the same domain as `A`. -/
theorem domain_add {V A : E →ₗ.[𝕜] F} (h : V.IsRelativelyBounded A a b) :
    (A + V).domain = A.domain :=
  inf_eq_left.2 h.domain_le

/-- Relative bounds add under the sum of two partial linear maps. -/
theorem add (hV : V.IsRelativelyBounded A a b) (hW : W.IsRelativelyBounded A a' b') :
    (V + W).IsRelativelyBounded A (a + a') (b + b') where
  domain_le := le_inf hV.domain_le hW.domain_le
  norm_apply_le x := by
    rw [add_apply]
    calc _ ≤ ‖V ⟨x, hV.domain_le x.2⟩‖ + ‖W ⟨x, hW.domain_le x.2⟩‖ := norm_add_le _ _
      _ ≤ _ := by linarith [hV.norm_apply_le x, hW.norm_apply_le x]

/-- Negation does not change a relative bound. -/
theorem neg (h : V.IsRelativelyBounded A a b) : (-V).IsRelativelyBounded A a b where
  domain_le := h.domain_le
  norm_apply_le x := by
    rw [neg_apply, norm_neg]
    exact h.norm_apply_le x

/-- Relative bounds add under the difference of two partial linear maps. -/
theorem sub (hV : V.IsRelativelyBounded A a b) (hW : W.IsRelativelyBounded A a' b') :
    (V - W).IsRelativelyBounded A (a + a') (b + b') where
  domain_le := le_inf hV.domain_le hW.domain_le
  norm_apply_le x := by
    rw [sub_apply]
    calc _ ≤ ‖V ⟨x, hV.domain_le x.2⟩‖ + ‖W ⟨x, hW.domain_le x.2⟩‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hV.norm_apply_le x, hW.norm_apply_le x]

/-- A scalar multiple `c • V` is relatively bounded with the constants scaled by `‖c‖`. -/
theorem smul (h : V.IsRelativelyBounded A a b) (c : 𝕜) :
    (c • V).IsRelativelyBounded A (‖c‖ * a) (‖c‖ * b) where
  domain_le := h.domain_le
  norm_apply_le x := by
    rw [smul_apply, norm_smul]
    calc ‖c‖ * ‖V ⟨x, h.domain_le x.2⟩‖ ≤ ‖c‖ * (a * ‖(x : E)‖ + b * ‖A x‖) :=
          mul_le_mul_of_nonneg_left (h.norm_apply_le x) (norm_nonneg c)
      _ = _ := by ring

end IsRelativelyBounded

/-- The zero map is relatively bounded with constants `0, 0`. -/
theorem isRelativelyBounded_zero (A : E →ₗ.[𝕜] F) :
    (0 : E →ₗ.[𝕜] G).IsRelativelyBounded A 0 0 where
  domain_le := le_top
  norm_apply_le x := by simp

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bounded operator `T` on the whole space, viewed as a partial linear map with domain `⊤`, is
relatively bounded with respect to every partial linear map, with constants `‖T‖, 0`. -/
theorem isRelativelyBounded_toPMap (T : E →L[𝕜] G) (A : E →ₗ.[𝕜] F) :
    ((T : E →ₗ[𝕜] G).toPMap ⊤).IsRelativelyBounded A ‖T‖ 0 where
  domain_le := le_top
  norm_apply_le x := by simpa using T.le_opNorm x

end ContinuousLinearMap
