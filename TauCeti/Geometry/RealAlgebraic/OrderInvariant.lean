/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# Constant order and constant sign

A polynomial `p` has constant order on a set `S` when its order of vanishing `p.orderAt x` is the
same at every point `x ∈ S`. On a preconnected set this forces `p` to be sign-invariant: constant
order zero means that `p` has no zero on `S`, so its sign is locally constant there, while a
constant positive order means that `p` vanishes on all of `S`.

The converse fails, even on a connected set: `X₀ * X₁` vanishes identically on the line
`x₀ = 0` of the plane, but its order of vanishing there is `2` at the origin and `1` at every
other point. This is why order-invariant decompositions, used for McCallum's projection, ask
for more than sign-invariant ones.

## Main results

* `IsPreconnected.signInvariant_eval_of_orderAt_eq`: constant order on a preconnected set implies
  sign-invariance.
* `TauCeti.exists_signInvariant_orderAt_ne`: sign-invariance on a connected set does not imply
  constant order.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  pp. 242–268, Section 2.
-/

public section

open MvPolynomial Set

/-- A polynomial whose order of vanishing is the same at all points of a preconnected set `S` is
sign-invariant on `S`. -/
theorem IsPreconnected.signInvariant_eval_of_orderAt_eq {σ R : Type*} [CommRing R]
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [IsTopologicalSemiring R]
    {p : MvPolynomial σ R} {S : Set (σ → R)} (hS : IsPreconnected S)
    (h : ∀ x ∈ S, ∀ y ∈ S, p.orderAt x = p.orderAt y) :
    TauCeti.SignInvariant (fun x ↦ eval x p) S :=
  hS.signInvariant_of_eq_zero_iff (continuous_eval p).continuousOn fun x hx y hy ↦ by
    rw [← orderAt_pos_iff, ← orderAt_pos_iff, h x hx y hy]

namespace TauCeti

/-- Sign-invariance does not imply constant order, even on a connected set: the polynomial
`X₀ * X₁` vanishes on the line `x₀ = 0`, but its order of vanishing there is `2` at the origin
and `1` at `(0, 1)`. -/
theorem exists_signInvariant_orderAt_ne :
    ∃ (p : MvPolynomial (Fin 2) ℝ) (S : Set (Fin 2 → ℝ)), IsConnected S ∧
      SignInvariant (fun x ↦ eval x p) S ∧ ∃ x ∈ S, ∃ y ∈ S, p.orderAt x ≠ p.orderAt y := by
  have hX₀ (t : ℝ) : (X 0 : MvPolynomial (Fin 2) ℝ).orderAt ![0, t] = 1 := by
    simpa using orderAt_X_sub_C (![0, t] : Fin 2 → ℝ) 0
  have hX₁ : (X 1 : MvPolynomial (Fin 2) ℝ).orderAt ![0, 0] = 1 := by
    simpa using orderAt_X_sub_C (![0, 0] : Fin 2 → ℝ) 1
  refine ⟨X 0 * X 1, range fun t : ℝ ↦ ![0, t],
    ⟨range_nonempty _, isPreconnected_range (by fun_prop)⟩, ?_, ![0, 0], ⟨0, rfl⟩, ![0, 1],
    ⟨1, rfl⟩, ?_⟩
  · rw [signInvariant_def]
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    simp
  · have h₁ : (X 1 : MvPolynomial (Fin 2) ℝ).orderAt ![0, 1] = 0 := by
      simp [orderAt_eq_zero_iff]
    rw [orderAt_mul, orderAt_mul, hX₀, hX₀, hX₁, h₁]
    decide

end TauCeti
