/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Gonality.Basic
import TauCeti.FieldTheory.IntermediateField.LinearDisjoint

/-!
# Gonality over the field of constants

Let `F / k` be a field extension and `K` an algebraic extension of `k` inside `F`, for instance the
field of constants `algebraicClosure k F` of an algebraic function field. Then
`gonality k F = [K : k] · gonality K F`.

An element of `F` is transcendental over `k` exactly when it is transcendental over the algebraic
extension `K`, so both gonalities are infima over the same elements `x`. For each of them,
`K` and `k(x)` are linearly disjoint over `k`, so `[K(x) : k(x)] = [K : k]` and the tower
`k(x) ⊆ K(x) ⊆ F` gives `[F : k(x)] = [K : k] · [F : K(x)]`.

Geometrically, when the constant field `K` of a function field `F / k` is larger than `k` and
separable over it, the regular projective curve of `F / k` is geometrically disconnected: over an
algebraic closure of `k` it splits into `[K : k]` conjugate components. A map to `ℙ¹` defined
over `k` has the same degree on each of them, so its degree is `[K : k]` times its degree on one
component. This is why gonality tables record the `K`-gonality of a component rather than the
`k`-gonality of the whole curve.

## Main results

* `TauCeti.gonality_eq_finrank_mul_gonality`: `gonality k F = [K : k] · gonality K F` for an
  algebraic extension `K / k` inside `F`.
* `TauCeti.gonality_eq_finrank_mul_gonality_algebraicClosure`: the case of the field of
  constants `K = algebraicClosure k F`.
* `TauCeti.gonality_ratFunc_of_isAlgebraic`: `gonality k K(t) = [K : k]`, the genuine gonality of
  `K(t)` over `k` when `K / k` is finite; for infinite `K / k` both sides are the junk value `0`.

## References

* B. Poonen, *Gonality of modular curves in characteristic `p`*, Math. Res. Lett. 14 (2007),
  Appendix A.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k K F : Type*} [Field k] [Field K] [Field F] [Algebra k K] [Algebra K F] [Algebra k F]
  [IsScalarTower k K F]

/-- **Gonality over an algebraic extension of the constants**: if `K / k` is algebraic and `F` is
an extension of `K`, then `gonality k F = [K : k] · gonality K F`. No finiteness is assumed: when
`K / k` is infinite both sides are the junk value `0`. -/
theorem gonality_eq_finrank_mul_gonality [Algebra.IsAlgebraic k K] :
    gonality k F = Module.finrank k K * gonality K F := by
  by_cases halg : Algebra.IsAlgebraic K F
  · -- With no transcendental element both infima are over the empty set.
    have := Algebra.IsAlgebraic.trans k K F
    rw [gonality_eq_zero_of_isAlgebraic, gonality_eq_zero_of_isAlgebraic, mul_zero]
  obtain ⟨x₀, hx₀⟩ : ∃ x : F, Transcendental K x :=
    not_forall.mp (halg ∘ Algebra.isAlgebraic_def.mpr)
  have htr (y : F) : Transcendental k y ↔ Transcendental K y :=
    Algebra.IsAlgebraic.transcendental_iff k K
  -- Compare the two infima through elements `x` and `y` attaining them over `K` and over `k`.
  obtain ⟨x, hx, hrank⟩ := exists_finrank_adjoin_eq_gonality_of_transcendental hx₀
  refine le_antisymm ?_ ?_
  · rw [← hrank, ← IntermediateField.finrank_adjoin_simple_eq_finrank_mul_finrank_adjoin_simple hx]
    exact gonality_le_finrank_adjoin ((htr x).2 hx)
  · obtain ⟨y, hy, hrank'⟩ := exists_finrank_adjoin_eq_gonality_of_transcendental ((htr x).2 hx)
    rw [← hrank', IntermediateField.finrank_adjoin_simple_eq_finrank_mul_finrank_adjoin_simple
      ((htr y).1 hy)]
    exact Nat.mul_le_mul_left _ (gonality_le_finrank_adjoin ((htr y).1 hy))

/-- **The gonality is the degree of the field of constants times the gonality over it**:
`gonality k F = [K : k] · gonality K F` for the field of constants `K = algebraicClosure k F`.
For an algebraic function field `F / k`, the field `F` is a function field over `K` with exact
constants, so the right-hand side reduces the gonality to the exact-constants case. -/
theorem gonality_eq_finrank_mul_gonality_algebraicClosure :
    gonality k F =
      Module.finrank k (algebraicClosure k F) * gonality (algebraicClosure k F) F :=
  gonality_eq_finrank_mul_gonality

omit [Algebra K F] [Algebra k F] [IsScalarTower k K F] in
/-- For an algebraic extension `K / k`, `gonality k K(t) = [K : k]`. When `K / k` is finite this is
the genuine gonality of `K(t)` over `k`; for instance `ℂ(t)` has gonality two over `ℝ`. When
`K / k` is infinite both sides are the junk value `0`. -/
@[simp]
theorem gonality_ratFunc_of_isAlgebraic [Algebra.IsAlgebraic k K] :
    gonality k (RatFunc K) = Module.finrank k K := by
  rw [gonality_eq_finrank_mul_gonality (K := K), gonality_ratFunc, mul_one]

end TauCeti
