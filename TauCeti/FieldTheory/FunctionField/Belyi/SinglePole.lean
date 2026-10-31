/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.SinglePole

/-!
# A generator of a Belyi pair with a single pole

Let `F / k(t)` be an algebraic Belyi pair over a field `k` of characteristic zero, and let `P` be
a place of `F` lying over a place of `k(t)` other than `t = 0`, `t = 1` and `t = ∞`, with relative
degree one over it, as is the case for a place of degree one. Then `P` is unramified over `k(t)`,
so every `z ∈ F` whose only pole is `P` generates `F` over `k(t)`: `F = k(t, z)`
(`TauCeti.Place.adjoin_simple_eq_top_of_forall_ne_ord_nonneg`). Such functions exist, by
Riemann–Roch: for `n ≥ 2g`, where `g` is the genus of `F`, some function has a pole of order
exactly `n` at `P` and no other pole.

Over an algebraically closed field `k`, such as `ℂ`, every place has degree one, and for every
`a ∈ k` other than `0` and `1` some place of `F` lies over `t = a`. Taking `a` rational, this is the
starting point of Köck's proof that every Belyi pair over `ℂ` is defined over a number field: the
pair is presented as `k(t)[Z] / (μ)` for the minimal polynomial `μ` of such a `z`, and `z` is then
normalized so that automorphisms of `ℂ` fixing the isomorphism class of the pair fix `μ`.

## Main results

* `TauCeti.IsAlgebraicBelyiPair.exists_ord_neg_and_adjoin_simple_eq_top`: at every unmarked
  place of relative degree one there is a function with a single pole there generating `F` over
  `k(t)`.
* `TauCeti.IsAlgebraicBelyiPair.exists_restrict_eq_and_adjoin_simple_eq_top`: over an
  algebraically closed field, for every `a ≠ 0, 1` there are a place `P` over `t = a` and a
  function with only pole `P` generating `F` over `k(t)`.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.6.
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace IsAlgebraicBelyiPair

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- **A Belyi pair has a generator with a single pole at an unmarked place.** Let `F / k(t)` be
an algebraic Belyi pair and `P` a place of `F` with relative degree one over a place of `k(t)` other
than `t = 0`, `t = 1` and `t = ∞`, for instance a place of degree one. Then some `z ∈ F` has a pole
at `P`, no other pole, and generates `F` over `k(t)`. -/
theorem exists_ord_neg_and_adjoin_simple_eq_top (h : IsAlgebraicBelyiPair k F)
    {P : Place k F} (hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k)
    (hf : Place.relativeDegree k (RatFunc k) P = 1) :
    ∃ z : F, P.ord z < 0 ∧ (∀ P' : Place k F, P' ≠ P → 0 ≤ P'.ord z) ∧
      (RatFunc k)⟮z⟯ = ⊤ := by
  -- Riemann–Roch gives a function with a pole of order `2g + 1` at `P` and no other pole.
  obtain ⟨z, -, hz, hreg⟩ := P.exists_ord_eq_neg_and_forall_ne_ord_nonneg
    ((IsFunctionField.ratFunc k).finite_extension (E := F)) h.isIntegrallyClosedIn
    (n := 2 * genus k F + 1) (by omega)
  have hz : P.ord z < 0 := by rw [hz]; omega
  -- Over an unmarked place `P` is unramified, so `z` generates `F` over `k(t)`.
  exact ⟨z, hz, hreg, Place.adjoin_simple_eq_top_of_forall_ne_ord_nonneg
    (IsFunctionField.ratFunc k) (h.ramificationIdx_eq_one hP) hf hz hreg⟩

/-- **A Belyi pair over an algebraically closed field has a generator with a single pole over any
unmarked point.** If `k` is algebraically closed and `a ∈ k` is neither `0` nor `1`, then there
are a place `P` of `F` over `t = a` and a function `z ∈ F` with a pole at `P` and no other pole
which generates `F` over `k(t)`. -/
theorem exists_restrict_eq_and_adjoin_simple_eq_top [IsAlgClosed k]
    (h : IsAlgebraicBelyiPair k F) {a : k} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    ∃ (P : Place k F) (z : F),
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a) ∧
        P.ord z < 0 ∧ (∀ P' : Place k F, P' ≠ P → 0 ≤ P'.ord z) ∧ (RatFunc k)⟮z⟯ = ⊤ := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc k) hF
    (Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a))
  have hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k := by
    simp only at hPa
    simp [hPa, ha₀, ha₁]
  -- Every place of `F` has degree one, hence relative degree one over `k(t)`.
  have hf : Place.relativeDegree k (RatFunc k) P = 1 := by
    have h := Place.degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P
    rw [P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF] at h
    exact Nat.eq_one_of_mul_eq_one_left h.symm
  obtain ⟨z, hz⟩ := h.exists_ord_neg_and_adjoin_simple_eq_top hP hf
  exact ⟨P, z, hPa, hz⟩

end IsAlgebraicBelyiPair

end TauCeti
