/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.FieldTheory.FunctionField.Place.ArtinSchreier
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# Artin–Schreier reduction fails over `𝔽_p(a)`

Let `k = 𝔽_p(a)` and let `P` be the place `t = 0` of `k(t)`. Its residue field is `k`, which
is not perfect, since `a` is not a `p`-th power. The function `a t⁻ᵖ` has no reduced
Artin–Schreier representative at `P`. For every `w`, the function `a t⁻ᵖ - (wᵖ - w)` has a pole
at `P` whose order is divisible by `p`. The same holds in the completion `k((t))` of `k(t)` at
`P`, so even Laurent series cannot cancel the term `a t⁻ᵖ`.

So `TauCeti.Place.exists_reduced_artinSchreier_representative` needs its perfect residue field.
This is also why the Artin–Schreier genus formula takes reduced representatives as input when
residue fields may be imperfect. Both statements are instances of
`TauCeti.Place.not_exists_reduced_artinSchreier_representative_of_degree_eq_one`.

## Main results

* `TauCeti.Place.not_exists_reduced_artinSchreier_representative_ratFunc_ratFunc`: the
  obstruction at the place `t = 0` of `𝔽_p(a)(t)`.
* `TauCeti.Place.not_exists_reduced_artinSchreier_representative_completion_ratFunc_ratFunc`:
  the obstruction in the completion `𝔽_p(a)((t))`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

open Polynomial

namespace TauCeti.Place

variable (p : ℕ) [Fact p.Prime]

/-- **No reduced Artin–Schreier representative over `𝔽_p(a)`.** At the place `t = 0` of
`𝔽_p(a)(t)`, written `RatFunc (RatFunc (ZMod p))` with `a` the inner and `t` the outer variable,
no function `a t⁻ᵖ - (wᵖ - w)` is integral or has a pole of order prime to `p`. -/
theorem not_exists_reduced_artinSchreier_representative_ratFunc_ratFunc :
    ¬∃ w : RatFunc (RatFunc (ZMod p)),
      algebraMap (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p))) RatFunc.X / RatFunc.X ^ p -
          (w ^ p - w) ∈ (adicOfIrreducible (irreducible_X (R := RatFunc (ZMod p)))).integers ∨
        ((adicOfIrreducible (irreducible_X (R := RatFunc (ZMod p)))).ord
            (algebraMap (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p))) RatFunc.X /
              RatFunc.X ^ p - (w ^ p - w)) < 0 ∧
          ¬(p : ℤ) ∣ (adicOfIrreducible (irreducible_X (R := RatFunc (ZMod p)))).ord
            (algebraMap (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p))) RatFunc.X /
              RatFunc.X ^ p - (w ^ p - w))) :=
  not_exists_reduced_artinSchreier_representative_of_degree_eq_one _
    (by simp) (Fact.out : p.Prime).one_lt (RatFunc.pow_ne_X (Fact.out : p.Prime).one_lt)
    (by simp)

/-- **No reduced Artin–Schreier representative in `𝔽_p(a)((t))`.** In the completion of
`𝔽_p(a)(t)` at `t = 0`, no element `a t⁻ᵖ - (wᵖ - w)` is integral or has a pole of order prime
to `p`. Laurent series do not cancel the leading term `a t⁻ᵖ` either. -/
theorem not_exists_reduced_artinSchreier_representative_completion_ratFunc_ratFunc :
    ¬∃ w : (adicOfIrreducible (irreducible_X (R := RatFunc (ZMod p)))).Completion,
      algebraMap (RatFunc (ZMod p)) _ RatFunc.X /
            (adicOfIrreducible irreducible_X).completionEmbedding RatFunc.X ^ p - (w ^ p - w) ∈
          (adicOfIrreducible irreducible_X).completionPlace.integers ∨
        ((adicOfIrreducible irreducible_X).completionPlace.ord
            (algebraMap (RatFunc (ZMod p)) _ RatFunc.X /
              (adicOfIrreducible irreducible_X).completionEmbedding RatFunc.X ^ p -
                (w ^ p - w)) < 0 ∧
          ¬(p : ℤ) ∣ (adicOfIrreducible irreducible_X).completionPlace.ord
            (algebraMap (RatFunc (ZMod p)) _ RatFunc.X /
              (adicOfIrreducible irreducible_X).completionEmbedding RatFunc.X ^ p -
                (w ^ p - w))) :=
  not_exists_reduced_artinSchreier_representative_of_degree_eq_one _
    (by simp [degree_completionPlace]) (Fact.out : p.Prime).one_lt
    (RatFunc.pow_ne_X (Fact.out : p.Prime).one_lt) (by simp)

end TauCeti.Place
