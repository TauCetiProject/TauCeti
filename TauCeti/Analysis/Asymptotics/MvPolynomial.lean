/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Polynomial growth of multivariate polynomials along a filter

If every coordinate of `x : α → ι → A` is `O(u)` along a filter `l`, and `‖u‖` is eventually
bounded away from zero in the sense that `1 = O(u)`, then evaluating a polynomial `P` of total
degree at most `n` at `x` gives a function that is `O(u ^ n)`. This is the multivariate analogue
of the elementary bound `|p(x)| ≤ C |x| ^ deg p` for large `|x|`, with the variables allowed to
grow at a common rate `u` rather than being the argument itself. It is the growth input for
integrals of a polynomial against an exponentially decaying function.

## Main results

* `TauCeti.isBigO_aeval_of_totalDegree_le`: `aeval (x a) P = O(u a ^ n)` when each coordinate of
  `x` is `O(u)`, `1 = O(u)`, and `P.totalDegree ≤ n`.
-/

public section

open Asymptotics Filter MvPolynomial

namespace TauCeti

/-- **Polynomial growth of a polynomial in `O(u)` variables.** If each coordinate of `x` is `O(u)`
along `l`, and `1 = O(u)`, then `aeval (x a) P` is `O(u a ^ n)` for every `n ≥ P.totalDegree`. -/
theorem isBigO_aeval_of_totalDegree_le {α ι R A 𝕜 : Type*} [CommSemiring R]
    [SeminormedCommRing A] [Algebra R A] [NormedField 𝕜] {l : Filter α} {P : MvPolynomial ι R}
    {n : ℕ} (hP : P.totalDegree ≤ n) {x : α → ι → A} {u : α → 𝕜}
    (hx : ∀ i, (fun a ↦ x a i) =O[l] u) (hu : (fun _ ↦ (1 : ℝ)) =O[l] u) :
    (fun a ↦ aeval (x a) P) =O[l] fun a ↦ u a ^ n := by
  have hu' : (fun _ ↦ (1 : A)) =O[l] u := (isBigO_const_const _ one_ne_zero l).trans hu
  simp only [aeval_def, eval₂_eq]
  refine IsBigO.fun_sum fun d hd ↦ IsBigO.const_mul_left ?_ _
  -- each monomial has degree at most `n`; pad its exponent up to `n` using `1 = O(u)`
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le ((le_totalDegree hd).trans hP)
  simpa [Finset.prod_pow_eq_pow_sum, ← pow_add, hm, Finsupp.sum] using
    (IsBigO.finsetProd (s := d.support) fun i _ ↦ (hx i).pow (d i)).mul (hu'.pow m)

end TauCeti

end
